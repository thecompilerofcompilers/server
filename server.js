// --- START OF FILE server.js ---

try {
    require("dotenv").config();
} catch {
    // dotenv is optional on Render when environment variables are set in the dashboard
}

const http = require("http");
const https = require("https");
const fs = require("fs");
const path = require("path");
const querystring = require("querystring");
const crypto = require("crypto");
const dns = require("dns");
const net = require("net");

const parsedPort = Number(process.env.PORT);
const PORT = Number.isInteger(parsedPort) && parsedPort > 0 && parsedPort <= 65535 ? parsedPort : 8085;
const WEB_DIR = process.env.WEB_DIR ? path.resolve(process.env.WEB_DIR) : __dirname;

let DATA_DIR = process.env.DATA_DIR ? path.resolve(process.env.DATA_DIR) : WEB_DIR;
try {
    if (!fs.existsSync(DATA_DIR)) {
        fs.mkdirSync(DATA_DIR, { recursive: true });
    }
} catch (err) {
    console.warn(`[⚠️ Storage] Cannot use DATA_DIR (${DATA_DIR}): ${err.message}. Falling back to /tmp/reos-data`);
    DATA_DIR = "/tmp/reos-data";
    if (!fs.existsSync(DATA_DIR)) {
        fs.mkdirSync(DATA_DIR, { recursive: true });
    }
}

const DB_PATH = path.join(DATA_DIR, "users.json");
const CLIENTS_TXT_PATH = path.join(DATA_DIR, "clients.txt");
const EMAILS_DB = path.join(DATA_DIR, "emails.json");
const FORMS_DB = path.join(DATA_DIR, "forms.json");
const RESPONSES_DB = path.join(DATA_DIR, "form_responses.json");

const RECAPTCHA_SECRET_KEY = (process.env.RECAPTCHA_SECRET_KEY || "").trim();
const RECAPTCHA_SITE_KEY = (process.env.RECAPTCHA_SITE_KEY || "").trim();
const parsedMinScore = Number(process.env.RECAPTCHA_MIN_SCORE);
const RECAPTCHA_MIN_SCORE =
    process.env.RECAPTCHA_MIN_SCORE !== undefined &&
    process.env.RECAPTCHA_MIN_SCORE !== "" &&
    Number.isFinite(parsedMinScore)
        ? parsedMinScore
        : 0.5;
const GOOGLE_CLIENT_ID = (process.env.GOOGLE_CLIENT_ID || "").trim();
const MAX_BODY_BYTES = 2 * 1024 * 1024; // 2 MB limit
const MAX_FETCH_BYTES = 100 * 1024; // 100 KB limit for URL fetcher

const BLOCKED_STATIC_FILES = new Set([
    "users.json",
    "clients.txt",
    "emails.json",
    "forms.json",
    "form_responses.json",
    "package.json",
    "package-lock.json",
    ".env",
    path.basename(__filename).toLowerCase()
]);

const RESERVED_KEYS = new Set(["__proto__", "constructor", "prototype"]);

const authorizationCodes = new Map();
const accessTokens = new Map();

function hasOwn(obj, key) {
    return (
        Boolean(obj) &&
        typeof obj === "object" &&
        typeof key === "string" &&
        !RESERVED_KEYS.has(key) &&
        Object.prototype.hasOwnProperty.call(obj, key)
    );
}

function isSafeKey(key) {
    return typeof key === "string" && key.length > 0 && !RESERVED_KEYS.has(key);
}

function escapeHtml(str) {
    return String(str || "")
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#39;");
}

function sanitizePipeField(str) {
    return String(str || "").replace(/[\r\n|]/g, "").trim();
}

function stripWrappingQuotes(value) {
    const trimmed = String(value || "").trim();
    if (
        (trimmed.startsWith('"') && trimmed.endsWith('"')) ||
        (trimmed.startsWith("'") && trimmed.endsWith("'"))
    ) {
        return trimmed.slice(1, -1).trim();
    }
    return trimmed;
}

function isRecaptchaEnabled() {
    return Boolean(RECAPTCHA_SECRET_KEY && RECAPTCHA_SITE_KEY);
}

function pruneExpiredTokens(map) {
    const now = Date.now();
    for (const [k, v] of map.entries()) {
        if (!v || now > v.expiresAt) {
            map.delete(k);
        }
    }
}

function isValidHttpUrl(rawUrl) {
    try {
        const parsed = new URL(rawUrl);
        return parsed.protocol === "http:" || parsed.protocol === "https:";
    } catch {
        return false;
    }
}

function isRedirectUriAllowed(registeredRaw, requestedUrl) {
    if (!registeredRaw || typeof registeredRaw !== "string") return false;
    const candidates = registeredRaw.split(",").map(s => s.trim()).filter(Boolean);
    for (const candidate of candidates) {
        let regUrl;
        try {
            regUrl = new URL(candidate);
        } catch {
            continue;
        }
        if (regUrl.origin !== requestedUrl.origin) continue;
        if (regUrl.pathname === "/" || regUrl.pathname === "") {
            return true;
        }
        const normalizedRegPath = regUrl.pathname.replace(/\/+$/, "");
        const normalizedReqPath = requestedUrl.pathname.replace(/\/+$/, "");
        if (
            normalizedReqPath === normalizedRegPath ||
            normalizedReqPath.startsWith(normalizedRegPath + "/")
        ) {
            return true;
        }
    }
    return false;
}

function isPrivateIpv4(ip) {
    const parts = ip.split(".").map(Number);
    if (parts.length !== 4 || parts.some(n => !Number.isInteger(n) || n < 0 || n > 255)) {
        return true;
    }
    const [a, b, c] = parts;
    if (a === 0) return true; // 0.0.0.0/8
    if (a === 10) return true; // 10.0.0.0/8
    if (a === 100 && b >= 64 && b <= 127) return true; // 100.64.0.0/10 CGNAT
    if (a === 127) return true; // 127.0.0.0/8 loopback
    if (a === 169 && b === 254) return true; // 169.254.0.0/16 link-local & metadata
    if (a === 172 && b >= 16 && b <= 31) return true; // 172.16.0.0/12
    if (a === 192 && b === 0 && c === 0) return true; // 192.0.0.0/24
    if (a === 192 && b === 168) return true; // 192.168.0.0/16
    if (a === 198 && (b === 18 || b === 19)) return true; // 198.18.0.0/15
    if (a >= 224) return true; // multicast & reserved
    return false;
}

function isPrivateIp(ip) {
    const normalized = String(ip || "").trim().toLowerCase().split("%")[0];
    const family = net.isIP(normalized);
    if (!family) return true;
    if (family === 4) return isPrivateIpv4(normalized);

    if (normalized === "::" || normalized === "::1") return true;
    if (normalized.startsWith("::ffff:")) {
        const mapped = normalized.slice(7);
        if (net.isIP(mapped) === 4) return isPrivateIpv4(mapped);
        const hexParts = mapped.split(":");
        if (hexParts.length === 2) {
            const hi = parseInt(hexParts[0], 16);
            const lo = parseInt(hexParts[1], 16);
            if (!Number.isNaN(hi) && !Number.isNaN(lo)) {
                const v4 = `${(hi >> 8) & 255}.${hi & 255}.${(lo >> 8) & 255}.${lo & 255}`;
                return isPrivateIpv4(v4);
            }
        }
        return true;
    }
    const firstWord = parseInt(normalized.split(":")[0] || "0", 16);
    if ((firstWord & 0xfe00) === 0xfc00) return true; // fc00::/7 ULA
    if ((firstWord & 0xffc0) === 0xfe80) return true; // fe80::/10 link-local
    if ((firstWord & 0xff00) === 0xff00) return true; // ff00::/8 multicast
    return false;
}

function safeLookup(hostname, options, callback) {
    if (typeof options === "function") {
        callback = options;
        options = {};
    }
    const ipFamily = net.isIP(hostname);
    if (ipFamily) {
        if (isPrivateIp(hostname)) {
            return callback(new Error("Access to private or loopback IP addresses is blocked"));
        }
        if (options && options.all) {
            return callback(null, [{ address: hostname, family: ipFamily }]);
        }
        return callback(null, hostname, ipFamily);
    }

    dns.lookup(hostname, { all: true }, (err, addresses) => {
        if (err) return callback(err);
        if (!Array.isArray(addresses) || addresses.length === 0) {
            return callback(new Error("Host resolution returned no addresses"));
        }
        for (const entry of addresses) {
            if (isPrivateIp(entry.address)) {
                return callback(new Error("Target host resolves to a blocked private or internal IP"));
            }
        }
        if (options && options.all) {
            return callback(null, addresses);
        }
        return callback(null, addresses[0].address, addresses[0].family);
    });
}

function getGeminiApiKey() {
    const candidates = [
        process.env.GEMINI_API_KEY,
        process.env.GOOGLE_API_KEY,
        process.env.VERTEX_API_KEY,
        process.env.GEMINI_AUTH_KEY
    ];
    for (const candidate of candidates) {
        const cleaned = stripWrappingQuotes(candidate);
        if (cleaned) return cleaned;
    }
    return "";
}

function extractGeminiRestText(data) {
    const parts = data?.candidates?.[0]?.content?.parts;
    if (!Array.isArray(parts)) return "";
    const answer = parts
        .filter(part => part && typeof part.text === "string" && !part.thought)
        .map(part => part.text)
        .join("");
    if (answer) return answer;
    return parts
        .filter(part => part && typeof part.text === "string")
        .map(part => part.text)
        .join("");
}

function isSurfaceOrAuthError(err) {
    const status = Number(err?.status || err?.code);
    const msg = String(err?.message || "");
    const lowerMsg = msg.toLowerCase();
    const apiStatus = String(err?.apiStatus || "");
    return (
        status === 401 ||
        status === 403 ||
        (status === 400 && (msg.includes("API_KEY_INVALID") || lowerMsg.includes("api key not valid"))) ||
        apiStatus === "UNAUTHENTICATED" ||
        apiStatus === "PERMISSION_DENIED" ||
        msg.includes("API_KEY_INVALID") ||
        msg.includes("API_KEY_SERVICE_BLOCKED") ||
        msg.includes("ACCESS_TOKEN_TYPE_UNSUPPORTED") ||
        msg.includes("UNAUTHENTICATED") ||
        msg.includes("PERMISSION_DENIED")
    );
}

function generateGeminiReplyRest({ apiKey, model, prompt, useVertexExpress }) {
    const hostname = useVertexExpress ? "aiplatform.googleapis.com" : "generativelanguage.googleapis.com";
    const apiPath = useVertexExpress
        ? `/v1/publishers/google/models/${encodeURIComponent(model)}:generateContent`
        : `/v1beta/models/${encodeURIComponent(model)}:generateContent`;

    const payload = JSON.stringify({
        contents: [{ role: "user", parts: [{ text: prompt }] }]
    });

    return new Promise((resolve, reject) => {
        let settled = false;
        const done = (fn, val) => {
            if (settled) return;
            settled = true;
            fn(val);
        };

        const apiReq = https.request(
            {
                hostname,
                path: apiPath,
                method: "POST",
                headers: {
                    "Content-Type": "application/json",
                    "Content-Length": Buffer.byteLength(payload),
                    "x-goog-api-key": apiKey
                }
            },
            (apiRes) => {
                let raw = "";
                apiRes.on("data", (chunk) => { raw += chunk; });
                apiRes.on("end", () => {
                    let parsed = {};
                    try {
                        parsed = JSON.parse(raw || "{}");
                    } catch {
                        // ignore non-JSON body
                    }

                    if (apiRes.statusCode >= 200 && apiRes.statusCode < 300) {
                        return done(resolve, extractGeminiRestText(parsed));
                    }

                    const errInfo = parsed?.error || {};
                    const err = new Error(errInfo.message || `Gemini API HTTP ${apiRes.statusCode}`);
                    err.status = apiRes.statusCode;
                    err.code = errInfo.code || apiRes.statusCode;
                    err.apiStatus = errInfo.status || "";
                    err.details = errInfo.details || [];
                    done(reject, err);
                });
            }
        );

        apiReq.setTimeout(30000, () => {
            apiReq.destroy(new Error("Gemini API request timeout"));
        });

        apiReq.on("error", (err) => done(reject, err));
        apiReq.write(payload);
        apiReq.end();
    });
}

async function callGeminiSurface({ apiKey, model, prompt, useVertexExpress }) {
    try {
        const { GoogleGenAI } = require("@google/genai");
        const ai = new GoogleGenAI({
            vertexai: Boolean(useVertexExpress),
            apiKey
        });
        const response = await ai.models.generateContent({
            model,
            contents: prompt
        });
        return response?.text ?? "";
    } catch (sdkErr) {
        if (
            sdkErr?.code === "MODULE_NOT_FOUND" ||
            sdkErr instanceof TypeError ||
            isSurfaceOrAuthError(sdkErr)
        ) {
            return await generateGeminiReplyRest({ apiKey, model, prompt, useVertexExpress });
        }
        throw sdkErr;
    }
}

async function generateGeminiReply(prompt) {
    const apiKey = getGeminiApiKey();
    if (!apiKey) {
        const err = new Error("Missing GEMINI_API_KEY (or GOOGLE_API_KEY / VERTEX_API_KEY).");
        err.status = 500;
        throw err;
    }

    const model = process.env.GEMINI_MODEL || "gemini-4-hydrogen";
    const useVertexEnv = (
        process.env.GOOGLE_GENAI_USE_VERTEXAI ||
        process.env.GOOGLE_GENAI_USE_ENTERPRISE ||
        ""
    ).trim().toLowerCase();

    if (useVertexEnv === "true") {
        return await callGeminiSurface({ apiKey, model, prompt, useVertexExpress: true });
    }
    if (useVertexEnv === "false") {
        return await callGeminiSurface({ apiKey, model, prompt, useVertexExpress: false });
    }

    const preferVertexFirst =
        !process.env.GEMINI_API_KEY &&
        !process.env.GOOGLE_API_KEY &&
        Boolean(process.env.VERTEX_API_KEY);

    try {
        return await callGeminiSurface({ apiKey, model, prompt, useVertexExpress: preferVertexFirst });
    } catch (firstErr) {
        if (isSurfaceOrAuthError(firstErr) && (apiKey.startsWith("AQ.") || process.env.VERTEX_API_KEY)) {
            return await callGeminiSurface({ apiKey, model, prompt, useVertexExpress: !preferVertexFirst });
        }
        throw firstErr;
    }
}

function sendJson(res, statusCode, payload, extraHeaders = {}) {
    if (res.headersSent) return;
    res.writeHead(statusCode, { "Content-Type": "application/json", ...extraHeaders });
    res.end(JSON.stringify(payload));
}

function sendHtml(res, statusCode, html, extraHeaders = {}) {
    if (res.headersSent) return;
    res.writeHead(statusCode, { "Content-Type": "text/html", ...extraHeaders });
    res.end(html);
}

function readBody(req, maxBytes = MAX_BODY_BYTES) {
    return new Promise((resolve, reject) => {
        const chunks = [];
        let totalBytes = 0;
        let settled = false;

        req.on("data", (chunk) => {
            if (settled) return;
            totalBytes += chunk.length;
            if (totalBytes > maxBytes) {
                settled = true;
                const err = new Error("Payload Too Large");
                err.statusCode = 413;
                reject(err);
                req.destroy();
                return;
            }
            chunks.push(chunk);
        });

        req.on("end", () => {
            if (settled) return;
            settled = true;
            resolve(Buffer.concat(chunks).toString("utf8"));
        });

        req.on("error", (err) => {
            if (settled) return;
            settled = true;
            reject(err);
        });
    });
}

function parseFormOrJson(req, body) {
    const contentType = (req.headers["content-type"] || "").toLowerCase();
    if (contentType.includes("application/json")) {
        const parsed = JSON.parse(body || "{}");
        return parsed && typeof parsed === "object" && !Array.isArray(parsed) ? parsed : {};
    }
    return querystring.parse(body);
}

function getClientIp(req) {
    const forwarded = req.headers["x-forwarded-for"];
    let ip = "";
    if (typeof forwarded === "string" && forwarded.length > 0) {
        ip = forwarded.split(",")[0].trim();
    } else {
        ip = req.socket?.remoteAddress || "";
    }
    return ip.startsWith("::ffff:") ? ip.slice(7) : ip;
}

function verifyRecaptcha(token, remoteIp) {
    if (!isRecaptchaEnabled()) {
        if (RECAPTCHA_SECRET_KEY && !RECAPTCHA_SITE_KEY) {
            console.warn("[⚠️ reCAPTCHA] RECAPTCHA_SITE_KEY is not set; skipping verification.");
        }
        return Promise.resolve({ success: true, skipped: true });
    }

    if (!token || typeof token !== "string") {
        return Promise.resolve({ success: false, reason: "Please complete the Google reCAPTCHA challenge." });
    }

    const postData = querystring.stringify({
        secret: RECAPTCHA_SECRET_KEY,
        response: token.trim(),
        remoteip: remoteIp || ""
    });

    return new Promise((resolve) => {
        let settled = false;
        const finish = (result) => {
            if (settled) return;
            settled = true;
            resolve(result);
        };

        const options = {
            hostname: "www.google.com",
            path: "/recaptcha/api/siteverify",
            method: "POST",
            headers: {
                "Content-Type": "application/x-www-form-urlencoded",
                "Content-Length": Buffer.byteLength(postData)
            }
        };

        const verifyReq = https.request(options, (verifyRes) => {
            let raw = "";
            verifyRes.on("data", (chunk) => { raw += chunk; });
            verifyRes.on("end", () => {
                try {
                    const data = JSON.parse(raw || "{}");
                    if (!data.success) {
                        const codes = Array.isArray(data["error-codes"]) ? data["error-codes"].join(", ") : "verification_failed";
                        return finish({ success: false, reason: `reCAPTCHA failed (${codes})` });
                    }
                    if (typeof data.score === "number" && data.score < RECAPTCHA_MIN_SCORE) {
                        return finish({ success: false, reason: "Suspicious activity detected by reCAPTCHA." });
                    }
                    return finish({ success: true, score: data.score });
                } catch {
                    return finish({ success: false, reason: "Invalid response from Google reCAPTCHA." });
                }
            });
        });

        verifyReq.setTimeout(10000, () => {
            verifyReq.destroy(new Error("reCAPTCHA verification timeout"));
        });

        verifyReq.on("error", (err) => {
            console.error("[⚠️ reCAPTCHA] Network error:", err.message);
            finish({ success: false, reason: "Unable to reach Google reCAPTCHA service." });
        });

        verifyReq.write(postData);
        verifyReq.end();
    });
}

function atomicWriteFileSync(filePath, content) {
    const tmpPath = `${filePath}.${process.pid}.${crypto.randomBytes(4).toString("hex")}.tmp`;
    fs.writeFileSync(tmpPath, content, "utf8");
    fs.renameSync(tmpPath, filePath);
}

function readJsonDb(filePath) {
    const target = Object.create(null);
    if (!fs.existsSync(filePath)) return target;
    try {
        const parsed = JSON.parse(fs.readFileSync(filePath, "utf8") || "{}");
        if (!parsed || typeof parsed !== "object" || Array.isArray(parsed)) {
            return target;
        }
        for (const [k, v] of Object.entries(parsed)) {
            if (!RESERVED_KEYS.has(k)) {
                target[k] = v;
            }
        }
        return target;
    } catch {
        return target;
    }
}

function writeJsonDb(filePath, data) {
    const clean = {};
    if (data && typeof data === "object") {
        for (const [k, v] of Object.entries(data)) {
            if (!RESERVED_KEYS.has(k)) {
                clean[k] = v;
            }
        }
    }
    atomicWriteFileSync(filePath, JSON.stringify(clean, null, 4));
}

function ensureUsersDbSeeded() {
    if (!fs.existsSync(DB_PATH) || fs.readFileSync(DB_PATH, "utf8").trim() === "") {
        writeJsonDb(DB_PATH, {
            reos_user: {
                password: "password123",
                picture: "https://ui-avatars.com/api/?name=reos_user&background=2563eb&color=fff",
                type: "reos"
            }
        });
    }
}

function getEmailsDb() {
    return readJsonDb(EMAILS_DB);
}

function getClientsFromTxt() {
    const clients = Object.create(null);
    try {
        if (fs.existsSync(CLIENTS_TXT_PATH)) {
            const fileContent = fs.readFileSync(CLIENTS_TXT_PATH, "utf8");
            const lines = fileContent.split(/\r?\n/);
            for (let line of lines) {
                line = line.trim();
                if (line && !line.startsWith("#")) {
                    const parts = line.split("|");
                    if (parts.length >= 3) {
                        const cId = parts[0].trim();
                        const cSecret = parts[1].trim();
                        const cRedirect = parts[2].trim();
                        const cOwner = parts[3] ? parts[3].trim() : "system";
                        if (isSafeKey(cId)) {
                            clients[cId] = { secret: cSecret, redirectUri: cRedirect, owner: cOwner };
                        }
                    }
                }
            }
        } else {
            const defaultData = "sample_app_id|sample_app_secret|https://jwt.io|system\ngoogle_client_id|google_secret_key_123|https://www.google.com|system\n";
            atomicWriteFileSync(CLIENTS_TXT_PATH, defaultData);
            clients["sample_app_id"] = { secret: "sample_app_secret", redirectUri: "https://jwt.io", owner: "system" };
            clients["google_client_id"] = { secret: "google_secret_key_123", redirectUri: "https://www.google.com", owner: "system" };
        }
    } catch (err) {
        console.error("Failed reading/initializing clients.txt:", err);
    }
    return clients;
}

function saveClientsToTxt(clientsObj) {
    const lines = [];
    for (const [id, data] of Object.entries(clientsObj)) {
        const cleanId = sanitizePipeField(id);
        if (!cleanId) continue;
        lines.push(`${cleanId}|${sanitizePipeField(data.secret)}|${sanitizePipeField(data.redirectUri)}|${sanitizePipeField(data.owner || "system")}`);
    }
    atomicWriteFileSync(CLIENTS_TXT_PATH, lines.join("\n") + "\n");
}

async function handleAuthWorkflow(formData, res, req) {
    const action = formData.auth_action === "register" ? "register" : "login";
    const userIn = typeof formData.username === "string" ? formData.username.trim() : "";
    const passIn = typeof formData.password === "string" ? formData.password.trim() : "";
    const recaptchaToken =
        (typeof formData["g-recaptcha-response"] === "string" && formData["g-recaptcha-response"]) ||
        (typeof formData.recaptcha_token === "string" && formData.recaptcha_token) ||
        "";

    if (!userIn || !passIn || !isSafeKey(userIn)) {
        return sendHtml(res, 400, "<h3>Username and Password are required.</h3><a href=\"/login.html\">Back to Login</a>");
    }

    const remoteIp = getClientIp(req);
    const result = await verifyRecaptcha(recaptchaToken, remoteIp);

    if (!result.success) {
        return sendHtml(
            res,
            403,
            `<h3>Access Blocked</h3><p>[reCAPTCHA] ${escapeHtml(result.reason)}</p><a href="/login.html">Try Again</a>`
        );
    }

    ensureUsersDbSeeded();

    const users = readJsonDb(DB_PATH);
    const defaultPic = "https://ui-avatars.com/api/?name=" + encodeURIComponent(userIn) + "&background=2563eb&color=fff";

    if (action === "register") {
        if (hasOwn(users, userIn)) {
            return sendHtml(res, 400, "<h3>Username already registered!</h3><a href=\"/login.html\">Try Another</a>");
        }

        users[userIn] = { password: passIn, picture: defaultPic, type: "reos" };
        writeJsonDb(DB_PATH, users);

        const redirectUrl = `/pg2.html?user=${encodeURIComponent(userIn)}&pic=${encodeURIComponent(defaultPic)}`;
        res.writeHead(302, {
            "Location": redirectUrl,
            "Set-Cookie": `session=${encodeURIComponent(userIn)}; Path=/; HttpOnly; SameSite=Lax`
        });
        return res.end();
    } else {
        const storedUser = hasOwn(users, userIn) ? users[userIn] : null;
        const storedPass = storedUser && typeof storedUser === "object" ? storedUser.password : storedUser;
        const userPic = storedUser && typeof storedUser === "object" && storedUser.picture ? storedUser.picture : defaultPic;

        if (storedUser && typeof storedPass === "string" && storedPass.length > 0 && storedPass === passIn) {
            const redirectUrl = `/pg2.html?user=${encodeURIComponent(userIn)}&pic=${encodeURIComponent(userPic)}`;
            res.writeHead(302, {
                "Location": redirectUrl,
                "Set-Cookie": `session=${encodeURIComponent(userIn)}; Path=/; HttpOnly; SameSite=Lax`
            });
            return res.end();
        } else {
            return sendHtml(res, 401, "<h3>Access Denied</h3><p>Invalid credentials or user not registered.</p><a href=\"/login.html\">Back to Login</a>");
        }
    }
}

async function handleDeleteAccount(req, res) {
    try {
        const body = await readBody(req);
        const { username, password } = JSON.parse(body || "{}");
        const cleanUser = typeof username === "string" ? username.trim() : "";

        if (!cleanUser || !isSafeKey(cleanUser)) {
            return sendJson(res, 400, { success: false, message: "Username is required." });
        }

        if (!fs.existsSync(DB_PATH)) {
            return sendJson(res, 404, { success: false, message: "Account not found." });
        }

        const users = readJsonDb(DB_PATH);
        const targetKey = hasOwn(users, cleanUser)
            ? cleanUser
            : Object.keys(users).find(k => k.trim().toLowerCase() === cleanUser.toLowerCase());

        if (!targetKey || !hasOwn(users, targetKey)) {
            return sendJson(res, 404, { success: false, message: "Account not found." });
        }

        const storedUser = users[targetKey];
        const storedPass = storedUser && typeof storedUser === "object" ? storedUser.password : storedUser;
        const isStoredGoogleAccount =
            Boolean(storedUser && typeof storedUser === "object" && storedUser.type === "google" && !storedPass);

        if (!isStoredGoogleAccount) {
            if (typeof password !== "string" || !password) {
                return sendJson(res, 400, { success: false, message: "Password is required for Reos accounts." });
            }
            if (typeof storedPass !== "string" || !storedPass || storedPass !== password) {
                return sendJson(res, 401, { success: false, message: "Invalid username or password." });
            }
        }

        delete users[targetKey];
        writeJsonDb(DB_PATH, users);

        const clients = getClientsFromTxt();
        let clientsUpdated = false;
        for (const [id, data] of Object.entries(clients)) {
            if (data.owner && data.owner.trim().toLowerCase() === targetKey.trim().toLowerCase()) {
                delete clients[id];
                clientsUpdated = true;
            }
        }
        if (clientsUpdated) {
            saveClientsToTxt(clients);
        }

        return sendJson(res, 200, { success: true, message: "Account deleted successfully from disk." });
    } catch (err) {
        console.error("Delete Error:", err);
        const status = err.statusCode || (err instanceof SyntaxError ? 400 : 500);
        return sendJson(res, status, {
            success: false,
            message: status === 413 ? "Request too large." : status === 400 ? "Invalid JSON body." : "Server error during account deletion."
        });
    }
}

async function handleRequest(req, res) {
    res.setHeader("Access-Control-Allow-Origin", "*");
    res.setHeader("Access-Control-Allow-Methods", "GET, POST, HEAD, OPTIONS");
    res.setHeader("Access-Control-Allow-Headers", "Content-Type, Authorization");

    if (req.method === "OPTIONS") {
        res.writeHead(204);
        return res.end();
    }

    const rawUrl = req.url || "/";
    const qIndex = rawUrl.indexOf("?");
    const rawPath = qIndex === -1 ? rawUrl : rawUrl.slice(0, qIndex);
    const queryString = qIndex === -1 ? "" : rawUrl.slice(qIndex + 1);

    let parsedUrl;
    try {
        parsedUrl = decodeURIComponent(rawPath);
    } catch {
        res.writeHead(400, { "Content-Type": "text/plain" });
        return res.end("400 Bad Request");
    }

    const queryParams = querystring.parse(queryString);

    // Render Health Check (supports GET and HEAD)
    if (parsedUrl === "/healthz" && (req.method === "GET" || req.method === "HEAD")) {
        res.writeHead(200, { "Content-Type": "application/json" });
        return res.end(req.method === "HEAD" ? undefined : JSON.stringify({ status: "ok" }));
    }

    // --- GOOGLE RECAPTCHA CONFIG ENDPOINT ---
    if (parsedUrl === "/api/recaptcha/config" && req.method === "GET") {
        return sendJson(res, 200, {
            enabled: isRecaptchaEnabled(),
            siteKey: RECAPTCHA_SITE_KEY
        });
    }

    // --- OAUTH 2.0 ENDPOINTS ---
    if (parsedUrl === "/oauth/authorize" || parsedUrl === "/oauth/auth") {
        if (req.method !== "GET" && req.method !== "POST") {
            return sendHtml(res, 405, "<h3>Method Not Allowed</h3>");
        }

        const clientId = typeof queryParams.client_id === "string" ? queryParams.client_id.trim() : "";
        const redirectUri = typeof queryParams.redirect_uri === "string" ? queryParams.redirect_uri.trim() : "";
        const state = typeof queryParams.state === "string" ? queryParams.state : "";

        if (!clientId || !redirectUri) {
            return sendHtml(res, 400, "<h3>Missing required OAuth parameters: client_id and redirect_uri.</h3>");
        }

        let validatedRedirectUrl;
        try {
            validatedRedirectUrl = new URL(redirectUri);
            if (!["http:", "https:"].includes(validatedRedirectUrl.protocol)) {
                return sendHtml(res, 400, "<h3>Invalid redirect_uri protocol.</h3>");
            }
        } catch {
            return sendHtml(res, 400, "<h3>Invalid redirect_uri format.</h3>");
        }

        const clients = getClientsFromTxt();
        const client = hasOwn(clients, clientId) ? clients[clientId] : null;

        if (!client) {
            return sendHtml(res, 400, "<h3>Invalid Client ID</h3>");
        }

        if (!isRedirectUriAllowed(client.redirectUri, validatedRedirectUrl)) {
            return sendHtml(res, 400, "<h3>Mismatching or unauthorized redirect_uri.</h3>");
        }

        if (req.method === "POST") {
            const body = await readBody(req);
            const formData = querystring.parse(body);
            const username = typeof formData.username === "string" ? formData.username.trim() : "";
            const password = typeof formData.password === "string" ? formData.password.trim() : "";

            if (isRecaptchaEnabled()) {
                const captchaToken = typeof formData["g-recaptcha-response"] === "string" ? formData["g-recaptcha-response"] : "";
                const captchaResult = await verifyRecaptcha(captchaToken, getClientIp(req));
                if (!captchaResult.success) {
                    return sendHtml(res, 403, `<script>alert(${JSON.stringify(captchaResult.reason)});window.history.back();</script>`);
                }
            }

            ensureUsersDbSeeded();
            const users = readJsonDb(DB_PATH);
            const storedUser = hasOwn(users, username) ? users[username] : null;
            const storedPass = storedUser && typeof storedUser === "object" ? storedUser.password : storedUser;

            if (!storedUser || typeof storedPass !== "string" || !storedPass || storedPass !== password) {
                return sendHtml(res, 401, `<script>alert("Invalid username or password. Please try again.");window.history.back();</script>`);
            }

            pruneExpiredTokens(authorizationCodes);
            const authCode = crypto.randomBytes(16).toString("hex");
            authorizationCodes.set(authCode, {
                clientId,
                redirectUri,
                user: username,
                expiresAt: Date.now() + 600000
            });

            validatedRedirectUrl.searchParams.set("code", authCode);
            if (state) validatedRedirectUrl.searchParams.set("state", state);

            res.writeHead(302, { "Location": validatedRedirectUrl.toString() });
            return res.end();
        }

        const useRecaptchaWidget = isRecaptchaEnabled();
        const recaptchaScript = useRecaptchaWidget ? '<script src="https://www.google.com/recaptcha/api.js" async defer></script>' : "";
        const recaptchaWidget = useRecaptchaWidget
            ? `<div class="g-recaptcha" data-sitekey="${escapeHtml(RECAPTCHA_SITE_KEY)}" data-theme="dark" style="margin-bottom:16px;"></div>`
            : "";

        return sendHtml(res, 200, `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Sign in with Reos Account</title>
    ${recaptchaScript}
    <style>
        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; background: #0f172a; color: #f8fafc; display: flex; justify-content: center; align-items: center; height: 100vh; margin: 0; }
        .login-card { background: #1e293b; padding: 32px; border-radius: 12px; width: 100%; max-width: 380px; box-shadow: 0 10px 25px rgba(0,0,0,0.3); border: 1px solid #334155; }
        .logo { font-size: 24px; font-weight: bold; color: #3b82f6; text-align: center; margin-bottom: 8px; }
        .subtitle { font-size: 14px; color: #94a3b8; text-align: center; margin-bottom: 24px; }
        .app-info { background: #0f172a; padding: 12px; border-radius: 8px; font-size: 13px; color: #cbd5e1; margin-bottom: 20px; border-left: 4px solid #3b82f6; }
        label { font-size: 12px; font-weight: 600; text-transform: uppercase; color: #94a3b8; display: block; margin-bottom: 6px; }
        input { width: 100%; padding: 10px; margin-bottom: 16px; border: 1px solid #475569; background: #0f172a; color: #fff; border-radius: 6px; box-sizing: border-box; }
        input:focus { border-color: #3b82f6; outline: none; }
        button { width: 100%; background: #2563eb; color: white; border: none; padding: 12px; border-radius: 6px; font-weight: 600; cursor: pointer; font-size: 14px; }
        button:hover { background: #1d4ed8; }
        .footer { font-size: 11px; color: #64748b; text-align: center; margin-top: 20px; }
    </style>
</head>
<body>
    <div class="login-card">
        <div class="logo">Reos Security</div>
        <div class="subtitle">OAuth 2.0 Identity Service</div>
        <div class="app-info"><strong>${escapeHtml(clientId)}</strong> requests access to your Reos Account.</div>
        <form method="POST" action="${escapeHtml(`/oauth/authorize?client_id=${encodeURIComponent(clientId)}&redirect_uri=${encodeURIComponent(redirectUri)}&state=${encodeURIComponent(state)}`)}">
            <label>Username</label>
            <input type="text" name="username" placeholder="Enter Reos Username" required autocomplete="username">
            <label>Password</label>
            <input type="password" name="password" placeholder="Enter Password" required autocomplete="current-password">
            ${recaptchaWidget}
            <button type="submit">Authorize & Continue</button>
        </form>
        <div class="footer">Protected by Google reCAPTCHA</div>
    </div>
</body>
</html>`);
    }

    if (parsedUrl === "/oauth/token" && req.method === "POST") {
        const body = await readBody(req);
        const params = querystring.parse(body);
        const grantType = params.grant_type;
        const clientId = typeof params.client_id === "string" ? params.client_id : "";
        const clientSecret = params.client_secret;

        const clients = getClientsFromTxt();
        const client = hasOwn(clients, clientId) ? clients[clientId] : null;

        if (!client || client.secret !== clientSecret) {
            return sendJson(res, 401, { error: "invalid_client", error_description: "Invalid client credentials." });
        }

        let tokenUser = client.owner || "system";

        if (grantType === "authorization_code") {
            const code = typeof params.code === "string" ? params.code : "";
            const authData = authorizationCodes.get(code);

            if (
                !authData ||
                authData.clientId !== clientId ||
                Date.now() > authData.expiresAt ||
                (typeof params.redirect_uri === "string" && params.redirect_uri && params.redirect_uri !== authData.redirectUri)
            ) {
                if (authData && Date.now() > authData.expiresAt) {
                    authorizationCodes.delete(code);
                }
                return sendJson(res, 400, { error: "invalid_grant", error_description: "Invalid or expired authorization code." });
            }

            tokenUser = authData.user || tokenUser;
            authorizationCodes.delete(code);
        } else if (grantType !== "client_credentials") {
            return sendJson(res, 400, { error: "unsupported_grant_type", error_description: "Grant type not supported." });
        }

        pruneExpiredTokens(accessTokens);
        const token = crypto.randomBytes(24).toString("hex");
        const expiresIn = 3600;
        accessTokens.set(token, {
            user: tokenUser,
            clientId,
            expiresAt: Date.now() + expiresIn * 1000
        });

        return sendJson(res, 200, {
            access_token: token,
            token_type: "Bearer",
            expires_in: expiresIn
        });
    }

    if (parsedUrl === "/oauth/userinfo" && (req.method === "GET" || req.method === "POST")) {
        const authHeader = req.headers["authorization"];
        if (!authHeader || !authHeader.startsWith("Bearer ")) {
            return sendJson(res, 401, { error: "unauthorized" });
        }

        const token = authHeader.slice("Bearer ".length).trim();
        const tokenData = accessTokens.get(token);
        if (!tokenData || Date.now() > tokenData.expiresAt) {
            if (tokenData) accessTokens.delete(token);
            return sendJson(res, 401, { error: "invalid_token" });
        }

        const users = readJsonDb(DB_PATH);
        const userRecord = hasOwn(users, tokenData.user) ? users[tokenData.user] : null;
        const email = tokenData.user.includes("@") ? tokenData.user : `${tokenData.user}@reos.internal`;

        return sendJson(res, 200, {
            sub: tokenData.user,
            name: tokenData.user,
            email,
            picture: userRecord && typeof userRecord === "object" ? userRecord.picture || "" : ""
        });
    }

    // --- REOS EMAIL SERVICE ENDPOINTS ---
    if (parsedUrl === "/api/email/create" && req.method === "POST") {
        try {
            const body = await readBody(req);
            const { username, emailPrefix } = JSON.parse(body || "{}");
            if (typeof username !== "string" || typeof emailPrefix !== "string") {
                return sendJson(res, 400, { success: false, message: "Missing username or emailPrefix." });
            }

            const cleanUser = username.trim();
            let cleanPrefix = emailPrefix.trim().toLowerCase();
            if (cleanPrefix.endsWith("@reostech")) {
                cleanPrefix = cleanPrefix.slice(0, -"@reostech".length);
            }

            if (!cleanUser || !cleanPrefix || !/^[a-z0-9._-]+$/i.test(cleanPrefix)) {
                return sendJson(res, 400, { success: false, message: "Invalid username or email prefix." });
            }

            const cleanEmail = `${cleanPrefix}@reostech`;
            const db = getEmailsDb();

            if (hasOwn(db, cleanEmail)) {
                return sendJson(res, 400, { success: false, message: "This @reostech email address is already taken." });
            }

            db[cleanEmail] = {
                email: cleanEmail,
                owner: cleanUser,
                createdAt: new Date().toISOString(),
                inbox: []
            };

            writeJsonDb(EMAILS_DB, db);
            return sendJson(res, 200, { success: true, email: cleanEmail });
        } catch (err) {
            const status = err.statusCode || (err instanceof SyntaxError ? 400 : 500);
            return sendJson(res, status, { success: false, message: status === 413 ? "Request too large." : "Server error parsing request." });
        }
    }

    if (parsedUrl === "/api/email/list" && req.method === "GET") {
        const currentUser = typeof queryParams.user === "string" ? queryParams.user.trim() : "";
        if (!currentUser) {
            return sendJson(res, 400, { success: false, message: "Missing ?user= parameter." });
        }

        const db = getEmailsDb();
        const userEmails = Object.values(db).filter(e => e && e.owner && e.owner.toLowerCase() === currentUser.toLowerCase());
        return sendJson(res, 200, { success: true, emails: userEmails });
    }

    if (parsedUrl === "/api/email/send" && req.method === "POST") {
        try {
            const body = await readBody(req);
            const { recipient, sender, subject, message } = JSON.parse(body || "{}");
            const cleanRecipient = typeof recipient === "string" ? recipient.trim().toLowerCase() : "";
            const db = getEmailsDb();

            if (!cleanRecipient || !hasOwn(db, cleanRecipient) || !Array.isArray(db[cleanRecipient].inbox)) {
                return sendJson(res, 404, { success: false, message: "Recipient @reostech address does not exist." });
            }

            db[cleanRecipient].inbox.push({
                id: "msg_" + Math.random().toString(36).slice(2, 11),
                sender: typeof sender === "string" && sender.trim() ? sender.trim() : "Anonymous",
                subject: typeof subject === "string" && subject.trim() ? subject.trim() : "No Subject",
                message: typeof message === "string" ? message : String(message || ""),
                receivedAt: new Date().toISOString()
            });

            writeJsonDb(EMAILS_DB, db);
            return sendJson(res, 200, { success: true, message: "Email sent successfully!" });
        } catch (err) {
            const status = err.statusCode || (err instanceof SyntaxError ? 400 : 500);
            return sendJson(res, status, { success: false, message: status === 413 ? "Request too large." : "Failed to send email." });
        }
    }

    // --- REOS FORMS SYSTEM ENDPOINTS ---
    if (parsedUrl === "/api/forms/save" && req.method === "POST") {
        try {
            const body = await readBody(req);
            const formData = JSON.parse(body || "{}");
            const { id, userId, title, description, fields } = formData;
            const cleanId = typeof id === "string" ? id.trim() : "";
            const cleanUserId = typeof userId === "string" ? userId.trim() : "";

            if (!cleanId || !isSafeKey(cleanId) || !cleanUserId || !Array.isArray(fields)) {
                return sendJson(res, 400, { success: false, message: "Missing required form fields or userId." });
            }

            const forms = readJsonDb(FORMS_DB);
            if (hasOwn(forms, cleanId) && forms[cleanId].userId) {
                if (forms[cleanId].userId.toLowerCase() !== cleanUserId.toLowerCase()) {
                    return sendJson(res, 403, { success: false, message: "Unauthorized: You do not own this form." });
                }
            }

            forms[cleanId] = {
                id: cleanId,
                userId: cleanUserId,
                title: typeof title === "string" && title.trim() ? title.trim() : "Untitled Form",
                description: typeof description === "string" ? description : "",
                fields,
                updatedAt: new Date().toISOString()
            };

            writeJsonDb(FORMS_DB, forms);
            return sendJson(res, 200, { success: true, form: forms[cleanId], message: "Form saved successfully!" });
        } catch (err) {
            const status = err.statusCode || (err instanceof SyntaxError ? 400 : 500);
            return sendJson(res, status, { success: false, message: status === 413 ? "Request too large." : "Error saving form schema." });
        }
    }

    if (parsedUrl.startsWith("/api/forms/get/") && req.method === "GET") {
        const formId = parsedUrl.slice("/api/forms/get/".length).trim();
        const forms = readJsonDb(FORMS_DB);

        if (formId && hasOwn(forms, formId)) {
            return sendJson(res, 200, { success: true, form: forms[formId] });
        }
        return sendJson(res, 404, { success: false, message: "Form not found." });
    }

    if (parsedUrl.startsWith("/api/forms/submit/") && req.method === "POST") {
        const formId = parsedUrl.slice("/api/forms/submit/".length).trim();
        try {
            const body = await readBody(req);
            const submissionData = JSON.parse(body || "{}");
            const formsDb = readJsonDb(FORMS_DB);
            const targetForm = formId && hasOwn(formsDb, formId) ? formsDb[formId] : null;

            if (!targetForm) {
                return sendJson(res, 404, { success: false, message: "Form not found." });
            }

            const responsesDb = readJsonDb(RESPONSES_DB);
            if (!hasOwn(responsesDb, formId) || !Array.isArray(responsesDb[formId])) {
                responsesDb[formId] = [];
            }

            const answers = submissionData && typeof submissionData.answers === "object" && submissionData.answers ? submissionData.answers : {};
            responsesDb[formId].push({
                submissionId: "sub_" + Math.random().toString(36).slice(2, 11),
                submittedAt: new Date().toISOString(),
                answers
            });
            writeJsonDb(RESPONSES_DB, responsesDb);

            if (targetForm.userId) {
                const emailsDb = getEmailsDb();
                const ownerEmailKey = Object.keys(emailsDb).find(
                    key => emailsDb[key] && emailsDb[key].owner && emailsDb[key].owner.toLowerCase() === targetForm.userId.toLowerCase()
                );

                if (ownerEmailKey && Array.isArray(emailsDb[ownerEmailKey].inbox)) {
                    let answerSummary = "";
                    if (Array.isArray(targetForm.fields)) {
                        targetForm.fields.forEach(f => {
                            let ans = answers[f.id];
                            if (Array.isArray(ans)) ans = ans.join(", ");
                            answerSummary += `- ${f.label}: ${ans || "No answer"}\n`;
                        });
                    }

                    emailsDb[ownerEmailKey].inbox.push({
                        id: "msg_" + Math.random().toString(36).slice(2, 11),
                        sender: "notifications@reostech",
                        subject: `New Submission: ${targetForm.title}`,
                        message: `You received a new response for your form "${targetForm.title}".\n\nSubmitted Answers:\n${answerSummary}`,
                        receivedAt: new Date().toISOString()
                    });
                    writeJsonDb(EMAILS_DB, emailsDb);
                }
            }

            return sendJson(res, 201, { success: true, message: "Response recorded successfully!" });
        } catch (err) {
            const status = err.statusCode || (err instanceof SyntaxError ? 400 : 500);
            return sendJson(res, status, { success: false, message: status === 413 ? "Request too large." : "Error recording submission." });
        }
    }

    if (parsedUrl.startsWith("/api/forms/responses/") && req.method === "GET") {
        const formId = parsedUrl.slice("/api/forms/responses/".length).trim();
        const currentUser = typeof queryParams.user === "string" ? queryParams.user.trim() : "";

        const forms = readJsonDb(FORMS_DB);
        const form = formId && hasOwn(forms, formId) ? forms[formId] : null;

        if (!form) {
            return sendJson(res, 404, { success: false, message: "Form not found." });
        }
        if (!currentUser || !form.userId || form.userId.toLowerCase() !== currentUser.toLowerCase()) {
            return sendJson(res, 403, { success: false, message: "Unauthorized: You do not own this form." });
        }

        const responsesDb = readJsonDb(RESPONSES_DB);
        const submissions = hasOwn(responsesDb, formId) && Array.isArray(responsesDb[formId]) ? responsesDb[formId] : [];
        return sendJson(res, 200, { success: true, form, submissions });
    }

    // --- GEMINI AI CHAT (supports AQ. auth keys for AI Studio & Vertex Express Mode) ---
    if (parsedUrl === "/api/chat" && req.method === "POST") {
        const body = await readBody(req);
        let userPrompt = "";
        if ((req.headers["content-type"] || "").toLowerCase().includes("application/json")) {
            try {
                const parsed = JSON.parse(body || "{}");
                userPrompt = typeof parsed?.message === "string" ? parsed.message.trim() : "";
            } catch {
                return sendJson(res, 400, { error: "Invalid JSON body" });
            }
        } else {
            const rawMsg = querystring.parse(body).message;
            userPrompt = typeof rawMsg === "string" ? rawMsg.trim() : "";
        }

        if (!userPrompt) {
            return sendJson(res, 400, { error: "No prompt provided" });
        }

        try {
            const reply = await generateGeminiReply(userPrompt);
            return sendJson(res, 200, { reply });
        } catch (err) {
            console.error("Gemini API Error:", err?.message || err);
            return sendJson(res, 500, { error: "Failed to generate AI response" });
        }
    }

    // --- URL FETCHER (with SSRF protection) ---
    if (parsedUrl === "/api/fetch-url" && req.method === "POST") {
        try {
            const body = await readBody(req);
            const { url } = JSON.parse(body || "{}");
            let parsedTarget;
            try {
                parsedTarget = new URL(url);
            } catch {
                return sendJson(res, 400, { error: "Valid HTTP/HTTPS URL required" });
            }

            if (!["http:", "https:"].includes(parsedTarget.protocol)) {
                return sendJson(res, 400, { error: "Valid HTTP/HTTPS URL required" });
            }

            const hostLower = parsedTarget.hostname.toLowerCase();
            if (
                hostLower === "localhost" ||
                hostLower.endsWith(".localhost") ||
                hostLower.endsWith(".local") ||
                hostLower.endsWith(".internal") ||
                (net.isIP(hostLower) && isPrivateIp(hostLower))
            ) {
                return sendJson(res, 403, { error: "Target host is not permitted" });
            }

            const fetchClient = parsedTarget.protocol === "https:" ? https : http;
            return await new Promise((resolve) => {
                let settled = false;
                let truncated = false;

                const finish = (status, payload) => {
                    if (settled) return;
                    settled = true;
                    sendJson(res, status, payload);
                    resolve();
                };

                const fetchReq = fetchClient.get(
                    parsedTarget.toString(),
                    { lookup: safeLookup },
                    (webRes) => {
                        if (webRes.statusCode >= 400) {
                            webRes.resume();
                            return finish(502, { error: `Target returned HTTP ${webRes.statusCode}` });
                        }

                        const chunks = [];
                        let byteCount = 0;

                        webRes.on("data", (chunk) => {
                            if (settled || truncated) return;
                            const remaining = MAX_FETCH_BYTES - byteCount;
                            if (chunk.length >= remaining) {
                                chunks.push(chunk.subarray(0, remaining));
                                byteCount += remaining;
                                truncated = true;
                                webRes.destroy();
                                const cleanText = Buffer.concat(chunks)
                                    .toString("utf8")
                                    .replace(/<[^>]*>?/gm, " ")
                                    .replace(/\s+/g, " ")
                                    .slice(0, 5000);
                                finish(200, { text: cleanText });
                                return;
                            }
                            chunks.push(chunk);
                            byteCount += chunk.length;
                        });

                        webRes.on("end", () => {
                            const cleanText = Buffer.concat(chunks)
                                .toString("utf8")
                                .replace(/<[^>]*>?/gm, " ")
                                .replace(/\s+/g, " ")
                                .slice(0, 5000);
                            finish(200, { text: cleanText });
                        });

                        webRes.on("error", () => {
                            if (!truncated) {
                                finish(500, { error: "Unable to read webpage content" });
                            }
                        });
                    }
                );

                fetchReq.setTimeout(10000, () => fetchReq.destroy(new Error("Request timeout")));
                fetchReq.on("error", (err) => {
                    if (truncated) return;
                    const msg = String(err?.message || "");
                    if (msg.includes("blocked") || msg.includes("private")) {
                        return finish(403, { error: "Target host is not permitted" });
                    }
                    finish(500, { error: "Unable to fetch webpage content" });
                });
            });
        } catch (err) {
            const status = err.statusCode || (err instanceof SyntaxError ? 400 : 500);
            return sendJson(res, status, { error: status === 413 ? "Payload Too Large" : "Invalid JSON body" });
        }
    }

    // --- USER & AUTH ENDPOINTS ---
    if (parsedUrl === "/api/user/delete" && req.method === "POST") {
        return handleDeleteAccount(req, res);
    }

    if (parsedUrl === "/auth/workflow" && req.method === "POST") {
        const body = await readBody(req);
        const formData = parseFormOrJson(req, body);
        return handleAuthWorkflow(formData, res, req);
    }

    if (parsedUrl === "/auth/google" && req.method === "POST") {
        try {
            const body = await readBody(req);
            const parsed = JSON.parse(body || "{}");
            const token = parsed.token;
            if (!token || typeof token !== "string") {
                return sendJson(res, 400, { status: "error", message: "Token missing" });
            }

            return await new Promise((resolve) => {
                let settled = false;
                const finish = (status, payload, headers = {}) => {
                    if (settled) return;
                    settled = true;
                    sendJson(res, status, payload, headers);
                    resolve();
                };

                const gReq = https.get(
                    "https://oauth2.googleapis.com/tokeninfo?id_token=" + encodeURIComponent(token),
                    (gRes) => {
                        let gData = "";
                        gRes.on("data", chunk => { gData += chunk; });
                        gRes.on("end", () => {
                            try {
                                const gPayload = JSON.parse(gData || "{}");
                                const emailVerified =
                                    gPayload.email_verified === true || gPayload.email_verified === "true";
                                const audienceOk = !GOOGLE_CLIENT_ID || gPayload.aud === GOOGLE_CLIENT_ID;

                                if (
                                    gRes.statusCode === 200 &&
                                    gPayload.email &&
                                    emailVerified &&
                                    audienceOk &&
                                    isSafeKey(gPayload.email)
                                ) {
                                    const email = gPayload.email;
                                    const picture = typeof gPayload.picture === "string" ? gPayload.picture : "";

                                    const users = readJsonDb(DB_PATH);
                                    if (!hasOwn(users, email) || typeof users[email] !== "object" || users[email] === null) {
                                        users[email] = { picture, type: "google" };
                                    } else {
                                        users[email].picture = picture;
                                    }
                                    writeJsonDb(DB_PATH, users);

                                    finish(
                                        200,
                                        {
                                            status: "success",
                                            redirect: "/pg2.html?user=" + encodeURIComponent(email) + "&pic=" + encodeURIComponent(picture)
                                        },
                                        { "Set-Cookie": `session=${encodeURIComponent(email)}; Path=/; HttpOnly; SameSite=Lax` }
                                    );
                                } else {
                                    finish(401, { status: "error", message: "Invalid Google Token" });
                                }
                            } catch {
                                finish(500, { status: "error", message: "Failed to parse Google response" });
                            }
                        });
                    }
                );

                gReq.setTimeout(10000, () => gReq.destroy(new Error("Google verification timeout")));
                gReq.on("error", () => {
                    finish(500, { status: "error", message: "Google verification request failed" });
                });
            });
        } catch (err) {
            const status = err.statusCode || 400;
            return sendJson(res, status, { status: "error", message: status === 413 ? "Request too large" : "Invalid request payload" });
        }
    }

    // --- DEVELOPER CONSOLE ENDPOINTS ---
    if (parsedUrl === "/console/add-client" && req.method === "POST") {
        const body = await readBody(req);
        const formData = parseFormOrJson(req, body);
        const user = sanitizePipeField(formData.user || "system") || "system";
        const redirectUri = sanitizePipeField(formData.redirect_uri);

        if (redirectUri && isValidHttpUrl(redirectUri)) {
            const clients = getClientsFromTxt();
            const newClientId = "client_" + crypto.randomBytes(4).toString("hex");
            const newSecret = "sec_" + crypto.randomBytes(12).toString("hex");
            clients[newClientId] = { secret: newSecret, redirectUri, owner: user };
            saveClientsToTxt(clients);
        }

        res.writeHead(302, { "Location": "/console?user=" + encodeURIComponent(user) });
        return res.end();
    }

    if (parsedUrl === "/console/add-guard" && req.method === "POST") {
        try {
            const body = await readBody(req);
            const formData = parseFormOrJson(req, body);
            const user = sanitizePipeField(formData.user || "system") || "system";
            const websiteUrl = sanitizePipeField(formData.website_url);

            if (!websiteUrl || !isValidHttpUrl(websiteUrl)) {
                return sendJson(res, 400, { status: "error", message: "Valid HTTP/HTTPS website_url is required." });
            }

            const clients = getClientsFromTxt();
            const guardId = "guard_" + crypto.randomBytes(4).toString("hex");
            const guardSecret = "guard_sec_" + crypto.randomBytes(12).toString("hex");
            clients[guardId] = { secret: guardSecret, redirectUri: websiteUrl, owner: user };
            saveClientsToTxt(clients);

            return sendJson(res, 200, {
                status: "success",
                guardId,
                guardSecret,
                redirect: "/console?user=" + encodeURIComponent(user)
            });
        } catch (err) {
            const status = err.statusCode || (err instanceof SyntaxError ? 400 : 500);
            return sendJson(res, status, { status: "error", message: "Invalid request payload" });
        }
    }

    if (parsedUrl === "/console/delete-client" && req.method === "POST") {
        const body = await readBody(req);
        const formData = parseFormOrJson(req, body);
        const user = sanitizePipeField(formData.user || "system") || "system";
        const clientId = typeof formData.client_id === "string" ? formData.client_id.trim() : "";

        if (clientId) {
            const clients = getClientsFromTxt();
            if (hasOwn(clients, clientId)) {
                const owner = (clients[clientId].owner || "").trim().toLowerCase();
                if (owner === user.toLowerCase()) {
                    delete clients[clientId];
                    saveClientsToTxt(clients);
                }
            }
        }

        res.writeHead(302, { "Location": "/console?user=" + encodeURIComponent(user) });
        return res.end();
    }

    if (req.method === "GET" && parsedUrl === "/console") {
        const currentUser = typeof queryParams.user === "string" ? queryParams.user.trim() : "";

        if (!currentUser) {
            return sendHtml(
                res,
                401,
                "<h3>Access Denied</h3><p>You must log in with an official account to access the console.</p><a href=\"/login.html?next=console.html\">Go to Login</a>"
            );
        }

        const clients = getClientsFromTxt();
        let rowsHtml = "";
        for (const [id, data] of Object.entries(clients)) {
            const isOwner = (data.owner || "").trim().toLowerCase() === currentUser.toLowerCase();
            const actionCell = isOwner
                ? `<form action="/console/delete-client" method="POST" style="margin:0;">
                        <input type="hidden" name="client_id" value="${escapeHtml(id)}">
                        <input type="hidden" name="user" value="${escapeHtml(currentUser)}">
                        <button type="submit" style="background: #ef4444; color: white; border: none; padding: 6px 12px; font-size: 12px; border-radius: 4px; cursor: pointer;">Delete</button>
                   </form>`
                : `<span style="font-size: 12px; color: #64748b;">Protected</span>`;

            rowsHtml += `
                <tr style="border-bottom: 1px solid #e2e8f0;">
                    <td style="padding: 12px; font-family: monospace;">${escapeHtml(id)}</td>
                    <td style="padding: 12px; font-family: monospace; color: #d97706;">${escapeHtml(isOwner ? data.secret : "••••••••")}</td>
                    <td style="padding: 12px; font-size: 13px;">${escapeHtml(data.redirectUri)}</td>
                    <td style="padding: 12px; font-size: 13px; font-weight: bold; color: #2563eb;">${escapeHtml(data.owner)}</td>
                    <td style="padding: 12px;">${actionCell}</td>
                </tr>`;
        }

        return sendHtml(res, 200, `<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <title>Reos Developer Console</title>
    <style>
        body { font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif; margin: 0; background: #f8fafc; color: #0f172a; }
        header { background: #ffffff; border-bottom: 1px solid #e2e8f0; padding: 16px 32px; display: flex; justify-content: space-between; align-items: center; }
        .logo { font-size: 20px; font-weight: 700; color: #2563eb; }
        .container { max-width: 950px; margin: 40px auto; padding: 0 20px; }
        .card { background: white; padding: 28px; border-radius: 12px; border: 1px solid #e2e8f0; margin-bottom: 24px; box-shadow: 0 1px 3px rgba(0,0,0,0.05); }
        h2 { margin-top: 0; font-size: 20px; }
        input { width: 100%; padding: 10px; margin-top: 6px; margin-bottom: 16px; border: 1px solid #cbd5e1; border-radius: 6px; box-sizing: border-box; }
        button { background: #2563eb; color: white; border: none; padding: 10px 20px; border-radius: 6px; font-weight: 600; cursor: pointer; }
        button:hover { opacity: 0.9; }
        table { width: 100%; border-collapse: collapse; text-align: left; }
        th { padding: 12px; border-bottom: 2px solid #cbd5e1; font-size: 13px; color: #64748b; }
    </style>
</head>
<body>
    <header>
        <div class="logo">Reos Developer Console</div>
        <div>Account: <strong>${escapeHtml(currentUser)}</strong> | <a href="/login.html?next=console.html" style="color: #64748b; text-decoration: none;">Switch Account</a></div>
    </header>
    <div class="container">
        <div class="card">
            <h2>Create OAuth 2.0 Client ID</h2>
            <form action="/console/add-client" method="POST">
                <input type="hidden" name="user" value="${escapeHtml(currentUser)}">
                <label style="font-size: 14px; font-weight: 500;">Authorized Redirect URI</label>
                <input type="url" name="redirect_uri" placeholder="https://yourdomain.com/callback" required>
                <button type="submit">+ Create Credentials</button>
            </form>
        </div>
        <div class="card">
            <h2>Registered OAuth Apps</h2>
            <table>
                <thead>
                    <tr>
                        <th>Client ID</th>
                        <th>Client Secret</th>
                        <th>Redirect URI</th>
                        <th>Linked Account</th>
                        <th>Action</th>
                    </tr>
                </thead>
                <tbody>${rowsHtml}</tbody>
            </table>
        </div>
    </div>
</body>
</html>`);
    }

    // --- SAFE STATIC FILE SERVING ---
    if (req.method !== "GET" && req.method !== "HEAD") {
        res.writeHead(404, { "Content-Type": "text/plain" });
        return res.end("404 Not Found");
    }

    if (parsedUrl.includes("\0")) {
        res.writeHead(403, { "Content-Type": "text/plain" });
        return res.end("403 Forbidden");
    }

    let relativeUrl = parsedUrl;
    if (relativeUrl === "/" || relativeUrl === "/index" || relativeUrl === "/index.html") {
        relativeUrl = "/index.html";
    }

    const segments = relativeUrl.replace(/^\/+/, "").split(/[/\\]+/).filter(Boolean);
    if (
        segments.length === 0 ||
        segments.some(seg => seg === "." || seg === ".." || seg.startsWith("."))
    ) {
        res.writeHead(403, { "Content-Type": "text/plain" });
        return res.end("403 Forbidden");
    }

    const filePath = path.resolve(WEB_DIR, ...segments);
    const fileName = path.basename(filePath).toLowerCase();

    if (
        !filePath.startsWith(WEB_DIR + path.sep) ||
        fileName.startsWith(".") ||
        fileName.endsWith(".cjs") ||
        fileName.endsWith(".tmp") ||
        BLOCKED_STATIC_FILES.has(fileName)
    ) {
        res.writeHead(403, { "Content-Type": "text/plain" });
        return res.end("403 Forbidden");
    }

    const ext = path.extname(filePath).toLowerCase();
    const mimeTypes = {
        ".html": "text/html",
        ".css": "text/css",
        ".js": "application/javascript",
        ".json": "application/json",
        ".jpg": "image/jpeg",
        ".jpeg": "image/jpeg",
        ".png": "image/png",
        ".svg": "image/svg+xml",
        ".ico": "image/x-icon",
        ".txt": "text/plain",
        ".apk": "application/vnd.android.package-archive",
        ".exe": "application/x-msdownload",
        ".gz": "application/gzip"
    };
    const contentType = mimeTypes[ext] || "application/octet-stream";

    fs.readFile(filePath, (err, content) => {
        if (err) {
            res.writeHead(404, { "Content-Type": "text/plain" });
            return res.end(req.method === "HEAD" ? undefined : "404 Not Found");
        }
        res.writeHead(200, { "Content-Type": contentType });
        return res.end(req.method === "HEAD" ? undefined : content);
    });
}

const server = http.createServer((req, res) => {
    handleRequest(req, res).catch((err) => {
        console.error("Unhandled request error:", err);
        const status = err?.statusCode || 500;
        if (!res.headersSent) {
            res.writeHead(status, { "Content-Type": "text/plain" });
            res.end(status === 413 ? "413 Payload Too Large" : "500 Internal Server Error");
        } else {
            res.destroy();
        }
    });
});

server.on("clientError", (err, socket) => {
    if (err.code === "ECONNRESET" || !socket.writable) return;
    socket.end("HTTP/1.1 400 Bad Request\r\n\r\n");
});

server.on("error", (err) => {
    console.error("Server error:", err);
    process.exit(1);
});

server.listen(PORT, "0.0.0.0", () => {
    console.log(`⚡ Reos Server running on Port ${PORT} (WEB_DIR=${WEB_DIR}, DATA_DIR=${DATA_DIR})`);
});

process.on("SIGTERM", () => server.close(() => process.exit(0)));
process.on("SIGINT", () => server.close(() => process.exit(0)));