local Players      = game:GetService("Players")
local RunService   = game:GetService("RunService")
local UIS          = game:GetService("UserInputService")
local TweenService = game:GetService("TweenService")
local Workspace    = game:GetService("Workspace")

local LP  = Players.LocalPlayer
local HttpService = game:GetService("HttpService")

----------------------------------------------------------------
-- ACCESS  (admin key / generated keys)
----------------------------------------------------------------
local CONFIG = {
    -- Cloudflare Worker URL (see key_server_worker.js), e.g. "https://yl-keys.YOURNAME.workers.dev"
    -- With a URL: keys are shared on every device and admins see who uses each key.
    -- Leave "" for LOCAL mode (keys only on this device, no server).
    API_URL    = "",
    -- SHA-256 of the original admin key. The key itself is NOT stored in this script.
    ADMIN_HASH = "be72b534cbec6e07c61039e5d62b2bde0084bd6b5ec1065b2c5236e94f9bba25",
    -- Pre-validated keys (SHA-256). Always valid, never expire, work without any server.
    PRESET_HASHES = {
        ["459542b5010a3db7c4e5bb45d431f166e33187974bf804bda55e1a13ace83837"] = "user",
        ["2f84b20f75da58aba4c9e8233d29d27c18fb89306a8544a21622756e840ef538"] = "admin",
    },
    DB_FILE    = "YL_KUKIRIN_keys.json",
    SAVED_KEY  = "YL_KUKIRIN_key.txt",
}

local session = { key = nil, admin = false, master = false, expires = nil, t = 0 }
local fmtDur, Backend

do
    local K = {
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
        0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
        0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
        0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
        0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
        0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
        0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
        0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
        0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
        0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
        0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
        0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
        0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
        0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    }

    local function sha256(msg)
        local band, bxor, bnot = bit32.band, bit32.bxor, bit32.bnot
        local rrot, rshift = bit32.rrotate, bit32.rshift
        local h = { 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 }
        local len = #msg
        local bits = len * 8
        msg = msg .. "\128" .. string.rep("\0", (55 - len) % 64)
            .. string.char(0, 0, 0, 0, band(rshift(bits, 24), 255), band(rshift(bits, 16), 255), band(rshift(bits, 8), 255), band(bits, 255))
        for chunk = 1, #msg, 64 do
            local w = {}
            for i = 0, 15 do
                local b1, b2, b3, b4 = string.byte(msg, chunk + i * 4, chunk + i * 4 + 3)
                w[i + 1] = b1 * 16777216 + b2 * 65536 + b3 * 256 + b4
            end
            for i = 17, 64 do
                local s0 = bxor(rrot(w[i - 15], 7), rrot(w[i - 15], 18), rshift(w[i - 15], 3))
                local s1 = bxor(rrot(w[i - 2], 17), rrot(w[i - 2], 19), rshift(w[i - 2], 10))
                w[i] = (w[i - 16] + s0 + w[i - 7] + s1) % 4294967296
            end
            local a, b, c, d, e, f, g, hh = h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8]
            for i = 1, 64 do
                local S1 = bxor(rrot(e, 6), rrot(e, 11), rrot(e, 25))
                local ch = bxor(band(e, f), band(bnot(e), g))
                local t1 = (hh + S1 + ch + K[i] + w[i]) % 4294967296
                local S0 = bxor(rrot(a, 2), rrot(a, 13), rrot(a, 22))
                local maj = bxor(band(a, b), band(a, c), band(b, c))
                local t2 = (S0 + maj) % 4294967296
                hh, g, f, e, d, c, b, a = g, f, e, (d + t1) % 4294967296, c, b, a, (t1 + t2) % 4294967296
            end
            h[1] = (h[1] + a) % 4294967296; h[2] = (h[2] + b) % 4294967296
            h[3] = (h[3] + c) % 4294967296; h[4] = (h[4] + d) % 4294967296
            h[5] = (h[5] + e) % 4294967296; h[6] = (h[6] + f) % 4294967296
            h[7] = (h[7] + g) % 4294967296; h[8] = (h[8] + hh) % 4294967296
        end
        return string.format("%08x%08x%08x%08x%08x%08x%08x%08x", h[1], h[2], h[3], h[4], h[5], h[6], h[7], h[8])
    end

    fmtDur = function(sec)
        sec = math.max(0, math.floor(sec))
        local d = math.floor(sec / 86400)
        local h = math.floor(sec % 86400 / 3600)
        local m = math.floor(sec % 3600 / 60)
        if d > 0 then return string.format("%dd %dh", d, h) end
        if h > 0 then return string.format("%dh %dm", h, m) end
        return string.format("%dm", m)
    end

    -- http (works on PC and mobile executors)
    local httpReq = (syn and syn.request) or (http and http.request) or http_request or request or (fluxus and fluxus.request)

    local function apiCall(payload)
        if CONFIG.API_URL == "" or not httpReq then return nil end
        local ok, res = pcall(httpReq, {
            Url = CONFIG.API_URL, Method = "POST",
            Headers = { ["Content-Type"] = "application/json" },
            Body = HttpService:JSONEncode(payload),
        })
        if not ok or type(res) ~= "table" or not res.Body then return nil end
        local ok2, data = pcall(function() return HttpService:JSONDecode(res.Body) end)
        if not ok2 or type(data) ~= "table" then return nil end
        return data
    end

    local function userInfo()
        return { name = LP.Name, id = LP.UserId, display = LP.DisplayName }
    end

    local ALPHA = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    local rng = Random.new()
    local function genKey()
        local parts = {}
        for g = 1, 3 do
            local part = ""
            for _ = 1, 5 do
                local i = rng:NextInteger(1, #ALPHA)
                part = part .. ALPHA:sub(i, i)
            end
            parts[g] = part
        end
        return "YL-" .. table.concat(parts, "-")
    end

    ------------------------------------------------------------
    -- LOCAL mode (keys stored in a file on this device)
    ------------------------------------------------------------
    local db = { keys = {} }
    pcall(function()
        if isfile and readfile and isfile(CONFIG.DB_FILE) then
            local d = HttpService:JSONDecode(readfile(CONFIG.DB_FILE))
            if type(d) == "table" and type(d.keys) == "table" then db = d end
        end
    end)
    local function saveDB()
        pcall(function()
            if writefile then writefile(CONFIG.DB_FILE, HttpService:JSONEncode(db)) end
        end)
    end

    local function trackUser(rec, ping)
        rec.users = rec.users or {}
        local u = userInfo()
        local id = tostring(u.id)
        local cur = rec.users[id] or { id = u.id, name = u.name, display = u.display, first = os.time(), count = 0 }
        cur.name, cur.display, cur.last = u.name, u.display, os.time()
        if not ping then cur.count = (cur.count or 0) + 1 end
        rec.users[id] = cur
    end

    local function toPublic(rec)
        local out = {}
        for k, v in pairs(rec) do out[k] = v end
        local arr = {}
        for _, u in pairs(rec.users or {}) do table.insert(arr, u) end
        table.sort(arr, function(a, b) return (a.count or 0) > (b.count or 0) end)
        out.users = arr
        return out
    end

    local function localCheck(key, isAdminKey, ping)
        local rec
        if isAdminKey then
            rec = db.keys["__admin"] or { key = "__admin", master = true, admin = true, duration = 0, label = "", created = os.time(), users = {} }
            db.keys["__admin"] = rec
        else
            rec = db.keys[key]
            if not rec then return { ok = false, msg = "invalid" } end
            if rec.revoked then return { ok = false, msg = "revoked" } end
            local now = os.time()
            if (rec.duration or 0) > 0 then
                if not rec.firstUse and not ping then rec.firstUse = now; rec.expires = now + rec.duration end
                if rec.expires and now > rec.expires then return { ok = false, msg = "expired" } end
            end
        end
        trackUser(rec, ping)
        saveDB()
        return { ok = true, admin = rec.admin == true, master = rec.master == true, expires = rec.expires }
    end

    local function localList()
        local keys = {}
        for _, rec in pairs(db.keys) do table.insert(keys, toPublic(rec)) end
        return { ok = true, keys = keys }
    end

    local function localCreate(o)
        local k = genKey()
        local rec = {
            key = k, admin = o.admin == true, duration = math.max(0, math.floor(o.duration or 0)),
            label = tostring(o.label or ""):sub(1, 40), created = os.time(), users = {},
        }
        db.keys[k] = rec
        saveDB()
        return { ok = true, key = toPublic(rec) }
    end

    local function localUpdate(target, o)
        local rec = db.keys[target]
        if not rec or rec.master then return { ok = false, msg = "invalid" } end
        if o.admin ~= nil then rec.admin = o.admin end
        if o.revoked ~= nil then rec.revoked = o.revoked end
        if o.duration ~= nil then
            rec.duration = math.max(0, math.floor(o.duration))
            rec.expires = (rec.duration > 0 and rec.firstUse) and (rec.firstUse + rec.duration) or nil
        end
        saveDB()
        return { ok = true, key = toPublic(rec) }
    end

    local function localDelete(target)
        local rec = db.keys[target]
        if not rec or rec.master then return { ok = false, msg = "invalid" } end
        db.keys[target] = nil
        saveDB()
        return { ok = true }
    end

    ------------------------------------------------------------
    -- public interface (server mode if API_URL is set, else local)
    ------------------------------------------------------------
    Backend = {}

    function Backend.mode()
        return (CONFIG.API_URL ~= "" and httpReq) and "server" or "local"
    end

    function Backend.check(key, ping)
        local keyHash = sha256(key)
        local preset = CONFIG.PRESET_HASHES[keyHash]
        local isAdminKey = keyHash == CONFIG.ADMIN_HASH
        if Backend.mode() == "server" then
            local data = apiCall({ action = "check", key = key, user = userInfo(), ping = ping and true or nil })
            if data and data.ok then return data end
            -- the admin key always opens the panel, even if the server is down / not set up yet
            if isAdminKey then return { ok = true, admin = true, master = true } end
            -- pre-validated keys open the panel when the server is unreachable
            if not data and preset then return { ok = true, admin = (preset == "admin"), master = false } end
            if data then return data end
            return { ok = false, msg = "offline" }
        end
        -- local mode: pre-validated keys always open, no server needed
        if preset then return { ok = true, admin = (preset == "admin"), master = false } end
        return localCheck(key, isAdminKey, ping)
    end

    local function adminCall(payload)
        payload.key = session.key
        return apiCall(payload) or { ok = false, msg = "offline" }
    end

    function Backend.list()
        if Backend.mode() == "server" then return adminCall({ action = "list" }) end
        return localList()
    end

    function Backend.create(o)
        if Backend.mode() == "server" then
            return adminCall({ action = "create", duration = o.duration, admin = o.admin, label = o.label })
        end
        return localCreate(o)
    end

    function Backend.update(target, o)
        if Backend.mode() == "server" then
            return adminCall({ action = "update", target = target, admin = o.admin, revoked = o.revoked, duration = o.duration })
        end
        return localUpdate(target, o)
    end

    function Backend.delete(target)
        if Backend.mode() == "server" then return adminCall({ action = "delete", target = target }) end
        return localDelete(target)
    end
end

----------------------------------------------------------------
-- LANGUAGES
----------------------------------------------------------------
local LANGS = {
    { code = "en", name = "English" },
    { code = "fr", name = "Français" },
    { code = "es", name = "Español" },
}

local L = {}

L.en = {
    tab_wheelie = "Wheelie", tab_road = "Road", tab_events = "Events",
    tab_prot = "Protection", tab_status = "Status", tab_set = "Settings",

    info_wheelie = "Sit on your scooter, then enable Wheelie (key G). Front wheel stays up, scooter rides by itself and follows the road.",
    wheelie_t = "Wheelie + Auto Ride", pitch = "Front wheel angle", speed = "Ride speed",
    autofwd = "Auto forward", turnrate = "Turn rate", flip = "Flip direction (if backwards)",

    info_road = "The road is analysed automatically (nothing to press). The scooter follows it by itself and stays glued to it.",
    autofollow = "Auto follow road (turns)", gain = "Follow strength", glue = "Stick to road (no hops)",
    slopes = "Follow slopes", rear = "Rear wheel offset", learn = "Learn road under me",

    info_events = "Pumpkin event: scans the map for pumpkins you can pick up by touching them and goes onto each one. You stay off the scooter until you turn it off or every pumpkin is collected.",
    ev_auto = "Auto collect pumpkins", ev_delay = "Wait per pumpkin", ev_scan = "Scan pumpkins",

    anti_rag = "Anti Ragdoll", stay = "Stay on scooter (anti eject)", anti_spin = "Anti spin / fling",

    st_seat = "Seat: %s", seated = "seated", not_seated = "not seated",
    st_whee = "Wheelie: %s", w_active = "ACTIVE", w_wait = "waiting for seat", w_off = "OFF",
    st_speed = "Speed: %s studs/s", st_pitch = "Front wheel: %s",
    st_road = "Road: %s", r_found = "found (offset %d°)", r_lost = "lost / off",
    st_surf = "Road surface: %s",
    st_pump = "Pumpkins: %d collected / %d found - %s",
    ev_idle = "idle", ev_scanning = "scanning...", ev_collecting = "collecting", ev_returning = "back to scooter",

    language = "Language", panel_size = "Panel size", particles = "Background particles",
    panel_key = "Panel key", wheelie_key = "Wheelie key", press = "press key...",

    enter_key = "Enter your key", key_ph = "key...", unlock = "Unlock", invalid = "Invalid key",

    sit_first = "Sit on your scooter first", nothing_scan = "Nothing to scan", no_ground = "No ground found",
    road_learned = "Road learned: %s",
    ev_none = "No collectable pumpkin found", ev_found = "%d collectable pumpkin(s) found (%d ignored)",
    ev_done = "All pumpkins collected!", ev_off = "Pumpkin collect stopped",
    ev_back_fail = "Scooter not found, staying here",

    tab_admin = "Admin", k_checking = "Checking...", k_revoked = "Key revoked", k_expired = "Key expired",
    k_offline = "Server unreachable",
    adm_mode_server = "Key server connected: generated keys work on every device.",
    adm_mode_local = "LOCAL mode: generated keys only work on this device (set API_URL in the script to share keys).",
    adm_duration = "Duration of new keys (counts from first use)", adm_isadmin = "New key is admin",
    adm_label_ph = "Label (who is it for?)", adm_generate = "Generate key", adm_refresh = "Refresh list",
    adm_newkey_ph = "Generated key appears here",
    adm_revoke = "Revoke", adm_restore = "Restore", adm_delete = "Delete",
    adm_admin_on = "Make admin", adm_admin_off = "Remove admin", adm_dur_btn = "Time: %s",
    adm_unused = "not used yet (%s)", adm_expires = "expires in %s", adm_expired = "expired", adm_never = "no limit",
    adm_used_by = "Used by: %s", adm_nobody = "Not used yet", adm_master = "MASTER ADMIN KEY", adm_revoked = "REVOKED",
    adm_copied = "Key generated (copied if possible)", adm_err = "Action failed",
    st_key = "Key: %s", key_admin = "admin", key_user = "user", logout = "Change key / log out",
}

L.fr = {
    tab_wheelie = "Wheelie", tab_road = "Route", tab_events = "Events",
    tab_prot = "Protection", tab_status = "Statut", tab_set = "Réglages",

    info_wheelie = "Assieds-toi sur ta trottinette puis active le Wheelie (touche G). La roue avant reste levée, la trot roule seule et suit la route.",
    wheelie_t = "Wheelie + Roulage auto", pitch = "Angle roue avant", speed = "Vitesse",
    autofwd = "Avancer automatiquement", turnrate = "Vitesse de virage", flip = "Inverser le sens (si à l'envers)",

    info_road = "La route est analysée automatiquement (rien à faire). La trottinette la suit toute seule et reste collée dessus.",
    autofollow = "Suivre la route (virages)", gain = "Force de suivi", glue = "Coller à la route (sans sauts)",
    slopes = "Suivre les pentes", rear = "Décalage roue arrière", learn = "Apprendre la route sous moi",

    info_events = "Event citrouilles : repère sur la map les citrouilles ramassables en marchant dessus et se déplace sur chacune. Tu restes hors de la trot tant que tu ne désactives pas ou que toutes les citrouilles ne sont pas récupérées.",
    ev_auto = "Auto-collecte des citrouilles", ev_delay = "Attente par citrouille", ev_scan = "Scanner les citrouilles",

    anti_rag = "Anti Ragdoll", stay = "Rester sur la trot (anti éjection)", anti_spin = "Anti spin / fling",

    st_seat = "Siège : %s", seated = "assis", not_seated = "pas assis",
    st_whee = "Wheelie : %s", w_active = "ACTIF", w_wait = "attend un siège", w_off = "OFF",
    st_speed = "Vitesse : %s studs/s", st_pitch = "Roue avant : %s",
    st_road = "Route : %s", r_found = "trouvée (écart %d°)", r_lost = "perdue / off",
    st_surf = "Surface route : %s",
    st_pump = "Citrouilles : %d ramassées / %d trouvées - %s",
    ev_idle = "inactif", ev_scanning = "scan en cours...", ev_collecting = "collecte", ev_returning = "retour sur la trot",

    language = "Langue", panel_size = "Taille du panel", particles = "Particules en fond",
    panel_key = "Touche du panel", wheelie_key = "Touche wheelie", press = "appuie sur une touche...",

    enter_key = "Entre ta clé", key_ph = "clé...", unlock = "Déverrouiller", invalid = "Clé invalide",

    sit_first = "Assieds-toi d'abord sur ta trot", nothing_scan = "Rien à scanner", no_ground = "Aucun sol trouvé",
    road_learned = "Route apprise : %s",
    ev_none = "Aucune citrouille ramassable trouvée", ev_found = "%d citrouille(s) ramassable(s) trouvée(s) (%d ignorée(s))",
    ev_done = "Toutes les citrouilles sont ramassées !", ev_off = "Collecte arrêtée",
    ev_back_fail = "Trot introuvable, je reste ici",

    tab_admin = "Admin", k_checking = "Vérification...", k_revoked = "Clé révoquée", k_expired = "Clé expirée",
    k_offline = "Serveur injoignable",
    adm_mode_server = "Serveur de clés connecté : les clés générées marchent sur tous les appareils.",
    adm_mode_local = "Mode LOCAL : les clés générées ne marchent que sur cet appareil (mets API_URL dans le script pour les partager).",
    adm_duration = "Durée des nouvelles clés (compte dès la 1re utilisation)", adm_isadmin = "La nouvelle clé est admin",
    adm_label_ph = "Nom (pour qui ?)", adm_generate = "Générer une clé", adm_refresh = "Actualiser la liste",
    adm_newkey_ph = "La clé générée apparaît ici",
    adm_revoke = "Révoquer", adm_restore = "Rétablir", adm_delete = "Supprimer",
    adm_admin_on = "Mettre admin", adm_admin_off = "Retirer admin", adm_dur_btn = "Durée : %s",
    adm_unused = "pas encore utilisée (%s)", adm_expires = "expire dans %s", adm_expired = "expirée", adm_never = "illimitée",
    adm_used_by = "Utilisée par : %s", adm_nobody = "Pas encore utilisée", adm_master = "CLÉ ADMIN PRINCIPALE", adm_revoked = "RÉVOQUÉE",
    adm_copied = "Clé générée (copiée si possible)", adm_err = "Action échouée",
    st_key = "Clé : %s", key_admin = "admin", key_user = "utilisateur", logout = "Changer de clé / se déconnecter",
}

L.es = {
    tab_wheelie = "Wheelie", tab_road = "Ruta", tab_events = "Eventos",
    tab_prot = "Protección", tab_status = "Estado", tab_set = "Ajustes",

    info_wheelie = "Siéntate en tu scooter y activa el Wheelie (tecla G). La rueda delantera queda levantada, el scooter avanza solo y sigue la ruta.",
    wheelie_t = "Wheelie + Conducción auto", pitch = "Ángulo rueda delantera", speed = "Velocidad",
    autofwd = "Avance automático", turnrate = "Velocidad de giro", flip = "Invertir dirección (si va al revés)",

    info_road = "La ruta se analiza automáticamente (nada que pulsar). El scooter la sigue solo y se mantiene pegado a ella.",
    autofollow = "Seguir la ruta (curvas)", gain = "Fuerza de seguimiento", glue = "Pegado a la ruta (sin saltos)",
    slopes = "Seguir pendientes", rear = "Desfase rueda trasera", learn = "Aprender la ruta bajo mí",

    info_events = "Evento calabazas: busca en el mapa las calabazas que se recogen al tocarlas y va a cada una. No vuelves al scooter hasta que lo desactives o se recojan todas.",
    ev_auto = "Recoger calabazas auto", ev_delay = "Espera por calabaza", ev_scan = "Escanear calabazas",

    anti_rag = "Anti Ragdoll", stay = "Quedarse en el scooter (anti expulsión)", anti_spin = "Anti giro / fling",

    st_seat = "Asiento: %s", seated = "sentado", not_seated = "no sentado",
    st_whee = "Wheelie: %s", w_active = "ACTIVO", w_wait = "esperando asiento", w_off = "OFF",
    st_speed = "Velocidad: %s studs/s", st_pitch = "Rueda delantera: %s",
    st_road = "Ruta: %s", r_found = "encontrada (desvío %d°)", r_lost = "perdida / off",
    st_surf = "Superficie de ruta: %s",
    st_pump = "Calabazas: %d recogidas / %d encontradas - %s",
    ev_idle = "inactivo", ev_scanning = "escaneando...", ev_collecting = "recogiendo", ev_returning = "volviendo al scooter",

    language = "Idioma", panel_size = "Tamaño del panel", particles = "Partículas de fondo",
    panel_key = "Tecla del panel", wheelie_key = "Tecla wheelie", press = "pulsa una tecla...",

    enter_key = "Introduce tu clave", key_ph = "clave...", unlock = "Desbloquear", invalid = "Clave inválida",

    sit_first = "Siéntate primero en tu scooter", nothing_scan = "Nada que escanear", no_ground = "No se encontró suelo",
    road_learned = "Ruta aprendida: %s",
    ev_none = "No hay calabazas recogibles", ev_found = "%d calabaza(s) recogible(s) (%d ignorada(s))",
    ev_done = "¡Todas las calabazas recogidas!", ev_off = "Recogida detenida",
    ev_back_fail = "Scooter no encontrado, me quedo aquí",

    tab_admin = "Admin", k_checking = "Comprobando...", k_revoked = "Clave revocada", k_expired = "Clave caducada",
    k_offline = "Servidor inaccesible",
    adm_mode_server = "Servidor de claves conectado: las claves generadas funcionan en todos los dispositivos.",
    adm_mode_local = "Modo LOCAL: las claves generadas solo funcionan en este dispositivo (pon API_URL en el script para compartirlas).",
    adm_duration = "Duración de las claves nuevas (desde el primer uso)", adm_isadmin = "La clave nueva es admin",
    adm_label_ph = "Nombre (¿para quién?)", adm_generate = "Generar clave", adm_refresh = "Actualizar lista",
    adm_newkey_ph = "La clave generada aparece aquí",
    adm_revoke = "Revocar", adm_restore = "Restaurar", adm_delete = "Borrar",
    adm_admin_on = "Hacer admin", adm_admin_off = "Quitar admin", adm_dur_btn = "Tiempo: %s",
    adm_unused = "sin usar (%s)", adm_expires = "caduca en %s", adm_expired = "caducada", adm_never = "sin límite",
    adm_used_by = "Usada por: %s", adm_nobody = "Aún sin usar", adm_master = "CLAVE ADMIN PRINCIPAL", adm_revoked = "REVOCADA",
    adm_copied = "Clave generada (copiada si es posible)", adm_err = "Acción fallida",
    st_key = "Clave: %s", key_admin = "admin", key_user = "usuario", logout = "Cambiar clave / cerrar sesión",
}

local LANG_FILE = "YL_KUKIRIN_lang.txt"

local function detectLang()
    local ok, saved = pcall(function()
        if isfile and readfile and isfile(LANG_FILE) then return readfile(LANG_FILE) end
    end)
    if ok and type(saved) == "string" then
        saved = saved:gsub("%s", "")
        if L[saved] then return saved end
    end
    local ok2, id = pcall(function() return LP.LocaleId end)
    id = ok2 and tostring(id):lower() or "en"
    local p = id:sub(1, 2)
    if L[p] then return p end
    return "en"
end

----------------------------------------------------------------
-- STATE
----------------------------------------------------------------
local S = {
    -- wheelie
    wheelie = false, pitch = 35, speed = 45, autoForward = true,
    turnRate = 2.2, flip = false,
    -- road
    autoFollow = true, followGain = 3, roadGlue = true,
    followSlope = true, rearOffset = 2.5,
    -- events
    autoPumpkin = false, pumpDelay = .35,
    -- admin
    newAdmin = false,
    -- protection
    antiRagdoll = true, stayOnSeat = true, antiSpin = true,
    -- settings
    lang = detectLang(),
    accent = Color3.fromRGB(90, 140, 255), particles = true, scale = 1,
    openKey = Enum.KeyCode.F4, wheelieKey = Enum.KeyCode.G,
}
if UIS.TouchEnabled and not UIS.KeyboardEnabled then S.scale = 0.8 end

local function T(k)
    return (L[S.lang] and L[S.lang][k]) or L.en[k] or k
end

local langBinds = {}
local function bindText(inst, key, prefix)
    local function f() inst.Text = (prefix or "") .. T(key) end
    f()
    table.insert(langBinds, f)
end

local C = {
    bg   = Color3.fromRGB(11, 12, 18),
    el   = Color3.fromRGB(24, 26, 38),
    el2  = Color3.fromRGB(33, 36, 52),
    off  = Color3.fromRGB(52, 55, 74),
    text = Color3.fromRGB(235, 237, 245),
    sub  = Color3.fromRGB(140, 146, 165),
}

-- events state (declared early: used by protection + UI)
local ev = { active = false, found = 0, collected = 0, state = "ev_idle", list = {} }

----------------------------------------------------------------
-- UI HELPERS
----------------------------------------------------------------
local function new(class, props, parent)
    local o = Instance.new(class)
    for k, v in pairs(props or {}) do o[k] = v end
    if parent then o.Parent = parent end
    return o
end
local function corner(o, r) return new("UICorner", { CornerRadius = UDim.new(0, r) }, o) end

local function guiParent()
    local ok, h = pcall(function() return gethui and gethui() end)
    if ok and h then return h end
    local ok2, cg = pcall(function() return game:GetService("CoreGui") end)
    if ok2 and cg then
        local t = Instance.new("Folder")
        local ok3 = pcall(function() t.Parent = cg end)
        t:Destroy()
        if ok3 then return cg end
    end
    return LP:WaitForChild("PlayerGui")
end

local parentGui = guiParent()
local old = parentGui:FindFirstChild("YL_KUKIRIN_EXEC")
if old then old:Destroy() end

local gui = new("ScreenGui", {
    Name = "YL_KUKIRIN_EXEC", ResetOnSpawn = false, IgnoreGuiInset = true,
    ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
}, parentGui)

local accentList, refreshers, toggles = {}, {}, {}
local function accentBind(inst, prop)
    table.insert(accentList, { inst, prop })
    inst[prop] = S.accent
end

local particleFrames = {}
local function setAccent(c)
    S.accent = c
    for _, a in ipairs(accentList) do
        if a[1] and a[1].Parent then a[1][a[2]] = c end
    end
    for _, p in ipairs(particleFrames) do p.f.BackgroundColor3 = c end
    for _, fn in ipairs(refreshers) do fn() end
end

local function makeDraggable(handle, target, getScale, onClick, clampFn)
    local dragging, startIn, startPos, moved = false, nil, nil, 0
    handle.InputBegan:Connect(function(i)
        if i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch then
            dragging, moved, startIn, startPos = true, 0, i.Position, target.Position
        end
    end)
    UIS.InputChanged:Connect(function(i)
        if dragging and (i.UserInputType == Enum.UserInputType.MouseMovement or i.UserInputType == Enum.UserInputType.Touch) then
            local d = i.Position - startIn
            moved = math.max(moved, d.Magnitude)
            local sc = getScale and getScale() or 1
            target.Position = UDim2.new(startPos.X.Scale, startPos.X.Offset + d.X / sc,
                                        startPos.Y.Scale, startPos.Y.Offset + d.Y / sc)
            if clampFn then clampFn() end
        end
    end)
    UIS.InputEnded:Connect(function(i)
        if dragging and (i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch) then
            dragging = false
            if onClick and moved < 6 then onClick() end
        end
    end)
end

----------------------------------------------------------------
-- MAIN WINDOW
----------------------------------------------------------------
local W, H = 580, 360
local main = new("Frame", {
    Name = "Main", AnchorPoint = Vector2.new(.5, .5), Position = UDim2.fromScale(.5, .5),
    Size = UDim2.fromOffset(W, H), BackgroundColor3 = C.bg, BorderSizePixel = 0,
    ClipsDescendants = true, Visible = false,
}, gui)
corner(main, 12)
local mainStroke = new("UIStroke", { Thickness = 1.5, Transparency = .35 }, main)
accentBind(mainStroke, "Color")
local uiScale = new("UIScale", { Scale = S.scale }, main)

local function viewport()
    local cam = Workspace.CurrentCamera
    return cam and cam.ViewportSize or Vector2.new(1280, 720)
end

-- panel always fits the screen
local function applyScale()
    local vp = viewport()
    local fit = math.min(S.scale, (vp.X - 16) / W, (vp.Y - 16) / H)
    uiScale.Scale = math.max(fit, .4)
end
applyScale()

-- keep a gui object inside the screen
local function clampToScreen(t)
    local vp = viewport()
    local ap, as = t.AbsolutePosition, t.AbsoluteSize
    local dx, dy = 0, 0
    if ap.X < 0 then dx = -ap.X elseif ap.X + as.X > vp.X then dx = vp.X - (ap.X + as.X) end
    if ap.Y < 0 then dy = -ap.Y elseif ap.Y + as.Y > vp.Y then dy = vp.Y - (ap.Y + as.Y) end
    if dx ~= 0 or dy ~= 0 then
        local sc = (t == main) and uiScale.Scale or 1
        local p = t.Position
        t.Position = UDim2.new(p.X.Scale, p.X.Offset + dx / sc, p.Y.Scale, p.Y.Offset + dy / sc)
    end
end

-- particles (behind everything)
local pc = new("Frame", { Size = UDim2.fromOffset(W, H), BackgroundTransparency = 1, BorderSizePixel = 0 }, main)
for i = 1, 32 do
    local r = math.random(2, 5)
    local f = new("Frame", {
        BackgroundColor3 = S.accent, BorderSizePixel = 0, Size = UDim2.fromOffset(r, r),
        BackgroundTransparency = .5 + math.random() * .4,
    }, pc)
    corner(f, 4)
    table.insert(particleFrames, {
        f = f, x = math.random(), y = math.random(),
        vx = (math.random() - .5) * .04, vy = (math.random() - .5) * .04,
    })
end

-- title bar
local title = new("Frame", { Size = UDim2.new(1, 0, 0, 40), BackgroundColor3 = C.el, BackgroundTransparency = .25, BorderSizePixel = 0 }, main)
local dot = new("Frame", { Position = UDim2.fromOffset(14, 15), Size = UDim2.fromOffset(10, 10), BorderSizePixel = 0 }, title)
corner(dot, 5); accentBind(dot, "BackgroundColor3")
new("TextLabel", {
    BackgroundTransparency = 1, Position = UDim2.fromOffset(32, 0), Size = UDim2.fromOffset(240, 40),
    Text = "YL KUKIRIN // EXEC", Font = Enum.Font.GothamBold, TextSize = 15,
    TextColor3 = C.text, TextXAlignment = Enum.TextXAlignment.Left,
}, title)
local timeLbl = new("TextLabel", {
    BackgroundTransparency = 1, AnchorPoint = Vector2.new(1, 0), Position = UDim2.new(1, -92, 0, 0),
    Size = UDim2.fromOffset(90, 40), Text = "00:00", Font = Enum.Font.GothamMedium, TextSize = 13,
    TextColor3 = C.sub, TextXAlignment = Enum.TextXAlignment.Right,
}, title)

local function titleBtn(txt, xOff)
    local b = new("TextButton", {
        AnchorPoint = Vector2.new(1, .5), Position = UDim2.new(1, xOff, .5, 0), Size = UDim2.fromOffset(26, 26),
        BackgroundColor3 = C.el2, Text = txt, Font = Enum.Font.GothamBold, TextSize = 15,
        TextColor3 = C.text, AutoButtonColor = true, BorderSizePixel = 0,
    }, title)
    corner(b, 7)
    return b
end
local btnMin   = titleBtn("-", -40)
local btnClose = titleBtn("x", -8)

-- body
local body = new("Frame", { Position = UDim2.fromOffset(0, 40), Size = UDim2.new(1, 0, 1, -40), BackgroundTransparency = 1 }, main)

local side = new("Frame", { Size = UDim2.new(0, 128, 1, 0), BackgroundColor3 = C.el, BackgroundTransparency = .35, BorderSizePixel = 0 }, body)
new("UIListLayout", { Padding = UDim.new(0, 6), SortOrder = Enum.SortOrder.LayoutOrder }, side)
new("UIPadding", { PaddingTop = UDim.new(0, 10), PaddingLeft = UDim.new(0, 8), PaddingRight = UDim.new(0, 8) }, side)

local content = new("Frame", { Position = UDim2.fromOffset(136, 0), Size = UDim2.new(1, -144, 1, 0), BackgroundTransparency = 1 }, body)

local pages, tabBtns = {}, {}
local function showPage(id)
    for n, p in pairs(pages) do p.Visible = (n == id) end
    for n, t in pairs(tabBtns) do
        local on = (n == id)
        t.btn.BackgroundColor3 = on and C.el2 or C.el
        t.btn.BackgroundTransparency = on and 0 or 1
        t.btn.TextColor3 = on and C.text or C.sub
        t.bar.Visible = on
    end
end

local function Page(id, tkey, order)
    local p = new("ScrollingFrame", {
        Size = UDim2.new(1, 0, 1, 0), BackgroundTransparency = 1, BorderSizePixel = 0,
        ScrollBarThickness = 3, CanvasSize = UDim2.new(), AutomaticCanvasSize = Enum.AutomaticSize.Y,
        Visible = false,
    }, content)
    new("UIListLayout", { Padding = UDim.new(0, 6), SortOrder = Enum.SortOrder.LayoutOrder }, p)
    new("UIPadding", { PaddingTop = UDim.new(0, 10), PaddingBottom = UDim.new(0, 10), PaddingRight = UDim.new(0, 6) }, p)
    pages[id] = p

    local b = new("TextButton", {
        Size = UDim2.new(1, 0, 0, 34), BackgroundColor3 = C.el, BackgroundTransparency = 1, BorderSizePixel = 0,
        Text = "", Font = Enum.Font.GothamMedium, TextSize = 13, TextColor3 = C.sub,
        TextXAlignment = Enum.TextXAlignment.Left, AutoButtonColor = false, LayoutOrder = order,
    }, side)
    bindText(b, tkey, "   ")
    corner(b, 8)
    local bar = new("Frame", { Size = UDim2.new(0, 3, .6, 0), Position = UDim2.new(0, 0, .2, 0), BorderSizePixel = 0, Visible = false }, b)
    corner(bar, 2); accentBind(bar, "BackgroundColor3")
    tabBtns[id] = { btn = b, bar = bar }
    b.MouseButton1Click:Connect(function() showPage(id) end)
    return p
end

----------------------------------------------------------------
-- WIDGETS
----------------------------------------------------------------
local function Label(page, key, h)
    local row = new("Frame", { Size = UDim2.new(1, -6, 0, h or 30), BackgroundColor3 = C.el, BackgroundTransparency = .2, BorderSizePixel = 0 }, page)
    corner(row, 8)
    local l = new("TextLabel", {
        BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 0), Size = UDim2.new(1, -24, 1, 0),
        Text = "", Font = Enum.Font.Gotham, TextSize = 12, TextColor3 = C.sub,
        TextXAlignment = Enum.TextXAlignment.Left, TextWrapped = true,
    }, row)
    if key then bindText(l, key) end
    return l
end

local function Toggle(page, tkey, key, cb)
    local row = new("Frame", { Size = UDim2.new(1, -6, 0, 34), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, page)
    corner(row, 8)
    local lbl = new("TextLabel", {
        BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 0), Size = UDim2.new(1, -70, 1, 0),
        Text = "", Font = Enum.Font.GothamMedium, TextSize = 13, TextColor3 = C.text, TextXAlignment = Enum.TextXAlignment.Left,
        TextTruncate = Enum.TextTruncate.AtEnd,
    }, row)
    bindText(lbl, tkey)
    local sw = new("TextButton", {
        AnchorPoint = Vector2.new(1, .5), Position = UDim2.new(1, -10, .5, 0), Size = UDim2.fromOffset(40, 20),
        Text = "", AutoButtonColor = false, BackgroundColor3 = C.off, BorderSizePixel = 0,
    }, row)
    corner(sw, 10)
    local knob = new("Frame", { Size = UDim2.fromOffset(14, 14), Position = UDim2.fromOffset(3, 3), BackgroundColor3 = Color3.new(1, 1, 1), BorderSizePixel = 0 }, sw)
    corner(knob, 7)
    local function render()
        local on = S[key]
        TweenService:Create(knob, TweenInfo.new(.15), { Position = on and UDim2.fromOffset(23, 3) or UDim2.fromOffset(3, 3) }):Play()
        TweenService:Create(sw, TweenInfo.new(.15), { BackgroundColor3 = on and S.accent or C.off }):Play()
    end
    sw.MouseButton1Click:Connect(function()
        S[key] = not S[key]
        render()
        if cb then cb(S[key]) end
    end)
    render()
    table.insert(refreshers, render)
    toggles[key] = render
end

local function Slider(page, tkey, key, mn, mx, step, fmt, cb)
    local row = new("Frame", { Size = UDim2.new(1, -6, 0, 46), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, page)
    corner(row, 8)
    local lbl = new("TextLabel", {
        BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 4), Size = UDim2.new(.6, 0, 0, 18),
        Text = "", Font = Enum.Font.GothamMedium, TextSize = 13, TextColor3 = C.text, TextXAlignment = Enum.TextXAlignment.Left,
        TextTruncate = Enum.TextTruncate.AtEnd,
    }, row)
    bindText(lbl, tkey)
    local val = new("TextLabel", {
        BackgroundTransparency = 1, AnchorPoint = Vector2.new(1, 0), Position = UDim2.new(1, -12, 0, 4), Size = UDim2.fromOffset(80, 18),
        Font = Enum.Font.GothamBold, TextSize = 13, TextColor3 = C.sub, TextXAlignment = Enum.TextXAlignment.Right,
    }, row)
    local bar = new("Frame", { Position = UDim2.new(0, 12, 0, 31), Size = UDim2.new(1, -24, 0, 6), BackgroundColor3 = C.off, BorderSizePixel = 0 }, row)
    corner(bar, 3)
    local fill = new("Frame", { Size = UDim2.fromScale(0, 1), BorderSizePixel = 0 }, bar)
    corner(fill, 3); accentBind(fill, "BackgroundColor3")
    local hit = new("TextButton", { BackgroundTransparency = 1, Text = "", Position = UDim2.new(0, -6, 0, -10), Size = UDim2.new(1, 12, 0, 26) }, bar)

    local function render()
        local a = (S[key] - mn) / (mx - mn)
        fill.Size = UDim2.fromScale(math.clamp(a, 0, 1), 1)
        local v = S[key]
        if fmt and fmt:find("%%d") then v = math.floor(v + .5) end
        val.Text = string.format(fmt or "%d", v)
    end
    local function setFromX(x)
        local a = math.clamp((x - bar.AbsolutePosition.X) / bar.AbsoluteSize.X, 0, 1)
        local v = mn + a * (mx - mn)
        v = math.floor(v / step + .5) * step
        S[key] = math.clamp(v, mn, mx)
        render()
        if cb then cb(S[key]) end
    end
    local dragging = false
    hit.InputBegan:Connect(function(i)
        if i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch then
            dragging = true; setFromX(i.Position.X)
        end
    end)
    UIS.InputChanged:Connect(function(i)
        if dragging and (i.UserInputType == Enum.UserInputType.MouseMovement or i.UserInputType == Enum.UserInputType.Touch) then
            setFromX(i.Position.X)
        end
    end)
    UIS.InputEnded:Connect(function(i)
        if i.UserInputType == Enum.UserInputType.MouseButton1 or i.UserInputType == Enum.UserInputType.Touch then dragging = false end
    end)
    render()
end

local function Button(page, tkey, cb)
    local b = new("TextButton", {
        Size = UDim2.new(1, -6, 0, 34), BorderSizePixel = 0, Text = "", Font = Enum.Font.GothamBold,
        TextSize = 13, TextColor3 = Color3.new(1, 1, 1), AutoButtonColor = true,
    }, page)
    bindText(b, tkey)
    corner(b, 8); accentBind(b, "BackgroundColor3")
    b.MouseButton1Click:Connect(function() if cb then cb() end end)
    return b
end

local listening
local function KeyBind(page, tkey, key)
    local row = new("Frame", { Size = UDim2.new(1, -6, 0, 34), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, page)
    corner(row, 8)
    local lbl = new("TextLabel", {
        BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 0), Size = UDim2.new(1, -110, 1, 0),
        Text = "", Font = Enum.Font.GothamMedium, TextSize = 13, TextColor3 = C.text, TextXAlignment = Enum.TextXAlignment.Left,
        TextTruncate = Enum.TextTruncate.AtEnd,
    }, row)
    bindText(lbl, tkey)
    local b = new("TextButton", {
        AnchorPoint = Vector2.new(1, .5), Position = UDim2.new(1, -8, .5, 0), Size = UDim2.fromOffset(84, 24),
        BackgroundColor3 = C.el2, BorderSizePixel = 0, Text = S[key].Name, Font = Enum.Font.GothamBold,
        TextSize = 11, TextColor3 = C.text, TextTruncate = Enum.TextTruncate.AtEnd,
    }, row)
    corner(b, 6)
    b.MouseButton1Click:Connect(function()
        b.Text = T("press")
        listening = { key = key, btn = b }
    end)
end

----------------------------------------------------------------
-- TOAST
----------------------------------------------------------------
local toastLbl = new("TextLabel", {
    AnchorPoint = Vector2.new(.5, 1), Position = UDim2.new(.5, 0, 1, -10), Size = UDim2.fromOffset(340, 28),
    BackgroundColor3 = C.el2, TextColor3 = C.text, Font = Enum.Font.GothamMedium, TextSize = 12,
    BorderSizePixel = 0, Visible = false, ZIndex = 10, TextTruncate = Enum.TextTruncate.AtEnd,
}, main)
corner(toastLbl, 8)
local toastId = 0
local function toast(t)
    toastId += 1
    local id = toastId
    toastLbl.Text = t; toastLbl.Visible = true
    task.delay(2.4, function() if id == toastId then toastLbl.Visible = false end end)
end

----------------------------------------------------------------
-- LOGIC : CONTROLLER (wheelie + road)
----------------------------------------------------------------
local rayP = RaycastParams.new()
rayP.FilterType = Enum.RaycastFilterType.Exclude

local ctl = {}
local lastSeat, lastJump = nil, 0

-- ROAD DETECTION
-- The road is recognised by what it is made of (material + colour), learned from the
-- surface under the scooter. Grass, dirt, walls, houses and roofs are never "road".
-- Then the script measures where the left and right edges of the road are, ahead of the
-- scooter, and steers to the middle between them (works on straight roads, curves, meshes).
local NOT_ROAD = {
    [Enum.Material.Grass] = true, [Enum.Material.LeafyGrass] = true, [Enum.Material.Ground] = true,
    [Enum.Material.Sand] = true, [Enum.Material.Mud] = true, [Enum.Material.Snow] = true,
    [Enum.Material.Rock] = true, [Enum.Material.Water] = true, [Enum.Material.Wood] = true,
    [Enum.Material.WoodPlanks] = true, [Enum.Material.Brick] = true, [Enum.Material.Sandstone] = true,
}
local roadSigs = {} -- { mat = Enum.Material, col = Color3 }

local function stopCtl()
    for _, k in ipairs({ "ao", "lv", "att" }) do
        if ctl[k] then pcall(function() ctl[k]:Destroy() end) end
    end
    ctl = {}
end

local function surfColor(res)
    local i = res.Instance
    if not i then return nil end
    if i:IsA("Terrain") then
        local ok, c = pcall(function() return i:GetMaterialColor(res.Material) end)
        return ok and c or nil
    end
    if i:IsA("BasePart") then return i.Color end
    return nil
end

local function colorDist(a, b)
    return math.abs(a.R - b.R) + math.abs(a.G - b.G) + math.abs(a.B - b.B)
end

-- thin white / yellow painted line lying on the road
local function isLine(res)
    local i = res.Instance
    if i and i:IsA("BasePart") and not i:IsA("Terrain") and i.Size.Y <= 1.5 then
        local c = i.Color
        if c.R > .7 and c.G > .7 and c.B > .55 then return true end -- white
        if c.R > .8 and c.G > .65 and c.B < .4 then return true end -- yellow
    end
    return false
end

local function isRoad(res, gy)
    if math.abs(res.Position.Y - gy) > 3 then return false end
    if NOT_ROAD[res.Material] then return false end
    if res.Normal.Y < .7 then return false end
    local c = surfColor(res)
    if not c then return false end
    for _, s in ipairs(roadSigs) do
        if s.mat == res.Material and colorDist(s.col, c) < .12 then return true end
    end
    return isLine(res)
end

-- remember what the road is made of (surface under the scooter)
local function learnRoad(g)
    if not g or NOT_ROAD[g.Material] or isLine(g) then return false end
    local c = surfColor(g)
    if not c then return false end
    for _, s in ipairs(roadSigs) do
        if s.mat == g.Material and colorDist(s.col, c) < .12 then return true end
    end
    table.insert(roadSigs, { mat = g.Material, col = c })
    return true
end

local function startCtl(seat)
    stopCtl()
    local char = LP.Character
    local filter = { char }
    local ok, parts = pcall(function() return seat:GetConnectedParts(true) end)
    if ok then for _, p in ipairs(parts) do table.insert(filter, p) end end
    table.insert(filter, seat)
    rayP.FilterDescendantsInstances = filter

    local mass = math.max(seat.AssemblyMass, 1)
    local F = mass * Workspace.Gravity * 25

    local att = new("Attachment", { Name = "YL_Att" }, seat)
    local ao = new("AlignOrientation", {
        Mode = Enum.OrientationAlignmentMode.OneAttachment, Attachment0 = att,
        RigidityEnabled = false, MaxTorque = 1e9, MaxAngularVelocity = 1e3, Responsiveness = 60,
    }, seat)
    local lv = new("LinearVelocity", {
        Attachment0 = att, RelativeTo = Enum.ActuatorRelativeTo.World,
        ForceLimitsEnabled = true, ForceLimitMode = Enum.ForceLimitMode.PerAxis,
        MaxAxesForce = Vector3.new(F, F, F), VelocityConstraintMode = Enum.VelocityConstraintMode.Vector,
        VectorVelocity = Vector3.zero,
    }, seat)

    local g = Workspace:Raycast(seat.Position + Vector3.new(0, 2, 0), Vector3.new(0, -60, 0), rayP)
    local look = seat.CFrame.LookVector * (S.flip and -1 or 1)

    ctl = {
        seat = seat, att = att, ao = ao, lv = lv, F = F,
        yaw = math.atan2(-look.X, -look.Z), pitch = 0, slope = 0, spd = 0,
        hover = g and (seat.Position.Y - g.Position.Y) or nil,
        groundY = g and g.Position.Y or seat.Position.Y,
        scanT = 0, lostT = 0, roadAngle = nil, roadOff = 0,
    }
    if g then learnRoad(g) end
end

local function wrapPi(a) return (a + math.pi) % (2 * math.pi) - math.pi end

-- Measures the road ahead on 3 rows (near / mid / far). On each row it casts rays across
-- (+-30 studs), finds the road run around the middle, and takes the middle between its
-- left and right edges. Returns the angle to steer (deg, + = left) and the side offset.
local STEP, NSIDE = 2.5, 12
local function edgeSteer(pos, yaw, spd, gy)
    local h = Vector3.new(-math.sin(yaw), 0, -math.cos(yaw))
    local r = Vector3.new(math.cos(yaw), 0, -math.sin(yaw))
    local Ls = 8 + spd * .3
    local rows = { { 3, .25 }, { Ls, .5 }, { Ls * 2, .25 } }
    local sumA, sumW, off0 = 0, 0, nil
    for ri, row in ipairs(rows) do
        local dist, w = row[1], row[2]
        local base = pos + h * dist
        local flags = {}
        for k = -NSIDE, NSIDE do
            local p = base + r * (k * STEP)
            local res = Workspace:Raycast(Vector3.new(p.X, gy + 5, p.Z), Vector3.new(0, -25, 0), rayP)
            flags[k] = (res ~= nil) and isRoad(res, gy) or false
        end
        local c0
        for d = 0, NSIDE do
            if flags[d] then c0 = d; break end
            if flags[-d] then c0 = -d; break end
        end
        if c0 then
            local lo, hi = c0, c0
            local miss, k = 0, c0 - 1
            while k >= -NSIDE do -- left edge (one missing sample tolerated, e.g. lane line gaps)
                if flags[k] then lo = k; miss = 0
                elseif miss < 1 then miss += 1
                else break end
                k -= 1
            end
            miss, k = 0, c0 + 1
            while k <= NSIDE do -- right edge
                if flags[k] then hi = k; miss = 0
                elseif miss < 1 then miss += 1
                else break end
                k += 1
            end
            local oc = (lo + hi) / 2 * STEP -- + = road middle is on my right
            if ri == 1 then off0 = oc end
            sumA += -math.deg(math.atan2(oc, dist)) * w
            sumW += w
        end
    end
    if sumW == 0 then return nil end
    return sumA / sumW, off0
end

local function stepCtl(dt, hum)
    local seat = ctl.seat
    local pos = seat.Position

    -- steering
    local right = Vector3.new(math.cos(ctl.yaw), 0, -math.sin(ctl.yaw))
    local steer = 0
    if not UIS:GetFocusedTextBox() then
        if UIS:IsKeyDown(Enum.KeyCode.A) or UIS:IsKeyDown(Enum.KeyCode.Left) then steer -= 1 end
        if UIS:IsKeyDown(Enum.KeyCode.D) or UIS:IsKeyDown(Enum.KeyCode.Right) then steer += 1 end
    end
    if steer == 0 then steer = math.clamp(hum.MoveDirection:Dot(right) * 1.2, -1, 1) end

    -- ground (before the road scan)
    local g = Workspace:Raycast(pos + Vector3.new(0, 2, 0), Vector3.new(0, -60, 0), rayP)
    if g then ctl.groundY = g.Position.Y end

    -- road following: steer to the middle of the road
    ctl.scanT += dt
    if S.autoFollow then
        if ctl.scanT > .05 then
            ctl.scanT = 0
            local raw, off = edgeSteer(pos, ctl.yaw, ctl.spd, ctl.groundY)
            if raw then
                ctl.lostT = 0
                ctl.roadOff = off or 0
                ctl.roadAngle = ctl.roadAngle and (ctl.roadAngle + (raw - ctl.roadAngle) * .6) or raw
            else
                ctl.lostT += .05
                if ctl.lostT > .5 then ctl.roadAngle = nil end
            end
        end
    else
        ctl.roadAngle = nil
    end
    local auto = 0
    if S.autoFollow and ctl.roadAngle and math.abs(ctl.roadAngle) > .8 then
        auto = math.clamp(math.rad(ctl.roadAngle) * S.followGain, -3, 3)
        if steer ~= 0 then auto *= .25 end
    end
    ctl.yaw += (-steer * S.turnRate + auto) * dt

    local dir = Vector3.new(-math.sin(ctl.yaw), 0, -math.cos(ctl.yaw))

    -- slope
    local slopeT = 0
    if g and S.followSlope then
        slopeT = math.clamp(math.atan2(-g.Normal:Dot(dir), g.Normal.Y), -.8, .8)
    end
    ctl.slope += (slopeT - ctl.slope) * math.min(1, dt * 8)

    -- pitch (front wheel up)
    ctl.pitch += (math.rad(S.pitch) - ctl.pitch) * math.min(1, dt * 5)
    local cf = CFrame.Angles(0, ctl.yaw, 0) * CFrame.Angles(ctl.pitch + ctl.slope, 0, 0)
    if S.flip then cf = cf * CFrame.Angles(0, math.pi, 0) end
    ctl.ao.CFrame = cf

    -- speed
    local want = S.autoForward and 1 or math.clamp(hum.MoveDirection:Dot(dir), 0, 1)
    if S.autoFollow then
        if ctl.roadAngle then
            want *= math.clamp(1 - math.abs(ctl.roadAngle) / 70, .4, 1) -- slow down in curves
        else
            want *= .15 -- road lost: crawl instead of driving into houses / grass
        end
    end
    ctl.spd += (S.speed * want - ctl.spd) * math.min(1, dt * 3)

    -- stick to road (no hops)
    local vy, ymax = 0, 0
    if S.roadGlue and g and ctl.hover then
        local target = g.Position.Y + ctl.hover + math.sin(ctl.pitch) * S.rearOffset
        vy = math.clamp((target - pos.Y) * 12, -80, 40)
        ymax = ctl.F
    end
    ctl.lv.MaxAxesForce = Vector3.new(ctl.F, ymax, ctl.F)
    ctl.lv.VectorVelocity = dir * ctl.spd + Vector3.new(0, vy, 0)
end

----------------------------------------------------------------
-- LOGIC : PUMPKIN EVENT
----------------------------------------------------------------
-- names that identify a pumpkin (add more if the game uses another name)
local PUMPKIN_WORDS = { "pumpkin", "pumpink", "citrouille", "courge", "calabaza" }

local function nameMatches(n)
    n = n:lower()
    for _, w in ipairs(PUMPKIN_WORDS) do
        if n:find(w, 1, true) then return true end
    end
    return false
end

-- returns the list of parts that can really be picked up (touch or proximity prompt)
local function findCollectables(root)
    local out = {}
    local parts = {}
    if root:IsA("BasePart") then table.insert(parts, root) end
    for _, d in ipairs(root:GetDescendants()) do
        if d:IsA("BasePart") then table.insert(parts, d) end
    end
    for _, p in ipairs(parts) do
        if p.CanTouch and p:FindFirstChild("TouchInterest") then
            table.insert(out, { part = p, kind = "touch" })
        end
    end
    for _, d in ipairs(root:GetDescendants()) do
        if d:IsA("ProximityPrompt") and d.Enabled and d.Parent and d.Parent:IsA("BasePart") then
            table.insert(out, { part = d.Parent, kind = "prompt", prompt = d })
        end
    end
    return out
end

local function scanPumpkins()
    local roots, rootSet = {}, {}
    local char = LP.Character
    local cnt = 0
    for _, d in ipairs(Workspace:GetDescendants()) do
        cnt += 1
        if cnt % 5000 == 0 then task.wait() end
        if nameMatches(d.Name) and (d:IsA("BasePart") or d:IsA("Model") or d:IsA("Folder"))
            and not d:IsA("Terrain") and not (char and d:IsDescendantOf(char)) then
            if d:IsA("Folder") then
                for _, c in ipairs(d:GetChildren()) do
                    if (c:IsA("BasePart") or c:IsA("Model")) and not rootSet[c] then
                        rootSet[c] = true; table.insert(roots, c)
                    end
                end
            elseif not rootSet[d] then
                rootSet[d] = true; table.insert(roots, d)
            end
        end
    end

    local list, byPart, ignored = {}, {}, 0
    for _, r in ipairs(roots) do
        local found = findCollectables(r)
        if #found == 0 then
            ignored += 1
            print("[YL] ignored (not collectable): " .. r:GetFullName())
        end
        for _, e in ipairs(found) do
            if not byPart[e.part] then
                byPart[e.part] = true
                e.root, e.t0 = r, e.part.Transparency
                table.insert(list, e)
            end
        end
    end
    return list, ignored
end

-- still there / still collectable ?
local function alive(e)
    local p = e.part
    if not p.Parent or not p:IsDescendantOf(Workspace) then return false end
    if p.Transparency > e.t0 + .5 then return false end
    if e.kind == "touch" and not p.CanTouch then return false end
    if e.kind == "prompt" and (not e.prompt.Parent or not e.prompt.Enabled) then return false end
    return true
end

local function tpTo(hrp, pos)
    hrp.AssemblyLinearVelocity = Vector3.zero
    hrp.AssemblyAngularVelocity = Vector3.zero
    hrp.CFrame = CFrame.new(pos)
end

local function poke(e, hrp)
    pcall(function()
        if e.kind == "touch" and firetouchinterest then
            firetouchinterest(hrp, e.part, 0)
            task.wait()
            firetouchinterest(hrp, e.part, 1)
        elseif e.kind == "prompt" and fireproximityprompt then
            fireproximityprompt(e.prompt)
        end
    end)
end

local function getChar()
    local char = LP.Character
    local hum = char and char:FindFirstChildOfClass("Humanoid")
    local hrp = char and char:FindFirstChild("HumanoidRootPart")
    return char, hum, hrp
end

local function collectLoop()
    if ev.active then return end
    ev.active = true
    ev.collected, ev.found, ev.list = 0, 0, {}

    local _, hum, hrp = getChar()
    if not (hum and hrp) then
        ev.active = false
        S.autoPumpkin = false
        if toggles.autoPumpkin then toggles.autoPumpkin() end
        return
    end

    local seat = hum.SeatPart or lastSeat
    if seat and not seat.Parent then seat = nil end
    local homePos = hrp.Position

    -- scan
    ev.state = "ev_scanning"
    local list, ignored = scanPumpkins()
    ev.list, ev.found = list, #list
    toast(#list == 0 and T("ev_none") or T("ev_found"):format(#list, ignored))

    local natural = false
    if S.autoPumpkin and #list > 0 then
        -- get off the scooter and stay off until done / disabled
        if hum.SeatPart then
            hum.Sit = false
            task.wait(.1)
            if hum.SeatPart then
                pcall(function() hum:ChangeState(Enum.HumanoidStateType.Jumping) end)
                task.wait(.25)
            end
        end

        ev.state = "ev_collecting"
        local rescanned = false

        local function nextTarget(pos)
            local best, bd
            for _, e in ipairs(ev.list) do
                if not e.done then
                    if not alive(e) then
                        e.done = true -- already gone (taken / hidden)
                    else
                        local d = (e.part.Position - pos).Magnitude
                        if not bd or d < bd then best, bd = e, d end
                    end
                end
            end
            return best
        end

        while S.autoPumpkin do
            local _, h2, r2 = getChar()
            if not (h2 and r2) then
                task.wait(.3)
            else
                local e = nextTarget(r2.Position)
                if not e then
                    if rescanned then natural = true; break end
                    rescanned = true -- one last scan for pumpkins that appeared meanwhile
                    local nl = scanPumpkins()
                    local known = {}
                    for _, x in ipairs(ev.list) do known[x.part] = true end
                    for _, x in ipairs(nl) do
                        if not known[x.part] then table.insert(ev.list, x) end
                    end
                    ev.found = #ev.list
                else
                    local got = false
                    for _ = 1, 2 do
                        if not S.autoPumpkin then break end
                        local _, h3, r3 = getChar()
                        if not (h3 and r3) then break end
                        tpTo(r3, e.part.Position + Vector3.new(0, 1.5, 0))
                        task.wait(S.pumpDelay)
                        poke(e, r3)
                        task.wait(.12)
                        if not alive(e) then got = true; break end
                    end
                    e.done = true
                    if got then ev.collected += 1 end
                end
            end
        end
    end

    -- done or disabled: switch the toggle off, then go back to the scooter
    S.autoPumpkin = false
    if toggles.autoPumpkin then toggles.autoPumpkin() end
    if #ev.list > 0 then toast(natural and T("ev_done") or T("ev_off")) end

    ev.state = "ev_returning"
    local _, h4, r4 = getChar()
    if h4 and r4 and #ev.list > 0 then
        if seat and seat.Parent then
            for _ = 1, 12 do
                if h4.SeatPart == seat then break end
                tpTo(r4, seat.Position + Vector3.new(0, 3, 0))
                task.wait(.1)
                pcall(function() seat:Sit(h4) end)
                task.wait(.15)
            end
            if h4.SeatPart ~= seat then toast(T("ev_back_fail")) end
        else
            tpTo(r4, homePos + Vector3.new(0, 3, 0))
            toast(T("ev_back_fail"))
        end
    end

    ev.state = "ev_idle"
    ev.active = false
end

----------------------------------------------------------------
-- LOGIC : PROTECTION
----------------------------------------------------------------
local function applyRagdollStates(char)
    local hum = char and char:FindFirstChildOfClass("Humanoid")
    if not hum then return end
    for _, st in ipairs({ Enum.HumanoidStateType.Ragdoll, Enum.HumanoidStateType.FallingDown }) do
        pcall(function() hum:SetStateEnabled(st, not S.antiRagdoll) end)
    end
end

local protT = 0
local function protectionStep(dt, char, hum, hrp)
    if S.antiRagdoll then
        local st = hum:GetState()
        if st == Enum.HumanoidStateType.Ragdoll or st == Enum.HumanoidStateType.FallingDown
            or (st == Enum.HumanoidStateType.Physics and not hum.SeatPart) then
            pcall(function() hum:ChangeState(hum.SeatPart and Enum.HumanoidStateType.Seated or Enum.HumanoidStateType.GettingUp) end)
        end
        if hum.PlatformStand then hum.PlatformStand = false end
        protT += dt
        if protT > .25 then
            protT = 0
            for _, d in ipairs(char:GetDescendants()) do
                if d:IsA("BallSocketConstraint") then
                    pcall(function() d:Destroy() end)
                elseif d:IsA("Motor6D") and not d.Enabled then
                    d.Enabled = true
                end
            end
        end
    end

    if S.antiSpin and hrp and not ctl.seat then
        if hrp.AssemblyAngularVelocity.Magnitude > 40 then hrp.AssemblyAngularVelocity = Vector3.zero end
    end

    -- stay on scooter if ejected (paused while the pumpkin event runs)
    if S.stayOnSeat and not ev.active and hum.SeatPart == nil and lastSeat and lastSeat.Parent and hrp
        and (tick() - lastJump) > 1.2 and (hrp.Position - lastSeat.Position).Magnitude < 12
        and (lastSeat:IsA("Seat") or lastSeat:IsA("VehicleSeat")) and not lastSeat.Occupant then
        pcall(function() lastSeat:Sit(hum) end)
    end
end

UIS.JumpRequest:Connect(function() lastJump = tick() end)

LP.CharacterAdded:Connect(function(char)
    stopCtl()
    lastSeat = ev.active and lastSeat or nil
    char:WaitForChild("Humanoid", 5)
    applyRagdollStates(char)
end)

----------------------------------------------------------------
-- LANGUAGE
----------------------------------------------------------------
local function setLang(code)
    if not L[code] then return end
    S.lang = code
    for _, f in ipairs(langBinds) do f() end
    for _, fn in ipairs(refreshers) do fn() end
    pcall(function()
        if writefile then writefile(LANG_FILE, code) end
    end)
end

----------------------------------------------------------------
-- PAGES
----------------------------------------------------------------
local pWheelie = Page("wheelie", "tab_wheelie", 1)
Label(pWheelie, "info_wheelie", 46)
Toggle(pWheelie, "wheelie_t", "wheelie", function(on)
    if on then
        local _, hum = getChar()
        if not (hum and hum.SeatPart) then toast(T("sit_first")) end
    else
        stopCtl()
    end
end)
Slider(pWheelie, "pitch", "pitch", 5, 70, 1, "%d°")
Slider(pWheelie, "speed", "speed", 10, 150, 1, "%d")
Toggle(pWheelie, "autofwd", "autoForward")
Slider(pWheelie, "turnrate", "turnRate", .5, 4, .1, "%.1f")
Toggle(pWheelie, "flip", "flip", function() stopCtl() end)

local pRoad = Page("road", "tab_road", 2)
Label(pRoad, "info_road", 46)
Toggle(pRoad, "autofollow", "autoFollow")
Slider(pRoad, "gain", "followGain", .5, 8, .1, "%.1f")
Toggle(pRoad, "glue", "roadGlue")
Toggle(pRoad, "slopes", "followSlope")
Slider(pRoad, "rear", "rearOffset", 0, 8, .25, "%.2f")
Button(pRoad, "learn", function()
    -- forget what the road is made of and learn the surface under the scooter now
    local _, hum, hrp = getChar()
    if not (hum and hrp) then return end
    local f = { LP.Character }
    if hum.SeatPart then table.insert(f, hum.SeatPart:FindFirstAncestorOfClass("Model") or hum.SeatPart) end
    rayP.FilterDescendantsInstances = f
    local origin = (hum.SeatPart and hum.SeatPart.Position or hrp.Position) + Vector3.new(0, 2, 0)
    local g = Workspace:Raycast(origin, Vector3.new(0, -60, 0), rayP)
    if not g then toast(T("no_ground")); return end
    roadSigs = {}
    if learnRoad(g) then toast(T("road_learned"):format(tostring(g.Material):gsub("Enum.Material.", ""))) end
end)

local pEv = Page("events", "tab_events", 3)
Label(pEv, "info_events", 74)
Toggle(pEv, "ev_auto", "autoPumpkin", function(on)
    if on then
        task.spawn(function()
            while ev.active do task.wait(.1) end
            if S.autoPumpkin then collectLoop() end
        end)
    end
end)
Slider(pEv, "ev_delay", "pumpDelay", .1, 1.5, .05, "%.2fs")
Button(pEv, "ev_scan", function()
    if ev.active then return end
    task.spawn(function()
        local list, ignored = scanPumpkins()
        ev.found = #list
        toast(#list == 0 and T("ev_none") or T("ev_found"):format(#list, ignored))
    end)
end)
local stPump = Label(pEv, nil, 30)

local pProt = Page("prot", "tab_prot", 4)
Toggle(pProt, "anti_rag", "antiRagdoll", function() applyRagdollStates(LP.Character) end)
Toggle(pProt, "stay", "stayOnSeat")
Toggle(pProt, "anti_spin", "antiSpin")

local pStat = Page("status", "tab_status", 5)
local stSeat  = Label(pStat, nil)
local stWhee  = Label(pStat, nil)
local stSpeed = Label(pStat, nil)
local stPitch = Label(pStat, nil)
local stRoad  = Label(pStat, nil)
local stPump2 = Label(pStat, nil)
local stKey   = Label(pStat, nil)

local pSet = Page("set", "tab_set", 6)
do
    -- language
    local row = new("Frame", { Size = UDim2.new(1, -6, 0, 66), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, pSet)
    corner(row, 8)
    local lbl = new("TextLabel", {
        BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 4), Size = UDim2.new(1, -24, 0, 18),
        Text = "", Font = Enum.Font.GothamMedium, TextSize = 13, TextColor3 = C.text, TextXAlignment = Enum.TextXAlignment.Left,
    }, row)
    bindText(lbl, "language")
    local holder = new("Frame", { BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 28), Size = UDim2.new(1, -24, 0, 30) }, row)
    new("UIListLayout", {
        FillDirection = Enum.FillDirection.Horizontal, Padding = UDim.new(0, 8),
        VerticalAlignment = Enum.VerticalAlignment.Center,
    }, holder)
    local btns = {}
    for _, lg in ipairs(LANGS) do
        local b = new("TextButton", {
            Size = UDim2.fromOffset(100, 28), BackgroundColor3 = C.el2, Text = lg.name, Font = Enum.Font.GothamBold,
            TextSize = 12, TextColor3 = C.text, BorderSizePixel = 0, AutoButtonColor = false,
        }, holder)
        corner(b, 7)
        btns[lg.code] = b
        b.MouseButton1Click:Connect(function() setLang(lg.code) end)
    end
    local function render()
        for code, b in pairs(btns) do b.BackgroundColor3 = (code == S.lang) and S.accent or C.el2 end
    end
    render()
    table.insert(refreshers, render)
end
do
    -- accent colors
    local row = new("Frame", { Size = UDim2.new(1, -6, 0, 40), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, pSet)
    corner(row, 8)
    new("UIListLayout", { FillDirection = Enum.FillDirection.Horizontal, Padding = UDim.new(0, 8), VerticalAlignment = Enum.VerticalAlignment.Center }, row)
    new("UIPadding", { PaddingLeft = UDim.new(0, 12) }, row)
    local presets = {
        Color3.fromRGB(90, 140, 255), Color3.fromRGB(150, 100, 255), Color3.fromRGB(60, 210, 230),
        Color3.fromRGB(70, 220, 130), Color3.fromRGB(255, 110, 200), Color3.fromRGB(255, 165, 60),
    }
    for _, col in ipairs(presets) do
        local b = new("TextButton", { Size = UDim2.fromOffset(26, 26), BackgroundColor3 = col, Text = "", BorderSizePixel = 0 }, row)
        corner(b, 13)
        b.MouseButton1Click:Connect(function() setAccent(col) end)
    end
end
Slider(pSet, "panel_size", "scale", .6, 1.3, .05, "%.2f", function() applyScale() end)
Toggle(pSet, "particles", "particles", function(on) pc.Visible = on end)
KeyBind(pSet, "panel_key", "openKey")
KeyBind(pSet, "wheelie_key", "wheelieKey")

local refreshKeys

do
    local pAdm = Page("admin", "tab_admin", 7)
    tabBtns.admin.btn.Visible = false

    local DURS = { { 3600, "1h" }, { 86400, "1d" }, { 604800, "7d" }, { 2592000, "30d" }, { 0, "∞" } }
    local durIdx = 2

    local modeLbl = Label(pAdm, nil, 44)
    local function renderMode()
        modeLbl.Text = Backend.mode() == "server" and T("adm_mode_server") or T("adm_mode_local")
    end
    renderMode()
    table.insert(langBinds, renderMode)

    -- duration presets
    do
        local row = new("Frame", { Size = UDim2.new(1, -6, 0, 66), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, pAdm)
        corner(row, 8)
        local lbl = new("TextLabel", {
            BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 4), Size = UDim2.new(1, -24, 0, 18),
            Text = "", Font = Enum.Font.GothamMedium, TextSize = 13, TextColor3 = C.text,
            TextXAlignment = Enum.TextXAlignment.Left, TextTruncate = Enum.TextTruncate.AtEnd,
        }, row)
        bindText(lbl, "adm_duration")
        local holder = new("Frame", { BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 28), Size = UDim2.new(1, -24, 0, 30) }, row)
        new("UIListLayout", { FillDirection = Enum.FillDirection.Horizontal, Padding = UDim.new(0, 8), VerticalAlignment = Enum.VerticalAlignment.Center }, holder)
        local btns = {}
        local function render()
            for i, b in ipairs(btns) do b.BackgroundColor3 = (i == durIdx) and S.accent or C.el2 end
        end
        for i, d in ipairs(DURS) do
            local b = new("TextButton", {
                Size = UDim2.fromOffset(56, 28), BackgroundColor3 = C.el2, Text = d[2], Font = Enum.Font.GothamBold,
                TextSize = 12, TextColor3 = C.text, BorderSizePixel = 0, AutoButtonColor = false,
            }, holder)
            corner(b, 7)
            btns[i] = b
            b.MouseButton1Click:Connect(function() durIdx = i; render() end)
        end
        render()
        table.insert(refreshers, render)
    end

    Toggle(pAdm, "adm_isadmin", "newAdmin")

    -- label box
    local labelBox
    do
        local row = new("Frame", { Size = UDim2.new(1, -6, 0, 34), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, pAdm)
        corner(row, 8)
        labelBox = new("TextBox", {
            BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 0), Size = UDim2.new(1, -24, 1, 0),
            Text = "", PlaceholderText = T("adm_label_ph"), PlaceholderColor3 = C.sub, TextColor3 = C.text,
            Font = Enum.Font.GothamMedium, TextSize = 13, TextXAlignment = Enum.TextXAlignment.Left,
            ClearTextOnFocus = false,
        }, row)
        table.insert(langBinds, function() labelBox.PlaceholderText = T("adm_label_ph") end)
    end

    -- generated key box (read only, selectable)
    local newKeyBox
    do
        local row = new("Frame", { Size = UDim2.new(1, -6, 0, 34), BackgroundColor3 = C.el, BackgroundTransparency = .15, BorderSizePixel = 0 }, pAdm)
        corner(row, 8)
        newKeyBox = new("TextBox", {
            BackgroundTransparency = 1, Position = UDim2.fromOffset(12, 0), Size = UDim2.new(1, -24, 1, 0),
            Text = "", PlaceholderText = T("adm_newkey_ph"), PlaceholderColor3 = C.sub, TextColor3 = C.text,
            Font = Enum.Font.GothamBold, TextSize = 13, TextXAlignment = Enum.TextXAlignment.Left,
            ClearTextOnFocus = false, TextEditable = false,
        }, row)
        table.insert(langBinds, function() newKeyBox.PlaceholderText = T("adm_newkey_ph") end)
    end

    local listHolder -- created below, used by refreshKeys

    Button(pAdm, "adm_generate", function()
        task.spawn(function()
            local res = Backend.create({ duration = DURS[durIdx][1], admin = S.newAdmin, label = labelBox.Text })
            if res and res.ok and res.key then
                newKeyBox.Text = res.key.key
                pcall(function() if setclipboard then setclipboard(res.key.key) end end)
                toast(T("adm_copied"))
                refreshKeys()
            else
                toast(T("adm_err"))
            end
        end)
    end)
    Button(pAdm, "adm_refresh", function() refreshKeys() end)

    listHolder = new("Frame", { Size = UDim2.new(1, -6, 0, 0), AutomaticSize = Enum.AutomaticSize.Y, BackgroundTransparency = 1, BorderSizePixel = 0 }, pAdm)
    new("UIListLayout", { Padding = UDim.new(0, 6), SortOrder = Enum.SortOrder.LayoutOrder }, listHolder)

    local function durInfo(rec)
        if (rec.duration or 0) == 0 then return T("adm_never") end
        if not rec.firstUse then return T("adm_unused"):format(fmtDur(rec.duration)) end
        local left = (rec.expires or 0) - os.time()
        if left <= 0 then return T("adm_expired") end
        return T("adm_expires"):format(fmtDur(left))
    end

    local function describe(rec)
        local head = rec.admin and "ADMIN" or "USER"
        if rec.label and rec.label ~= "" then head = head .. "  |  " .. rec.label end
        head = head .. "  |  " .. durInfo(rec)
        if rec.revoked then head = head .. "  |  " .. T("adm_revoked") end
        local users = {}
        for _, u in ipairs(rec.users or {}) do
            table.insert(users, string.format("%s (%dx)", tostring(u.name or "?"), u.count or 0))
        end
        local used = #users == 0 and T("adm_nobody") or T("adm_used_by"):format(table.concat(users, ", "))
        return head .. "\n" .. used
    end

    local function smallBtn(parent, text, w, cb)
        local b = new("TextButton", {
            Size = UDim2.fromOffset(w, 26), BackgroundColor3 = C.el2, Text = text, Font = Enum.Font.GothamBold,
            TextSize = 11, TextColor3 = C.text, BorderSizePixel = 0, AutoButtonColor = true,
            TextTruncate = Enum.TextTruncate.AtEnd,
        }, parent)
        corner(b, 6)
        b.MouseButton1Click:Connect(function() task.spawn(cb) end)
        return b
    end

    local function buildRow(rec, order)
        local row = new("Frame", {
            Size = UDim2.new(1, 0, 0, 0), AutomaticSize = Enum.AutomaticSize.Y, BackgroundColor3 = C.el,
            BackgroundTransparency = .15, BorderSizePixel = 0, LayoutOrder = order,
        }, listHolder)
        corner(row, 8)
        new("UIListLayout", { Padding = UDim.new(0, 5), SortOrder = Enum.SortOrder.LayoutOrder }, row)
        new("UIPadding", { PaddingTop = UDim.new(0, 8), PaddingBottom = UDim.new(0, 8), PaddingLeft = UDim.new(0, 10), PaddingRight = UDim.new(0, 10) }, row)

        new("TextBox", {
            Size = UDim2.new(1, 0, 0, 18), BackgroundTransparency = 1, Text = rec.master and T("adm_master") or rec.key,
            TextEditable = false, ClearTextOnFocus = false, Font = Enum.Font.GothamBold, TextSize = 12,
            TextColor3 = C.text, TextXAlignment = Enum.TextXAlignment.Left, LayoutOrder = 1,
        }, row)
        new("TextLabel", {
            Size = UDim2.new(1, 0, 0, 0), AutomaticSize = Enum.AutomaticSize.Y, BackgroundTransparency = 1,
            TextWrapped = true, Font = Enum.Font.Gotham, TextSize = 11, TextColor3 = C.sub,
            TextXAlignment = Enum.TextXAlignment.Left, Text = describe(rec), LayoutOrder = 2,
        }, row)

        if rec.master then return end
        local bar = new("Frame", { Size = UDim2.new(1, 0, 0, 26), BackgroundTransparency = 1, LayoutOrder = 3 }, row)
        new("UIListLayout", { FillDirection = Enum.FillDirection.Horizontal, Padding = UDim.new(0, 6) }, bar)

        smallBtn(bar, rec.admin and T("adm_admin_off") or T("adm_admin_on"), 96, function()
            Backend.update(rec.key, { admin = not rec.admin }); refreshKeys()
        end)
        local cur = 1
        for i, d in ipairs(DURS) do if d[1] == (rec.duration or 0) then cur = i end end
        smallBtn(bar, T("adm_dur_btn"):format(DURS[cur][2]), 96, function()
            local nxt = DURS[cur % #DURS + 1][1]
            Backend.update(rec.key, { duration = nxt }); refreshKeys()
        end)
        smallBtn(bar, rec.revoked and T("adm_restore") or T("adm_revoke"), 96, function()
            Backend.update(rec.key, { revoked = not rec.revoked }); refreshKeys()
        end)
        smallBtn(bar, T("adm_delete"), 96, function()
            Backend.delete(rec.key); refreshKeys()
        end)
    end

    refreshKeys = function()
        task.spawn(function()
            local res = Backend.list()
            for _, c in ipairs(listHolder:GetChildren()) do
                if c:IsA("Frame") then c:Destroy() end
            end
            if not (res and res.ok) then toast(T("adm_err")); return end
            local keys = res.keys or {}
            table.sort(keys, function(a, b)
                if (a.master == true) ~= (b.master == true) then return a.master == true end
                return (a.created or 0) > (b.created or 0)
            end)
            for i, rec in ipairs(keys) do buildRow(rec, i) end
        end)
    end
end

showPage("wheelie")

----------------------------------------------------------------
-- MINIMIZE / CLOSE / REOPEN
----------------------------------------------------------------
local minimized = false
btnMin.MouseButton1Click:Connect(function()
    minimized = not minimized
    body.Visible = not minimized
    main.Size = minimized and UDim2.fromOffset(W, 40) or UDim2.fromOffset(W, H)
    clampToScreen(main)
end)

local reopen = new("TextButton", {
    Size = UDim2.fromOffset(46, 46), Position = UDim2.new(0, 20, .5, 0), BackgroundColor3 = C.bg,
    Text = "YL", Font = Enum.Font.GothamBold, TextSize = 15, TextColor3 = C.text,
    BorderSizePixel = 0, Visible = false, AutoButtonColor = false,
}, gui)
corner(reopen, 23)
do local st = new("UIStroke", { Thickness = 2 }, reopen); accentBind(st, "Color") end

local unlocked = false
local function setPanel(v)
    if not unlocked then return end
    main.Visible = v
    reopen.Visible = not v
    if v then clampToScreen(main) end
end
btnClose.MouseButton1Click:Connect(function() setPanel(false) end)
makeDraggable(reopen, reopen, nil, function() setPanel(true) end, function() clampToScreen(reopen) end)
makeDraggable(title, main, function() return uiScale.Scale end, nil, function() clampToScreen(main) end)

----------------------------------------------------------------
-- KEY SCREEN
----------------------------------------------------------------
local keyFrame = new("Frame", {
    AnchorPoint = Vector2.new(.5, .5), Position = UDim2.fromScale(.5, .5), Size = UDim2.fromOffset(320, 180),
    BackgroundColor3 = C.bg, BorderSizePixel = 0,
}, gui)
corner(keyFrame, 12)
do local st = new("UIStroke", { Thickness = 1.5, Transparency = .35 }, keyFrame); accentBind(st, "Color") end
new("TextLabel", {
    BackgroundTransparency = 1, Position = UDim2.fromOffset(0, 14), Size = UDim2.new(1, 0, 0, 26),
    Text = "YL KUKIRIN // EXEC", Font = Enum.Font.GothamBold, TextSize = 18, TextColor3 = C.text,
}, keyFrame)
local keyHint = new("TextLabel", {
    BackgroundTransparency = 1, Position = UDim2.fromOffset(0, 40), Size = UDim2.new(1, 0, 0, 18),
    Text = "", Font = Enum.Font.Gotham, TextSize = 12, TextColor3 = C.sub,
}, keyFrame)
bindText(keyHint, "enter_key")
local box = new("TextBox", {
    Position = UDim2.fromOffset(30, 70), Size = UDim2.new(1, -60, 0, 36), BackgroundColor3 = C.el,
    Text = "", PlaceholderText = T("key_ph"), PlaceholderColor3 = C.sub, TextColor3 = C.text,
    Font = Enum.Font.GothamMedium, TextSize = 14, ClearTextOnFocus = false, BorderSizePixel = 0,
}, keyFrame)
corner(box, 8)
table.insert(langBinds, function() box.PlaceholderText = T("key_ph") end)
local keyErr = new("TextLabel", {
    BackgroundTransparency = 1, Position = UDim2.fromOffset(0, 150), Size = UDim2.new(1, 0, 0, 18),
    Text = "", Font = Enum.Font.Gotham, TextSize = 12, TextColor3 = Color3.fromRGB(255, 170, 90),
}, keyFrame)
local unlockBtn = new("TextButton", {
    Position = UDim2.fromOffset(30, 114), Size = UDim2.new(1, -60, 0, 34), Text = "",
    Font = Enum.Font.GothamBold, TextSize = 14, TextColor3 = Color3.new(1, 1, 1), BorderSizePixel = 0,
}, keyFrame)
bindText(unlockBtn, "unlock")
corner(unlockBtn, 8); accentBind(unlockBtn, "BackgroundColor3")

local ORANGE = Color3.fromRGB(255, 170, 90)
local busy = false

-- lock everything again (key expired / revoked)
local function lockPanel(msgKey)
    unlocked = false
    session.key, session.admin, session.master, session.expires, session.t = nil, false, false, nil, 0
    S.wheelie, S.autoPumpkin = false, false
    if toggles.wheelie then toggles.wheelie() end
    if toggles.autoPumpkin then toggles.autoPumpkin() end
    stopCtl()
    main.Visible = false
    reopen.Visible = false
    if tabBtns.admin then tabBtns.admin.btn.Visible = false end
    showPage("wheelie")
    keyFrame.Visible = true
    keyErr.TextColor3 = ORANGE
    keyErr.Text = msgKey and T(msgKey) or ""
end

-- log out: forget the saved key so another key can be typed
Button(pSet, "logout", function()
    pcall(function() if delfile and isfile and isfile(CONFIG.SAVED_KEY) then delfile(CONFIG.SAVED_KEY) end end)
    pcall(function() if writefile then writefile(CONFIG.SAVED_KEY, "") end end)
    box.Text = ""
    lockPanel(nil)
end)

local function onUnlocked(res, key)
    unlocked = true
    session.key, session.admin, session.master = key, res.admin == true, res.master == true
    session.expires, session.t = res.expires, 0
    keyFrame.Visible = false
    main.Visible = true
    clampToScreen(main)
    if tabBtns.admin then tabBtns.admin.btn.Visible = session.admin end
    pcall(function() if writefile then writefile(CONFIG.SAVED_KEY, key) end end)
    if session.admin and refreshKeys then refreshKeys() end
end

local function tryKey()
    if busy then return end
    local typed = box.Text:gsub("%s", ""):upper()
    if typed == "" then return end
    busy = true
    keyErr.TextColor3 = C.sub
    keyErr.Text = T("k_checking")
    task.spawn(function()
        local res = Backend.check(typed)
        busy = false
        if res and res.ok then
            keyErr.Text = ""
            onUnlocked(res, typed)
        else
            local m = res and res.msg
            keyErr.TextColor3 = ORANGE
            keyErr.Text = T(m == "revoked" and "k_revoked" or m == "expired" and "k_expired" or m == "offline" and "k_offline" or "invalid")
        end
    end)
end
unlockBtn.MouseButton1Click:Connect(tryKey)
box.FocusLost:Connect(function(enter) if enter then tryKey() end end)

-- remembered key: log in again automatically
pcall(function()
    if isfile and readfile and isfile(CONFIG.SAVED_KEY) then
        local saved = readfile(CONFIG.SAVED_KEY):gsub("%s", "")
        if saved ~= "" then
            box.Text = saved
            task.defer(tryKey)
        end
    end
end)

----------------------------------------------------------------
-- INPUT
----------------------------------------------------------------
UIS.InputBegan:Connect(function(i, gp)
    if listening and i.UserInputType == Enum.UserInputType.Keyboard then
        S[listening.key] = i.KeyCode
        listening.btn.Text = i.KeyCode.Name
        listening = nil
        return
    end
    if gp or i.UserInputType ~= Enum.UserInputType.Keyboard or not unlocked then return end
    if i.KeyCode == S.openKey then
        setPanel(not main.Visible)
    elseif i.KeyCode == S.wheelieKey then
        S.wheelie = not S.wheelie
        if toggles.wheelie_t then toggles.wheelie_t() end
        if toggles.wheelie then toggles.wheelie() end
        if S.wheelie then
            local _, hum = getChar()
            if not (hum and hum.SeatPart) then toast(T("sit_first")) end
        else
            stopCtl()
        end
    end
end)

----------------------------------------------------------------
-- MAIN LOOP
----------------------------------------------------------------
local t0, uiT = tick(), 0

RunService.Heartbeat:Connect(function(dt)
    -- particles
    if S.particles and main.Visible then
        for _, p in ipairs(particleFrames) do
            p.x += p.vx * dt; p.y += p.vy * dt
            if p.x < -.02 then p.x = 1.02 elseif p.x > 1.02 then p.x = -.02 end
            if p.y < -.02 then p.y = 1.02 elseif p.y > 1.02 then p.y = -.02 end
            p.f.Position = UDim2.fromScale(p.x, p.y)
        end
    end

    local char = LP.Character
    local hum = char and char:FindFirstChildOfClass("Humanoid")
    local hrp = char and char:FindFirstChild("HumanoidRootPart")
    if not hum then return end

    local seat = hum.SeatPart
    if seat then lastSeat = seat end

    if S.wheelie and seat and seat:IsA("BasePart") then
        if ctl.seat ~= seat then startCtl(seat) end
        stepCtl(dt, hum)
    elseif ctl.seat then
        stopCtl()
    end

    protectionStep(dt, char, hum, hrp)

    -- UI refresh (4 Hz)
    uiT += dt
    if uiT > .25 then
        uiT = 0
        applyScale()

        -- key expiry / revoke check
        if unlocked then
            if session.expires and os.time() > session.expires then
                lockPanel("k_expired")
            else
                session.t = (session.t or 0) + .25
                if session.t > 60 and not session.master and Backend.mode() == "server" then
                    session.t = 0
                    local k = session.key
                    task.spawn(function()
                        local res = Backend.check(k, true)
                        if unlocked and res and not res.ok and res.msg ~= "offline" then
                            lockPanel(res.msg == "revoked" and "k_revoked" or (res.msg == "expired" and "k_expired" or "invalid"))
                        end
                    end)
                end
            end
            local exTxt = session.expires and T("adm_expires"):format(fmtDur(session.expires - os.time())) or T("adm_never")
            stKey.Text = T("st_key"):format((session.admin and T("key_admin") or T("key_user")) .. " - " .. exTxt)
        end

        local e = math.floor(tick() - t0)
        timeLbl.Text = string.format("%02d:%02d", math.floor(e / 60), e % 60)

        stSeat.Text = T("st_seat"):format(seat and T("seated") or T("not_seated"))
        stWhee.Text = T("st_whee"):format(S.wheelie and (ctl.seat and T("w_active") or T("w_wait")) or T("w_off"))
        local pumpTxt = T("st_pump"):format(ev.collected, ev.found, T(ev.state))
        stPump.Text, stPump2.Text = pumpTxt, pumpTxt

        if ctl.seat and ctl.roadAngle then
            stRoad.Text = T("st_road"):format(T("r_found"):format(math.floor(ctl.roadAngle + .5)) .. " [" .. "edges" .. " / " .. #roadSigs .. "]")
        else
            stRoad.Text = T("st_road"):format(T("r_lost") .. " [" .. #roadSigs .. "]")
        end

        if ctl.seat then
            stSpeed.Text = T("st_speed"):format(tostring(math.floor(ctl.seat.AssemblyLinearVelocity.Magnitude)))
            stPitch.Text = T("st_pitch"):format(math.floor(math.deg(ctl.pitch)) .. "° (" .. math.floor(math.deg(ctl.slope)) .. "°)")
        else
            stSpeed.Text = T("st_speed"):format("-")
            stPitch.Text = T("st_pitch"):format("-")
        end
    end
end)

if LP.Character then applyRagdollStates(LP.Character) end
