// ==UserScript==
// @name         AiScore Red Card GODiNjURED (v19.0 GHOST-TRACTOR)
// @version      21.1.0
// @description  Lê o feed do AiScore (sem scroll), filtros, perfis de alerta, histórico/CSV, voz, título/favicon, sniffer
// @author       iNjURED
// @match        https://www.aiscore.com/*
// @exclude      https://www.aiscore.com/*/match-*
// @exclude      https://www.aiscore.com/match-*
// @exclude      https://www.aiscore.com/*/basketball/match-*
// @exclude      https://www.aiscore.com/*/tennis/match-*
// @icon         https://i.pinimg.com/originals/34/6a/c6/346ac610a5ad0a369ec72e410607330b.gif
// @run-at       document-start
// @grant        GM_notification
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_addStyle
// @grant        GM_setClipboard
// @grant        GM_addElement
// @grant        unsafeWindow
// @grant        window.focus
// ==/UserScript==

(function () {
    'use strict';

    console.log('👑 AiScore GODiNjURED v21.1');

    //======================================================================
    // 1. CONSTANTS & CONFIG
    //======================================================================

    const STARTUP_DELAY    = 5000;
    const WAIT_GAMES_MAX   = 20000;
    const TIME_BUFFER_MINS = 30;
    const WORKER_TICK_MS   = 2000;
    const EMPTY_WARN_MS    = 120000;
    const STALE_GAME_MS    = 3 * 60 * 60 * 1000;
    const OBS_MIN_GAP_MS   = 1500;   // intervalo mínimo entre scans disparados pelo MutationObserver
    const HISTORY_MAX      = 1000;
    const MUTE_MS          = 10 * 60 * 1000;
    const SNIFF_MAX        = 40;
    const FEED_STALE_MS    = 3 * 60 * 1000;   // sem batimento MQTT há mais disto = feed considerado em baixo

    const STORAGE_KEY   = 'AiScore_God_v20_Data';
    const LOG_KEY       = 'AiScore_God_v181_Log';
    const LAST_SCAN_KEY = 'AiScore_God_v181_LastScan';
    const SETTINGS_KEY  = 'AiScore_God_v18_Settings';
    const HISTORY_KEY   = 'AiScore_God_v19_History';
    const SNIFF_KEY     = 'AiScore_God_v19_Sniff';

    const GIF_URL   = 'https://i.pinimg.com/originals/34/6a/c6/346ac610a5ad0a369ec72e410607330b.gif';
    const BET22_URL = 'https://22bet141.com/live/football/';

    const DEFAULT_COMP_SELECTOR = '[class*="competition"], [class*="league"], [class*="tournament"]';
    const SUGGESTED_EXCLUDES    = 'U17, U18, U19, U20, U21, U23, Women, Feminin, Femenin, Reserve, Esports, E-soccer, Virtual, Youth';

    const DEFAULT_SETTINGS = {
        minCards: 1,
        notificationsOn: true,
        scanInterval: 5,
        soundOn: true,
        voiceOn: false,
        titleBadge: true,
        crunchThreshold: 75,
        idleSeconds: 20,
        excludeComp: '',
        includeComp: '',
        compSelector: '',
        sniffer: false,
        dataSource: 'auto',     // 'auto' = lê o feed de rede (DOM só como reserva) | 'dom' = só ecrã + trator
        siteBadge: true,        // etiqueta "10 · perde" na linha do jogo, no próprio site
        realMinutes: true,      // lê os eventos do jogo (como o popup do site) para saber o minuto REAL do vermelho
        ui: {
            sort: 'minute',     // minute | sit | recent | comp
            dense: false,       // lista compacta
            theme: 'dark',      // dark | light | auto
            dimFab: true,       // bola fica discreta quando está tudo calmo
            panelW: 0, listH: 0, panelX: null, panelY: null,   // tamanho/posição do painel (0/null = por defeito)
            tab: 'live',
            collapsed: { fonte: true, ferramentas: true }
        },
        profile: {
            minMinute: 0,
            maxMinute: 95,
            maxRedTeamDeficit: 0,   // 0 = desligado
            onlyZeroZero: false,
            skipBothReds: false
        }
    };

    const $ = (id) => document.getElementById(id);

    //======================================================================
    // 2. STATE & MEMORY
    //======================================================================

    function normalizeSettings(saved) {
        saved = (saved && typeof saved === 'object') ? saved : {};
        const s = Object.assign({}, DEFAULT_SETTINGS, saved);
        s.profile = Object.assign({}, DEFAULT_SETTINGS.profile, saved.profile || {});
        const su = (saved.ui && typeof saved.ui === 'object') ? saved.ui : {};
        s.ui = Object.assign({}, DEFAULT_SETTINGS.ui, su);
        s.ui.collapsed = Object.assign({}, DEFAULT_SETTINGS.ui.collapsed, (su.collapsed && typeof su.collapsed === 'object') ? su.collapsed : {});
        return s;
    }

    let settings      = normalizeSettings(GM_getValue(SETTINGS_KEY, {}));
    let activeGamesDB = GM_getValue(STORAGE_KEY, {});
    let eventLog      = GM_getValue(LOG_KEY, []);
    let history       = GM_getValue(HISTORY_KEY, []);
    let sniffStore    = GM_getValue(SNIFF_KEY, []);

    for (const k in activeGamesDB) {
        if (activeGamesDB[k] && typeof activeGamesDB[k] === 'object') activeGamesDB[k].uid = k;
        else delete activeGamesDB[k];
    }

    let lastFullScan   = GM_getValue(LAST_SCAN_KEY, 0);
    let isFirstRun     = true;
    let isScanning     = false;
    const sonarPos     = new Map();   // uid -> posição vertical (px) onde o jogo foi visto pela última vez
    let finishedGames  = new Set();
    let gameContainers = [];
    let lastSeenGames  = Date.now();
    let emptyWarned    = false;
    let lastScanAt     = 0;
    let lastLiveCount  = 0;
    let observerActive = false;
    let tickCount      = 0;

    function saveSettings() { GM_setValue(SETTINGS_KEY, settings); }
    function saveDB()       { GM_setValue(STORAGE_KEY, activeGamesDB); }
    function saveHistory()  { GM_setValue(HISTORY_KEY, history); }

    window.addEventListener('beforeunload', saveDB);

    //======================================================================
    // 3. NETWORK SNIFFER (captura formato dos dados — só se ativado)
    //======================================================================

    const SNIFF_EVT  = '__god_sniff_evt__';
    const SNIFF_SKIP = /google|doubleclick|analytics|facebook|adservice|googletag|hotjar|sentry|gstatic|cloudflareinsights|\.(png|jpe?g|gif|webp|svg|ico|css|woff2?|ttf|js|map)(\?|$)/i;
    const sniffDiag  = { method: 'a iniciar…', fetch: 0, xhr: 0, wsOpen: 0, wsMsg: 0, skipped: 0, error: '', topics: {} };
    let sniffSaveTimer = null;
    const sniffBlobs = {}; // corpo completo (base64) das respostas binárias — só em memória
    const SAFE_PARAMS = /^(lang|sport_id|date|tz|page|size|limit|type|status|comp_id|competition_id)$/i;
    const SNIFF_MAX_STREAM = 30; // limite separado para WebSocket/MQTT, para o fluxo contínuo não expulsar os XHR
    // Tópico "normalizado": ids longos e números grandes viram {id}/{n}, para juntar mensagens do mesmo tipo
    const normTopic = (t) => String(t || '').replace(/[0-9a-z]{12,}/gi, '{id}').replace(/\d{4,}/g, '{n}');
    let sniffInstalled = false;
    const sniffHello   = { page: false, direct: false };

    // Corre no contexto real da página (injetado como <script>) ou, se a CSP o bloquear,
    // diretamente sobre o unsafeWindow. É serializado com toString(), por isso NÃO pode
    // usar nada do resto do script: só os dois parâmetros e globais do browser.
    function pageHook(win, send, sniffOn) {
        if (win.__godSniffHooked) return;
        try { win.__godSniffHooked = true; } catch (e) { /* ignora */ }
        send({ t: 'hello' });
        const SN = !!sniffOn;                                  // só grava capturas se o sniffer estiver ligado
        const FEED_URL = /\/api\/matches\?(?:[^#]*&)?sport_id=1(?:&|$)/;
        const FEED_TOPIC = '/sports/1/match/scores';
        const STATS_URL = /\/api\/match\/stats\?(?:[^#]*&)?match_id=([A-Za-z0-9_-]+)/;
        let lastBeat = 0;

        const KW = ['red', 'card', 'score', 'home', 'away', 'team', 'match', 'status', 'minute', 'live', 'competition', 'tournament'];
        const MAXDEC = 2000000, MAXTX = 3000;

        const relOf = (t) => {
            const l = String(t).toLowerCase();
            let n = 0;
            for (let i = 0; i < KW.length; i++) { if (l.indexOf(KW[i]) >= 0) n++; }
            return n;
        };
        const hexOf = (u8) => {
            let s = '';
            for (let i = 0; i < u8.length && i < 48; i++) s += (u8[i] < 16 ? '0' : '') + u8[i].toString(16) + ' ';
            return s.trim();
        };
        const b64Of = (u8) => {
            let s = '';
            for (let i = 0; i < u8.length; i += 0x8000) s += String.fromCharCode.apply(null, u8.subarray(i, i + 0x8000));
            return btoa(s);
        };

        // --- descodificador de protobuf SEM schema: descreve campos, tipos e intervalos observados ---
        const pbText = (u8, s, e) => {
            for (let i = s; i < e; i++) { if (u8[i] < 0x20 || u8[i] === 0x7f) return null; }
            try { return new TextDecoder('utf-8', { fatal: true }).decode(u8.subarray(s, e)); } catch (x) { return null; }
        };
        const pbParse = (u8, s, e) => {
            const out = [];
            let i = s;
            const varint = () => {
                let r = 0, mul = 1, b;
                do {
                    if (i >= e || mul > 1e15) throw new Error('varint');
                    b = u8[i++];
                    r += (b & 0x7f) * mul;
                    mul *= 128;
                } while (b & 0x80);
                return r;
            };
            try {
                while (i < e) {
                    const tag = varint();
                    const f = Math.floor(tag / 8), w = tag % 8;
                    if (f < 1 || f > 2000) return null;
                    if (w === 0) out.push([f, 'v', varint()]);
                    else if (w === 1) { if (i + 8 > e) return null; out.push([f, 'f64', null]); i += 8; }
                    else if (w === 5) { if (i + 4 > e) return null; out.push([f, 'f32', null]); i += 4; }
                    else if (w === 2) { const n = varint(); if (i + n > e) return null; out.push([f, 'b', [i, i + n]]); i += n; }
                    else return null;
                }
            } catch (x) { return null; }
            return out;
        };
        const RANK = { bytes: 0, f32: 1, f64: 1, int: 2, str: 3, msg: 4 };
        const pbAdd = (acc, f, it) => {
            const a = acc[f];
            if (!a) { acc[f] = it; return; }
            a.n += it.n;
            if (RANK[it.t] > RANK[a.t]) { a.t = it.t; a.ex = it.ex; a.kid = it.kid; a.mn = it.mn; a.mx = it.mx; return; }
            if (it.t !== a.t) return;
            if (it.t === 'int') { a.mn = Math.min(a.mn, it.mn); a.mx = Math.max(a.mx, it.mx); }
            else if (it.t === 'msg') { for (const g in it.kid) pbAdd(a.kid, g, it.kid[g]); }
        };
        const pbShape = (u8, s, e, d) => {
            const fields = pbParse(u8, s, e);
            if (!fields || !fields.length) return null;
            const agg = {};
            for (let k = 0; k < fields.length; k++) {
                const f = fields[k][0], t = fields[k][1], v = fields[k][2];
                let item;
                if (t === 'v') {
                    item = { n: 1, t: 'int', mn: v, mx: v, ex: null, kid: null };
                } else if (t === 'b') {
                    const bs = v[0], be = v[1];
                    const txt = be > bs ? pbText(u8, bs, be) : null;
                    const kid = (txt === null && d > 0 && be > bs) ? pbShape(u8, bs, be, d - 1) : null;
                    if (txt !== null) item = { n: 1, t: 'str', ex: txt.slice(0, 24), kid: null };
                    else if (kid) item = { n: 1, t: 'msg', ex: null, kid: kid };
                    else item = { n: 1, t: 'bytes', ex: null, kid: null };
                } else {
                    item = { n: 1, t: t, ex: null, kid: null };
                }
                pbAdd(agg, f, item);
            }
            return agg;
        };
        const pbRender = (agg) => Object.keys(agg).sort((x, y) => x - y).map(f => {
            const a = agg[f];
            const body = a.t === 'msg' ? '{' + pbRender(a.kid) + '}'
                : a.t === 'int' ? 'int[' + a.mn + (a.mx !== a.mn ? '..' + a.mx : '') + ']'
                : a.t === 'str' ? 'str"' + a.ex + '"'
                : a.t;
            return f + (a.n > 1 ? '×' + a.n : '') + ':' + body;
        }).join(',');
        // Descrição compacta da estrutura de um JSON: {a:Array(120)<{home:string,...}>,...}
        const outline = (v, d) => {
            if (v === null || typeof v !== 'object') return typeof v;
            if (Array.isArray(v)) return 'Array(' + v.length + ')' + ((v.length && d > 0) ? '<' + outline(v[0], d - 1) + '>' : '');
            const ks = Object.keys(v);
            if (d <= 0) return '{…' + ks.length + '}';
            return '{' + ks.slice(0, 25).map(k => k + ':' + outline(v[k], d - 1)).join(',') + (ks.length > 25 ? ',…' : '') + '}';
        };
        const safeTopic = (t) => String(t || '').replace(/[A-Za-z0-9_-]{24,}/g, '{tok}');
        const rec = (kind, url, status, ct, body, len, hex, outl, b64, topic) => {
            if (!SN) return;
            body = String(body || '');
            if (outl === undefined && body && (body.charAt(0) === '{' || body.charAt(0) === '[') && body.length < MAXDEC) {
                try { outl = outline(JSON.parse(body), 4); } catch (e) { outl = ''; }
            }
            send({
                t: 'rec', kind: kind, url: String(url || ''), status: status || 0, ct: ct || '',
                len: len || body.length, text: body.slice(0, MAXTX), hex: hex || '',
                outl: String(outl || '').slice(0, 8000), b64: b64 || '', rel: body ? relOf(body) : 0,
                topic: topic ? safeTopic(topic) : ''
            });
        };
        const fromBuf = (kind, url, status, ct, buf) => {
            if (!SN) return;
            try {
                const u8 = new Uint8Array(buf);
                let txt = '';
                try { txt = new TextDecoder('utf-8').decode(u8.subarray(0, Math.min(u8.length, MAXDEC))); } catch (e) { /* ignora */ }
                const probe = txt.slice(0, 2000);
                const bad = (probe.match(/[\u0000-\u0008\u000e-\u001f�]/g) || []).length;
                const printable = probe.length > 0 && bad / probe.length < 0.05;
                if (printable) { rec(kind, url, status, ct, txt, u8.length, ''); return; }
                let pb = '';
                if (u8.length <= MAXDEC) {
                    try { const sh = pbShape(u8, 0, u8.length, 6); if (sh) pb = 'protobuf: ' + pbRender(sh); } catch (x) { /* ignora */ }
                }
                rec(kind, url, status, ct, '', u8.length, hexOf(u8), pb, u8.length <= 1500000 ? b64Of(u8) : '');
            } catch (e) { /* ignora */ }
        };
        // --- MQTT sobre WebSocket: separa os pacotes, lê o tópico e descreve o payload ---
        // Nunca regista o conteúdo de CONNECT (traz utilizador/palavra-passe): só PUBLISH e SUBSCRIBE.
        const mqttPackets = (u8, allowPartial) => {
            const out = [];
            let i = 0;
            while (i < u8.length) {
                const type = u8[i] >> 4, flags = u8[i] & 15;
                if (type < 1 || type > 14) return null;
                if (type === 8 && flags !== 2) return null;
                let j = i + 1, rem = 0, mul = 1, b, n = 0, more = false;
                do {
                    if (j >= u8.length) { more = true; break; }
                    if (n++ > 3) return null;
                    b = u8[j++];
                    rem += (b & 127) * mul;
                    mul *= 128;
                } while (b & 128);
                const end = j + rem;
                if (more || end > u8.length) {
                    // pacote incompleto: o resto chega na próxima frame
                    if (!out.length && !allowPartial) return null;
                    return { packets: out, rest: u8.subarray(i) };
                }
                const p = { type: type, e: end };
                if (type === 3) {
                    if (j + 2 > end) return null;
                    const tl = (u8[j] << 8) | u8[j + 1];
                    if (j + 2 + tl > end) return null;
                    p.topic = new TextDecoder().decode(u8.subarray(j + 2, j + 2 + tl));
                    p.ps = j + 2 + tl + (((flags >> 1) & 3) ? 2 : 0);
                    if (p.ps > end) return null;
                } else if (type === 8 || type === 10) {
                    const topics = [];
                    let k = j + 2;
                    while (k + 2 <= end) {
                        const tl = (u8[k] << 8) | u8[k + 1];
                        if (k + 2 + tl > end) break;
                        topics.push(new TextDecoder().decode(u8.subarray(k + 2, k + 2 + tl)));
                        k += 2 + tl + (type === 8 ? 1 : 0);
                    }
                    p.sub = type === 8;
                    p.topics = topics;
                }
                out.push(p);
                i = end;
            }
            return { packets: out, rest: null };
        };
        const asText = (u8) => {
            try {
                const t = new TextDecoder('utf-8').decode(u8);
                const probe = t.slice(0, 2000);
                const bad = (probe.match(/[\u0000-\u0008\u000e-\u001f�]/g) || []).length;
                return (probe.length > 0 && bad / probe.length < 0.05) ? t : null;
            } catch (e) { return null; }
        };
        const fromWsBin = (url, buf, outgoing, st) => {
            try {
                const dir = outgoing ? 'out' : 'in';
                let u8 = new Uint8Array(buf);
                if (st && st[dir]) { // junta o que sobrou da frame anterior
                    const c = new Uint8Array(st[dir].length + u8.length);
                    c.set(st[dir], 0);
                    c.set(u8, st[dir].length);
                    u8 = c;
                    st[dir] = null;
                }
                const first = u8.length ? (u8[0] >> 4) : 0;
                const allowPartial = !!(st && (st.mqtt || (outgoing && first === 1) || (!outgoing && first === 2)));
                const r = mqttPackets(u8, allowPartial);
                if (!r) { fromBuf(outgoing ? 'ws-out-bin' : 'ws-bin', url, 0, '', u8.buffer.slice(u8.byteOffset, u8.byteOffset + u8.byteLength)); return; }
                if (st) st.mqtt = true;
                if (r.rest && r.rest.length && r.rest.length < 2000000 && st) st[dir] = r.rest;
                r.packets.forEach(p => {
                    if (p.type === 3) {
                        const pl = u8.subarray(p.ps, p.e);
                        const nowB = Date.now();
                        if (nowB - lastBeat > 4000) { lastBeat = nowB; send({ t: 'beat' }); }
                        if (p.topic === FEED_TOPIC) send({ t: 'feed', k: 'mqtt', b64: b64Of(pl) });
                        if (!SN) return;
                        const t = asText(pl);
                        if (t !== null) { rec('mqtt', url, 0, '', t, pl.length, '', undefined, '', p.topic); return; }
                        let pb = '';
                        try { const sh = pbShape(pl, 0, pl.length, 6); if (sh) pb = 'protobuf: ' + pbRender(sh); } catch (x) { /* ignora */ }
                        rec('mqtt', url, 0, '', '', pl.length, hexOf(pl), pb, pl.length <= 300000 ? b64Of(pl) : '', p.topic);
                    } else if (p.type === 8 || p.type === 10) {
                        const txt = (p.sub ? 'SUBSCRIBE ' : 'UNSUBSCRIBE ') + JSON.stringify(p.topics.map(safeTopic));
                        rec('mqtt-sub', url, 0, '', txt, txt.length, '');
                    }
                    // CONNECT e restantes pacotes de controlo: ignorados de propósito (CONNECT pode trazer credenciais)
                });
            } catch (e) { /* ignora */ }
        };
        const feedList = (buf) => {
            try { send({ t: 'feed', k: 'list', b64: b64Of(new Uint8Array(buf)) }); } catch (e) { /* ignora */ }
        };
        // Eventos do jogo (o que o popup do site mostra: vermelhos com minuto e jogador, golos, estatísticas)
        const sendStats = (id, st, buf) => {
            try { send({ t: 'stats', id: String(id), st: st || 0, b64: buf ? b64Of(new Uint8Array(buf)) : '' }); } catch (e) { /* ignora */ }
        };
        try {
            win.addEventListener('__god_cmd__', (ev) => {
                try {
                    const c = JSON.parse(ev.detail || '{}');
                    if (c.c !== 'stats' || !/^[A-Za-z0-9_-]{4,64}$/.test(String(c.id))) return;
                    const x = new win.XMLHttpRequest();
                    x.open('GET', 'https://api.aiscore.com/v1/web/api/match/stats?match_id=' + c.id + '&lang=' + (parseInt(c.lang, 10) || 5));
                    x.responseType = 'arraybuffer';
                    x.__godOwn = true;
                    x.timeout = 15000;
                    x.onload = () => sendStats(c.id, x.status, x.status === 200 ? x.response : null);
                    x.onerror = () => sendStats(c.id, 0, null);
                    x.ontimeout = () => sendStats(c.id, 0, null);
                    x.send();
                } catch (e) { /* ignora */ }
            });
        } catch (e) { /* ignora */ }
        const SKIP_CT = /^(image|font|video|audio)\/|text\/css|text\/html|javascript/i;

        // --- fetch ---
        try {
            const oFetch = win.fetch;
            if (typeof oFetch === 'function') {
                win.fetch = function () {
                    const args = arguments;
                    const p = oFetch.apply(this, args);
                    try {
                        const a0 = args[0];
                        const u = (typeof a0 === 'string') ? a0 : ((a0 && a0.url) ? a0.url : String(a0));
                        send({ t: 'count', k: 'fetch' });
                        p.then(r => {
                            try {
                                if (FEED_URL.test(u) && r.status === 200) r.clone().arrayBuffer().then(feedList).catch(() => {});
                                const fm = STATS_URL.exec(u);
                                if (fm && r.status === 200) r.clone().arrayBuffer().then(b => sendStats(fm[1], 200, b)).catch(() => {});
                                if (!SN) return;
                                const ct = r.headers.get('content-type') || '';
                                if (SKIP_CT.test(ct)) { send({ t: 'count', k: 'skip' }); return; }
                                const cl = parseInt(r.headers.get('content-length') || '0', 10);
                                if (cl > 3000000) { rec('fetch', u, r.status, ct, '', cl, '(grande, não lido)'); return; }
                                r.clone().arrayBuffer().then(b => fromBuf('fetch', u, r.status, ct, b)).catch(() => {});
                            } catch (e) { /* ignora */ }
                        }).catch(() => {});
                    } catch (e) { /* ignora */ }
                    return p;
                };
            }
        } catch (e) { send({ t: 'err', m: 'fetch: ' + (e && e.message) }); }

        // --- XMLHttpRequest ---
        try {
            const XP = win.XMLHttpRequest && win.XMLHttpRequest.prototype;
            if (XP) {
                const oOpen = XP.open, oSend = XP.send;
                XP.open = function (m, u) {
                    try { this.__godu = String(u); } catch (e) { /* ignora */ }
                    return oOpen.apply(this, arguments);
                };
                XP.send = function () {
                    if (this.__godOwn) return oSend.apply(this, arguments);   // pedidos do próprio script não entram na captura
                    try {
                        send({ t: 'count', k: 'xhr' });
                        this.addEventListener('load', function () {
                            try {
                                const rt = this.responseType, u = this.__godu || this.responseURL || '', st = this.status;
                                if (FEED_URL.test(u) && st === 200) {
                                    if (rt === 'arraybuffer' && this.response) feedList(this.response);
                                    else if (rt === 'blob' && this.response && this.response.arrayBuffer) this.response.arrayBuffer().then(feedList).catch(() => {});
                                }
                                const sm = STATS_URL.exec(u);
                                if (sm && st === 200) {
                                    if (rt === 'arraybuffer' && this.response) sendStats(sm[1], st, this.response);
                                    else if (rt === 'blob' && this.response && this.response.arrayBuffer) this.response.arrayBuffer().then(b => sendStats(sm[1], st, b)).catch(() => {});
                                }
                                if (!SN) return;
                                const ct = this.getResponseHeader('content-type') || '';
                                if (SKIP_CT.test(ct)) { send({ t: 'count', k: 'skip' }); return; }
                                if (rt === '' || rt === 'text') {
                                    const t = this.responseText || '';
                                    rec('xhr', u, st, ct, t, t.length, '');
                                } else if (rt === 'json') {
                                    let t = '';
                                    try { t = JSON.stringify(this.response); } catch (e) { /* ignora */ }
                                    rec('xhr', u, st, ct, t, t.length, '');
                                } else if (rt === 'arraybuffer' && this.response) {
                                    fromBuf('xhr', u, st, ct, this.response);
                                } else if (rt === 'blob' && this.response && this.response.arrayBuffer) {
                                    this.response.arrayBuffer().then(b => fromBuf('xhr', u, st, ct, b)).catch(() => {});
                                }
                            } catch (e) { /* ignora */ }
                        });
                    } catch (e) { /* ignora */ }
                    return oSend.apply(this, arguments);
                };
            }
        } catch (e) { send({ t: 'err', m: 'xhr: ' + (e && e.message) }); }

        // --- WebSocket (texto, binário e mensagens enviadas pelo cliente) ---
        try {
            const OW = win.WebSocket;
            if (OW) {
                win.WebSocket = new Proxy(OW, {
                    construct: function (target, args, newTarget) {
                        const ws = Reflect.construct(target, args, newTarget);
                        try {
                            const u = String(args[0]);
                            const st = {}; // reassemblagem MQTT desta ligação
                            send({ t: 'count', k: 'wsOpen' });
                            ws.addEventListener('message', function (ev) {
                                try {
                                    const d = ev.data;
                                    if (typeof d === 'string') {
                                        rec('ws', u, 0, '', d, d.length, '');
                                    } else if (d && typeof d.arrayBuffer === 'function') {
                                        st.chain = (st.chain || Promise.resolve()).then(() => d.arrayBuffer()).then(b => fromWsBin(u, b, false, st)).catch(() => {});
                                    } else if (d && d.byteLength !== undefined) {
                                        fromWsBin(u, ArrayBuffer.isView(d) ? d.buffer.slice(d.byteOffset, d.byteOffset + d.byteLength) : d, false, st);
                                    }
                                } catch (e) { /* ignora */ }
                            });
                            const oWsSend = ws.send;
                            ws.send = function (data) {
                                try {
                                    if (typeof data === 'string') rec('ws-out', u, 0, '', data, data.length, '');
                                    else if (data && data.byteLength !== undefined) fromWsBin(u, ArrayBuffer.isView(data) ? data.buffer.slice(data.byteOffset, data.byteOffset + data.byteLength) : data, true, st);
                                    else if (data && typeof data.arrayBuffer === 'function') st.chain = (st.chain || Promise.resolve()).then(() => data.arrayBuffer()).then(b => fromWsBin(u, b, true, st)).catch(() => {});
                                } catch (e) { /* ignora */ }
                                return oWsSend.apply(this, arguments);
                            };
                        } catch (e) { /* ignora */ }
                        return ws;
                    }
                });
            }
        } catch (e) { send({ t: 'err', m: 'ws: ' + (e && e.message) }); }

        // --- Estado embutido no HTML pelo servidor (SSR) ---
        const grabState = () => {
            ['__NUXT__', '__INITIAL_STATE__', '__NEXT_DATA__', '__APOLLO_STATE__', '__PRELOADED_STATE__'].forEach(k => {
                try {
                    const v = win[k];
                    if (!v || typeof v !== 'object') return;
                    const full = JSON.stringify(v);
                    if (full) rec('ssr', 'window.' + k, 0, '', full, full.length, '', outline(v, 4));
                } catch (e) { /* ignora */ }
            });
        };
        try {
            if (document.readyState === 'complete') setTimeout(grabState, 1500);
            else win.addEventListener('load', () => setTimeout(grabState, 1500));
        } catch (e) { /* ignora */ }
    }

    function maskUrl(u) {
        try {
            const x = new URL(u, location.href);
            const parts = [];
            x.searchParams.forEach((v, k) => { parts.push(SAFE_PARAMS.test(k) ? k + '=' + v : k); });
            return x.origin + x.pathname + (parts.length ? '?[' + parts.join(',') + ']' : '');
        } catch (e) {
            return String(u).split('?')[0];
        }
    }

    function scheduleSniffSave() {
        if (sniffSaveTimer) return;
        sniffSaveTimer = setTimeout(() => {
            sniffSaveTimer = null;
            GM_setValue(SNIFF_KEY, sniffStore);
        }, 2000);
    }

    function updateSniffMethod() {
        if (sniffHello.page && sniffHello.direct) sniffDiag.method = 'script injetado + unsafeWindow';
        else if (sniffHello.page) sniffDiag.method = 'script injetado na página';
        else if (sniffHello.direct) sniffDiag.method = 'unsafeWindow (direto)';
    }

    function handleSniffMsg(m, src) {
        if (!m) return;
        if (m.t === 'feed') { feedIngest(m); return; }
        if (m.t === 'beat') { FEED.beatAt = Date.now(); return; }
        if (m.t === 'stats') { statsIngest(m); return; }
        if (m.t === 'hello') { sniffHello[src || 'direct'] = true; updateSniffMethod(); return; }
        if (m.t === 'err') { sniffDiag.error = String(m.m || ''); return; }
        if (!settings.sniffer) return;
        if (m.t === 'count') {
            if (m.k === 'fetch') sniffDiag.fetch++;
            else if (m.k === 'xhr') sniffDiag.xhr++;
            else if (m.k === 'wsOpen') sniffDiag.wsOpen++;
            else if (m.k === 'skip') sniffDiag.skipped++;
        }
        else if (m.t === 'rec') sniffRecord(m);
    }

    function sniffRecord(r) {
        const kind = String(r.kind || '');
        const url = String(r.url || '');
        const isMqtt = kind === 'mqtt' || kind === 'mqtt-sub';
        const isWs = kind.indexOf('ws') === 0 || isMqtt;
        const isSsr = kind === 'ssr';
        if (isWs) sniffDiag.wsMsg++;

        if (!isWs && !isSsr && SNIFF_SKIP.test(url)) { sniffDiag.skipped++; return; }

        const text = String(r.text || '').trim();
        const hex = String(r.hex || '');
        if (!isWs && !isSsr) {
            const looksJson = text.charAt(0) === '{' || text.charAt(0) === '[';
            if (!looksJson && !hex) { sniffDiag.skipped++; return; } // texto simples/HTML sem interesse
        }
        if (!text && !hex) return;

        const masked = isSsr ? url : maskUrl(url); // nos URLs só ficam os nomes dos parâmetros, não os valores
        const topic = String(r.topic || '');
        const nt = normTopic(topic);
        if (nt) { const tk = sniffDiag.topics; if (tk[nt] || Object.keys(tk).length < 80) tk[nt] = (tk[nt] || 0) + 1; }
        // tópicos de odds são barulho; tópicos que parecem estado/eventos do jogo sobem na lista
        const topicRel = (nt && /live|event|card|score|status|incident|goal|match|state/i.test(nt) && !/odds/i.test(nt)) ? 8 : 0;
        const sig = kind === 'mqtt-sub' ? ' | ' + text.slice(0, 120)
            : (nt ? ' | ' + nt : (isWs ? ' | ' + (text ? text.slice(0, 16) : hex.slice(0, 17)) : ''));
        const key = kind + ' ' + masked + sig;
        const entry = {
            key: key, kind: kind, url: masked, status: r.status || 0, ct: r.ct || '',
            len: r.len || text.length, rel: Math.max(r.rel || (hex ? 6 : 0), topicRel), topic: topic, ts: new Date().toISOString(),
            outline: String(r.outl || ''), sample: text.slice(0, 3000), hex: hex, count: 1
        };

        const i = sniffStore.findIndex(e => e.key === key);
        if (i >= 0) { entry.count = (sniffStore[i].count || 1) + 1; entry.samples = sniffStore[i].samples || []; sniffStore.splice(i, 1); }
        if (kind === 'mqtt' && r.b64 && r.b64.length <= 600) entry.samples = (entry.samples || []).concat(r.b64).slice(-40);
        if (r.b64) {
            delete sniffBlobs[key];
            sniffBlobs[key] = r.b64;
            const ks = Object.keys(sniffBlobs);
            let total = 0;
            ks.forEach(k => { total += sniffBlobs[k].length; });
            for (let q = 0; total > 3000000 && q < ks.length - 1; q++) { total -= sniffBlobs[ks[q]].length; delete sniffBlobs[ks[q]]; }
        }
        sniffStore.push(entry);
        // Dois limites separados (fluxo contínuo vs pedidos), para uma enxurrada de mensagens não expulsar os XHR.
        const streamy = e => e.kind.indexOf('ws') === 0 || e.kind.indexOf('mqtt') === 0;
        const cls = sniffStore.filter(e => streamy(e) === streamy(entry));
        if (cls.length > (streamy(entry) ? SNIFF_MAX_STREAM : SNIFF_MAX)) {
            const older = cls.slice(0, -1);
            const victim = older.find(e => !e.rel) || older[0]; // sacrifica primeiro o que parece irrelevante
            delete sniffBlobs[victim.key];
            sniffStore.splice(sniffStore.indexOf(victim), 1);
        }
        scheduleSniffSave();
    }

    // Injeta o pageHook no contexto real da página. Devolve true se chegou a correr.
    function injectPageHook() {
        const parent = document.head || document.documentElement;
        if (!parent) return false;
        const code = '(' + pageHook.toString() + ')(window, function (o) { try { window.dispatchEvent(new CustomEvent(' +
            JSON.stringify(SNIFF_EVT) + ', { detail: JSON.stringify(o) })); } catch (e) {} }, ' + (settings.sniffer ? 'true' : 'false') + ');';

        // a) GM_addElement: no Tampermonkey/Violentmonkey contorna a CSP da página
        try {
            if (typeof GM_addElement === 'function') GM_addElement(parent, 'script', { textContent: code });
        } catch (e) { /* tenta o seguinte */ }

        // b) <script> normal (uma CSP restritiva pode bloqueá-lo)
        if (!sniffHello.page) {
            try {
                const s = document.createElement('script');
                s.textContent = code;
                parent.appendChild(s);
                s.remove();
            } catch (e) {
                sniffDiag.error = 'injeção: ' + (e && e.message);
            }
        }
        return sniffHello.page;
    }

    function installSniffer() {
        if (sniffInstalled) return;
        sniffInstalled = true;

        const W = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        const hookedFlag = () => { try { return !!W.__godSniffHooked; } catch (e) { return false; } };

        // Mensagens vindas do script injetado na página
        window.addEventListener(SNIFF_EVT, ev => {
            try { handleSniffMsg(JSON.parse(ev.detail), 'page'); } catch (e) { /* ignora */ }
        });

        // 1) Injeção na página. Em document-start o <html> pode ainda não existir: espera por ele.
        if (!injectPageHook() && !document.documentElement) {
            const mo = new MutationObserver(() => {
                if (document.documentElement) { mo.disconnect(); injectPageHook(); }
            });
            mo.observe(document, { childList: true });
        }

        // 2) Em paralelo, hooks diretos no unsafeWindow. Se a injeção já instalou os hooks
        //    no mesmo window, isto não faz nada (há uma marca que evita instalar duas vezes).
        try { pageHook(W, m => handleSniffMsg(m, 'direct'), settings.sniffer); } catch (e) { sniffDiag.error = 'hooks: ' + (e && e.message); }

        setTimeout(() => {
            if (sniffHello.page || sniffHello.direct) return;
            sniffDiag.method = hookedFlag() ? 'script injetado (sem confirmação)' : 'FALHOU';
        }, 5000);
        console.log('🕵️ Sniffer de rede iniciado.');
    }

    function copyText(text) {
        return new Promise((resolve, reject) => {
            try {
                if (typeof GM_setClipboard === 'function') { GM_setClipboard(text, 'text'); resolve(); return; }
            } catch (e) { /* tenta o seguinte */ }
            if (navigator.clipboard && navigator.clipboard.writeText) navigator.clipboard.writeText(text).then(resolve, reject);
            else reject(new Error('sem acesso à área de transferência'));
        });
    }

    // O que a página mostra neste momento (verdade para cruzar com os dados binários)
    function sniffDomHints() {
        try {
            const all = detectGameContainers();
            const comVermelho = [], semVermelho = [];
            all.forEach(c => {
                const info = extractGameInfo(c), cards = detectRedCards(c);
                const o = {
                    jogo: info.gameName, placar: info.score, estado: info.gameTime,
                    vermelhosCasa: cards.homeCards, vermelhosFora: cards.awayCards,
                    href: (c.getAttribute('href') || '').split('?')[0].slice(-70)
                };
                if (cards.total > 0) { if (comVermelho.length < 30) comVermelho.push(o); }
                else if (semVermelho.length < 30) semVermelho.push(o);
            });
            return { totalNaPagina: all.length, comVermelho: comVermelho, semVermelho: semVermelho };
        } catch (e) {
            return { erro: String(e && e.message) };
        }
    }

    // Copiar: só as entradas mais relevantes (cabe numa mensagem). Ficheiro: tudo, incluindo os binários completos.
    function buildSniffPayload(full) {
        const byRel = (a, b) => ((b.rel || 0) - (a.rel || 0)) || ((b.len || 0) - (a.len || 0));
        const streamy = e => e.kind.indexOf('ws') === 0 || e.kind.indexOf('mqtt') === 0;
        const reqs = sniffStore.filter(e => !streamy(e)).sort(byRel);
        const flow = sniffStore.filter(streamy).sort(byRel);
        const pick = full ? reqs.concat(flow) : reqs.slice(0, 8).concat(flow.slice(0, 12));
        const entradas = pick.map((e, i) => ({
            tipo: e.kind, url: e.url, topico: e.topic || undefined, status: e.status, contentType: e.ct || undefined,
            bytes: e.len, vezes: e.count, relevancia: e.rel || 0,
            estrutura: (full || i < 6) ? (e.outline || undefined) : (e.outline || '').slice(0, 600) || undefined,
            hex: e.hex || undefined,
            amostra: (e.kind === 'ssr' && e.len > 200000) ? undefined : ((full || i < 3) ? e.sample : (e.sample || '').slice(0, 1000)),
            base64Inicio: (!full && e.kind === 'mqtt' && sniffBlobs[e.key]) ? sniffBlobs[e.key].slice(0, 800) : undefined,
            amostrasB64: (e.samples && e.samples.length) ? (full ? e.samples : e.samples.slice(-12)) : undefined,
            blobBase64: full ? (sniffBlobs[e.key] || undefined) : undefined,
            temBlob: (!full && sniffBlobs[e.key]) ? true : undefined
        }));
        const out = { diag: Object.assign({}, sniffDiag), feed: { listAt: FEED.listAt, jogos: FEED.games.size, mqtt: FEED.mqttCount, desconhecidos: FEED.mqttUnknown, erro: FEED.err }, pagina: location.pathname, dom: sniffDomHints(), entradas: entradas };
        if (!full) out.nota = 'Os binários completos só vão no ficheiro (💾 Guardar ficheiro).';
        return JSON.stringify(out, null, 1);
    }

    function sniffEmptyHint() {
        if (!settings.sniffer) return 'Sniffer desligado. Liga-o, recarrega a página e espera ~1 min.';
        const seen = sniffDiag.fetch + sniffDiag.xhr + sniffDiag.wsOpen;
        if (seen === 0) return 'Nenhum pedido visto: os hooks não estão a apanhar nada (método: ' + sniffDiag.method + '). Usa o separador Network do DevTools.';
        return 'Vi ' + seen + ' pedidos mas nenhum com dados úteis. Espera um pouco mais ou usa o separador Network do DevTools.';
    }

    function refreshSniffDiag() {
        const el = $('x_sniff_diag');
        if (el) {
            if (!settings.sniffer) {
                el.textContent = 'Sniffer desligado.';
            } else {
                const d = sniffDiag;
                el.innerHTML = `Método: <b>${escapeHTML(d.method)}</b><br>` +
                    `Pedidos vistos — fetch: <b>${d.fetch}</b> · xhr: <b>${d.xhr}</b> · WebSockets: <b>${d.wsOpen}</b> (msgs: <b>${d.wsMsg}</b>)<br>` +
                    `Guardadas: <b>${sniffStore.length}</b> · tópicos MQTT: <b>${Object.keys(d.topics).length}</b> · ignoradas: ${d.skipped}` +
                    (d.error ? `<br><span style="color:#f87171">${escapeHTML(d.error)}</span>` : '');
            }
        }
        const fd = $('x_feed_diag');
        if (fd) fd.innerHTML = feedDiagText() + '<br>' + realDiagText();
        updateFeedIndicator();
        const b = $('x_sniff_copy');
        if (b) b.textContent = `📋 Copiar captura (${sniffStore.length})`;
    }
    setInterval(refreshSniffDiag, 1500);


    //======================================================================
    // 3b. FEED (lê os dados que o próprio AiScore recebe — sem scroll)
    //======================================================================
    // Lista de jogos (XHR protobuf, valores em zigzag) + tópico MQTT /sports/1/match/scores (valores simples).
    // Cada equipa tem um array [golos, golos ao intervalo, VERMELHOS, amarelos, cantos, prolongamento, penáltis].

    const FEED = { games: new Map(), teams: {}, comps: {}, listAt: 0, beatAt: 0, mqttAt: 0, listCount: 0, mqttCount: 0, mqttUnknown: 0, err: '' };
    const FEED_LIVE = { 2: 1, 3: 1, 4: 1, 5: 1, 6: 1, 7: 1 };   // 2=1ª parte 3=intervalo 4=2ª parte 5-7=prolongamento/penáltis
    const FEED_DONE = { 8: 1, 11: 1 };           // 8 = terminado · 11 = abandonado a meio → fim (com histórico)
    const FEED_VOID = { 1: 1, 12: 1, 13: 1 };    // 1 = por começar · 12 = cancelado · 13 = por definir → sai sem histórico
    const FEED_PAUSED = { 9: 'Adiado', 10: 'Interr.' };   // jogo parado: mantém-se com etiqueta
    const ABSENT_MS = 45 * 60 * 1000;            // jogo que o feed não conhece e ninguém atualiza há este tempo
    const DOM_ABSENT_MS = 30 * 60 * 1000;        // modo ecrã: jogo que já não aparece na página há este tempo
    let feedReady = false;

    function b64ToU8(b64) {
        const s = atob(b64);
        const u = new Uint8Array(s.length);
        for (let i = 0; i < s.length; i++) u[i] = s.charCodeAt(i);
        return u;
    }

    // Leitor mínimo de protobuf: devolve [{f, w, v}] (varint) ou [{f, w, s, e}] (bytes); null se inválido
    function pbFields(u8, s, e) {
        const out = [];
        let i = s;
        const vi = () => {
            let r = 0, m = 1, b;
            do {
                if (i >= e || m > 1e15) throw new Error('varint');
                b = u8[i++];
                r += (b & 127) * m;
                m *= 128;
            } while (b & 128);
            return r;
        };
        try {
            while (i < e) {
                const tag = vi();
                const f = Math.floor(tag / 8), w = tag % 8;
                if (f < 1) return null;
                if (w === 0) out.push({ f: f, w: 0, v: vi() });
                else if (w === 2) { const n = vi(); if (i + n > e) return null; out.push({ f: f, w: 2, s: i, e: i + n }); i += n; }
                else if (w === 1) { if (i + 8 > e) return null; i += 8; }
                else if (w === 5) { if (i + 4 > e) return null; i += 4; }
                else return null;
            }
        } catch (x) { return null; }
        return out;
    }
    const pbFirst = (fs, f) => { for (let i = 0; i < fs.length; i++) if (fs[i].f === f) return fs[i]; return null; };
    function pbStr(u8, it) {
        if (!it || it.w !== 2) return '';
        try { return new TextDecoder('utf-8').decode(u8.subarray(it.s, it.e)); } catch (e) { return ''; }
    }
    function pbSub(u8, it) { return (it && it.w === 2) ? pbFields(u8, it.s, it.e) : null; }
    // array "packed" de varints; zz = true na lista (zigzag), false no MQTT
    function pbArr(u8, it, zz) {
        if (!it || it.w !== 2) return null;
        const out = [];
        let i = it.s;
        while (i < it.e) {
            let r = 0, m = 1, b;
            do {
                if (i >= it.e) return out;
                b = u8[i++];
                r += (b & 127) * m;
                m *= 128;
            } while (b & 128);
            out.push(zz ? Math.floor(r / 2) : r);
        }
        return out;
    }

    //======================================================================
    // 3c. MINUTO REAL DO VERMELHO (eventos do jogo, como no popup do site)
    //======================================================================
    // GET /v1/web/api/match/stats?match_id=…  → protobuf:
    //   15 { 1 { 1×N { 2:tipo  3:segundos  5:"minuto"  7:lado(1 casa,2 fora)  9:{4:"jogador"} } }
    //        2 { 1×M { 1:id  2:{1:"casa" 2:"fora"} } } }       tipos vistos: 1 golo · 4 vermelho · 8 penálti marcado
    // Só se aceita se o nº de vermelhos por lado bater certo com o feed; senão fica o minuto aproximado de antes.
    const RS = { ok: 0, fail: 0, mismatch: 0, lastErr: '', inflight: 0, st: {} };
    const RS_PAR = 3;
    const RS_DELAYS = [0, 15000, 60000, 180000, 600000];
    const RS_GOAL = { 1: 1, 8: 1, 17: 1 };       // golo · penálti marcado · autogolo
    const RS_RED = { 4: 1, 15: 1 };              // vermelho direto · 2.º amarelo

    function parseStatsPayload(u8) {
        const top = pbFields(u8, 0, u8.length);
        const box = top && top.find(x => x.f === 15 && x.w === 2);
        if (!box) return null;
        const inner = pbFields(u8, box.s, box.e);
        if (!inner) return null;
        const events = [], stats = {};
        const evBox = inner.find(x => x.f === 1 && x.w === 2), stBox = inner.find(x => x.f === 2 && x.w === 2);
        if (evBox) {
            (pbFields(u8, evBox.s, evBox.e) || []).forEach(it => {
                if (it.f !== 1 || it.w !== 2) return;
                const d = pbFields(u8, it.s, it.e);
                if (!d) return;
                const t = pbFirst(d, 2), sec = pbFirst(d, 3), lab = pbFirst(d, 5), sd = pbFirst(d, 7), pl = pbSub(u8, pbFirst(d, 9));
                events.push({ type: t ? t.v : 0, sec: sec ? sec.v : 0, label: pbStr(u8, lab), side: sd ? sd.v : 0, player: pl ? pbStr(u8, pbFirst(pl, 4)) : '' });
            });
        }
        if (stBox) {
            (pbFields(u8, stBox.s, stBox.e) || []).forEach(it => {
                if (it.f !== 1 || it.w !== 2) return;
                const d = pbFields(u8, it.s, it.e);
                const id = d && pbFirst(d, 1), v = d && pbSub(u8, pbFirst(d, 2));
                if (id && v) stats[id.v] = [parseInt(pbStr(u8, pbFirst(v, 1)), 10) || 0, parseInt(pbStr(u8, pbFirst(v, 2)), 10) || 0];
            });
        }
        return { events: events, stats: stats };
    }

    // Aplica os eventos ao jogo. Devolve 'ok' | 'reds' (golos não bateram) | 'mismatch'
    function applyRealStats(g, parsed) {
        const hR = g.homeCards || 0, aR = g.awayCards || 0;
        const cnt = (l) => ({ h: l.filter(e => e.side === 1).length, a: l.filter(e => e.side === 2).length });
        const l415 = parsed.events.filter(e => RS_RED[e.type]), l4 = parsed.events.filter(e => e.type === 4);
        let reds = null;
        [l415, l4].forEach(l => { if (!reds) { const c = cnt(l); if (c.h === hR && c.a === aR) reds = l; } });
        if (!reds || !reds.length) {
            RS.lastErr = 'vermelhos não batem: site ' + cnt(l415).h + '-' + cnt(l415).a + ' vs feed ' + hR + '-' + aR + ' (tipos: ' + parsed.events.map(e => e.type).join(',') + ')';
            return 'mismatch';
        }
        // pontuação em cada momento, pela ordem dos eventos (tenta com e sem inverter autogolos)
        const evs = parsed.events.map((e, i) => ({ e: e, i: i })).sort((x, y) => (x.e.sec - y.e.sec) || (x.i - y.i)).map(x => x.e);
        const cur = parseScore(g.score);
        const run = (flipOwn) => {
            let h = 0, a = 0;
            const atRed = new Map(), goals = [];
            evs.forEach(e => {
                if (RS_GOAL[e.type]) {
                    let home = e.side === 1;
                    if (e.type === 17 && flipOwn) home = !home;
                    if (home) h++; else a++;
                    goals.push({ e: e, h: h, a: a, home: home });
                } else if (reds.indexOf(e) >= 0) atRed.set(e, h + '-' + a);
            });
            return { h: h, a: a, atRed: atRed, goals: goals };
        };
        let rs = null;
        if (cur) [false, true].forEach(f => { if (!rs) { const r = run(f); if (r.h === cur.h && r.a === cur.a) rs = r; } });

        const old = g.redEvents || [];
        const label = (e) => (e.label || String(Math.floor(e.sec / 60))) + "'";
        g.redEvents = reds.slice().sort((x, y) => x.sec - y.sec).map((e, i) => ({
            time: label(e), sec: e.sec,
            score: (rs && rs.atRed.get(e)) || (old[i] && old[i].score) || '?',
            side: e.side === 1 ? 'home' : 'away', approx: false, real: true, player: e.player || '',
            at: (old[i] && old[i].at) || Date.now()
        }));
        g.firstRed = g.redEvents[0];
        g.real = true;
        g.realCards = hR + aR;
        if (rs) {
            g.goals = rs.goals.map(x => ({ time: label(x.e), score: x.h + '-' + x.a, side: x.home ? 'h' : 'a', at: Date.now(), real: true, player: x.e.player || '' })).slice(-24);
            g.realScore = g.score;
        }
        updateTags(g);
        return rs ? 'ok' : 'reds';
    }

    function statsIngest(m) {
        setTimeout(realTick, 150);                    // há mais jogos na fila? continua já, sem esperar pelo próximo batimento
        const id = String(m.id || ''), uid = 'id_' + id;
        const s = RS.st[uid];
        if (s && s.busy) { s.busy = false; RS.inflight = Math.max(0, RS.inflight - 1); }
        if (m.st !== 200 || !m.b64) { RS.fail++; RS.lastErr = m.st ? 'HTTP ' + m.st : 'sem ligação ao pedido'; return; }
        let parsed = null;
        try { parsed = parseStatsPayload(b64ToU8(m.b64)); } catch (e) { parsed = null; }
        if (!parsed) { RS.fail++; RS.lastErr = 'resposta com formato desconhecido'; return; }
        const g = activeGamesDB[uid];
        if (!g || !(g.cards > 0)) return;
        const r = applyRealStats(g, parsed);
        if (r === 'mismatch') { RS.mismatch++; return; }
        RS.ok++;
        saveDB();
        renderLiveList();
        highlightDom();
    }

    function rsSend(id) {
        const W = (typeof unsafeWindow !== 'undefined') ? unsafeWindow : window;
        try { W.dispatchEvent(new CustomEvent('__god_cmd__', { detail: JSON.stringify({ c: 'stats', id: id, lang: 5 }) })); } catch (e) { RS.lastErr = 'não consegui falar com a página'; }
    }

    // Pede os eventos dos jogos que ainda não têm minuto real (poucos de cada vez, com recuo se falhar)
    function realTick() {
        if (!settings.realMinutes || isFirstRun) return;
        const now = Date.now();
        Object.keys(RS.st).forEach(u => {
            const s = RS.st[u];
            if (s.busy && now - s.sentAt > 20000) { s.busy = false; RS.inflight = Math.max(0, RS.inflight - 1); RS.fail++; RS.lastErr = 'sem resposta do pedido'; }
            if (!activeGamesDB[u]) delete RS.st[u];
        });
        if (RS.inflight >= RS_PAR) return;
        const todo = [];
        Object.keys(activeGamesDB).forEach(uid => {
            const g = activeGamesDB[uid];
            if (!g || !(g.cards > 0) || !/^id_[A-Za-z0-9_-]{4,64}$/.test(uid)) return;
            if (now - (g.timestamp || 0) > 20 * 60000) return;
            if (g.real && g.realCards === g.cards && g.realScore === g.score) return;
            const key = g.cards + '|' + g.score;
            let s = RS.st[uid];
            if (!s || s.key !== key) s = RS.st[uid] = { key: key, tries: 0, next: 0, busy: false, sentAt: 0 };
            if (s.busy || now < s.next) return;
            todo.push([uid, s, getMinuteSortValue(liveTime(g))]);
        });
        todo.sort((x, y) => y[2] - x[2]);
        todo.slice(0, RS_PAR - RS.inflight).forEach(t => {
            const s = t[1];
            s.busy = true; s.sentAt = now;
            s.next = now + RS_DELAYS[Math.min(s.tries + 1, RS_DELAYS.length - 1)];
            s.tries++;
            RS.inflight++;
            rsSend(t[0].slice(3));
        });
    }

    function realDiagText() {
        if (!settings.realMinutes) return '⏱️ Minuto real do vermelho: <b>desligado</b>';
        let n = 0, tot = 0;
        Object.keys(activeGamesDB).forEach(u => {
            const g = activeGamesDB[u];
            if (!g || !(g.cards > 0)) return;
            tot++;
            if (g.real && g.realCards === g.cards) n++;
        });
        return '⏱️ Minuto real do vermelho: <b>' + n + '/' + tot + '</b> jogos · pedidos ok ' + RS.ok + ' · falhas ' + RS.fail + ' · não batem ' + RS.mismatch +
            (RS.lastErr ? '<br><span style="color:#f59e0b">último problema: ' + escapeHTML(RS.lastErr) + '</span>' : '');
    }

    function parseMatchesList(u8) {
        const top = pbFields(u8, 0, u8.length);
        const box = top && top.find(x => x.f === 15 && x.w === 2);
        if (!box) return null;
        const inner = pbFields(u8, box.s, box.e);
        if (!inner) return null;
        let n = 0;
        inner.forEach(it => {
            if (it.w !== 2) return;
            const d = pbFields(u8, it.s, it.e);
            if (!d) return;
            const id = pbStr(u8, pbFirst(d, 1));
            if (!id) return;
            if (it.f === 1) FEED.comps[id] = pbStr(u8, pbFirst(d, 5));
            else if (it.f === 3) FEED.teams[id] = pbStr(u8, pbFirst(d, 6));
            else if (it.f === 2) {
                const idOf = (f) => { const sub = pbSub(u8, pbFirst(d, f)); return sub ? pbStr(u8, pbFirst(sub, 1)) : ''; };
                const p8 = pbSub(u8, pbFirst(d, 8)) || [];
                const t3 = pbFirst(p8, 3), t4 = pbFirst(p8, 4);
                const st = pbFirst(d, 16);
                const g = FEED.games.get(id) || { id: id };
                g.st  = st ? st.v : 0;
                g.h   = pbArr(u8, pbFirst(d, 12), true) || [];
                g.a   = pbArr(u8, pbFirst(d, 13), true) || [];
                g.hid = idOf(6); g.aid = idOf(7); g.cid = idOf(4);
                g.ts  = t3 ? t3.v : 0;
                g.el  = t4 ? t4.v : 0;
                g.updAt = Date.now();
                FEED.games.set(id, g);
                n++;
            }
        });
        return n;
    }

    // Devolve os ids que mudaram
    function parseScoresPayload(u8) {
        const top = pbFields(u8, 0, u8.length);
        if (!top) return null;
        const ids = [];
        top.forEach(it => {
            if (it.f !== 1 || it.w !== 2) return;
            const d = pbFields(u8, it.s, it.e);
            if (!d) return;
            const id = pbStr(u8, pbFirst(d, 1));
            let g = FEED.games.get(id);
            if (!g) {
                const saved = activeGamesDB['id_' + id];
                if (!saved) { FEED.mqttUnknown++; return; }
                // jogo guardado mas fora da lista carregada: acompanha-o só pelas mensagens, com o nome já conhecido
                g = { id: id, st: 0, h: [], a: [], hid: '', aid: '', cid: '', ts: 0, el: 0, updAt: Date.now(), stub: true };
                FEED.games.set(id, g);
            }
            const st = pbFirst(d, 3);
            if (st && st.w === 0) g.st = st.v;
            const p4 = pbSub(u8, pbFirst(d, 4));
            if (p4) {
                const t3 = pbFirst(p4, 3), t4 = pbFirst(p4, 4);
                if (t3) g.ts = t3.v;
                if (t4) g.el = t4.v;
            }
            const h = pbArr(u8, pbFirst(d, 5), false), a = pbArr(u8, pbFirst(d, 6), false);
            if (h && h.length) g.h = h;
            if (a && a.length) g.a = a;
            g.updAt = Date.now();
            ids.push(id);
        });
        return ids;
    }

    function feedUsable() {
        return settings.dataSource === 'auto' && FEED.listAt > 0 && (Date.now() - FEED.beatAt) < FEED_STALE_MS;
    }

    function feedIngest(m) {
        if (settings.dataSource !== 'auto') return;
        try {
            if (m.k === 'list') {
                const n = parseMatchesList(b64ToU8(m.b64));
                if (n === null) { FEED.err = 'lista ilegível'; return; }
                FEED.listAt = Date.now();
                FEED.listCount = FEED.games.size;
                FEED.err = '';
                if (feedReady) feedProcess(null, true);
            } else if (m.k === 'mqtt') {
                const ids = parseScoresPayload(b64ToU8(m.b64));
                if (ids === null) { FEED.err = 'MQTT ilegível'; return; }
                FEED.mqttAt = Date.now();
                FEED.mqttCount++;
                if (feedReady && ids.length) feedProcess(ids, false);
            }
        } catch (e) { FEED.err = String(e && e.message); }
    }

    // Minuto estimado a partir do estado e do instante de início da parte
    function feedMinute(g) {
        if (g.st === 3) return 'HT';
        if (g.st === 5 || g.st === 6) return 'ET';
        if (g.st === 7) return 'Pen';
        if (!g.ts) return '?';
        const dt = Math.floor((Date.now() / 1000 - g.ts) / 60);
        if (dt < -2 || dt > 150) return '?';
        const m = (g.st === 4 ? 45 : 0) + Math.max(0, dt) + 1;
        if (g.st === 2 && m > 45) return '45+';
        if (g.st === 4 && m > 90) return '90+';
        return m + "'";
    }

    // Estado "ao vivo" que já não pode ser verdade (mensagem de fim perdida, PC adormecido, reconexão…)
    function feedLooksOver(g) {
        if (!FEED_LIVE[g.st] && !FEED_PAUSED[g.st]) return false;
        const now = Date.now();
        const age = (now - (g.updAt || now)) / 60000;               // minutos desde a última informação deste jogo
        const since = g.ts ? (now / 1000 - g.ts) / 60 : null;       // minutos desde o início da parte atual
        switch (g.st) {
            case 2: return since !== null ? since > 90 : age > 100;   // 1ª parte
            case 4: return since !== null ? since > 100 : age > 100;  // 2ª parte
            case 3: return age > 60;                                  // intervalo
            case 5: case 6: return since !== null ? since > 60 : age > 70;  // prolongamento
            case 7: return age > 45;                                  // penáltis
            case 9: case 10: return age > 180;                        // parado há demasiado tempo
            default: return false;
        }
    }

    function feedGameInfo(g) {
        const uid = 'id_' + g.id;
        const inDB = !!activeGamesDB[uid];
        const saved = activeGamesDB[uid];
        const noArr = !g.h.length || !g.a.length;                       // mensagem sem números: usa o que já está guardado
        const hr = noArr ? ((saved && saved.homeCards) | 0) : (g.h[2] | 0), ar = noArr ? ((saved && saved.awayCards) | 0) : (g.a[2] | 0);
        const score = noArr ? ((saved && saved.score) || '0-0') : ((g.h[0] | 0) + '-' + (g.a[0] | 0));
        let homeTeam = FEED.teams[g.hid] || '?', awayTeam = FEED.teams[g.aid] || '?';
        let gname = homeTeam + ' vs ' + awayTeam, gcomp = FEED.comps[g.cid] || '';
        if (g.stub && saved) {
            gname = saved.name; gcomp = saved.comp || '';
            const parts = String(saved.name).split(' vs ');
            homeTeam = parts[0] || '?'; awayTeam = parts[1] || '?';
        }
        const base = {
            uid: uid, container: null, homeTeam: homeTeam, awayTeam: awayTeam, gameName: gname,
            score: score, comp: gcomp, cards: { total: hr + ar, homeCards: hr, awayCards: ar }
        };
        if (FEED_DONE[g.st] || feedLooksOver(g)) {
            if (!inDB) return null;
            base.finished = true; base.gameTime = 'FT';
            return base;
        }
        if (FEED_VOID[g.st]) {
            if (!inDB) return null;
            base.finished = true; base.noHistory = true; base.gameTime = 'FT';
            return base;
        }
        if (FEED_PAUSED[g.st]) {
            if (!inDB) return null;
            base.gameTime = FEED_PAUSED[g.st];
            return base;
        }
        if (!FEED_LIVE[g.st]) return null;
        if (hr + ar === 0 && !inDB) return null;
        base.gameTime = feedMinute(g);
        // se o jogo está no ecrã, usa o texto do próprio ecrã (é o que o utilizador vê)
        try {
            const c = document.querySelector('a.match-container[href*="/' + g.id + '"]');
            if (c) {
                base.container = c;
                const info = extractGameInfo(c);
                if (info.gameTime && /\d|HT/.test(info.gameTime)) base.gameTime = info.gameTime;
                if (info.homeTeam && info.awayTeam) { base.homeTeam = info.homeTeam; base.awayTeam = info.awayTeam; base.gameName = info.gameName; }
            }
        } catch (e) { /* ignora */ }
        return base;
    }

    function feedProcess(ids, baseline) {
        if (isScanning) return;
        const ctx = newScanCtx();
        const list = ids ? ids.map(id => FEED.games.get(id)).filter(Boolean) : Array.from(FEED.games.values());
        list.forEach(g => {
            const gi = feedGameInfo(g);
            if (gi) processGame(gi, ctx, baseline);
        });
        flushScan(ctx);
        highlightDom();
    }

    // Etiqueta pequena na linha do jogo, no próprio site: "10 · perde" (jogadores da equipa com menos um · situação)
    const BADGE_SIT = { losing: 'perde', draw: 'empata', winning: 'ganha' };
    function badgeText(g) {
        const hR = g.homeCards || 0, aR = g.awayCards || 0, s = situationOf(g);
        if (s) return Math.max(1, 11 - Math.max(hR, aR)) + ' · ' + BADGE_SIT[s];
        return '🟥 ' + hR + '-' + aR;
    }
    function markRow(c, gg) {
        if (!c || !gg) return;
        const s = situationOf(gg);
        if (s) c.setAttribute('data-god-sit', s); else c.removeAttribute('data-god-sit');
        if (settings.siteBadge) c.setAttribute('data-god-badge', badgeText(gg)); else c.removeAttribute('data-god-badge');
    }
    function unmarkRow(c) {
        if (c.hasAttribute('data-god-sit')) c.removeAttribute('data-god-sit');
        if (c.hasAttribute('data-god-badge')) c.removeAttribute('data-god-badge');
    }

    function highlightDom() {
        try {
            detectGameContainers().forEach(c => {
                const uid = getUID(c, '');
                const gg = uid && activeGamesDB[uid];
                const on = !!(gg && !finishedGames.has(uid));
                c.classList.toggle('god-mode-highlight', on);
                if (on) { notePos(uid, c); markRow(c, gg); }
                else unmarkRow(c);
            });
        } catch (e) { /* ignora */ }
    }

    // Limpeza periódica: tira da lista os jogos que já acabaram, mesmo que a mensagem de fim se tenha perdido
    function feedSweep() {
        if (!document.body) return;
        const now = Date.now();
        let changed = false;
        const drop = (uid, record) => {
            const a = activeGamesDB[uid];
            if (!a) return;
            if (record) recordHistory(a, a.score);
            delete activeGamesDB[uid];
            finishedGames.add(uid);
            changed = true;
        };

        if (feedUsable()) {
            for (const uid in activeGamesDB) {
                const a = activeGamesDB[uid];
                const fg = FEED.games.get(uid.slice(3));
                if (fg) {
                    if (FEED_DONE[fg.st] || feedLooksOver(fg)) drop(uid, true);
                    else if (FEED_VOID[fg.st]) drop(uid, false);
                    else if (FEED_LIVE[fg.st] || FEED_PAUSED[fg.st]) a.timestamp = now;   // confirmado (ao vivo ou parado): mantém
                } else if (now - (a.timestamp || 0) > ABSENT_MS) {
                    drop(uid, false);                                  // o feed não o conhece e ninguém o atualiza
                }
            }
        } else if (now - lastSeenGames < 5 * 60 * 1000) {
            // modo ecrã: se a página tem jogos mas este já não aparece há muito, acabou
            for (const uid in activeGamesDB) {
                if (now - (activeGamesDB[uid].timestamp || 0) > DOM_ABSENT_MS) drop(uid, false);
            }
        }
        if (changed) { saveDB(); renderLiveList(); }
    }

    function updateFeedIndicator() {
        const on = feedUsable();
        // Anel da bola: verde = script a ler dados (feed, ou ecrã como reserva) · vermelho = sem dados / a arrancar
        const ok = on || (!isFirstRun && !emptyWarned);
        const fab = $('x_fab_btn');
        if (fab) {
            fab.classList.toggle('fab-ok', ok);
            fab.classList.toggle('fab-bad', !ok);
            fab.title = ok ? (on ? 'Script ativo — feed sem scroll' : 'Script ativo — modo ecrã') : 'Script sem dados (a arrancar ou sem jogos detetados)';
        }
        const h = $('x_handle');
        if (h) h.innerHTML = '@AiScore • v21.1 <span class="x-feedtag ' + (on ? 'on' : 'off') + '">' + (on ? '📡 feed' : '🖥️ ecrã') + '</span>';
    }

    function feedDiagText() {
        const s = (ms) => ms ? Math.round((Date.now() - ms) / 1000) + 's' : '—';
        let live = 0, reds = 0;
        FEED.games.forEach(g => { if (FEED_LIVE[g.st]) { live++; if ((g.h[2] | 0) + (g.a[2] | 0) > 0) reds++; } });
        return `Feed: ${feedUsable() ? '<b style="color:#4ade80">ativo</b>' : '<b style="color:#fbbf24">inativo (modo ecrã)</b>'}` +
            ` · lista: ${FEED.listAt ? FEED.games.size + ' jogos (há ' + s(FEED.listAt) + ')' : 'não recebida'}` +
            ` · MQTT: ${FEED.mqttCount} msgs (batimento há ${s(FEED.beatAt)})` +
            ` · ao vivo: ${live} · com vermelho: ${reds}` + (FEED.err ? `<br><span style="color:#f87171">${escapeHTML(FEED.err)}</span>` : '');
    }

    installSniffer();

    //======================================================================
    // 4. SMART IDLE + WEB WORKER (anti-throttling)
    //======================================================================

    let lastUserActivity = Date.now();
    ['mousemove', 'mousedown', 'keydown', 'touchstart', 'wheel'].forEach(evt => {
        window.addEventListener(evt, () => { lastUserActivity = Date.now(); }, { passive: true });
    });

    let ghostWorker = null;
    let sleepSeq = 0;
    const sleepResolvers = new Map();

    function sleep(ms) {
        if (!ghostWorker) return new Promise(r => setTimeout(r, ms));
        return new Promise(resolve => {
            const id = ++sleepSeq;
            sleepResolvers.set(id, resolve);
            ghostWorker.postMessage({ type: 'sleep', id: id, ms: ms });
        });
    }

    function onTick() {
        tickCount++;
        applyTitleBadge();
        updateFabDim();
        realTick();
        if (Date.now() - lastClockAt > 15000) refreshLiveClocks();
        if (isFirstRun || isScanning || !document.body) return;

        const isIdle = document.hidden || (Date.now() - lastUserActivity > settings.idleSeconds * 1000);
        const due    = (Date.now() - lastFullScan) > settings.scanInterval * 60 * 1000;

        const feedOn = feedUsable();
        if (tickCount % 15 === 0) feedSweep();

        if (due && isIdle && !feedOn) fullPageScan(false);      // com o feed ativo não há scroll
        else if (!observerActive || tickCount % 5 === 0) scanGames(); // rede de segurança
    }

    function startAntiThrottlingWorker() {
        const workerCode = `
            let timer = null;
            self.onmessage = function (e) {
                const d = e.data;
                if (d.type === 'start') {
                    if (!timer) timer = setInterval(() => self.postMessage({ type: 'tick' }), d.every);
                } else if (d.type === 'sleep') {
                    setTimeout(() => self.postMessage({ type: 'wake', id: d.id }), d.ms);
                }
            };
        `;
        try {
            const blob = new Blob([workerCode], { type: 'application/javascript' });
            ghostWorker = new Worker(URL.createObjectURL(blob));
            ghostWorker.onmessage = function (e) {
                const d = e.data;
                if (d.type === 'tick') onTick();
                else if (d.type === 'wake') {
                    const res = sleepResolvers.get(d.id);
                    if (res) { sleepResolvers.delete(d.id); res(); }
                }
            };
            ghostWorker.onerror = function (err) {
                console.warn('Worker falhou, a usar setInterval normal.', err);
                ghostWorker = null;
                sleepResolvers.forEach(r => r());
                sleepResolvers.clear();
                setInterval(onTick, WORKER_TICK_MS);
            };
            ghostWorker.postMessage({ type: 'start', every: WORKER_TICK_MS });
            console.log('🧠 Motor Quântico Ativado.');
        } catch (e) {
            console.warn('Web Worker indisponível, a usar setInterval normal.', e);
            ghostWorker = null;
            setInterval(onTick, WORKER_TICK_MS);
        }
    }

    //======================================================================
    // 5. MUTATION OBSERVER (substitui o polling constante)
    //======================================================================

    let moPending = false;

    function isOurNode(n) {
        return n && n.nodeType === 1 && n.hasAttribute && n.hasAttribute('data-xui');
    }

    function setupObserver() {
        if (typeof MutationObserver === 'undefined') return false;

        const mo = new MutationObserver(muts => {
            if (isFirstRun || isScanning || moPending) return;

            let relevant = false;
            for (const m of muts) {
                const t = m.target.nodeType === 1 ? m.target : m.target.parentElement;
                if (t && t.closest && t.closest('[data-xui]')) continue;
                if (m.type === 'childList') {
                    const nodes = Array.from(m.addedNodes).concat(Array.from(m.removedNodes));
                    if (nodes.length && nodes.every(isOurNode)) continue;
                }
                relevant = true;
                break;
            }
            if (!relevant) return;

            moPending = true;
            const wait = Math.max(400, OBS_MIN_GAP_MS - (Date.now() - lastScanAt));
            sleep(wait).then(() => {
                moPending = false;
                if (!isScanning && !isFirstRun) scanGames();
            });
        });

        mo.observe(document.body, { childList: true, subtree: true, characterData: true });
        return true;
    }

    //======================================================================
    // 6. GHOST TRACTOR (auto-scroll inteligente)
    //======================================================================

    async function fullPageScan(manual) {
        if (isScanning) return;
        isScanning = true;

        const startedAt = Date.now();
        lastFullScan = startedAt;
        GM_setValue(LAST_SCAN_KEY, lastFullScan);

        const originalScrollPos = window.scrollY;
        const step = 800;
        let pos = 0;
        let stuckCounter = 0;
        let previousScrollPos = -1;
        let hitAbsoluteBottom = false;
        let aborted = false;

        const blocker = document.createElement('div');
        blocker.setAttribute('data-xui', '1');
        blocker.style.cssText = 'position:fixed;top:0;left:0;width:100%;height:100%;z-index:9999999;cursor:wait;background:transparent;';
        document.body.appendChild(blocker);

        console.log('🚜 Trator Fantasma Iniciado...');

        try {
            window.scrollTo({ top: 0, behavior: 'auto' });
            await sleep(150);
            gameContainers = detectGameContainers();
            scanGames();

            while (!hitAbsoluteBottom) {
                if (!manual && lastUserActivity > startedAt) { aborted = true; break; }

                pos += step;
                window.scrollTo({ top: pos, behavior: 'auto' });
                await sleep(150);

                const currentScrollPos = window.scrollY;
                if (currentScrollPos === previousScrollPos) {
                    stuckCounter++;
                    if (stuckCounter > 2) hitAbsoluteBottom = true;
                } else {
                    stuckCounter = 0;
                }
                previousScrollPos = currentScrollPos;

                gameContainers = detectGameContainers();
                scanGames();

                const visibleGames = gameContainers.slice(-8);
                let futureCount = 0;
                for (const c of visibleGames) { if (isTooFarInFuture(c)) futureCount++; }
                if (futureCount >= 3) break;

                if (pos > document.documentElement.scrollHeight + 1500) break;
            }
        } catch (e) {
            console.error('Erro no Trator Fantasma:', e);
        } finally {
            window.scrollTo({ top: originalScrollPos, behavior: 'auto' });
            if (document.body.contains(blocker)) blocker.remove();
            isScanning = false;

            if (aborted) {
                lastFullScan = Date.now() - settings.scanInterval * 60 * 1000 + 60000;
                console.log('⏸️ Trator interrompido (utilizador ativo).');
            } else {
                console.log('✅ Trator terminado. Posição restaurada.');
            }
        }
    }

    //======================================================================
    // 7. UTILS & DATA EXTRACTORS
    //======================================================================

    function escapeHTML(str) {
        if (!str) return '';
        return str.toString()
            .replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;')
            .replace(/"/g, '&quot;').replace(/'/g, '&#039;');
    }

    function pad2(n) { return n.toString().padStart(2, '0'); }

    function addToLog(name, matchTime, totalCards, homeCards, awayCards) {
        const now = new Date();
        eventLog.unshift({
            name: name, matchTime: matchTime || '?', totalCards: totalCards,
            homeCards: homeCards, awayCards: awayCards,
            logTime: pad2(now.getHours()) + ':' + pad2(now.getMinutes())
        });
        if (eventLog.length > 50) eventLog.pop();
        GM_setValue(LOG_KEY, eventLog);

        const logBox = $('x_log_box');
        if (logBox && !logBox.classList.contains('x-hidden')) renderLog();
    }

    function getMinuteSortValue(timeStr) {
        if (!timeStr) return 0;
        const t = timeStr.toUpperCase().trim();
        if (t === 'HT' || t === 'INT') return 45.5;
        if (t.includes('FT') || t.includes('FIM')) return -1;
        if (t.includes(':')) return 0;
        const numbers = t.match(/\d+/g);
        if (!numbers) return 0;
        return parseInt(numbers[0], 10) + (numbers.length > 1 ? parseInt(numbers[1], 10) * 0.01 : 0);
    }

    function parseGameTime(timeStr) {
        if (!timeStr) return null;
        const match = timeStr.trim().match(/(\d{1,2}):(\d{2})/);
        if (!match) return null;
        const h = parseInt(match[1], 10), m = parseInt(match[2], 10);
        return { hours: h, minutes: m, total: h * 60 + m };
    }

    function parseScore(s) {
        if (!s || !s.includes('-')) return null;
        const p = s.split('-');
        const h = parseInt(p[0], 10), a = parseInt(p[1], 10);
        if (isNaN(h) || isNaN(a)) return null;
        return { h: h, a: a };
    }

    function isTooFarInFuture(gameContainer) {
        const timeSpan = gameContainer.querySelector('span.time.minitext') || gameContainer.querySelector('span.time');
        if (!timeSpan) return false;
        const timeText = timeSpan.textContent.trim();
        if (timeText.match(/\d+'/)) return false;
        if (timeText.match(/HT|INT|Pen/i)) return false;
        if (timeText.match(/^\d{1,2}:\d{2}$/)) {
            const startTime = parseGameTime(timeText);
            if (!startTime) return false;
            const now = new Date();
            const current = now.getHours() * 60 + now.getMinutes();
            let diff = startTime.total - current;
            if (diff < -720) diff += 1440;
            if (diff > 720) diff -= 1440;
            if (diff > TIME_BUFFER_MINS) return true;
        }
        return false;
    }

    function detectGameContainers() {
        return Array.from(document.querySelectorAll('a.match-container'));
    }

    function getUID(container, gameName) {
        const href = container.getAttribute('href');
        if (href) {
            const seg = href.split('?')[0].replace(/\/+$/, '').split('/').pop();
            if (/^[a-z0-9]{8,}$/i.test(seg)) return 'id_' + seg;   // mesmo id que o feed usa
            return 'm_' + href.split('?')[0].replace(/[^a-zA-Z0-9]/g, '_');
        }
        const n = (gameName || '').toLowerCase().replace(/\s+/g, '');
        return n ? 'n_' + n : '';
    }

    function readRedCards(teamElement) {
        if (!teamElement) return 0;
        const red = teamElement.querySelector('span.card.red');
        if (!red) return 0;
        const n = parseInt(red.textContent.trim(), 10);
        return n > 0 ? n : 0;
    }

    function detectRedCards(gameContainer) {
        const homeCards = readRedCards(gameContainer.querySelector('span.team.home'));
        const awayCards = readRedCards(gameContainer.querySelector('span.team.away'));
        return { total: homeCards + awayCards, homeCards: homeCards, awayCards: awayCards };
    }

    function extractGameInfo(gameContainer) {
        let homeTeam = '', awayTeam = '', score = null, gameTime = null;

        const homeEl = gameContainer.querySelector('[itemprop="homeTeam"]');
        const awayEl = gameContainer.querySelector('[itemprop="awayTeam"]');
        if (homeEl) homeTeam = homeEl.textContent.trim();
        if (awayEl) awayTeam = awayEl.textContent.trim();

        const scoresSpan = gameContainer.querySelector('span.scores');
        if (scoresSpan) {
            const h = scoresSpan.querySelector('.score-home');
            const a = scoresSpan.querySelector('.score-away');
            if (h && a) score = `${h.textContent.trim()}-${a.textContent.trim()}`;
        }

        const statusSpan = gameContainer.querySelector('span.status');
        if (statusSpan) {
            const t = statusSpan.textContent.trim();
            gameTime = t.match(/FT|Ended|Fim/i) ? 'FT' : t;
        }

        if (!gameTime) {
            const text = gameContainer.textContent;
            const m = text.match(/(\d+)'/);
            if (m) gameTime = m[1] + "'";
            else if (text.match(/HT|INT/i)) gameTime = 'HT';
            else if (text.match(/Pen/i)) gameTime = 'Pen';
        }

        const gameName = (homeTeam && awayTeam)
            ? `${homeTeam} vs ${awayTeam}`
            : (gameContainer.textContent.split('\n')[0] || '').trim();

        return { homeTeam, awayTeam, gameName, score, gameTime };
    }

    function detectMortal(prevScore, newScore, cards, wasMortal) {
        if (wasMortal) return true;
        const o = parseScore(prevScore), n = parseScore(newScore);
        if (!o || !n || prevScore === newScore) return false;
        if (n.h > o.h && cards.homeCards > cards.awayCards) return true;
        if (n.a > o.a && cards.awayCards > cards.homeCards) return true;
        return false;
    }

    // Flags de estado de um jogo (usadas na lista, nas tags e no histórico)
    function computeFlags(g) {
        const parsed = parseScore(g.score);
        const sc = parsed || { h: 0, a: 0 };
        const hR = g.homeCards || 0, aR = g.awayCards || 0;
        return {
            bloodbath: Math.abs(hR - aR) >= 2,
            mortal: !!g.mortal || (hR > aR && sc.h > sc.a) || (aR > hR && sc.a > sc.h),
            despair: (hR < aR && sc.h <= sc.a - 2) || (aR < hR && sc.a <= sc.h - 2),
            zero: g.score === '0-0',
            top: !!parsed && ((hR > aR && sc.a <= sc.h) || (aR > hR && sc.h <= sc.a))
        };
    }

    function updateTags(g) {
        g.tags = g.tags || [];
        const f = computeFlags(g);
        let changed = false;
        const add = (t) => { if (!g.tags.includes(t)) { g.tags.push(t); changed = true; } };
        if (f.bloodbath) add('bloodbath');
        if (f.mortal)    add('mortal');
        if (f.despair)   add('despair');
        if (f.top)       add('top');
        if (g.firstRed && g.firstRed.score === '0-0') add('zero');
        return changed;
    }

    function goalsAfterRed(g, currentScore) {
        const a = parseScore(g.firstRed && g.firstRed.score);
        const b = parseScore(currentScore || g.score);
        if (!a || !b) return null;
        return Math.max(0, (b.h + b.a) - (a.h + a.a));
    }

    //======================================================================
    // 8. COMPETIÇÕES & FILTROS & PERFIL DE ALERTAS
    //======================================================================

    function cleanText(t) { return (t || '').replace(/\s+/g, ' ').trim().slice(0, 80); }

    // Heurística: o cabeçalho de competição é o último elemento "header" que precede o jogo no DOM.
    function computeCompetitions(containers) {
        const sel = (settings.compSelector || '').trim() || DEFAULT_COMP_SELECTOR;
        let headers = [];
        try { headers = Array.from(document.querySelectorAll(sel)); } catch (e) { headers = []; }
        headers = headers.filter(h =>
            !h.closest('a.match-container') &&
            !h.querySelector('a.match-container') &&
            !h.closest('[data-xui]') &&
            h.textContent.trim()
        );

        const out = [];
        let idx = -1;
        containers.forEach(c => {
            while (idx + 1 < headers.length &&
                   (headers[idx + 1].compareDocumentPosition(c) & Node.DOCUMENT_POSITION_FOLLOWING)) {
                idx++;
            }
            out.push(idx >= 0 ? cleanText(headers[idx].textContent) : '');
        });
        return out;
    }

    function parseList(str) {
        return (str || '').split(',').map(s => s.trim().toLowerCase()).filter(Boolean);
    }

    function passesCompFilter(gameName, comp) {
        const hay = ((comp || '') + ' ' + (gameName || '')).toLowerCase();
        const exc = parseList(settings.excludeComp);
        const inc = parseList(settings.includeComp);
        if (exc.some(k => hay.includes(k))) return false;
        if (inc.length && !inc.some(k => hay.includes(k))) return false;
        return true;
    }

    // Perfil de alertas: só afeta pop-up, som e voz (o jogo continua na lista e no log).
    function passesAlertProfile(cards, gameTime, score) {
        const p = settings.profile;
        const minute = getMinuteSortValue(gameTime);
        if (minute > 0 && (minute < p.minMinute || minute > p.maxMinute)) return false;
        if (p.skipBothReds && cards.homeCards > 0 && cards.awayCards > 0) return false;

        const sc = parseScore(score);
        if (p.onlyZeroZero && !(sc && sc.h === 0 && sc.a === 0)) return false;

        if (p.maxRedTeamDeficit > 0 && sc) {
            if (cards.homeCards > cards.awayCards && sc.a - sc.h >= p.maxRedTeamDeficit) return false;
            if (cards.awayCards > cards.homeCards && sc.h - sc.a >= p.maxRedTeamDeficit) return false;
        }
        return true;
    }

    //======================================================================
    // 9. HISTÓRICO
    //======================================================================

    function redTeamOutcome(g, finalScore) {
        const sc = parseScore(finalScore);
        if (!sc) return '-';
        const hR = g.homeCards || 0, aR = g.awayCards || 0;
        if (hR === aR) return '-';
        const mine = hR > aR ? sc.h : sc.a;
        const opp  = hR > aR ? sc.a : sc.h;
        return mine > opp ? 'W' : (mine === opp ? 'D' : 'L');
    }

    function recordHistory(g, finalScore) {
        if (!g || !g.firstRed) return;
        const now = new Date();
        const hR = g.homeCards || 0, aR = g.awayCards || 0;
        history.push({
            date: `${now.getFullYear()}-${pad2(now.getMonth() + 1)}-${pad2(now.getDate())} ${pad2(now.getHours())}:${pad2(now.getMinutes())}`,
            comp: g.comp || '',
            name: g.name,
            redMin: g.firstRed.time,
            scoreAtRed: g.firstRed.score,
            homeReds: hR,
            awayReds: aR,
            finalScore: finalScore || g.score || '',
            redTeam: hR > aR ? 'home' : (aR > hR ? 'away' : 'both'),
            result: redTeamOutcome(g, finalScore || g.score),
            goalsAfter: goalsAfterRed(g, finalScore || g.score),
            tags: (g.tags || []).join('|')
        });
        if (history.length > HISTORY_MAX) history = history.slice(-HISTORY_MAX);
        saveHistory();
    }

    // Métricas derivadas de uma entrada do histórico (funciona também com entradas antigas)
    const MIN_BUCKETS = ['1–30', '31–45', '46–60', '61–75', '76+'];
    function minuteBucket(m) {
        if (!(m > 0)) return 'Sem minuto';
        if (m <= 30) return MIN_BUCKETS[0];
        if (m < 46)  return MIN_BUCKETS[1];
        if (m <= 60) return MIN_BUCKETS[2];
        if (m <= 75) return MIN_BUCKETS[3];
        return MIN_BUCKETS[4];
    }
    function enrichHistory(h) {
        const minute = getMinuteSortValue(h.redMin);
        const out = { minute: minute > 0 ? minute : null, bucket: minuteBucket(minute), state: '', scored: null, conceded: null };
        const at = parseScore(h.scoreAtRed), fin = parseScore(h.finalScore);
        if (!at || !fin || (h.redTeam !== 'home' && h.redTeam !== 'away')) return out;
        const home = h.redTeam === 'home';
        const mineAt = home ? at.h : at.a, oppAt = home ? at.a : at.h;
        const mineFin = home ? fin.h : fin.a, oppFin = home ? fin.a : fin.h;
        out.state = mineAt < oppAt ? 'perdia' : (mineAt === oppAt ? 'empatava' : 'ganhava');
        out.scored = Math.max(0, mineFin - mineAt);
        out.conceded = Math.max(0, oppFin - oppAt);
        return out;
    }

    function buildMinuteStats() {
        const acc = {};
        history.forEach(h => {
            const e = enrichHistory(h);
            if (e.scored === null) return;
            const a = acc[e.bucket] = acc[e.bucket] || { n: 0, sc: 0, co: 0, res: 0, nl: 0 };
            a.n++; a.sc += e.scored; a.co += e.conceded;
            if (h.result === 'W' || h.result === 'D' || h.result === 'L') { a.res++; if (h.result !== 'L') a.nl++; }
        });
        const order = MIN_BUCKETS.concat(['Sem minuto']);
        const rows = order.filter(b => acc[b]).map(b => ({ label: b, a: acc[b] }));
        const tot = { n: 0, sc: 0, co: 0, res: 0, nl: 0 };
        rows.forEach(r => { for (const k in tot) tot[k] += r.a[k]; });
        if (rows.length) rows.push({ label: 'Total', a: tot, total: true });
        return rows;
    }

    function csvCell(v) {
        const s = (v === null || v === undefined) ? '' : String(v);
        return /[;"\n\r]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s;
    }

    function downloadFile(name, content, mime) {
        const blob = new Blob([content], { type: mime });
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.setAttribute('data-xui', '1');
        a.href = url;
        a.download = name;
        document.body.appendChild(a);
        a.click();
        setTimeout(() => { a.remove(); URL.revokeObjectURL(url); }, 500);
    }

    function exportHistoryCSV() {
        if (history.length === 0) { showToast('Histórico vazio.', 'warning'); return; }
        const cols = ['data', 'competicao', 'jogo', 'min_vermelho_visto', 'placar_no_vermelho', 'vermelhos_casa', 'vermelhos_fora', 'placar_final', 'equipa_com_10', 'resultado_equipa_com_10', 'golos_apos_vermelho', 'tags',
            'minuto_num', 'faixa_minuto', 'estado_no_vermelho', 'golos_marcados_pelos_10', 'golos_sofridos_pelos_10', 'saldo_apos_vermelho', 'total_vermelhos'];
        const rows = history.map(h => {
            const e = enrichHistory(h);
            const saldo = e.scored === null ? '' : e.scored - e.conceded;
            return [h.date, h.comp, h.name, h.redMin, h.scoreAtRed, h.homeReds, h.awayReds, h.finalScore, h.redTeam, h.result, h.goalsAfter, h.tags,
                e.minute === null ? '' : e.minute, e.bucket, e.state, e.scored === null ? '' : e.scored, e.conceded === null ? '' : e.conceded, saldo,
                (h.homeReds || 0) + (h.awayReds || 0)].map(csvCell).join(';');
        });
        const csv = '\uFEFF' + cols.join(';') + '\n' + rows.join('\n');
        const d = new Date();
        downloadFile(`aiscore_vermelhos_${d.getFullYear()}${pad2(d.getMonth() + 1)}${pad2(d.getDate())}.csv`, csv, 'text/csv;charset=utf-8');
        showToast('📥 CSV exportado (separador ;)', 'success');
    }

    const TAG_LABELS = {
        mortal: '💎 Mortal',
        despair: '🆘 Desespero',
        zero: '🎯 0-0 no vermelho',
        top: '🔥 Equipa com 10 não perde',
        bloodbath: '🚨 Banho de sangue'
    };

    function buildStats() {
        const calc = (list) => {
            const resolved = list.filter(h => h.result === 'W' || h.result === 'D' || h.result === 'L');
            const notLost = resolved.filter(h => h.result !== 'L').length;
            const gl = list.filter(h => typeof h.goalsAfter === 'number');
            return {
                n: list.length,
                resolved: resolved.length,
                notLostPct: resolved.length ? Math.round(notLost * 100 / resolved.length) : null,
                avgGoals: gl.length ? (gl.reduce((s, h) => s + h.goalsAfter, 0) / gl.length) : null
            };
        };
        const rows = [{ label: 'Todos', stat: calc(history) }];
        Object.keys(TAG_LABELS).forEach(tag => {
            const list = history.filter(h => (h.tags || '').split('|').includes(tag));
            rows.push({ label: TAG_LABELS[tag], stat: calc(list) });
        });
        return rows;
    }

    //======================================================================
    // 10. SCANNER
    //======================================================================

    function updateEmptyWatch(count) {
        if (count > 0) {
            lastSeenGames = Date.now();
            if (emptyWarned) { emptyWarned = false; setFabWarning(false); }
            return;
        }
        if (isFirstRun || emptyWarned) return;
        if (Date.now() - lastSeenGames > EMPTY_WARN_MS) {
            emptyWarned = true;
            setFabWarning(true);
            showToast('⚠️ Nenhum jogo detetado há 2 min. A página pode não ter jogos ou o AiScore mudou o HTML (seletores).', 'warning', 8000);
        }
    }

    function setFabWarning(on) {
        const fab = $('x_fab_btn');
        if (!fab) return;
        fab.classList.toggle('fab-warn', on);
        fab.title = on ? 'Aviso: nenhum jogo detetado (seletores podem ter mudado)' : '';
    }

    function newScanCtx() { return { dataChanged: false, hasNewRedCard: false, pendingAlerts: [] }; }

    // Lógica por jogo — igual para o ecrã (DOM) e para o feed de rede.
    // baseline = leitura inicial de uma lista: jogos novos com vermelhos antigos entram sem alertar.
    function processGame(gi, ctx, baseline) {
        const uid = gi.uid;
        if (!uid) return;
        const { container, homeTeam, awayTeam, gameName, score, gameTime, comp, cards } = gi;

        if (gi.finished || gameTime === 'FT') {
            const done = activeGamesDB[uid];
            if (done) {
                if (!gi.noHistory) recordHistory(done, score || done.score);
                delete activeGamesDB[uid];
                ctx.dataChanged = true;
            }
            finishedGames.add(uid);
            return;
        }

        if (finishedGames.has(uid)) return;
        if (cards.total === 0 || cards.total < settings.minCards) return;

        if (!passesCompFilter(gameName, comp)) {
            if (activeGamesDB[uid]) { delete activeGamesDB[uid]; ctx.dataChanged = true; }
            return;
        }

        let g = activeGamesDB[uid];
        const isNew = !g;
        const prev = isNew ? { h: 0, a: 0 } : { h: g.homeCards || 0, a: g.awayCards || 0 };
        const quiet = isFirstRun || (isNew && !!baseline);

        if (isNew) {
            ctx.dataChanged = true;
            g = activeGamesDB[uid] = {
                uid: uid, name: gameName, comp: comp, time: gameTime, score: score,
                cards: cards.total, homeCards: cards.homeCards, awayCards: cards.awayCards,
                timestamp: Date.now(), totalNotified: 0, mortal: false, starred: false,
                mutedUntil: 0, firstRed: null, redEvents: [], tags: []
            };
        } else {
            const isMortal = detectMortal(g.score, score, cards, g.mortal || false);
            if (g.time !== gameTime || g.score !== score || g.cards !== cards.total || g.mortal !== isMortal) ctx.dataChanged = true;

            g.name = gameName || g.name;
            if (!g.comp && comp) { g.comp = comp; ctx.dataChanged = true; }
            g.time = gameTime || g.time;
            if (score && g.score && score !== g.score) {
                const ps = parseScore(g.score), ns = parseScore(score);
                if (ps && ns) {
                    g.goals = Array.isArray(g.goals) ? g.goals : [];
                    const dg = (ns.h + ns.a) - (ps.h + ps.a);
                    if (dg > 0) {
                        const gside = ns.h > ps.h ? 'h' : (ns.a > ps.a ? 'a' : '');
                        for (let k = 0; k < Math.min(dg, 4); k++) g.goals.push({ time: gameTime || g.time || '?', score: score, side: gside, at: Date.now() });
                        if (g.goals.length > 24) g.goals = g.goals.slice(-24);
                    } else if (dg < 0) {
                        g.goals.splice(Math.max(0, g.goals.length + dg));   // golo anulado (VAR)
                    }
                    ctx.dataChanged = true;
                }
            }
            g.score = score || g.score;
            g.cards = cards.total;
            g.homeCards = cards.homeCards;
            g.awayCards = cards.awayCards;
            g.timestamp = Date.now();
            g.mortal = isMortal;
            g.redEvents = g.redEvents || [];
            g.tags = g.tags || [];

            if (cards.total < g.totalNotified) { g.totalNotified = cards.total; ctx.dataChanged = true; }
        }

        if (cards.total > g.totalNotified) {
            g.totalNotified = cards.total;
            ctx.dataChanged = true;

            const homeUp = cards.homeCards > prev.h, awayUp = cards.awayCards > prev.a;
            const side = (homeUp && awayUp) ? 'both' : (homeUp ? 'home' : (awayUp ? 'away' : 'both'));
            const ev = { time: gameTime || '?', score: score || '?', side: side, approx: quiet, at: Date.now() };
            g.redEvents.push(ev);
            if (!g.firstRed) g.firstRed = ev;

            addToLog(gameName, gameTime, cards.total, cards.homeCards, cards.awayCards);

            const muted = (g.mutedUntil || 0) > Date.now();
            if (!quiet && !muted && passesAlertProfile(cards, gameTime, score)) {
                ctx.hasNewRedCard = true;
                const hIcon = cards.homeCards > 0 ? '🟥'.repeat(cards.homeCards) + ' ' : '';
                const aIcon = cards.awayCards > 0 ? ' ' + '🟥'.repeat(cards.awayCards) : '';
                const title = `🚨 ${hIcon}${homeTeam} vs ${awayTeam}${aIcon}`;
                const redTeamName = cards.homeCards > cards.awayCards ? homeTeam : (cards.awayCards > cards.homeCards ? awayTeam : '');
                const who = cards.homeCards > cards.awayCards
                    ? `🛑 Desvantagem: ${homeTeam} (Casa)`
                    : (cards.awayCards > cards.homeCards ? `🛑 Desvantagem: ${awayTeam} (Fora)` : '🛑 Ambas com vermelhos!');
                ctx.pendingAlerts.push({
                    title: title,
                    text: `⏱️ ${gameTime || '?'} | ⚽ ${score || '?'}\n${who}` + (g.comp ? `\n🏆 ${g.comp}` : ''),
                    uid: uid,
                    speech: redTeamName ? `Cartão vermelho. ${redTeamName}` : 'Cartão vermelho. Ambas as equipas',
                    data: {
                        uid: uid, homeTeam: homeTeam, awayTeam: awayTeam, homeCards: cards.homeCards, awayCards: cards.awayCards,
                        total: cards.total, side: side, minute: gameTime || '?', score: score || '?', comp: g.comp || '',
                        sit: situationOf({ homeCards: cards.homeCards, awayCards: cards.awayCards, score: score })
                    }
                });
            }
        }

        if (updateTags(g)) ctx.dataChanged = true;
        if (container) { container.classList.add('god-mode-highlight'); notePos(uid, container); markRow(container, g); }
    }

    function flushScan(ctx) {
        if (ctx.dataChanged) saveDB();
        ctx.pendingAlerts.forEach(a => { showRedCardAlert(a.data, a.title, a.text); speakAlert(a.speech); });
        if (ctx.hasNewRedCard) { playAlertSound(); flashTitle(); wakeFab(); }
        if (ctx.dataChanged) renderLiveList();
    }

    function scanGames() {
        lastScanAt = Date.now();
        const containers = detectGameContainers();
        updateEmptyWatch(containers.length);
        const comps = computeCompetitions(containers);
        const ctx = newScanCtx();

        containers.forEach((container, idx) => {
            container.classList.remove('god-mode-highlight');
            const info = extractGameInfo(container);
            processGame({
                uid: getUID(container, info.gameName), container: container,
                homeTeam: info.homeTeam, awayTeam: info.awayTeam, gameName: info.gameName,
                score: info.score, gameTime: info.gameTime, comp: comps[idx] || '',
                cards: detectRedCards(container)
            }, ctx, false);
        });

        flushScan(ctx);
        highlightDom();
    }

    //======================================================================
    // 11. ALERTAS: SOM, VOZ, TÍTULO, FAVICON
    //======================================================================

    let audioCtx = null;
    let audioWarned = false;

    function unlockAudio() {
        try {
            if (!audioCtx) {
                const AC = window.AudioContext || window.webkitAudioContext;
                if (AC) audioCtx = new AC();
            }
            if (audioCtx && audioCtx.state === 'suspended') audioCtx.resume();
        } catch (e) { /* ignora */ }
    }
    ['click', 'keydown', 'touchend'].forEach(evt => window.addEventListener(evt, unlockAudio, { passive: true }));

    function playAlertSound() {
        if (!settings.soundOn) return;
        unlockAudio();
        if (!audioCtx || audioCtx.state !== 'running') {
            if (!audioWarned) {
                audioWarned = true;
                showToast('🔇 Som bloqueado pelo browser. Clica uma vez na página para ativar.', 'warning', 6000);
            }
            return;
        }
        const t0 = audioCtx.currentTime;
        [0, 0.22, 0.44].forEach((offset, i) => {
            const osc = audioCtx.createOscillator();
            const gain = audioCtx.createGain();
            osc.type = 'square';
            osc.frequency.value = i === 2 ? 1175 : 880;
            gain.gain.setValueAtTime(0.0001, t0 + offset);
            gain.gain.exponentialRampToValueAtTime(0.35, t0 + offset + 0.02);
            gain.gain.exponentialRampToValueAtTime(0.0001, t0 + offset + 0.18);
            osc.connect(gain);
            gain.connect(audioCtx.destination);
            osc.start(t0 + offset);
            osc.stop(t0 + offset + 0.2);
        });
    }

    function speakAlert(text) {
        if (!settings.voiceOn || !('speechSynthesis' in window)) return;
        try {
            const u = new SpeechSynthesisUtterance(text);
            u.lang = 'pt-PT';
            window.speechSynthesis.speak(u);
        } catch (e) { /* ignora */ }
    }

    let flashing = false;
    const TITLE_PREFIX = /^\(\d+\) 🟥 /;

    function setBadgeTitle() {
        if (!settings.titleBadge) return;
        const clean = document.title.replace(TITLE_PREFIX, '');
        const wanted = lastLiveCount > 0 ? `(${lastLiveCount}) 🟥 ${clean}` : clean;
        if (document.title !== wanted) document.title = wanted;
    }

    function applyTitleBadge() {
        if (flashing) return;
        setBadgeTitle();
    }

    async function flashTitle() {
        if (flashing || !settings.titleBadge) return;
        flashing = true;
        const base = document.title.replace(TITLE_PREFIX, '');
        for (let i = 0; i < 10; i++) {
            document.title = '🚨 NOVO VERMELHO 🚨';
            await sleep(900);
            document.title = base;
            await sleep(900);
            if (!document.hidden && i >= 2) break;
        }
        flashing = false;
        setBadgeTitle();
    }

    let origFavHref = null;
    let lastFavCount = -1;
    let lastFavColor = '#f4212e';

    // Cor do favicon: vermelho se alguma equipa com 10 perde · laranja se (só) há empates · verde se estão todas a ganhar
    function favColorOf(arr) {
        let l = 0, d = 0, w = 0;
        arr.forEach(g => { const s = situationOf(g); if (s === 'losing') l++; else if (s === 'draw') d++; else if (s === 'winning') w++; });
        return l ? '#f4212e' : (d ? '#f59e0b' : (w ? '#00ba7c' : '#f4212e'));
    }

    function setFavicon(count, color) {
        if (color) lastFavColor = color;
        const col = settings.siteBadge ? lastFavColor : '#f4212e';
        const key = count + '|' + col;
        if (!settings.titleBadge || key === lastFavCount) return;
        lastFavCount = key;
        try {
            let link = document.querySelector('link[rel~="icon"]');
            if (!link) {
                if (!document.head) return;
                link = document.createElement('link');
                link.rel = 'icon';
                document.head.appendChild(link);
            }
            if (origFavHref === null) origFavHref = link.href || '';
            if (count <= 0) {
                if (origFavHref && link.href !== origFavHref) link.href = origFavHref;
                return;
            }
            const c = document.createElement('canvas');
            c.width = c.height = 32;
            const ctx = c.getContext('2d');
            ctx.fillStyle = col;
            ctx.beginPath(); ctx.arc(16, 16, 15, 0, Math.PI * 2); ctx.fill();
            ctx.fillStyle = col === '#f59e0b' ? '#111' : '#fff';
            ctx.font = 'bold 20px Arial';
            ctx.textAlign = 'center';
            ctx.textBaseline = 'middle';
            ctx.fillText(count > 9 ? '9+' : String(count), 16, 17);
            link.href = c.toDataURL('image/png');
        } catch (e) { /* ignora */ }
    }

    //======================================================================
    // 12. UI HELPERS, CSS
    //======================================================================

    // ---------- Notificações visuais ----------
    const NOTIF_MAX = 4;     // cartões de alerta visíveis em simultâneo
    const NOTIF_MS  = 12000; // tempo antes de desaparecerem (pausa com o rato por cima)
    const TOAST_MAX = 3;

    function getStack(id, extra) {
        let s = document.getElementById(id);
        if (!s) {
            s = document.createElement('div');
            s.id = id;
            s.className = extra;
            s.setAttribute('data-xui', '1');
            document.body.appendChild(s);
        }
        return s;
    }

    function dismissNotif(el) {
        if (!el || el.__gone) return;
        el.__gone = true;
        el.classList.add('out');
        setTimeout(() => el.remove(), 220);
    }

    // Alerta de cartão vermelho: um cartão por evento, empilhados, com ações
    function showRedCardAlert(d, title, text) {
        if (!settings.notificationsOn) return;
        d = d || {};
        const stack = getStack('x_notif_stack', 'x-notif-stack');
        const nth = d.total > 1 ? `${d.total}.º CARTÃO VERMELHO` : 'CARTÃO VERMELHO';
        const hit = (side) => d.side === 'both' || d.side === side;
        const svg = (n, side) => n > 0 ? `<span class="x-nrc${hit(side) ? ' hit' : ''}">${getRedCardSVG(n)}</span>` : '';
        const redSide = (d.homeCards || 0) > (d.awayCards || 0) ? 'Casa' : 'Fora';
        const sitHtml = d.sit ? `<span class="x-sit ${d.sit}">${redSide} c/10 · ${SIT_TEXT[d.sit]}</span>` : '';

        const card = document.createElement('div');
        card.className = 'x-ncard';
        card.setAttribute('role', 'alert');
        card.setAttribute('data-xui', '1');
        card.innerHTML =
            `<i class="x-nbar"></i>` +
            `<div class="x-nhead"><span class="x-nkind">${escapeHTML(nth)}</span><span class="x-nmin">${escapeHTML(d.minute || '?')}</span><button class="x-nx" title="Fechar" aria-label="Fechar">×</button></div>` +
            `<div class="x-nmatch">` +
                `<div class="x-nteam home"><span class="x-nname" title="${escapeHTML(d.homeTeam || '')}">${escapeHTML(d.homeTeam || '')}</span>${svg(d.homeCards || 0, 'home')}</div>` +
                `<div class="x-nscore">${escapeHTML(d.score || '-')}</div>` +
                `<div class="x-nteam away">${svg(d.awayCards || 0, 'away')}<span class="x-nname" title="${escapeHTML(d.awayTeam || '')}">${escapeHTML(d.awayTeam || '')}</span></div>` +
            `</div>` +
            ((sitHtml || d.comp) ? `<div class="x-nmeta">${sitHtml}${d.comp ? `<span class="x-ncomp" title="${escapeHTML(d.comp)}">${escapeHTML(d.comp)}</span>` : ''}</div>` : '') +
            (d.uid ? `<div class="x-nact"><button class="x-nbtn pri" data-a="go">Ver jogo</button><button class="x-nbtn" data-a="mute">Silenciar 10 min</button></div>` : '') +
            `<div class="x-nprog"><b style="animation-duration:${NOTIF_MS}ms"></b></div>`;

        const go = () => { dismissNotif(card); if (d.uid) activateSonarSearch(d.uid); };
        card.addEventListener('click', e => {
            const b = e.target.closest('button');
            if (b && b.classList.contains('x-nx')) { e.stopPropagation(); dismissNotif(card); return; }
            if (b && b.getAttribute('data-a') === 'mute') {
                e.stopPropagation();
                const g = d.uid && activeGamesDB[d.uid];
                if (g) { g.mutedUntil = Date.now() + MUTE_MS; saveDB(); renderLiveList(); }
                dismissNotif(card);
                showToast('Alertas deste jogo silenciados 10 min.', 'info', 1800);
                return;
            }
            if (d.uid) go();
        });
        card.querySelector('.x-nprog b').addEventListener('animationend', () => dismissNotif(card));

        stack.insertBefore(card, stack.firstChild);   // o mais recente em cima
        const cards = stack.querySelectorAll('.x-ncard:not(.out)');
        for (let i = NOTIF_MAX; i < cards.length; i++) dismissNotif(cards[i]);

        try {
            GM_notification({
                title: title || '🚨 Cartão vermelho', text: text || '', image: GIF_URL, timeout: 5000,
                onclick: () => { window.focus(); if (d.uid) activateSonarSearch(d.uid); }
            });
        } catch (e) { /* ignora */ }
    }

    // Avisos curtos: ao centro em baixo, empilhados, sem tapar a bola nem os botões
    function showToast(msg, type = 'info', duration = 2500) {
        const icons = { success: '✓', error: '✕', warning: '!', info: 'i' };
        const stack = getStack('x_toast_stack', 'x-toast-stack');
        const t = document.createElement('div');
        t.className = 'x-toast ' + (icons[type] ? type : 'info');
        t.setAttribute('data-xui', '1');
        // o ícone já diz o tipo: tira o emoji do início da mensagem
        const clean = String(msg).replace(/^(?:\p{Extended_Pictographic}️?\s*)+/u, '');
        t.innerHTML = `<i>${icons[type] || 'i'}</i><span>${clean}</span>`;
        stack.appendChild(t);
        const all = stack.querySelectorAll('.x-toast:not(.out)');
        for (let i = 0; i < all.length - TOAST_MAX; i++) dismissNotif(all[i]);
        setTimeout(() => dismissNotif(t), duration);
    }

    function smartTruncate(teamName, maxChars = 14) {
        if (!teamName) return '';
        if (teamName.length <= maxChars) return teamName;
        const words = teamName.split(' ');
        let result = '';
        for (const w of words) {
            const test = result ? result + ' ' + w : w;
            if (test.length <= maxChars) result = test;
            else break;
        }
        return result || teamName.slice(0, maxChars) + '.';
    }

    function getRedCardSVG(count) {
        return `<svg viewBox="0 0 16 24" class="x-red-card-svg" xmlns="http://www.w3.org/2000/svg"><rect x="0" y="0" width="16" height="24" fill="#f4212e" rx="1"/><text x="8" y="16" font-size="10" font-weight="900" fill="white" text-anchor="middle" font-family="Arial">${count}</text></svg>`;
    }

    GM_addStyle(`
        :root { --x-card: rgba(0,0,0,0.98); --x-border:#2f3336; --x-blue:#1d9bf0; --x-red:#f4212e; --x-green:#00ba7c; --x-orange:#f59e0b; --x-text-main:#eff3f4; --x-text-muted:#71767b; }
        .god-mode-highlight { position:relative; z-index:5; background:linear-gradient(90deg,rgba(244,33,46,0.3)0%,rgba(0,0,0,0)100%)!important; box-shadow:inset 0 0 30px rgba(244,33,46,0.2)!important; transition:all .3s ease; border-left:4px solid #f4212e!important; }
        @keyframes god-focus-pulse { 0%{outline:2px solid transparent;}50%{outline:3px solid #ff4444;box-shadow:0 0 20px rgba(255,68,68,0.6),inset 0 0 30px rgba(255,68,68,0.2)!important;}100%{outline:2px solid #ff4444;} }
        .god-focused { animation:god-focus-pulse 2s ease-in-out; scroll-margin: 200px; }
        .god-target{position:relative!important;z-index:6;outline:3px solid #facc15!important;outline-offset:-3px;border-radius:6px;background-color:rgba(250,204,21,.13)!important;box-shadow:0 0 0 4px rgba(250,204,21,.25),0 0 28px 6px rgba(250,204,21,.55)!important;animation:god-target-pulse 1.1s ease-in-out 4;scroll-margin:200px;}
        .god-target::before{content:attr(data-god-label);position:absolute;top:0;left:0;background:#facc15;color:#111;font:800 10px/1 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:3px 7px;border-radius:0 0 6px 0;z-index:7;pointer-events:none;letter-spacing:.04em;}
        @keyframes god-target-pulse{0%,100%{box-shadow:0 0 0 4px rgba(250,204,21,.25),0 0 14px 2px rgba(250,204,21,.4);}50%{box-shadow:0 0 0 7px rgba(250,204,21,.35),0 0 38px 12px rgba(250,204,21,.8);}}
        #x_sonar_back{position:fixed;right:125px;bottom:62px;z-index:9999;background:rgba(0,0,0,.92);color:var(--x-text-main);border:1px solid var(--x-blue);border-radius:20px;padding:8px 14px;font:700 12px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;cursor:pointer;box-shadow:0 6px 24px rgba(0,0,0,.7);user-select:none;animation:x-back-in .25s ease-out;}
        #x_sonar_back:hover{background:var(--x-blue);color:#fff;}
        @keyframes x-back-in{from{opacity:0;transform:translateX(16px);}to{opacity:1;transform:translateX(0);}}
        #x_fab_btn{position:fixed;bottom:50px;right:50px;z-index:9999;width:60px;height:60px;border-radius:50%;border:3px solid var(--x-border);cursor:pointer;padding:0;overflow:hidden;background:black;box-shadow:0 0 15px rgba(0,0,0,.8);user-select:none;transition:transform .2s;}
        #x_fab_btn:hover{transform:scale(1.05);}
        .fab-ok{border-color:var(--x-green)!important;box-shadow:0 0 16px rgba(0,186,124,.55)!important;}
        .fab-bad{border-color:var(--x-red)!important;box-shadow:0 0 16px rgba(244,33,46,.55)!important;}
        .fab-warn{outline:3px dashed var(--x-orange)!important;outline-offset:3px;}
        .x-notif-stack{position:fixed;top:16px;right:16px;z-index:999999;display:flex;flex-direction:column;gap:10px;pointer-events:none;max-height:calc(100vh - 32px);}
        .x-ncard{pointer-events:auto;position:relative;width:380px;max-width:calc(100vw - 32px);box-sizing:border-box;background:#0b0d0f;border:1px solid #2f3336;border-radius:14px;padding:11px 14px 15px 18px;color:#eff3f4;font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;box-shadow:0 14px 40px rgba(0,0,0,.65),0 0 0 1px rgba(244,33,46,.12);overflow:hidden;cursor:pointer;animation:x-ncard-in .3s cubic-bezier(.2,.8,.2,1);transition:opacity .2s,transform .2s;}
        .x-ncard:hover{border-color:#3d4146;}
        .x-ncard.out{opacity:0;transform:translateX(28px);}
        .x-nbar{position:absolute;left:0;top:0;bottom:0;width:4px;background:var(--x-red);}
        .x-nhead{display:flex;align-items:center;gap:8px;margin-bottom:9px;}
        .x-nkind{font-size:10px;font-weight:800;letter-spacing:.08em;color:#ff6b73;}
        .x-nmin{font-size:11px;font-weight:700;color:var(--x-text-muted);background:#16181c;border-radius:6px;padding:1px 7px;}
        .x-nx{margin-left:auto;background:none;border:0;color:var(--x-text-muted);font-size:18px;line-height:1;cursor:pointer;padding:0 2px;}
        .x-nx:hover{color:#fff;}
        .x-nmatch{display:grid;grid-template-columns:1fr auto 1fr;align-items:center;gap:10px;}
        .x-nteam{display:flex;align-items:center;gap:6px;min-width:0;font-size:14px;font-weight:700;}
        .x-nteam.home{justify-content:flex-end;text-align:right;}
        .x-nteam.away{justify-content:flex-start;}
        .x-nname{overflow:hidden;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;line-height:1.2;word-break:break-word;min-width:0;}
        .x-nrc{display:inline-flex;flex-shrink:0;opacity:.6;}
        .x-nrc.hit{opacity:1;filter:drop-shadow(0 0 5px rgba(244,33,46,.8));}
        .x-nrc svg{width:12px;height:18px;}
        .x-nscore{font-size:16px;font-weight:800;background:#16181c;border-radius:8px;padding:3px 10px;font-variant-numeric:tabular-nums;}
        .x-nmeta{display:flex;align-items:center;gap:8px;margin-top:9px;flex-wrap:wrap;}
        .x-ncomp{font-size:10px;color:var(--x-text-muted);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:170px;}
        .x-nact{display:flex;gap:8px;margin-top:11px;}
        .x-nbtn{flex:1;font:700 11px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:7px 10px;border-radius:8px;border:1px solid #2f3336;background:#16181c;color:#eff3f4;cursor:pointer;transition:background .15s,border-color .15s;}
        .x-nbtn:hover{background:#1d2126;border-color:#3d4146;}
        .x-nbtn.pri{background:var(--x-blue);border-color:var(--x-blue);color:#fff;}
        .x-nbtn.pri:hover{background:#1a8cd8;}
        .x-nprog{position:absolute;left:0;right:0;bottom:0;height:3px;background:rgba(255,255,255,.05);}
        .x-nprog b{display:block;height:100%;background:var(--x-red);transform-origin:left;animation:x-nprog linear forwards;}
        .x-ncard:hover .x-nprog b{animation-play-state:paused;}
        @keyframes x-nprog{from{transform:scaleX(1);}to{transform:scaleX(0);}}
        @keyframes x-ncard-in{from{opacity:0;transform:translateX(36px) scale(.98);}to{opacity:1;transform:none;}}
        .x-toast-stack{position:fixed;bottom:24px;left:50%;transform:translateX(-50%);z-index:999998;display:flex;flex-direction:column;gap:8px;align-items:center;pointer-events:none;}
        .x-toast{display:flex;align-items:center;gap:10px;max-width:min(420px,calc(100vw - 32px));background:#111418;color:#eff3f4;border:1px solid #2f3336;border-radius:12px;padding:9px 14px 9px 10px;font:600 13px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;box-shadow:0 8px 28px rgba(0,0,0,.55);animation:x-toast-in .22s ease-out;transition:opacity .2s,transform .2s;}
        .x-toast.out{opacity:0;transform:translateY(8px);}
        .x-toast i{flex-shrink:0;width:20px;height:20px;border-radius:50%;display:inline-flex;align-items:center;justify-content:center;font:800 12px/1 -apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;font-style:normal;color:#fff;background:var(--x-blue);}
        .x-toast.success i{background:var(--x-green);} .x-toast.error i{background:var(--x-red);} .x-toast.warning i{background:var(--x-orange);}
        @keyframes x-toast-in{from{opacity:0;transform:translateY(10px);}to{opacity:1;transform:none;}}
        @media (prefers-reduced-motion:reduce){.x-ncard,.x-toast{animation:none!important;}}

        @keyframes x-feed-pulse{0%{box-shadow:0 0 0 0 rgba(0,186,124,.7);}70%{box-shadow:0 0 0 7px rgba(0,186,124,0);}100%{box-shadow:0 0 0 0 rgba(0,186,124,0);}}
        .x-feedtag{display:inline-block;font-size:9px;font-weight:700;padding:1px 6px;border-radius:8px;margin-left:4px;vertical-align:middle;}
        .x-feedtag.on{background:rgba(0,186,124,.18);color:#4ade80;}
        .x-feedtag.off{background:rgba(245,158,11,.18);color:#fbbf24;}
        .x-filter-bar{display:flex;flex-direction:column;gap:6px;margin-bottom:8px;}
        .x-filter-bar input{width:100%;box-sizing:border-box;background:#0b0d0f;border:1px solid var(--x-border);border-radius:8px;color:var(--x-text-main);font-size:12px;padding:6px 10px;outline:none;}
        .x-filter-bar input:focus{border-color:var(--x-blue);}
        .x-chips{display:flex;flex-wrap:nowrap;gap:4px;align-items:center;}
        .x-chip{display:inline-flex;align-items:center;gap:5px;font-size:10px;font-weight:600;padding:4px 8px;border-radius:6px;border:1px solid transparent;background:#0f1214;color:var(--x-text-muted);cursor:pointer;user-select:none;white-space:nowrap;transition:background .15s,color .15s,border-color .15s;}
        .x-chip:hover{color:var(--x-text-main);background:#16181c;}
        .x-chip.active{background:rgba(29,155,240,.14);border-color:rgba(29,155,240,.55);color:#e7f3fd;}
        .x-chip i{width:6px;height:6px;border-radius:50%;display:inline-block;flex-shrink:0;}
        .x-chip i.l{background:var(--x-red);} .x-chip i.d{background:var(--x-orange);} .x-chip i.w{background:var(--x-green);}
        .x-chip-sep{width:1px;height:14px;background:var(--x-border);margin:0 2px;flex-shrink:0;}
        .x-chip-cap{font-size:9px;color:var(--x-text-muted);text-transform:uppercase;letter-spacing:.04em;margin:0 2px 0 0;flex-shrink:0;}
        .x-item.x-sit-losing{box-shadow:inset 3px 0 0 var(--x-red);}
        .x-item.x-sit-draw{box-shadow:inset 3px 0 0 var(--x-orange);}
        .x-item.x-sit-winning{box-shadow:inset 3px 0 0 var(--x-green);}
        .x-sit{font-size:9px;font-weight:700;padding:0 5px;border-radius:6px;white-space:nowrap;}
        .x-sit-losing .x-sit,.x-sit.losing{background:rgba(244,33,46,.2);color:#fca5a5;}
        .x-sit.draw{background:rgba(245,158,11,.2);color:#fcd34d;}
        .x-sit.winning{background:rgba(0,186,124,.2);color:#6ee7b7;}
        .x-tl{position:relative;width:96px;height:5px;border-radius:3px;background:#1f2933;margin-top:4px;overflow:visible;}
        .x-tl .now{position:absolute;left:0;top:0;bottom:0;border-radius:3px;background:rgba(29,155,240,.55);}
        .x-tl .ht{position:absolute;left:47.4%;top:-1px;bottom:-1px;width:1px;background:#4b5563;}
        .x-tl .rc{position:absolute;top:-2px;width:5px;height:9px;margin-left:-2px;border-radius:1px;background:var(--x-red);box-shadow:0 0 4px rgba(244,33,46,.9);}
        .x-stats{font-size:9px;color:var(--x-text-muted);margin-top:3px;white-space:nowrap;}
        .god-mode-highlight[data-god-sit="draw"]{border-left-color:#f59e0b!important;}
        .god-mode-highlight[data-god-sit="winning"]{border-left-color:#00ba7c!important;}
        .x-fab-gif{width:100%;height:100%;object-fit:cover;pointer-events:none;}
        .x-panel{position:fixed;z-index:9998;width:390px;background:var(--x-card);border:1px solid var(--x-border);border-radius:16px;padding:16px;color:var(--x-text-main);font-family:-apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,Helvetica,Arial,sans-serif;backdrop-filter:blur(15px);box-shadow:0 15px 50px rgba(0,0,0,.8);display:flex;flex-direction:column;gap:10px;top:150px;right:50px;max-height:620px;overflow-y:auto;}
        .x-hidden{display:none!important;}
        .x-drag-handle{position:absolute;top:0;left:0;right:0;height:30px;cursor:grab;z-index:10;background:transparent;}
        .x-header-row{display:flex;align-items:center;margin-bottom:8px;margin-top:0;padding:0;justify-content:space-between;}
        .x-header-left{display:flex;align-items:center;}
        .x-profile-pic-cont{width:44px;height:44px;border-radius:50%;overflow:hidden;border:1px solid var(--x-border);flex-shrink:0;}
        .x-profile-gif{width:100%;height:100%;object-fit:cover;}
        .x-user-info{margin-left:10px;display:flex;flex-direction:column;justify-content:center;}
        .x-name-line{display:flex;align-items:center;gap:4px;}
        .x-name{font-weight:800;font-size:15px;color:var(--x-text-main);}
        .x-verified{width:18px;height:18px;fill:var(--x-blue);}
        .x-status-dot{width:8px;height:8px;border-radius:50%;margin-left:8px;}
        .x-dot-on{background-color:var(--x-red);box-shadow:0 0 6px var(--x-red);animation:pulse-dot 1s infinite;}
        .x-dot-off{background-color:var(--x-green);}
        @keyframes pulse-dot{0%{opacity:1;}50%{opacity:.4;}100%{opacity:1;}}
        .x-reset-btn{font-size:14px;cursor:pointer;opacity:.5;transition:opacity .2s;padding:5px;}
        .x-reset-btn:hover{opacity:1;color:var(--x-red);}
        @keyframes spin-fast { 100% { transform: rotate(360deg); } }
        .x-spin { animation: spin-fast 1s linear infinite; opacity: 1 !important; color: var(--x-blue) !important; display: inline-block !important; transform-origin: center center; }
        .x-tabs{display:flex;gap:0;margin-top:8px;margin-bottom:10px;border-bottom:1px solid var(--x-border);padding:0;}
        .x-tab{flex:1;padding:8px 0;text-align:center;cursor:pointer;font-size:10px;font-weight:600;color:var(--x-text-muted);border-bottom:2px solid transparent;transition:all .2s;white-space:nowrap;}
        .x-tab.active{color:var(--x-red);border-bottom-color:var(--x-red);}
        .x-tab#tab_top.active{color:var(--x-orange);border-bottom-color:var(--x-orange);}
        .x-tab#tab_zero.active{color: #e2e8f0; border-bottom-color: #e2e8f0;}
        .x-tab#tab_star.active{color: #fbbf24; border-bottom-color: #fbbf24;}
        .x-tab#tab_stats.active{color: var(--x-blue); border-bottom-color: var(--x-blue);}
        .x-list-box{max-height:300px;overflow-y:auto;border-radius:8px;border:1px solid var(--x-border);background:#000;min-height:50px; position:relative;}
        #x_settings_box{max-height:400px;}
        .x-item{display:flex;align-items:center;padding:10px;border-bottom:1px solid #16181c;font-size:13px;user-select:none;cursor:pointer;transition:all .2s;gap:6px;}
        .x-item:hover{background:#16181c; transform:translateX(4px);}
        .x-item-time{color:var(--x-red);font-weight:700;text-align:center;font-size:11px;min-width:35px;flex-shrink:0;}
        .x-action-col { display:flex; flex-direction:column; gap:2px; align-items:center; flex-shrink:0; }
        .x-sniper-btn { font-size: 14px; opacity: 0.5; transition: all 0.2s; cursor: pointer; padding: 1px; }
        .x-sniper-btn:hover { opacity: 1; transform: scale(1.2); }
        .x-star-btn, .x-mute-btn { font-size: 14px; opacity: 0.3; transition: all 0.2s; cursor: pointer; padding: 1px; filter: grayscale(1); }
        .x-star-btn:hover, .x-mute-btn:hover { opacity: 0.8; transform: scale(1.2); }
        .x-star-btn.active { opacity: 1; filter: grayscale(0); text-shadow: 0 0 8px rgba(251,191,36,0.8); }
        .x-mute-btn.active { opacity: 1; filter: grayscale(0); }
        .x-crunch-time span:first-child { color: #ffeb3b; text-shadow: 0 0 5px rgba(255,152,0,0.8); animation: crunch-pulse 0.8s infinite alternate; }
        @keyframes crunch-pulse { from { transform: scale(1); } to { transform: scale(1.15); } }
        .x-bomb { font-size: 11px; animation: bomb-shake 0.5s infinite; display:inline-block; }
        @keyframes bomb-shake { 0% { transform: rotate(0deg); } 25% { transform: rotate(-15deg); } 50% { transform: rotate(0deg); } 75% { transform: rotate(15deg); } 100% { transform: rotate(0deg); } }
        .x-score-despair { background: linear-gradient(135deg, #ef4444, #991b1b) !important; box-shadow: 0 0 12px rgba(239,68,68,0.8) !important; animation: despair-pulse 0.8s infinite alternate; cursor: help; }
        @keyframes despair-pulse { from { transform: scale(1); } to { transform: scale(1.1); box-shadow: 0 0 20px rgba(239,68,68,1); } }
        .x-sos { font-size: 11px; animation: sos-flash 1s infinite alternate; display:inline-block; cursor: help; }
        @keyframes sos-flash { 0% { opacity: 0.5; transform: scale(0.9); } 100% { opacity: 1; transform: scale(1.1); } }
        @keyframes bloodbath-glow { 0% { box-shadow: inset 0 0 10px rgba(244,33,46,0.2); border-color: #16181c; } 100% { box-shadow: inset 0 0 40px rgba(244,33,46,0.8); border-color: #f4212e; } }
        .x-bloodbath { animation: bloodbath-glow 0.5s infinite alternate !important; background: linear-gradient(90deg, rgba(244,33,46,0.25) 0%, rgba(0,0,0,0) 50%, rgba(244,33,46,0.25) 100%) !important; }
        .x-bloodbath-badge { background: linear-gradient(135deg, #f4212e, #800000) !important; box-shadow: 0 2px 10px rgba(244,33,46,0.8) !important; animation: crunch-pulse 0.5s infinite alternate; cursor: help; }
        .x-bloodbath-badge::before { content: '🚨 '; }
        .x-bloodbath-badge::after { content: ' 🚨'; }
        .x-score-badge{background:linear-gradient(135deg,var(--x-blue),#0f7bd9);color:#fff;padding:4px 10px;border-radius:6px;font-weight:700;font-size:13px;min-width:40px;text-align:center;box-shadow:0 2px 8px rgba(29,155,240,0.3);}
        .x-score-zero { background: linear-gradient(135deg, #e2e8f0, #94a3b8) !important; color: #0f172a !important; box-shadow: 0 0 10px rgba(255,255,255,0.4) !important; text-shadow: none !important; cursor: help; }
        .x-score-mortal { background: linear-gradient(135deg, #0284c7, #2563eb) !important; box-shadow: 0 0 12px rgba(37,99,235,0.8) !important; animation: mortal-pulse 1s infinite alternate; cursor: help; }
        @keyframes mortal-pulse { from { transform: scale(1); } to { transform: scale(1.1); } }
        .x-item-text{flex:1;font-weight:500;color:#fff;display:flex;align-items:center;justify-content:center;gap:6px;}
        .x-team-col{display:flex;align-items:center;gap:4px;flex:0 0 auto;}
        .x-team-col.home{justify-content:flex-end;}
        .x-team-col.away{justify-content:flex-start;}
        .x-team-name{font-size:12px;font-weight:600;text-align:center;}
        .x-meta{font-size:9px;color:#fca5a5;margin-top:3px;white-space:nowrap;}
        .x-comp{font-size:9px;color:var(--x-text-muted);margin-top:1px;white-space:nowrap;max-width:110px;overflow:hidden;text-overflow:ellipsis;}
        .x-red-card-svg{width:18px;height:27px;flex-shrink:0;filter:drop-shadow(0 0 2px rgba(0,0,0,.5));display:block;}
        .x-log-time{color:var(--x-text-muted);font-size:10px;display:block;margin-top:2px;}
        .x-clear-btn{text-align:center;padding:8px;font-size:11px;color:var(--x-text-muted);cursor:pointer;border-top:1px solid var(--x-border);}
        .x-clear-btn:hover{color:var(--x-red);}
        #x_sonar_pill{position:fixed;top:14px;left:50%;transform:translateX(-50%) translateY(-6px);z-index:9997;display:flex;align-items:center;gap:8px;background:rgba(0,0,0,.9);color:var(--x-text-main);border:1px solid var(--x-border);border-radius:18px;padding:6px 14px 6px 10px;font:600 12px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;pointer-events:none;box-shadow:0 6px 24px rgba(0,0,0,.6);opacity:0;transition:opacity .18s,transform .18s;max-width:80vw;}
        #x_sonar_pill.show{opacity:1;transform:translateX(-50%) translateY(0);}
        #x_sonar_pill i{width:12px;height:12px;border:2px solid rgba(255,255,255,.22);border-top-color:var(--x-blue);border-radius:50%;animation:x-pill-spin .7s linear infinite;flex-shrink:0;}
        #x_sonar_pill span{white-space:nowrap;overflow:hidden;text-overflow:ellipsis;}
        @keyframes x-pill-spin{to{transform:rotate(360deg);}}
        .x-settings-group{padding:10px 0;border-bottom:1px solid var(--x-border);}
        .x-settings-group:last-child{border-bottom:none;}
        .x-settings-label{font-size:11px;font-weight:600;color:var(--x-text-muted);margin-bottom:6px;text-transform:uppercase;}
        .x-settings-control{display:flex;align-items:center;gap:8px;}
        .x-section-title{font-size:11px;font-weight:800;color:var(--x-orange);margin:14px 0 2px;text-transform:uppercase;}
        .x-toggle{width:36px;height:20px;background:var(--x-border);border-radius:10px;cursor:pointer;position:relative;transition:background .2s;flex-shrink:0;}
        .x-toggle.on{background:var(--x-red);}
        .x-toggle::after{content:'';position:absolute;top:2px;left:2px;width:16px;height:16px;background:white;border-radius:50%;transition:left .2s;}
        .x-toggle.on::after{left:18px;}
        .x-input{width:100%;background:#16181c;border:1px solid var(--x-border);color:#eff3f4;border-radius:6px;padding:6px 8px;font-size:12px;box-sizing:border-box;}
        .x-mini-btn{background:#16181c;color:var(--x-text-main);border:1px solid var(--x-border);border-radius:6px;padding:7px 10px;font-weight:700;cursor:pointer;font-size:11px;margin:6px 6px 0 0;}
        .x-mini-btn:hover{border-color:var(--x-blue);color:var(--x-blue);}
        .x-test-btn { background: var(--x-blue); color: white; border: none; border-radius: 6px; padding: 10px 12px; font-weight: 800; cursor: pointer; font-size: 11px; margin-top: 15px; width: 100%; text-transform: uppercase; transition: background 0.2s;}
        .x-test-btn:hover { background: #0f7bd9; }
        .x-stat-row{display:flex;align-items:center;gap:8px;padding:8px 10px;border-bottom:1px solid #16181c;font-size:12px;}
        .x-stat-row .lbl{flex:1;font-weight:600;}
        .x-stat-row .num{width:62px;text-align:right;color:var(--x-text-muted);}
        .x-stat-head{color:var(--x-text-muted);font-size:10px;text-transform:uppercase;font-weight:700;}
        .x-stat-row .num{width:54px;}
        .x-stat-total{font-weight:800;border-top:1px solid var(--x-border);}
        #x_fab_btn{transition:transform .2s,opacity .45s;}
        #x_fab_btn.x-idle{opacity:.4;transform:scale(.8);}
        #x_fab_btn.x-idle:hover{opacity:1;transform:scale(1.05);}
        .x-fb-row{display:flex;gap:6px;align-items:center;}
        .x-fb-row input{flex:1;min-width:0;width:auto!important;}
        .x-sel{background:#0b0d0f;border:1px solid var(--x-border);border-radius:8px;color:var(--x-text-main);font-size:11px;padding:6px 4px;outline:none;cursor:pointer;max-width:116px;flex-shrink:0;}
        .x-sel:focus{border-color:var(--x-blue);}
        .x-dens{width:29px;height:29px;display:inline-flex;align-items:center;justify-content:center;border:1px solid var(--x-border);border-radius:8px;cursor:pointer;color:var(--x-text-muted);font-size:14px;user-select:none;flex-shrink:0;}
        .x-dens:hover{color:var(--x-text-main);}
        .x-dens.on{color:#e7f3fd;border-color:rgba(29,155,240,.55);background:rgba(29,155,240,.16);}
        .x-summary{font-size:10px;color:var(--x-text-muted);font-weight:600;min-height:12px;padding:0 2px;}
        .x-w10{color:#fbbf24;font-weight:700;}
        .x-tl .gl{position:absolute;top:-1px;width:7px;height:7px;margin-left:-3px;border-radius:50%;background:#fff;border:2px solid var(--x-blue);box-sizing:border-box;}
        @keyframes x-flash-goal{0%{background-color:rgba(29,155,240,.5);}100%{background-color:transparent;}}
        @keyframes x-flash-red{0%{background-color:rgba(244,33,46,.55);}100%{background-color:transparent;}}
        @keyframes x-flash-sit{0%{background-color:rgba(245,158,11,.45);}100%{background-color:transparent;}}
        .x-item.x-flash-goal{animation:x-flash-goal 2.4s ease-out;}
        .x-item.x-flash-red{animation:x-flash-red 2.4s ease-out;}
        .x-item.x-flash-sit{animation:x-flash-sit 2.4s ease-out;}
        .x-dense .x-item{padding:5px 8px;}
        .x-dense .x-comp,.x-dense .x-stats,.x-dense .x-tl{display:none;}
        .x-dense .x-meta{margin-top:1px;}
        @media (prefers-reduced-motion:reduce){.x-item.x-flash-goal,.x-item.x-flash-red,.x-item.x-flash-sit{animation:none!important;}#x_fab_btn{transition:none;}}
        .god-mode-highlight[data-god-badge]::after{content:attr(data-god-badge);position:absolute;right:6px;top:3px;z-index:8;pointer-events:none;font:800 10px/1 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:3px 7px;border-radius:9px;background:#f4212e;color:#fff;box-shadow:0 2px 8px rgba(0,0,0,.35);letter-spacing:.02em;white-space:nowrap;}
        .god-mode-highlight[data-god-sit="draw"][data-god-badge]::after{background:#f59e0b;color:#111;}
        .god-mode-highlight[data-god-sit="winning"][data-god-badge]::after{background:#00ba7c;color:#04130c;}
        .x-panel{max-width:calc(100vw - 16px);}
        .x-real{color:var(--x-green);font-weight:800;margin-left:1px;}
        .x-pos{color:#6ee7b7;} .x-neg{color:#fca5a5;}
        .x-chart-card{padding:2px 10px 8px;}
        svg.x-chart{width:100%;height:auto;display:block;}
        .cg-g{fill:var(--x-green);} .cg-r{fill:var(--x-red);} .cg-o{fill:var(--x-orange);} .cg-b{fill:var(--x-blue);}
        .cg-sg,.cg-so,.cg-sr{fill:none;stroke-width:14;}
        .cg-sg{stroke:var(--x-green);} .cg-so{stroke:var(--x-orange);} .cg-sr{stroke:var(--x-red);}
        .cg-t{fill:var(--x-text-muted);font:600 9px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;}
        .cg-v{fill:var(--x-text-main);font:700 9px -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;}
        .cg-axis{stroke:var(--x-border);stroke-width:1;}
        .cg-ref{stroke:var(--x-border);stroke-width:1;stroke-dasharray:3 3;}
        .cg-line{fill:none;stroke:var(--x-blue);stroke-width:2;stroke-linejoin:round;stroke-linecap:round;}
        .x-heat-grid{display:grid;grid-template-columns:1fr 1fr;gap:5px;padding:2px 10px 8px;}
        .x-heat{border-radius:8px;padding:6px 8px;color:#fff;line-height:1.3;min-width:0;}
        .x-heat b{display:block;font-size:14px;}
        .x-heat span{display:block;font-size:10px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;opacity:.92;}
        .x-sec-head{display:flex;align-items:center;justify-content:space-between;cursor:pointer;user-select:none;}
        .x-sec-head b{font-size:10px;transition:transform .2s;}
        .x-sec.collapsed .x-sec-head b{transform:rotate(-90deg);}
        .x-sec.collapsed:not(.force-open) .x-sec-body{display:none;}
        .x-prev{display:flex;flex-direction:column;gap:4px;border:1px solid var(--x-border);border-radius:8px;padding:7px 8px;font-size:11px;margin-bottom:4px;}
        .x-prev-row{display:flex;align-items:center;gap:8px;}
        .x-prev-tag{font-size:9px;font-weight:800;padding:2px 6px;border-radius:6px;min-width:62px;text-align:center;flex-shrink:0;}
        .x-prev-tag.ok{background:rgba(0,186,124,.2);color:#6ee7b7;}
        .x-prev-tag.no{background:rgba(113,118,123,.25);color:var(--x-text-muted);}
        .x-panel{box-sizing:border-box;width:424px;max-height:calc(100vh - 16px);}
        .x-list-box{max-height:var(--x-listh,300px);}
        #x_settings_box{max-height:calc(var(--x-listh,300px) + 100px);}
        .x-resize{position:absolute;left:2px;bottom:2px;width:18px;height:18px;cursor:nesw-resize;z-index:12;opacity:.5;touch-action:none;}
        .x-resize::before{content:'';position:absolute;left:4px;bottom:4px;width:8px;height:8px;border-left:2px solid var(--x-text-muted);border-bottom:2px solid var(--x-text-muted);}
        .x-resize:hover{opacity:1;}
        .x-panel.x-light{--x-card:rgba(255,255,255,.98);--x-border:#d3dbe0;--x-text-main:#0f1419;--x-text-muted:#5b6670;--x-blue:#0a74c4;--x-red:#d61f2c;--x-green:#008f63;--x-orange:#c26d00;box-shadow:0 15px 50px rgba(15,20,25,.28);}
        .x-light .x-list-box{background:#f6f8f9;}
        .x-light .x-item{border-bottom-color:#e3e9ed;}
        .x-light .x-item:hover{background:#eaf0f3;}
        .x-light .x-item-text{color:#0f1419;}
        .x-light .x-filter-bar input,.x-light .x-sel,.x-light .x-input,.x-light .x-mini-btn{background:#fff;color:#0f1419;}
        .x-light .x-chip{background:#edf1f4;} .x-light .x-chip:hover{background:#e1e8ec;color:#0f1419;}
        .x-light .x-chip.active{background:rgba(10,116,196,.12);border-color:rgba(10,116,196,.55);color:#0a4f8a;}
        .x-light .x-dens.on{color:#0a4f8a;background:rgba(10,116,196,.12);border-color:rgba(10,116,196,.55);}
        .x-light .x-tl{background:#d5dde3;} .x-light .x-tl .ht{background:#8a97a1;}
        .x-light .x-meta{color:#b91c1c;} .x-light .x-w10{color:#b45309;}
        .x-light .x-sit-losing .x-sit,.x-light .x-sit.losing{background:rgba(214,31,44,.14);color:#b91c1c;}
        .x-light .x-sit.draw{background:rgba(194,109,0,.16);color:#92400e;}
        .x-light .x-sit.winning{background:rgba(0,143,99,.16);color:#047857;}
        .x-light .x-feedtag.on{color:#047857;} .x-light .x-feedtag.off{color:#92400e;}
        .x-light .x-stat-row{border-bottom-color:#e3e9ed;}
        .x-light .x-pos{color:#047857;} .x-light .x-neg{color:#b91c1c;}
        .x-light .x-crunch-time span:first-child{color:#b45309;text-shadow:none;}
        .x-light .x-tab#tab_zero.active{color:#334155;border-bottom-color:#334155;}
        .x-light .x-tab#tab_star.active{color:#b45309;border-bottom-color:#b45309;}
        .x-light .x-toggle{background:#cdd5db;} .x-light .x-toggle.on{background:var(--x-red);}
        .x-light .x-prev-tag.ok{background:rgba(0,143,99,.16);color:#047857;}
        .x-light .x-clear-btn:hover{color:var(--x-red);}
        .x-light ::-webkit-scrollbar-thumb{background:#c5ced5;}
        ::-webkit-scrollbar{width:6px;}
        ::-webkit-scrollbar-thumb{background:#333;border-radius:3px;}
    `);

    //======================================================================
    // 13. UI: CRIAÇÃO DO PAINEL
    //======================================================================

    function createUI() {
        if ($('x_fab_btn')) return;

        const fab = document.createElement('div');
        fab.id = 'x_fab_btn';
        fab.setAttribute('data-xui', '1');
        fab.className = 'fab-bad';
        fab.innerHTML = `<img src="${GIF_URL}" class="x-fab-gif" alt="GOD">`;
        document.body.appendChild(fab);

        const verifiedIcon = `<svg viewBox="0 0 22 22" class="x-verified"><path d="M20.396 11c-.018-.646-.215-1.275-.57-1.816-.354-.54-.852-.972-1.438-1.246.223-.607.27-1.264.14-1.897-.131-.634-.437-1.218-.882-1.687-.47-.445-1.053-.75-1.687-.882-.633-.13-1.29-.083-1.897.14-.273-.587-.704-1.086-1.245-1.44S11.647 1.62 11 1.604c-.646.018-1.273.213-1.813.568s-.969.854-1.24 1.44c-.608-.223-1.267-.272-1.902-.14-.635.13-1.22.436-1.69.882-.445.47-.749 1.055-.878 1.688-.13.633-.08 1.29.144 1.896-.587.274-1.087.705-1.443 1.245-.356.54-.555 1.17-.574 1.817.02.647.218 1.276.574 1.817.356.54.856.972 1.443 1.245-.224.606-.274 1.263-.144 1.896.13.634.433 1.218.878 1.688.47.443 1.054.748 1.69.878.635.132 1.294.083 1.902-.14.27.586.7 1.084 1.24 1.438.54.354 1.167.55 1.813.568.647-.018 1.276-.213 1.817-.568.541-.354.972-.852 1.245-1.438.607.223 1.264.27 1.897.14.634-.13 1.218-.433 1.687-.878.445-.47.75-1.054.882-1.688.13-.633.083-1.29-.14-1.896.586-.273 1.084-.704 1.438-1.244.354-.54.55-1.17.57-1.816zM9.662 14.85l-3.429-3.428 1.293-1.302 2.136 2.135 5.914-5.916 1.293 1.302-7.207 7.21z"></path></svg>`;

        const panel = document.createElement('div');
        panel.id = 'x_panel';
        panel.setAttribute('data-xui', '1');
        panel.className = 'x-panel x-hidden';
        panel.innerHTML = `
            <div class="x-drag-handle"></div>
            <div class="x-header-row">
                <div class="x-header-left">
                    <div class="x-profile-pic-cont"><img src="${GIF_URL}" class="x-profile-gif" alt="Profile"></div>
                    <div class="x-user-info">
                        <div class="x-name-line"><span class="x-name">GODiNjURED</span>${verifiedIcon}<div class="x-status-dot x-dot-off" id="ui_status_dot"></div></div>
                        <span class="x-handle" id="x_handle">@AiScore • v21.1</span>
                    </div>
                </div>
                <div style="display:flex; align-items:center; gap:8px;">
                    <div class="x-reset-btn" id="x_manual_scan" title="Forçar Scan Manual">🔄</div>
                    <div class="x-reset-btn" id="x_hard_reset" title="Limpar Cache">🗑️</div>
                </div>
            </div>
            <div class="x-tabs">
                <div class="x-tab active" id="tab_live">LIVE (<span id="count_reds">0</span>)</div>
                <div class="x-tab" id="tab_top">🔥 (<span id="count_top">0</span>)</div>
                <div class="x-tab" id="tab_zero">🎯 (<span id="count_zero">0</span>)</div>
                <div class="x-tab" id="tab_star">⭐ (<span id="count_star">0</span>)</div>
                <div class="x-tab" id="tab_log">LOG</div>
                <div class="x-tab" id="tab_stats">📊</div>
                <div class="x-tab" id="tab_settings">⚙️</div>
            </div>
            <div class="x-filter-bar" id="x_filter_bar">
                <div class="x-fb-row">
                    <input type="search" id="x_f_q" placeholder="🔎 Equipa ou competição..." autocomplete="off">
                    <select id="x_sort" class="x-sel" title="Ordenar a lista">
                        ${Object.keys(SORT_LABELS).map(k => `<option value="${k}"${settings.ui.sort === k ? ' selected' : ''}>${SORT_LABELS[k]}</option>`).join('')}
                    </select>
                    <span class="x-dens${settings.ui.dense ? ' on' : ''}" id="x_dens" title="Lista compacta">☰</span>
                </div>
                <div class="x-chips" id="x_chips">
                    <span class="x-chip active" data-sit="all">Todos</span>
                    <span class="x-chip-sep"></span>
                    <span class="x-chip-cap">c/10</span>
                    <span class="x-chip" data-sit="losing" title="Equipa com 10 a perder"><i class="l"></i>Perde</span>
                    <span class="x-chip" data-sit="draw" title="Equipa com 10 a empatar"><i class="d"></i>Empata</span>
                    <span class="x-chip" data-sit="winning" title="Equipa com 10 a ganhar"><i class="w"></i>Ganha</span>
                    <span class="x-chip-sep"></span>
                    <span class="x-chip" data-sit="late" title="Jogos já na fase final (Crunch Time)">Final</span>
                    <span class="x-chip" data-sit="multi" title="Jogos com 2 ou mais vermelhos">2+</span>
                </div>
                <div class="x-summary" id="x_summary"></div>
            </div>
            <div style="position:relative;">
                <div class="x-list-box" id="x_live_box"><div style="padding:20px;text-align:center;color:var(--x-text-muted);font-size:12px;">À procura de expulsões...</div></div>
                <div class="x-list-box x-hidden" id="x_top_box"></div>
                <div class="x-list-box x-hidden" id="x_zero_box"></div>
                <div class="x-list-box x-hidden" id="x_star_box"></div>
                <div class="x-list-box x-hidden" id="x_log_box"></div>
                <div class="x-list-box x-hidden" id="x_stats_box"></div>
                <div class="x-list-box x-hidden" id="x_settings_box"></div>
            </div>
            <div class="x-resize" id="x_resize" title="Arrastar para redimensionar"></div>`;
        document.body.appendChild(panel);

        const pill = document.createElement('div');
        pill.id = 'x_sonar_pill';
        pill.setAttribute('data-xui', '1');
        pill.innerHTML = '<i></i><span></span>';
        document.body.appendChild(pill);

        $('x_hard_reset').onclick = () => {
            if (confirm('Limpar cache dos jogos ativos e reiniciar script? (O histórico é mantido.)')) {
                activeGamesDB = {};
                saveDB();
                location.reload();
            }
        };

        $('x_manual_scan').onclick = async () => {
            if (isScanning) { showToast('⚠️ Aguarde, Scan em progresso!', 'warning'); return; }
            const btn = $('x_manual_scan');
            btn.classList.add('x-spin');
            await fullPageScan(true);
            btn.classList.remove('x-spin');
            showToast('✅ Scan Manual concluído!', 'success');
        };

        ['live', 'top', 'zero', 'star', 'log', 'stats', 'settings'].forEach(tab => {
            const el = $(`tab_${tab}`);
            if (!el) return;
            el.onclick = () => {
                if (settings.ui.tab !== tab) { settings.ui.tab = tab; saveSettings(); }
                document.querySelectorAll('.x-tab').forEach(t => t.classList.remove('active'));
                document.querySelectorAll('#x_panel [id$="_box"]').forEach(b => b.classList.add('x-hidden'));
                el.classList.add('active');
                $(`x_${tab}_box`).classList.remove('x-hidden');
                $('x_filter_bar').classList.toggle('x-hidden', !['live', 'top', 'zero', 'star'].includes(tab));
                if (tab === 'log') renderLog();
                if (tab === 'stats') renderStats();
                if (tab === 'settings') renderSettings();
                if (['live', 'top', 'zero', 'star'].includes(tab)) renderLiveList();
            };
        });

        let fqTimer = null;
        $('x_f_q').addEventListener('input', () => {
            clearTimeout(fqTimer);
            fqTimer = setTimeout(() => { uiFilter.q = $('x_f_q').value.trim().toLowerCase(); renderLiveList(); }, 150);
        });
        $('x_chips').addEventListener('click', ev => {
            const c = ev.target.closest('.x-chip');
            if (!c) return;
            uiFilter.sit = c.getAttribute('data-sit');
            document.querySelectorAll('#x_chips .x-chip').forEach(x => x.classList.toggle('active', x === c));
            renderLiveList();
        });
        $('x_sort').onchange = () => { settings.ui.sort = $('x_sort').value; saveSettings(); renderLiveList(); };
        $('x_dens').onclick = () => {
            settings.ui.dense = !settings.ui.dense;
            saveSettings();
            $('x_dens').classList.toggle('on', settings.ui.dense);
            panel.classList.toggle('x-dense', settings.ui.dense);
        };
        panel.classList.toggle('x-dense', !!settings.ui.dense);
        updateFeedIndicator();

        setupDragAndToggle(fab, panel);
        restorePanelLayout(panel);
        applyTheme();
        try {
            const mq = window.matchMedia('(prefers-color-scheme: light)');
            if (mq.addEventListener) mq.addEventListener('change', applyTheme);
        } catch (e) { /* ignora */ }
        window.addEventListener('resize', () => clampPanel(panel));
        const t0 = settings.ui.tab;
        if (t0 && t0 !== 'live' && $('tab_' + t0)) $('tab_' + t0).onclick();
    }

    //======================================================================
    // 14. UI: RENDERS (LOG, STATS, SETTINGS, LISTAS)
    //======================================================================

    function renderLog() {
        const logBox = $('x_log_box');
        if (!logBox) return;
        const savedScroll = logBox.scrollTop;

        if (eventLog.length === 0) {
            logBox.innerHTML = '<div style="padding:20px;text-align:center;color:var(--x-text-muted);font-size:12px;">Registo vazio.</div>';
            return;
        }

        const html = eventLog.map(e => {
            const homeSvg = e.homeCards ? getRedCardSVG(e.homeCards) : '';
            const awaySvg = e.awayCards ? getRedCardSVG(e.awayCards) : '';
            const parts = (e.name || '').split(' vs ');
            return `<div class="x-item" style="cursor:default">
                <div class="x-item-time" style="color:var(--x-text-muted)"><span>${escapeHTML(e.matchTime)}</span></div>
                <div class="x-item-text">
                    <div class="x-team-col home">${homeSvg}</div>
                    <div style="font-size:11px;flex:1;text-align:center;">${smartTruncate(escapeHTML(parts[0] || ''), 13)} vs ${smartTruncate(escapeHTML(parts[1] || ''), 13)}</div>
                    <div class="x-team-col away">${awaySvg}</div>
                </div>
                <span class="x-log-time">${escapeHTML(e.logTime)}</span>
            </div>`;
        }).join('');

        logBox.innerHTML = html + '<div class="x-clear-btn" id="x_clear_log_btn">Limpar Histórico do Log</div>';
        logBox.scrollTop = savedScroll;
        $('x_clear_log_btn').onclick = () => { eventLog = []; GM_setValue(LOG_KEY, []); renderLog(); };
    }

    function minuteStatsHTML() {
        const rows = buildMinuteStats();
        if (!rows.length) return '';
        const f = (a, k) => (a[k] / a.n).toFixed(2);
        const body = rows.map(r => {
            const a = r.a, low = a.n < 5;
            const nl = a.res ? Math.round(a.nl * 100 / a.res) + '%' : '-';
            return `<div class="x-stat-row${r.total ? ' x-stat-total' : ''}"${low && !r.total ? ' style="opacity:.6" title="Amostra pequena (menos de 5 jogos)"' : ''}>
                <div class="lbl">${escapeHTML(r.label)}${(r.total || r.label === 'Sem minuto') ? '' : "'"}</div>
                <div class="num">${a.n}</div>
                <div class="num x-pos">${f(a, 'sc')}</div>
                <div class="num x-neg">${f(a, 'co')}</div>
                <div class="num">${nl}</div>
            </div>`;
        }).join('');
        return `<div class="x-section-title" style="padding:0 10px;">Equipa com 10 · por minuto do vermelho</div>
            <div class="x-stat-row x-stat-head"><div class="lbl">Faixa</div><div class="num">Jogos</div><div class="num" title="Golos marcados por jogo pela equipa com 10">Marca</div><div class="num" title="Golos sofridos por jogo pela equipa com 10">Sofre</div><div class="num" title="% em que a equipa com 10 não perdeu">Não perde</div></div>
            ${body}
            <div style="padding:6px 10px 0;font-size:10px;color:var(--x-text-muted);">Marca/Sofre = golos por jogo da equipa com 10 <b>depois</b> do vermelho. Linhas a cinzento: menos de 5 jogos.</div>`;
    }

    // ---------- gráficos (SVG sem bibliotecas) ----------
    const isRes = (h) => h.result === 'W' || h.result === 'D' || h.result === 'L';

    function chartBars() {
        const rows = buildMinuteStats().filter(r => !r.total && r.label !== 'Sem minuto');
        if (!rows.length) return '';
        const x0 = 14, x1 = 346, yb = 118, ph = 84;
        const vals = rows.map(r => ({ l: r.label, n: r.a.n, sc: r.a.sc / r.a.n, co: r.a.co / r.a.n }));
        const mx = Math.max.apply(null, [0.5].concat(vals.map(v => Math.max(v.sc, v.co)))) * 1.12;
        const gw = (x1 - x0) / vals.length, bw = Math.min(18, gw / 2 - 3);
        let s = `<rect class="cg-g" x="14" y="4" width="8" height="8" rx="2"/><text class="cg-t" x="26" y="11.5">Marca</text>` +
                `<rect class="cg-r" x="70" y="4" width="8" height="8" rx="2"/><text class="cg-t" x="82" y="11.5">Sofre</text>` +
                `<line class="cg-axis" x1="${x0}" y1="${yb}" x2="${x1}" y2="${yb}"/>`;
        vals.forEach((v, i) => {
            const cx = x0 + gw * i + gw / 2;
            const hs = Math.max(1, v.sc / mx * ph), hc = Math.max(1, v.co / mx * ph);
            const tip = `${v.l}: marca ${v.sc.toFixed(2)} · sofre ${v.co.toFixed(2)} (${v.n} jogos)`;
            s += `<g${v.n < 5 ? ' opacity=".55"' : ''}><title>${escapeHTML(tip)}</title>` +
                `<rect class="cg-g" x="${(cx - bw - 1).toFixed(1)}" y="${(yb - hs).toFixed(1)}" width="${bw.toFixed(1)}" height="${hs.toFixed(1)}" rx="2"/>` +
                `<rect class="cg-r" x="${(cx + 1).toFixed(1)}" y="${(yb - hc).toFixed(1)}" width="${bw.toFixed(1)}" height="${hc.toFixed(1)}" rx="2"/>` +
                `<text class="cg-v" x="${(cx - bw / 2 - 1).toFixed(1)}" y="${(yb - hs - 3).toFixed(1)}" text-anchor="middle">${v.sc.toFixed(1)}</text>` +
                `<text class="cg-v" x="${(cx + bw / 2 + 1).toFixed(1)}" y="${(yb - hc - 3).toFixed(1)}" text-anchor="middle">${v.co.toFixed(1)}</text>` +
                `<text class="cg-t" x="${cx.toFixed(1)}" y="${yb + 13}" text-anchor="middle">${escapeHTML(v.l)}</text>` +
                `<text class="cg-t" x="${cx.toFixed(1)}" y="${yb + 24}" text-anchor="middle" opacity=".8">${v.n}j</text></g>`;
        });
        return `<div class="x-section-title" style="padding:0 10px;">Golos por jogo da equipa com 10 · por faixa</div>` +
            `<div class="x-chart-card"><svg class="x-chart" viewBox="0 0 360 146" role="img" aria-label="Golos marcados e sofridos por faixa de minuto">${s}</svg></div>`;
    }

    function chartDonut() {
        const res = history.filter(isRes);
        if (!res.length) return '';
        const c = { W: 0, D: 0, L: 0 };
        res.forEach(h => { c[h.result]++; });
        const tot = res.length, r = 32, C = 2 * Math.PI * r;
        const defs = [['W', 'cg-sg', 'cg-g', 'Ganha'], ['D', 'cg-so', 'cg-o', 'Empata'], ['L', 'cg-sr', 'cg-r', 'Perde']];
        let off = 0, arcs = '', leg = '';
        defs.forEach((d, i) => {
            const n = c[d[0]], pct = Math.round(n * 100 / tot);
            if (n) {
                const len = n / tot * C;
                arcs += `<circle class="${d[1]}" cx="50" cy="50" r="${r}" stroke-dasharray="${len.toFixed(2)} ${(C - len).toFixed(2)}" stroke-dashoffset="${(-off).toFixed(2)}"><title>${d[3]}: ${n} (${pct}%)</title></circle>`;
                off += len;
            }
            leg += `<rect class="${d[2]}" x="116" y="${24 + i * 22}" width="9" height="9" rx="2"/><text class="cg-v" x="131" y="${32 + i * 22}">${d[3]} ${n}</text><text class="cg-t" x="214" y="${32 + i * 22}">${pct}%</text>`;
        });
        const nl = Math.round((c.W + c.D) * 100 / tot);
        return `<div class="x-section-title" style="padding:0 10px;">Resultado final da equipa com 10</div>` +
            `<div class="x-chart-card"><svg class="x-chart" viewBox="0 0 360 100" role="img" aria-label="Ganha, empata, perde">` +
            `<g transform="rotate(-90 50 50)">${arcs}</g>` +
            `<text class="cg-v" x="50" y="50" text-anchor="middle" style="font-size:15px">${nl}%</text><text class="cg-t" x="50" y="62" text-anchor="middle">não perde</text>` +
            `${leg}<text class="cg-t" x="116" y="94">${tot} jogos com resultado</text></svg></div>`;
    }

    function chartComps() {
        const by = {};
        history.forEach(h => {
            if (!h.comp || !isRes(h)) return;
            const a = by[h.comp] = by[h.comp] || { n: 0, nl: 0 };
            a.n++; if (h.result !== 'L') a.nl++;
        });
        const list = Object.keys(by).map(k => ({ k: k, n: by[k].n, p: Math.round(by[k].nl * 100 / by[k].n) }))
            .sort((a, b) => b.n - a.n || a.k.localeCompare(b.k)).slice(0, 8);
        if (!list.length) return '';
        const cells = list.map(c => {
            const hue = Math.round(c.p * 1.2);
            return `<div class="x-heat" style="background:hsl(${hue},62%,34%);${c.n < 3 ? 'opacity:.6;' : ''}" title="${escapeHTML(c.k)}: ${c.p}% não perde em ${c.n} jogos${c.n < 3 ? ' (amostra pequena)' : ''}">` +
                `<span>${escapeHTML(c.k)}</span><b>${c.p}%</b><span>${c.n} ${c.n === 1 ? 'jogo' : 'jogos'}</span></div>`;
        }).join('');
        return `<div class="x-section-title" style="padding:0 10px;">Por competição · % em que a equipa com 10 não perde</div><div class="x-heat-grid">${cells}</div>`;
    }

    function chartTrend() {
        const wk = {};
        history.forEach(h => {
            if (!isRes(h)) return;
            const m = /^(\d{4})-(\d{2})-(\d{2})/.exec(h.date || '');
            if (!m) return;
            const d = new Date(+m[1], +m[2] - 1, +m[3]);
            d.setDate(d.getDate() - ((d.getDay() + 6) % 7));              // segunda-feira dessa semana
            const key = d.getFullYear() + '-' + pad2(d.getMonth() + 1) + '-' + pad2(d.getDate());
            const a = wk[key] = wk[key] || { res: 0, nl: 0, d: d };
            a.res++; if (h.result !== 'L') a.nl++;
        });
        const keys = Object.keys(wk).sort().slice(-8);
        const title = `<div class="x-section-title" style="padding:0 10px;">Tendência semanal · % em que a equipa com 10 não perde</div>`;
        if (keys.length < 2) return title + `<div style="padding:2px 10px 8px;font-size:10px;color:var(--x-text-muted);">Precisa de pelo menos 2 semanas de histórico para mostrar a linha.</div>`;
        const x0 = 22, x1 = 338, yt = 20, ph = 62;
        const pts = keys.map((k, i) => {
            const a = wk[k], p = Math.round(a.nl * 100 / a.res);
            return { x: x0 + i * (x1 - x0) / (keys.length - 1), y: yt + (1 - p / 100) * ph, p: p, n: a.res, l: pad2(a.d.getDate()) + '/' + pad2(a.d.getMonth() + 1) };
        });
        const line = pts.map(p => p.x.toFixed(1) + ',' + p.y.toFixed(1)).join(' ');
        const dots = pts.map(p => `<g><title>${escapeHTML('Semana de ' + p.l + ': ' + p.p + '% em ' + p.n + ' jogos')}</title><circle class="cg-b" cx="${p.x.toFixed(1)}" cy="${p.y.toFixed(1)}" r="3.2"/>` +
            `<text class="cg-v" x="${p.x.toFixed(1)}" y="${(p.y - 7).toFixed(1)}" text-anchor="middle">${p.p}</text>` +
            `<text class="cg-t" x="${p.x.toFixed(1)}" y="104" text-anchor="middle">${p.l}</text></g>`).join('');
        const y50 = (yt + ph / 2).toFixed(1);
        return title + `<div class="x-chart-card"><svg class="x-chart" viewBox="0 0 360 110" role="img" aria-label="Tendência semanal">` +
            `<line class="cg-ref" x1="${x0}" y1="${y50}" x2="${x1}" y2="${y50}"/><text class="cg-t" x="2" y="${(+y50 + 3).toFixed(1)}">50</text>` +
            `<polyline class="cg-line" points="${line}"/>${dots}</svg></div>`;
    }

    function statsChartsHTML() {
        if (!history.length) return '';
        let h = '';
        try { h = chartBars() + chartDonut() + chartComps() + chartTrend(); } catch (e) { h = ''; }
        return h;
    }

    function renderStats() {
        const box = $('x_stats_box');
        if (!box) return;

        const rows = buildStats().map(r => {
            const s = r.stat;
            return `<div class="x-stat-row">
                <div class="lbl">${escapeHTML(r.label)}</div>
                <div class="num" title="Jogos registados">${s.n}</div>
                <div class="num" title="% em que a equipa com menos um jogador NÃO perdeu (V+E)">${s.notLostPct === null ? '-' : s.notLostPct + '%'}</div>
                <div class="num" title="Média de golos depois do 1º vermelho">${s.avgGoals === null ? '-' : s.avgGoals.toFixed(1)}</div>
            </div>`;
        }).join('');

        box.innerHTML = `
            <div class="x-stat-row x-stat-head"><div class="lbl">Categoria</div><div class="num">Jogos</div><div class="num">10 não perde</div><div class="num">Golos pós</div></div>
            ${rows}
            ${minuteStatsHTML()}
            ${statsChartsHTML()}
            <div style="padding:10px;font-size:10px;color:var(--x-text-muted);line-height:1.4;">
                Só entram jogos cujo FT foi visto pelo script. O minuto é o minuto em que o vermelho foi <b>visto</b> (pode ter atraso). Amostras pequenas não são estatística fiável.
            </div>
            <div style="padding:0 10px 10px;">
                <button class="x-mini-btn" id="x_export_csv">📥 Exportar CSV (${history.length})</button>
                <button class="x-mini-btn" id="x_clear_history">🗑️ Limpar histórico</button>
            </div>`;

        $('x_export_csv').onclick = exportHistoryCSV;
        $('x_clear_history').onclick = () => {
            if (confirm('Apagar todo o histórico de resultados?')) { history = []; saveHistory(); renderStats(); }
        };
    }

    // --- helpers de definições ---
    function sectionTitle(t) { return `<div class="x-section-title">${t}</div>`; }
    function secOpen(key, t) {
        const col = !!settings.ui.collapsed[key];
        return `<div class="x-sec${col ? ' collapsed' : ''}" data-sec="${key}"><div class="x-section-title x-sec-head"><span>${t}</span><b>▾</b></div><div class="x-sec-body">`;
    }
    const secClose = '</div></div>';
    const settingsSearchHTML = '<input class="x-input" type="search" id="x_set_q" placeholder="🔎 Procurar definição…" autocomplete="off" style="margin-bottom:4px;">';

    // Pré-visualização: o que o perfil de alertas faria com estes jogos-exemplo
    const ALERT_SAMPLES = [
        { t: "25'", s: '0-0', h: 1, a: 0 }, { t: "58'", s: '1-0', h: 0, a: 1 }, { t: "70'", s: '0-2', h: 1, a: 0 },
        { t: "82'", s: '0-0', h: 0, a: 1 }, { t: "40'", s: '1-1', h: 1, a: 1 }
    ];
    function alertPreviewHTML() {
        return ALERT_SAMPLES.map(x => {
            const ok = passesAlertProfile({ total: x.h + x.a, homeCards: x.h, awayCards: x.a }, x.t, x.s);
            const who = (x.h && x.a) ? 'ambas c/10' : (x.h ? 'Casa c/10' : 'Fora c/10');
            return `<div class="x-prev-row"><span class="x-prev-tag ${ok ? 'ok' : 'no'}">${ok ? '🔔 alerta' : '🔕 ignora'}</span><span>🟥 ${x.t} · ${x.s} · ${who}</span></div>`;
        }).join('');
    }
    function updateAlertPreview() { const e = $('x_alert_prev'); if (e) e.innerHTML = alertPreviewHTML(); }

    function bindSettingsUI(box) {
        box.onclick = (ev) => {
            const hd = ev.target.closest('.x-sec-head');
            if (!hd) return;
            const sec = hd.parentElement, key = sec.getAttribute('data-sec');
            const col = !sec.classList.contains('collapsed');
            sec.classList.toggle('collapsed', col);
            settings.ui.collapsed[key] = col;
            saveSettings();
        };
        const q = $('x_set_q');
        if (!q) return;
        q.addEventListener('input', () => {
            const v = q.value.trim().toLowerCase();
            box.querySelectorAll('.x-sec').forEach(sec => {
                const titleHit = !!v && (sec.querySelector('.x-sec-head span').textContent || '').toLowerCase().includes(v);
                const bodyHit = !!v && sec.textContent.toLowerCase().includes(v);
                sec.querySelectorAll('.x-settings-group').forEach(gp => {
                    gp.style.display = (!v || titleHit || gp.textContent.toLowerCase().includes(v)) ? '' : 'none';
                });
                sec.style.display = (!v || titleHit || bodyHit) ? '' : 'none';
                sec.classList.toggle('force-open', !!v);
            });
        });
    }

    function sliderHTML(id, label, min, max, step, val, suffix) {
        return `<div class="x-settings-group"><div class="x-settings-label">${label}</div><div class="x-settings-control"><input type="range" id="${id}" min="${min}" max="${max}" step="${step}" value="${val}" style="flex:1;cursor:pointer;"><span id="${id}_val" style="width:38px;text-align:center;font-weight:bold;">${val}${suffix}</span></div></div>`;
    }
    function bindSlider(id, set, suffix, after) {
        $(id).oninput = e => {
            const v = parseInt(e.target.value, 10);
            set(v);
            $(id + '_val').textContent = v + suffix;
            saveSettings();
            if (after) after();
        };
    }

    function toggleHTML(id, label, on) {
        return `<div class="x-settings-group"><div class="x-settings-label">${label}</div><div class="x-settings-control" id="${id}" style="cursor:pointer;padding:4px 0;"><div class="x-toggle ${on ? 'on' : ''}" style="pointer-events:none;"></div><span class="x-tlabel" style="font-size:12px;margin-left:6px;font-weight:bold;">${on ? 'ON' : 'OFF'}</span></div></div>`;
    }
    function bindToggle(id, get, set, msgOn, msgOff, after) {
        const row = $(id);
        row.onclick = () => {
            const v = !get();
            set(v);
            row.querySelector('.x-toggle').classList.toggle('on', v);
            row.querySelector('.x-tlabel').textContent = v ? 'ON' : 'OFF';
            saveSettings();
            if (msgOn) showToast(v ? msgOn : msgOff, 'info', 2500);
            if (after) after();
        };
    }

    function textHTML(id, label, val, placeholder) {
        return `<div class="x-settings-group"><div class="x-settings-label">${label}</div><input class="x-input" type="text" id="${id}" value="${escapeHTML(val)}" placeholder="${escapeHTML(placeholder)}"></div>`;
    }
    function bindText(id, set) {
        $(id).onchange = e => { set(e.target.value); saveSettings(); showToast('✅ Guardado. Aplica-se no próximo scan.', 'success', 1800); };
    }

    function renderSettings() {
        const box = $('x_settings_box');
        if (!box) return;
        const p = settings.profile;

        box.innerHTML = `<div style="padding:12px;">
            ${settingsSearchHTML}
            ${secOpen('geral', 'Geral')}
            ${sliderHTML('x_min_cards', 'Mínimo de Cartões (Global)', 1, 5, 1, settings.minCards, '')}
            ${sliderHTML('x_scan_interval', 'Ciclo do Trator Automático (Min)', 1, 15, 1, settings.scanInterval, 'm')}
            ${sliderHTML('x_idle_secs', 'Trator só após inatividade de (seg)', 5, 120, 5, settings.idleSeconds, 's')}
            ${sliderHTML('x_crunch_val', 'Início "Crunch Time" 💣', 60, 88, 1, settings.crunchThreshold, "'")}

            ${secClose}${secOpen('visual', 'Aparência')}
            <div class="x-settings-group"><div class="x-settings-label">Tema</div>
                <select class="x-input" id="x_theme">
                    <option value="dark"${settings.ui.theme === 'dark' ? ' selected' : ''}>🌙 Escuro</option>
                    <option value="light"${settings.ui.theme === 'light' ? ' selected' : ''}>☀️ Claro</option>
                    <option value="auto"${settings.ui.theme === 'auto' ? ' selected' : ''}>🖥️ Automático (segue o sistema)</option>
                </select></div>
            ${toggleHTML('x_dense_row', 'Lista compacta', settings.ui.dense)}
            ${toggleHTML('x_dim_row', 'Bola discreta quando está tudo calmo', settings.ui.dimFab)}
            ${toggleHTML('x_badge_row', 'Etiqueta no site (ex.: "10 · perde") e cor do favicon', settings.siteBadge)}
            <button class="x-mini-btn" id="x_reset_layout">↔️ Repor tamanho e posição do painel</button>
            ${secClose}${secOpen('perfil', 'Perfil de alertas (pop-up / som / voz)')}
            ${sliderHTML('x_p_min', 'Alertar só a partir do minuto', 0, 90, 5, p.minMinute, "'")}
            ${sliderHTML('x_p_max', 'Alertar só até ao minuto', 45, 95, 5, p.maxMinute, "'")}
            ${sliderHTML('x_p_def', 'Ignorar se a equipa com 10 perde por ≥ N golos (0 = off)', 0, 4, 1, p.maxRedTeamDeficit, '')}
            ${toggleHTML('x_p_zero', 'Só alertar com 0-0', p.onlyZeroZero)}
            ${toggleHTML('x_p_both', 'Ignorar se ambas as equipas têm vermelhos', p.skipBothReds)}
            <div class="x-settings-label" style="margin-top:8px;">Pré-visualização com este perfil</div>
            <div class="x-prev" id="x_alert_prev">${alertPreviewHTML()}</div>

            ${secClose}${secOpen('filtros', 'Filtros de competição')}
            ${textHTML('x_f_exc', 'Excluir (palavras separadas por vírgula)', settings.excludeComp, 'ex: U19, Women, Esports')}
            ${textHTML('x_f_inc', 'Só incluir (vazio = todas)', settings.includeComp, 'ex: Premier, Liga')}
            ${textHTML('x_f_sel', 'Seletor CSS dos cabeçalhos (avançado)', settings.compSelector, 'vazio = automático')}
            <button class="x-mini-btn" id="x_f_preset">Preencher exclusões sugeridas</button>

            ${secClose}${secOpen('avisos', 'Avisos')}
            ${toggleHTML('x_notif_row', 'Pop-ups visuais', settings.notificationsOn)}
            ${toggleHTML('x_sound_row', 'Som do radar', settings.soundOn)}
            ${toggleHTML('x_voice_row', 'Voz ("Cartão vermelho, equipa")', settings.voiceOn)}
            ${toggleHTML('x_title_row', 'Contador no título e favicon', settings.titleBadge)}

            ${secClose}${secOpen('fonte', 'Fonte de dados')}
            ${toggleHTML('x_feed_row', 'Ler dados da rede, sem scroll (recomendado)', settings.dataSource === 'auto')}
            ${toggleHTML('x_real_row', 'Minuto real do vermelho (lê os eventos do jogo)', settings.realMinutes)}
            <div id="x_feed_diag" style="font-size:10px;line-height:1.6;color:var(--x-text-muted);padding:2px 0 6px;"></div>

            ${secClose}${secOpen('ferramentas', 'Ferramentas')}
            ${toggleHTML('x_sniff_row', 'Sniffer de rede (requer recarregar a página)', settings.sniffer)}
            <div id="x_sniff_diag" style="font-size:10px;line-height:1.6;color:var(--x-text-muted);padding:2px 0 6px;"></div>
            <button class="x-mini-btn" id="x_sniff_copy">📋 Copiar captura (${sniffStore.length})</button>
            <button class="x-mini-btn" id="x_sniff_file">💾 Guardar ficheiro</button>
            <button class="x-mini-btn" id="x_sniff_clear">🧹 Limpar captura</button>
            <br>
            <button class="x-mini-btn" id="x_cfg_export">⬆️ Exportar definições</button>
            <button class="x-mini-btn" id="x_cfg_import">⬇️ Importar definições</button>
            <button class="x-test-btn" id="x_test_alert_btn">🚨 TESTAR ALERTAS 🚨</button>
            ${secClose}
        </div>`;

        bindSlider('x_min_cards', v => { settings.minCards = v; }, '', renderLiveList);
        bindSlider('x_scan_interval', v => { settings.scanInterval = v; }, 'm');
        bindSlider('x_idle_secs', v => { settings.idleSeconds = v; }, 's');
        bindSlider('x_crunch_val', v => { settings.crunchThreshold = v; }, "'", renderLiveList);
        bindSlider('x_p_min', v => { settings.profile.minMinute = v; }, "'", updateAlertPreview);
        bindSlider('x_p_max', v => { settings.profile.maxMinute = v; }, "'", updateAlertPreview);
        bindSlider('x_p_def', v => { settings.profile.maxRedTeamDeficit = v; }, '', updateAlertPreview);
        bindToggle('x_p_zero', () => settings.profile.onlyZeroZero, v => { settings.profile.onlyZeroZero = v; }, null, null, updateAlertPreview);
        bindToggle('x_p_both', () => settings.profile.skipBothReds, v => { settings.profile.skipBothReds = v; }, null, null, updateAlertPreview);

        bindText('x_f_exc', v => { settings.excludeComp = v; });
        bindText('x_f_inc', v => { settings.includeComp = v; });
        bindText('x_f_sel', v => { settings.compSelector = v; });
        $('x_f_preset').onclick = () => {
            settings.excludeComp = SUGGESTED_EXCLUDES;
            saveSettings();
            $('x_f_exc').value = SUGGESTED_EXCLUDES;
            showToast('✅ Exclusões sugeridas aplicadas.', 'success', 1800);
        };

        bindToggle('x_notif_row', () => settings.notificationsOn, v => { settings.notificationsOn = v; }, '🔔 Pop-ups ON', '🔕 Pop-ups OFF');
        bindToggle('x_sound_row', () => settings.soundOn, v => { settings.soundOn = v; }, '🔊 Som ON', '🔇 Som OFF');
        bindToggle('x_voice_row', () => settings.voiceOn, v => { settings.voiceOn = v; }, '🗣️ Voz ON', '🤐 Voz OFF');
        bindToggle('x_title_row', () => settings.titleBadge, v => { settings.titleBadge = v; }, '🏷️ Contador ON', '🏷️ Contador OFF', () => {
            lastFavCount = -1;
            if (settings.titleBadge) { setBadgeTitle(); setFavicon(lastLiveCount); }
            else { document.title = document.title.replace(TITLE_PREFIX, ''); lastFavCount = -2; setFaviconRestore(); }
        });
        bindToggle('x_feed_row', () => settings.dataSource === 'auto', v => { settings.dataSource = v ? 'auto' : 'dom'; },
            '📡 Feed ON (sem scroll). Recarrega a página para a primeira leitura.', '🖥️ Modo ecrã (com trator).', refreshSniffDiag);
        bindToggle('x_sniff_row', () => settings.sniffer, v => { settings.sniffer = v; }, '🕵️ Sniffer ON. Recarrega a página para apanhar tudo.', '🕵️ Sniffer OFF.', () => {
            if (settings.sniffer && !sniffInstalled) installSniffer();
            refreshSniffDiag();
        });

        $('x_sniff_copy').onclick = () => {
            if (sniffStore.length === 0) { showToast(sniffEmptyHint(), 'warning', 7000); return; }
            copyText(buildSniffPayload(false))
                .then(() => showToast(`📋 ${Math.min(sniffStore.length, 14)} entradas copiadas.`, 'success'))
                .catch(() => { downloadFile('aiscore_captura.json', buildSniffPayload(true), 'application/json'); showToast('Clipboard bloqueado. Ficheiro descarregado.', 'info', 4000); });
        };
        $('x_sniff_file').onclick = () => {
            if (sniffStore.length === 0) { showToast(sniffEmptyHint(), 'warning', 7000); return; }
            downloadFile('aiscore_captura.json', buildSniffPayload(true), 'application/json');
            showToast('💾 aiscore_captura.json descarregado.', 'success');
        };
        $('x_sniff_clear').onclick = () => { sniffStore = []; GM_setValue(SNIFF_KEY, []); renderSettings(); };
        refreshSniffDiag();

        $('x_cfg_export').onclick = () => {
            const payload = JSON.stringify(settings);
            navigator.clipboard.writeText(payload)
                .then(() => showToast('⬆️ Definições copiadas.', 'success'))
                .catch(() => { window.prompt('Copia as definições:', payload); });
        };
        $('x_cfg_import').onclick = () => {
            const txt = window.prompt('Cola aqui o JSON das definições:');
            if (!txt) return;
            try {
                settings = normalizeSettings(JSON.parse(txt));
                saveSettings();
                renderSettings();
                renderLiveList();
                showToast('⬇️ Definições importadas.', 'success');
            } catch (e) {
                showToast('❌ JSON inválido.', 'error');
            }
        };

        bindSettingsUI(box);
        $('x_theme').onchange = () => { settings.ui.theme = $('x_theme').value; saveSettings(); applyTheme(); };
        bindToggle('x_dense_row', () => settings.ui.dense, v => { settings.ui.dense = v; }, null, null, () => {
            const pn = $('x_panel'), dn = $('x_dens');
            if (pn) pn.classList.toggle('x-dense', settings.ui.dense);
            if (dn) dn.classList.toggle('on', settings.ui.dense);
        });
        bindToggle('x_real_row', () => settings.realMinutes, v => { settings.realMinutes = v; }, 'Minuto real ligado.', 'Minuto real desligado.', refreshSniffDiag);
        bindToggle('x_dim_row', () => settings.ui.dimFab, v => { settings.ui.dimFab = v; }, null, null, wakeFab);
        bindToggle('x_badge_row', () => settings.siteBadge, v => { settings.siteBadge = v; }, null, null, () => { lastFavCount = -1; highlightDom(); setFavicon(lastLiveCount); });
        $('x_reset_layout').onclick = () => {
            const pn = $('x_panel');
            if (pn) { pn.style.left = ''; pn.style.top = ''; pn.style.right = ''; pn.style.width = ''; pn.style.removeProperty('--x-listh'); }
            Object.assign(settings.ui, { panelW: 0, listH: 0, panelX: null, panelY: null });
            saveSettings();
            showToast('↔️ Painel reposto.', 'success', 1800);
        };

        $('x_test_alert_btn').onclick = () => {
            playAlertSound();
            speakAlert('Teste de alerta');
            showRedCardAlert({ uid: null, homeTeam: 'Equipa Casa', awayTeam: 'Equipa Fora', homeCards: 1, awayCards: 0, total: 1, side: 'home', minute: "67'", score: '0-1', comp: 'Liga de Teste', sit: 'losing' }, '🚨 TESTE', 'Alerta de teste');
            showToast('Teste Enviado!', 'success');
        };
    }

    function setFaviconRestore() {
        try {
            const link = document.querySelector('link[rel~="icon"]');
            if (link && origFavHref) link.href = origFavHref;
        } catch (e) { /* ignora */ }
    }

    const uiFilter = { q: '', sit: 'all' };

    // Situação da equipa com 10: 'losing' | 'draw' | 'winning' | '' (sem vermelhos assimétricos)
    function situationOf(g) {
        const hR = g.homeCards || 0, aR = g.awayCards || 0;
        const sc = parseScore(g.score);
        if (hR === aR || !sc) return '';
        const mine = hR > aR ? sc.h : sc.a, opp = hR > aR ? sc.a : sc.h;
        return mine < opp ? 'losing' : (mine === opp ? 'draw' : 'winning');
    }
    const SIT_TEXT = { losing: 'a perder', draw: 'empata', winning: 'a ganhar' };

    function passesUiFilter(g) {
        if (uiFilter.q) {
            const hay = ((g.name || '') + ' ' + (g.comp || '')).toLowerCase();
            if (!hay.includes(uiFilter.q)) return false;
        }
        const s = uiFilter.sit;
        if (s === 'all') return true;
        if (s === 'late') return getMinuteSortValue(liveTime(g)) >= settings.crunchThreshold;
        if (s === 'multi') return (g.cards || 0) >= 2;
        return situationOf(g) === s;
    }

    // ---- relógio vivo: o minuto avança mesmo sem eventos novos do feed
    let lastClockAt = 0;
    function liveTime(game) {
        const fg = FEED.games.get(String(game.uid).replace(/^id_/, ''));
        if (fg && feedUsable() && (fg.st === 2 || fg.st === 4) && fg.ts) {
            const m = feedMinute(fg);
            if (m !== '?') return m;
        }
        return game.time;
    }
    // "há N' com 10" — desde o 1.º vermelho visto (≥ se o vermelho já existia quando o script arrancou)
    function withTenText(game, nowMin) {
        const ev = game.firstRed;
        if (!ev || nowMin <= 0) return '';
        const m0 = getMinuteSortValue(ev.time);
        if (m0 <= 0) return '';
        const d = Math.max(0, Math.floor(nowMin - m0));
        if (ev.approx && d < 1) return '';
        return 'há ' + (ev.approx ? '≥' : '') + d + "' " + (situationOf(game) ? 'com 10' : 'após 🟥');
    }
    function timelineHTML(game, nowMin, lt) {
        const pct = (m) => Math.max(0, Math.min(100, m / 95 * 100));
        const evs = [];
        (game.redEvents || []).forEach(ev => { const m = getMinuteSortValue(ev.time); if (m > 0) evs.push({ k: 'r', m: m, ev: ev }); });
        (game.goals || []).forEach(ev => { const m = getMinuteSortValue(ev.time); if (m > 0) evs.push({ k: 'g', m: m, ev: ev }); });
        evs.sort((a, b) => a.m - b.m);
        const ticks = evs.map(e => `<span class="${e.k === 'r' ? 'rc' : 'gl'}" style="left:${pct(e.m).toFixed(1)}%"></span>`).join('');
        const side = (e) => e.k === 'r' ? (e.ev.side === 'home' ? ' · Casa' : (e.ev.side === 'away' ? ' · Fora' : ''))
                                        : (e.ev.side === 'h' ? ' · Casa' : (e.ev.side === 'a' ? ' · Fora' : ''));
        const lines = ['Agora ' + (lt || '-')].concat(evs.map(e =>
            (e.k === 'r' ? '🟥 ' : '⚽ ') + e.ev.time + (e.ev.score ? ' · ' + e.ev.score : '') + side(e) + (e.ev.player ? ' · ' + e.ev.player : '') + (e.ev.approx ? ' (aprox.)' : '')));
        const title = lines.map(escapeHTML).join('&#10;');
        return `<div class="x-tl" title="${title}"><span class="now" style="width:${pct(nowMin).toFixed(1)}%"></span><span class="ht"></span>${ticks}</div>`;
    }
    function feedLineText() {
        const ago = (ms) => { const s = Math.max(0, Math.round((Date.now() - ms) / 1000)); return s < 90 ? s + ' s' : Math.round(s / 60) + ' min'; };
        if (feedUsable()) {
            let live = 0;
            FEED.games.forEach(g => { if (FEED_LIVE[g.st]) live++; });
            return '📡 a ouvir · último batimento há ' + ago(FEED.beatAt) + ' · ' + live + ' jogos ao vivo no feed';
        }
        if (settings.dataSource === 'auto') {
            return FEED.listAt ? '⚠️ feed sem batimento há ' + ago(FEED.beatAt || FEED.listAt) + ' · modo ecrã de reserva' : '⏳ a aguardar o feed…';
        }
        return lastScanAt ? '🖥️ modo ecrã · último scan há ' + ago(lastScanAt) : '🖥️ modo ecrã';
    }
    function summaryText(arr) {
        if (!arr.length) return '';
        const c = { losing: 0, draw: 0, winning: 0 };
        let late = 0;
        arr.forEach(g => {
            const s = situationOf(g);
            if (s) c[s]++;
            if (getMinuteSortValue(liveTime(g)) >= settings.crunchThreshold) late++;
        });
        const parts = [arr.length + (arr.length === 1 ? ' jogo' : ' jogos')];
        if (c.losing) parts.push(c.losing + ' a perder');
        if (c.draw) parts.push(c.draw + ' a empatar');
        if (c.winning) parts.push(c.winning + ' a ganhar');
        if (late) parts.push(late + ' em fase final');
        return parts.join(' · ');
    }
    const SORT_LABELS = { minute: '⏱ Minuto', sit: '🚦 Situação', recent: '🆕 Mais recente', comp: '🏆 Competição' };
    function sortGames(arr) {
        const mode = settings.ui.sort;
        const mv = (g) => getMinuteSortValue(liveTime(g));
        const rank = { losing: 0, draw: 1, winning: 2, '': 3 };
        const lastAt = (g) => { const e = g.redEvents || []; const l = e.length ? e[e.length - 1] : null; return (l && l.at) || 0; };
        arr.sort((a, b) => {
            if (mode === 'sit') { const d = rank[situationOf(a)] - rank[situationOf(b)]; if (d) return d; }
            else if (mode === 'recent') { const d = lastAt(b) - lastAt(a); if (d) return d; }
            else if (mode === 'comp') { const d = String(a.comp || '~').localeCompare(String(b.comp || '~')); if (d) return d; }
            return mv(b) - mv(a);
        });
    }

    // ---- realce quando algo muda (golo / vermelho / situação)
    const FLASH_MS = 2400;
    const flashSig = new Map(), flashLive = new Map();
    function updateFlash(arr) {
        const now = Date.now(), seen = new Set();
        arr.forEach(g => {
            seen.add(g.uid);
            const sig = { sc: g.score, c: g.cards, sit: situationOf(g) };
            const p = flashSig.get(g.uid);
            if (p) {
                const kind = p.c !== sig.c ? 'red' : (p.sc !== sig.sc ? 'goal' : (p.sit !== sig.sit ? 'sit' : ''));
                if (kind) flashLive.set(g.uid, { kind: kind, at: now });
            }
            flashSig.set(g.uid, sig);
        });
        Array.from(flashSig.keys()).forEach(k => { if (!seen.has(k)) { flashSig.delete(k); flashLive.delete(k); } });
        flashLive.forEach((v, k) => { if (now - v.at > FLASH_MS) flashLive.delete(k); });
    }

    function refreshLiveClocks() {
        lastClockAt = Date.now();
        const panel = $('x_panel');
        if (!panel || panel.classList.contains('x-hidden')) return;
        panel.querySelectorAll('.x-item[data-uid]').forEach(it => {
            const g = activeGamesDB[it.getAttribute('data-uid')];
            if (!g) return;
            const lt = liveTime(g), nm = Math.max(0, getMinuteSortValue(lt));
            const tm = it.querySelector('.x-tm');
            if (tm && tm.textContent !== lt) tm.textContent = lt;
            const w = it.querySelector('.x-w10');
            if (w) { const t = withTenText(g, nm); if (t && w.textContent !== t) w.textContent = t; }
            const nw = it.querySelector('.x-tl .now');
            if (nw) nw.style.width = Math.max(0, Math.min(100, nm / 95 * 100)).toFixed(1) + '%';
        });
        panel.querySelectorAll('.x-feedline').forEach(el => { el.textContent = feedLineText(); });
    }

    // ---- bola discreta quando está tudo calmo
    const FAB_DIM_MS = 25000;
    let fabWakeAt = Date.now();
    function wakeFab() {
        fabWakeAt = Date.now();
        const f = $('x_fab_btn');
        if (f) f.classList.remove('x-idle');
    }
    function updateFabDim() {
        const f = $('x_fab_btn'), p = $('x_panel');
        if (!f) return;
        const open = p && !p.classList.contains('x-hidden');
        const calm = f.classList.contains('fab-ok') && !f.classList.contains('fab-warn');
        const idle = settings.ui.dimFab && !open && calm && !f.matches(':hover') && (Date.now() - fabWakeAt > FAB_DIM_MS);
        f.classList.toggle('x-idle', !!idle);
    }

    function renderLiveList() {
        const liveBox = $('x_live_box'), topBox = $('x_top_box'), zeroBox = $('x_zero_box'), starBox = $('x_star_box');
        if (!liveBox || !topBox || !zeroBox || !starBox) return;

        const ls = liveBox.scrollTop, ts = topBox.scrollTop, zs = zeroBox.scrollTop, ss = starBox.scrollTop;

        const now = Date.now();
        let pruned = false;
        for (const uid in activeGamesDB) {
            if (now - activeGamesDB[uid].timestamp > STALE_GAME_MS) { delete activeGamesDB[uid]; pruned = true; }
        }
        if (pruned) saveDB();

        const gamesArray = Object.keys(activeGamesDB)
            .map(uid => Object.assign({}, activeGamesDB[uid], { uid: uid }))
            .filter(g => g.cards >= settings.minCards && g.time !== 'FT');
        sortGames(gamesArray);
        updateFlash(gamesArray);
        const sumEl = $('x_summary');
        if (sumEl) sumEl.textContent = summaryText(gamesArray);

        const topArray  = gamesArray.filter(g => computeFlags(g).top);
        const zeroArray = gamesArray.filter(g => g.score === '0-0');
        const starArray = gamesArray.filter(g => g.starred);

        $('count_reds').textContent = String(gamesArray.length);
        $('count_top').textContent  = String(topArray.length);
        $('count_zero').textContent = String(zeroArray.length);
        $('count_star').textContent = String(starArray.length);

        const fab = $('x_fab_btn');
        $('ui_status_dot').className = gamesArray.length > 0 ? 'x-status-dot x-dot-on' : 'x-status-dot x-dot-off';

        lastLiveCount = gamesArray.length;
        applyTitleBadge();
        setFavicon(lastLiveCount, favColorOf(gamesArray));

        const generateHTML = (arrAll, emptyMsg) => {
            const arr = arrAll.filter(passesUiFilter);
            if (arrAll.length > 0 && arr.length === 0) {
                return `<div style="padding:20px;text-align:center;color:var(--x-text-muted);font-size:12px;">Nenhum jogo com este filtro.</div>`;
            }
            if (arr.length === 0) {
                return `<div style="padding:20px 20px 8px;text-align:center;color:var(--x-text-muted);font-size:12px;">${emptyMsg}</div>` +
                    `<div class="x-feedline" style="padding:0 20px 16px;text-align:center;font-size:10px;color:var(--x-text-muted);">${escapeHTML(feedLineText())}</div>`;
            }
            return arr.map(game => {
                const homeSvg = game.homeCards ? getRedCardSVG(game.homeCards) : '';
                const awaySvg = game.awayCards ? getRedCardSVG(game.awayCards) : '';
                const parts = (game.name || '').split(' vs ');
                const homeName = escapeHTML(parts[0] || '');
                const awayName = escapeHTML(parts[1] || '');
                const f = computeFlags(game);

                const lt = liveTime(game);
                const nowMin = Math.max(0, getMinuteSortValue(lt));
                const isCrunchTime = nowMin >= settings.crunchThreshold;
                const timeClass = isCrunchTime ? 'x-item-time x-crunch-time' : 'x-item-time';
                const crunchIcon = isCrunchTime ? `<span class="x-bomb" title="Hora do Abafa">💣</span>` : '';

                let badgeClass = 'x-score-badge', badgeTitle = '';
                if (f.bloodbath)    { badgeClass += ' x-bloodbath-badge'; badgeTitle = '🚨 Banho de Sangue!'; }
                else if (f.mortal)  { badgeClass += ' x-score-mortal';    badgeTitle = '💎 MORTAL: Golo marcado em desvantagem!'; }
                else if (f.despair) { badgeClass += ' x-score-despair';   badgeTitle = '🆘 DESESPERO: A perder por 2+ golos com +1 jogador!'; }
                else if (f.zero)    { badgeClass += ' x-score-zero';      badgeTitle = '🎯 Empate a zeros!'; }

                let meta = '';
                if (game.firstRed) {
                    const ga = goalsAfterRed(game);
                    meta = `🟥 ${escapeHTML(game.firstRed.time)}${game.firstRed.real ? '<span class="x-real" title="Minuto real, lido do site">✓</span>' : ''} (${escapeHTML(game.firstRed.score)})` + (ga !== null ? ` · +${ga}⚽` : '');
                }
                const sit = situationOf(game);
                const redSide = (game.homeCards || 0) > (game.awayCards || 0) ? 'Casa' : 'Fora';
                const sitHtml = sit ? `<span class="x-sit ${sit}" title="Equipa com menos um jogador">${redSide} c/10 · ${SIT_TEXT[sit]}</span>` : '';
                const tlHtml = timelineHTML(game, nowMin, lt);
                const w10 = game.firstRed ? withTenText(game, nowMin) : '';
                const fg = FEED.games.get(String(game.uid).replace(/^id_/, ''));
                let statsHtml = '';
                if (fg && fg.h.length > 4 && fg.a.length > 4) {
                    const yel = (fg.h[3] | 0) + '-' + (fg.a[3] | 0), cor = (fg.h[4] | 0) + '-' + (fg.a[4] | 0);
                    statsHtml = `<div class="x-stats" title="Amarelos · Cantos (casa-fora)">🟨 ${yel} · ⛳ ${cor}</div>`;
                }
                const compHtml = game.comp ? `<div class="x-comp" title="${escapeHTML(game.comp)}">${escapeHTML(game.comp)}</div>` : '';
                const muted = (game.mutedUntil || 0) > now;
                const safeUid = escapeHTML(game.uid);
                const fl = flashLive.get(game.uid);
                const flCls = fl ? ' x-flash-' + fl.kind : '';
                const flSty = fl ? ` style="animation-delay:-${Math.max(0, Math.min(FLASH_MS, now - fl.at))}ms"` : '';

                return `<div class="x-item${f.bloodbath ? ' x-bloodbath' : ''}${sit ? ' x-sit-' + sit : ''}${flCls}" data-uid="${safeUid}"${flSty}>
                    <div class="${timeClass}" style="display:flex;flex-direction:column;align-items:center;">
                        <span class="x-tm">${escapeHTML(lt) || '-'}</span>
                        <div style="display:flex;gap:3px;margin-top:2px;">${crunchIcon}${f.despair ? '<span class="x-sos">🆘</span>' : ''}</div>
                    </div>
                    <div class="x-item-text">
                        <div class="x-team-col home">${homeSvg}<span class="x-team-name">${smartTruncate(homeName, 12)}</span></div>
                        <div style="display:flex;flex-direction:column;align-items:center;">
                            <div class="${badgeClass}" title="${badgeTitle}">${escapeHTML(game.score) || '-'}</div>
                            ${meta ? `<div class="x-meta" title="Minuto/placar em que o 1º vermelho foi visto, golos desde então e tempo decorrido">${meta}${w10 ? ` · <span class="x-w10">${escapeHTML(w10)}</span>` : ''}</div>` : ''}
                            ${sitHtml ? `<div style="margin-top:3px;">${sitHtml}</div>` : ''}
                            ${tlHtml}
                            ${statsHtml}
                            ${compHtml}
                        </div>
                        <div class="x-team-col away"><span class="x-team-name">${smartTruncate(awayName, 12)}</span>${awaySvg}</div>
                    </div>
                    <div class="x-action-col">
                        <div class="x-sniper-btn" data-search="${homeName}" title="Procurar Casa na 22Bet">🔍</div>
                        <div class="x-star-btn ${game.starred ? 'active' : ''}" data-star="${safeUid}" title="Fixar">⭐</div>
                        <div class="x-mute-btn ${muted ? 'active' : ''}" data-mute="${safeUid}" title="${muted ? 'Silenciado (clica para reativar)' : 'Silenciar alertas deste jogo 10 min'}">🔕</div>
                    </div>
                </div>`;
            }).join('');
        };

        liveBox.innerHTML = generateHTML(gamesArray, 'À procura de expulsões...');
        topBox.innerHTML  = generateHTML(topArray, 'Nenhuma oportunidade top.');
        zeroBox.innerHTML = generateHTML(zeroArray, 'Nenhum empate a zero.');
        starBox.innerHTML = generateHTML(starArray, 'Nenhum jogo fixado.');
        liveBox.scrollTop = ls; topBox.scrollTop = ts; zeroBox.scrollTop = zs; starBox.scrollTop = ss;

        [liveBox, topBox, zeroBox, starBox].forEach(b => {
            b.querySelectorAll('.x-item').forEach(item => {
                item.addEventListener('click', async (e) => {
                    if (e.target.closest('.x-sniper-btn') || e.target.closest('.x-star-btn') || e.target.closest('.x-mute-btn')) return;
                    const pn = $('x_panel');
                    if (pn) pn.classList.add('x-hidden');
                    await activateSonarSearch(item.getAttribute('data-uid'));
                });
            });

            b.querySelectorAll('.x-sniper-btn').forEach(btn => {
                btn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    const team = btn.getAttribute('data-search');
                    navigator.clipboard.writeText(team).then(() => {
                        showToast(`🔍 Copiado: '<b>${escapeHTML(team)}</b>'`, 'success', 3000);
                        window.open(BET22_URL, '_blank');
                    }).catch(() => { showToast('❌ Erro a copiar.', 'error'); });
                });
            });

            b.querySelectorAll('.x-star-btn').forEach(btn => {
                btn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    const g = activeGamesDB[btn.getAttribute('data-star')];
                    if (g) { g.starred = !g.starred; saveDB(); renderLiveList(); }
                });
            });

            b.querySelectorAll('.x-mute-btn').forEach(btn => {
                btn.addEventListener('click', (e) => {
                    e.stopPropagation();
                    const g = activeGamesDB[btn.getAttribute('data-mute')];
                    if (!g) return;
                    const isMuted = (g.mutedUntil || 0) > Date.now();
                    g.mutedUntil = isMuted ? 0 : Date.now() + MUTE_MS;
                    saveDB();
                    renderLiveList();
                    showToast(isMuted ? '🔔 Alertas reativados.' : '🔕 Silenciado 10 min.', 'info', 1500);
                });
            });
        });
    }

    //======================================================================
    // 15. SONAR (procurar jogo na página)
    //======================================================================

    let sonarOrigin = null, sonarBackTimer = null, sonarKeeper = null;

    // O AiScore repete cada jogo na página (listas duplicadas/escondidas): só conta o que está mesmo visível.
    function isShown(el) {
        if (!el || !el.isConnected) return false;
        const r = el.getBoundingClientRect();
        if (r.width < 2 || r.height < 2) return false;
        if (r.right <= 0 || r.left >= (window.innerWidth || 1e9)) return false;
        const cs = getComputedStyle(el);
        return cs.visibility !== 'hidden' && cs.display !== 'none' && parseFloat(cs.opacity) !== 0;
    }

    // Todos os elementos visíveis do jogo (normalmente 1; mais se a página repetir o jogo)
    function findTargets(uid) {
        let list = [];
        if (/^id_[a-z0-9]+$/i.test(uid)) list = Array.from(document.querySelectorAll('a.match-container[href*="/' + uid.slice(3) + '"]'));
        else list = detectGameContainers().filter(c => getUID(c, '') === uid);
        return list.filter(isShown);
    }
    // O melhor: o mais perto do centro do ecrã
    function findTarget(uid) {
        const list = findTargets(uid);
        if (list.length < 2) return list[0] || null;
        const mid = (window.innerHeight || 800) / 2;
        const dist = el => { const r = el.getBoundingClientRect(); return Math.abs(r.top + r.height / 2 - mid); };
        return list.sort((a, b) => dist(a) - dist(b))[0];
    }

    function notePos(uid, c) {
        try { if (isShown(c)) sonarPos.set(uid, Math.round(c.getBoundingClientRect().top + window.scrollY)); } catch (e) { /* ignora */ }
    }
    function recordPositions() {
        try {
            detectGameContainers().forEach(c => {
                const uid = getUID(c, '');
                if (uid && activeGamesDB[uid]) notePos(uid, c);
            });
        } catch (e) { /* ignora */ }
    }

    function hideBackButton() {
        clearTimeout(sonarBackTimer);
        const b = $('x_sonar_back');
        if (b) b.remove();
        sonarOrigin = null;
    }
    function showBackButton() {
        let b = $('x_sonar_back');
        if (!b) {
            b = document.createElement('div');
            b.id = 'x_sonar_back';
            b.setAttribute('data-xui', '1');
            b.textContent = '↩ Voltar onde estava';
            b.onclick = () => {
                const y = sonarOrigin || 0;
                hideBackButton();
                window.scrollTo({ top: y, behavior: 'smooth' });
            };
            document.body.appendChild(b);
        }
        clearTimeout(sonarBackTimer);
        sonarBackTimer = setTimeout(hideBackButton, 30000);
    }

    function clearFocus() {
        clearInterval(sonarKeeper);
        document.querySelectorAll('.god-target').forEach(e => { e.classList.remove('god-target'); e.removeAttribute('data-god-label'); });
    }
    // Mantém o realce no(s) elemento(s) certos durante 8 s, mesmo que a página volte a desenhar a linha
    function keepFocus(uid, ms) {
        clearFocus();
        const t0 = Date.now();
        const apply = () => {
            const els = findTargets(uid);
            document.querySelectorAll('.god-target').forEach(e => {
                if (els.indexOf(e) < 0) { e.classList.remove('god-target'); e.removeAttribute('data-god-label'); }
            });
            els.forEach(e => {
                if (!e.classList.contains('god-target')) { e.setAttribute('data-god-label', '🎯 ALVO'); e.classList.add('god-target'); }
            });
        };
        apply();
        sonarKeeper = setInterval(() => {
            if (Date.now() - t0 > ms) { clearFocus(); return; }
            apply();
        }, 300);
    }

    async function settleScroll() {
        let last = -1, same = 0;
        for (let i = 0; i < 16 && same < 3; i++) {
            await sleep(80);
            const y = window.scrollY;
            same = (Math.abs(y - last) < 1) ? same + 1 : 0;
            last = y;
        }
    }

    async function activateSonarSearch(targetUID) {
        if (isScanning) { showToast('⚠️ Scan em curso, tenta daqui a 1s.', 'warning'); return; }
        isScanning = true;

        const pill = $('x_sonar_pill');
        const gname = (activeGamesDB[targetUID] && activeGamesDB[targetUID].name) || 'jogo';
        // só aparece se a busca demorar; discreta e sem tapar a página
        const pillTimer = setTimeout(() => {
            if (!pill) return;
            pill.querySelector('span').textContent = 'A localizar ' + gname + '…';
            pill.classList.add('show');
        }, 300);
        const startY = window.scrollY;
        const vh = window.innerHeight || 800;
        const maxY = () => Math.max(0, document.documentElement.scrollHeight - vh);
        const tryAt = async (y) => {
            window.scrollTo({ top: Math.max(0, Math.min(maxY(), y)), behavior: 'auto' });
            await sleep(140);
            recordPositions();
            return findTarget(targetUID);
        };
        // salta para onde o jogo foi visto e abre em leque à volta
        const nearMemory = async () => {
            const cached = sonarPos.get(targetUID);
            if (cached == null) return null;
            const base = cached - vh / 2;
            let c = await tryAt(base);
            for (let k = 1; !c && k <= 6; k++) {
                c = await tryAt(base + k * vh * 0.8);
                if (!c) c = await tryAt(base - k * vh * 0.8);
            }
            return c;
        };

        try {
            let c = findTarget(targetUID);
            if (!c) c = await nearMemory();
            if (!c) {
                // nunca visto: varrimento desde o topo (fica em memória para a próxima vez)
                for (let y = 0, i = 0; !c && i < 150; i++, y += vh * 0.8) {
                    c = await tryAt(y);
                    if (y > maxY() + vh) break;
                }
            }

            if (!c) {
                window.scrollTo({ top: startY, behavior: 'auto' });
                const fg = FEED.games.get(String(targetUID).replace(/^id_/, ''));
                if (fg && (FEED_DONE[fg.st] || FEED_VOID[fg.st] || feedLooksOver(fg))) showToast('❌ O jogo já acabou.', 'error');
                else if (fg && FEED_LIVE[fg.st]) showToast('⚠️ Jogo ao vivo, mas não está na lista (filtro, data ou grupo fechado?).', 'warning', 4500);
                else showToast('⚠️ Jogo não encontrado na página.', 'warning');
                return;
            }

            const info0 = extractGameInfo(c);
            if (info0.gameTime === 'FT') {
                const done = activeGamesDB[targetUID];
                if (done) recordHistory(done, info0.score || done.score);
                delete activeGamesDB[targetUID];
                saveDB();
                renderLiveList();
                window.scrollTo({ top: startY, behavior: 'auto' });
                showToast('❌ Jogo acabou.', 'error');
                return;
            }

            if (!$('x_sonar_back')) sonarOrigin = startY;   // mantém o ponto de partida original

            // centrar e confirmar: volta a procurar o elemento depois de cada scroll, porque a página
            // pode reciclar/redesenhar as linhas e o elemento anterior deixar de ser o jogo certo
            let placed = false;
            for (let attempt = 0; attempt < 3 && !placed; attempt++) {
                if (!c) c = findTarget(targetUID) || await nearMemory();
                if (!c) break;
                const r = c.getBoundingClientRect();
                const delta = r.top + r.height / 2 - vh / 2;
                if (Math.abs(delta) > vh * 0.3) {
                    const far = Math.abs(delta) > vh * 1.2;
                    window.scrollTo({ top: Math.max(0, Math.min(maxY(), window.scrollY + delta)), behavior: (far || attempt > 0) ? 'auto' : 'smooth' });
                    await settleScroll();
                }
                await sleep(120);
                c = findTarget(targetUID);
                if (c) { const r2 = c.getBoundingClientRect(); placed = r2.top >= 0 && r2.bottom <= vh; }
            }

            if (!c) { showToast('⚠️ O jogo desapareceu da lista durante a procura.', 'warning'); return; }

            keepFocus(targetUID, 8000);
            notePos(targetUID, c);
            if (sonarOrigin !== null && Math.abs(window.scrollY - sonarOrigin) > 80) showBackButton();
            const info = extractGameInfo(c);
            showToast(`🎯 ${escapeHTML(info.homeTeam || '')} vs ${escapeHTML(info.awayTeam || '')} · ${escapeHTML(info.gameTime || '')} · ${escapeHTML(info.score || '')}`, 'success', 3500);
        } catch (err) {
            console.error('Erro no Sonar:', err);
        } finally {
            clearTimeout(pillTimer);
            if (pill) pill.classList.remove('show');
            isScanning = false;
        }
    }

    //======================================================================
    // 16. DRAG UTILITY
    //======================================================================

    function getPoint(e) {
        return e.type.includes('touch')
            ? { x: e.touches[0].clientX, y: e.touches[0].clientY }
            : { x: e.clientX, y: e.clientY };
    }

    function applyTheme() {
        const panel = $('x_panel');
        if (!panel) return;
        let light = settings.ui.theme === 'light';
        if (settings.ui.theme === 'auto') {
            try { light = window.matchMedia('(prefers-color-scheme: light)').matches; } catch (e) { light = false; }
        }
        panel.classList.toggle('x-light', light);
    }

    // Repõe o tamanho e a posição guardados (sempre dentro do ecrã)
    function restorePanelLayout(panel) {
        const u = settings.ui;
        const vw = window.innerWidth || 1200, vh = window.innerHeight || 800;
        if (u.panelW >= 340) panel.style.width = Math.min(u.panelW, vw - 16) + 'px';
        if (u.listH >= 120) panel.style.setProperty('--x-listh', u.listH + 'px');
        if (typeof u.panelX === 'number' && typeof u.panelY === 'number') {
            const w = Math.min(u.panelW >= 340 ? u.panelW : 390, vw - 16);
            panel.style.left = Math.max(0, Math.min(u.panelX, vw - w - 4)) + 'px';
            panel.style.top = Math.max(0, Math.min(u.panelY, vh - 140)) + 'px';
            panel.style.right = 'auto';
        }
    }
    function clampPanel(panel) {
        if (!panel || panel.classList.contains('x-hidden')) return;
        const r = panel.getBoundingClientRect();
        const vw = window.innerWidth || 1200, vh = window.innerHeight || 800;
        let l = r.left, t = r.top;
        if (r.right > vw) l = Math.max(0, vw - r.width);
        if (r.left < 0) l = 0;
        if (r.bottom > vh) t = Math.max(0, vh - r.height);
        if (r.top < 0) t = 0;
        if (l !== r.left || t !== r.top) { panel.style.left = l + 'px'; panel.style.top = t + 'px'; panel.style.right = 'auto'; }
        panel.style.maxHeight = Math.max(220, vh - t - 8) + 'px';
    }

    function setupDragAndToggle(fab, panel) {
        let fabDragging = false, fSX, fSY, fIL, fIT;

        const onFMove = (e) => {
            const p = getPoint(e);
            const dx = p.x - fSX, dy = p.y - fSY;
            if (!fabDragging && Math.sqrt(dx * dx + dy * dy) > 5) fabDragging = true;
            if (!fabDragging) return;
            fab.style.left = (fIL + dx) + 'px';
            fab.style.top = (fIT + dy) + 'px';
            fab.style.right = 'auto';
            fab.style.bottom = 'auto';
        };
        const onFUp = () => {
            document.removeEventListener('mousemove', onFMove);
            document.removeEventListener('touchmove', onFMove);
            document.removeEventListener('mouseup', onFUp);
            document.removeEventListener('touchend', onFUp);
            if (!fabDragging) {
                panel.classList.toggle('x-hidden');
                if (!panel.classList.contains('x-hidden')) { clampPanel(panel); renderLiveList(); }
                wakeFab();
            }
        };
        const onFDown = (e) => {
            if (e.type === 'mousedown' && e.button !== 0) return;
            fabDragging = false;
            wakeFab();
            const p = getPoint(e);
            fSX = p.x; fSY = p.y;
            fIL = fab.offsetLeft; fIT = fab.offsetTop;
            document.addEventListener('mousemove', onFMove, { passive: false });
            document.addEventListener('touchmove', onFMove, { passive: false });
            document.addEventListener('mouseup', onFUp);
            document.addEventListener('touchend', onFUp);
        };
        fab.addEventListener('pointerenter', wakeFab);
        fab.addEventListener('mousedown', onFDown);
        fab.addEventListener('touchstart', onFDown, { passive: false });

        const h = panel.querySelector('.x-drag-handle');
        if (!h) return;

        let hSX, hSY, pSL, pST;
        const hMove = (e) => {
            const p = getPoint(e);
            panel.style.left = (pSL + (p.x - hSX)) + 'px';
            panel.style.top = (pST + (p.y - hSY)) + 'px';
            panel.style.right = 'auto';
        };
        const hUp = () => {
            document.removeEventListener('mousemove', hMove);
            document.removeEventListener('touchmove', hMove);
            document.removeEventListener('mouseup', hUp);
            document.removeEventListener('touchend', hUp);
            clampPanel(panel);
            settings.ui.panelX = panel.offsetLeft; settings.ui.panelY = panel.offsetTop;
            saveSettings();
        };
        const hDown = (e) => {
            if (e.type === 'mousedown' && e.button !== 0) return;
            const p = getPoint(e);
            hSX = p.x; hSY = p.y;
            pSL = panel.offsetLeft; pST = panel.offsetTop;
            document.addEventListener('mousemove', hMove, { passive: false });
            document.addEventListener('touchmove', hMove, { passive: false });
            document.addEventListener('mouseup', hUp);
            document.addEventListener('touchend', hUp);
        };
        h.addEventListener('mousedown', hDown);
        h.addEventListener('touchstart', hDown, { passive: false });

        // redimensionar pelo canto inferior direito
        const rz = panel.querySelector('.x-resize');
        if (!rz) return;
        let rSX, rSY, rW, rLH, rRight;
        const rMove = (e) => {
            const p = getPoint(e);
            const vh = window.innerHeight || 800;
            const w = Math.max(340, Math.min(rRight - 4, rW - (p.x - rSX)));     // arrastar para a esquerda alarga
            const lh = Math.max(120, Math.min(Math.max(140, vh - panel.offsetTop - 250), rLH + (p.y - rSY)));
            panel.style.width = w + 'px';
            panel.style.left = (rRight - w) + 'px';
            panel.style.setProperty('--x-listh', lh + 'px');
            if (e.cancelable) e.preventDefault();
        };
        const rUp = () => {
            document.removeEventListener('mousemove', rMove);
            document.removeEventListener('touchmove', rMove);
            document.removeEventListener('mouseup', rUp);
            document.removeEventListener('touchend', rUp);
            settings.ui.panelW = panel.offsetWidth;
            settings.ui.listH = parseInt(panel.style.getPropertyValue('--x-listh'), 10) || settings.ui.listH || 0;
            settings.ui.panelX = panel.offsetLeft; settings.ui.panelY = panel.offsetTop;
            saveSettings();
            clampPanel(panel);
        };
        const rDown = (e) => {
            if (e.type === 'mousedown' && e.button !== 0) return;
            if (e.cancelable) e.preventDefault();
            const p = getPoint(e);
            rSX = p.x; rSY = p.y; rW = panel.offsetWidth; rLH = settings.ui.listH >= 120 ? settings.ui.listH : 300;
            rRight = panel.offsetLeft + panel.offsetWidth;
            panel.style.left = panel.offsetLeft + 'px'; panel.style.top = panel.offsetTop + 'px'; panel.style.right = 'auto';
            document.addEventListener('mousemove', rMove, { passive: false });
            document.addEventListener('touchmove', rMove, { passive: false });
            document.addEventListener('mouseup', rUp);
            document.addEventListener('touchend', rUp);
        };
        rz.addEventListener('mousedown', rDown);
        rz.addEventListener('touchstart', rDown, { passive: false });
    }

    //======================================================================
    // 17. INIT BOOTSTRAP
    //======================================================================

    async function waitForGames(maxMs) {
        const t0 = Date.now();
        while (Date.now() - t0 < maxMs && detectGameContainers().length === 0) {
            await sleep(500);
        }
    }

    const initInt = setInterval(() => {
        if (!document.body) return;
        clearInterval(initInt);

        createUI();
        startAntiThrottlingWorker();
        observerActive = setupObserver();

        showToast(`⏳ V21.1 a carregar (${STARTUP_DELAY / 1000}s)...`, 'warning', STARTUP_DELAY - 500);

        setTimeout(async () => {
            await waitForGames(WAIT_GAMES_MAX);
            // dá algum tempo ao feed (lista + MQTT) antes de recorrer ao scroll
            if (settings.dataSource === 'auto') {
                for (let i = 0; i < 20 && !(FEED.listAt && FEED.beatAt); i++) await sleep(500);
            }
            if (feedUsable()) {
                feedReady = true;
                feedProcess(null, true);
                feedSweep();
                isFirstRun = false;
                lastSeenGames = Date.now();
                renderLiveList();
                showToast('📡 Feed ativo — sem scroll. Boa Sorte!', 'success', 2500);
            } else {
                feedReady = true;
                await fullPageScan(true);
                isFirstRun = false;
                lastSeenGames = Date.now();
                renderLiveList();
                showToast('🚀 Trator Fantasma Armado (feed indisponível).', 'success', 2500);
            }
        }, STARTUP_DELAY);
    }, 300);

})();
