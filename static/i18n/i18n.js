/* OreTime UI i18n — static dictionaries only. Do not load translate.google.com. */
(function (global) {
    'use strict';
    var LANGS = ['en', 'de', 'pl', 'cs', 'hr', 'fr', 'ja'];
    var COOKIE = 'ot_lang';
    var STORE = 'ot_lang';
    var catalog = global.OT_I18N || {};
    var lang = global.OT_LANG || 'en';

    function readCookie() {
        try {
            var m = document.cookie.match(/(?:^|; )ot_lang=([^;]*)/);
            if (!m) return null;
            var v = decodeURIComponent(m[1]);
            return LANGS.indexOf(v) >= 0 ? v : null;
        } catch (e) {
            return null;
        }
    }

    function readStored() {
        var cookie = readCookie();
        if (cookie) return cookie;
        try {
            var v = localStorage.getItem(STORE);
            if (LANGS.indexOf(v) >= 0) return v;
        } catch (e) {}
        return 'en';
    }

    function persist(code) {
        try { localStorage.setItem(STORE, code); } catch (e) {}
        document.cookie = COOKIE + '=' + encodeURIComponent(code) + ';path=/;max-age=31536000;SameSite=Lax';
    }

    function nested(obj, key) {
        if (!obj || !key) return null;
        var cur = obj;
        var parts = key.split('.');
        for (var i = 0; i < parts.length; i++) {
            if (!cur || typeof cur !== 'object' || !(parts[i] in cur)) return null;
            cur = cur[parts[i]];
        }
        return typeof cur === 'string' ? cur : null;
    }

    function t(key, vars) {
        var s = nested(catalog, key);
        if (s == null) s = key;
        if (vars) {
            Object.keys(vars).forEach(function (k) {
                s = s.split('{' + k + '}').join(String(vars[k]));
            });
        }
        return s;
    }

    function apply(root) {
        var scope = root || document;
        if (!scope.querySelectorAll) return;
        scope.querySelectorAll('[data-i18n]').forEach(function (el) {
            var key = el.getAttribute('data-i18n');
            if (!key) return;
            var htmlMode = el.hasAttribute('data-i18n-html');
            if (!htmlMode && el.children.length) return;
            var vars = null;
            var raw = el.getAttribute('data-i18n-vars');
            if (raw) {
                try { vars = JSON.parse(raw); } catch (e) { vars = null; }
            }
            var val = t(key, vars);
            if (htmlMode) el.innerHTML = val;
            else el.textContent = val;
        });
        scope.querySelectorAll('[data-i18n-placeholder]').forEach(function (el) {
            var key = el.getAttribute('data-i18n-placeholder');
            if (key) el.setAttribute('placeholder', t(key));
        });
        scope.querySelectorAll('[data-i18n-aria]').forEach(function (el) {
            var key = el.getAttribute('data-i18n-aria');
            if (key) el.setAttribute('aria-label', t(key));
        });
        scope.querySelectorAll('[data-i18n-title]').forEach(function (el) {
            var key = el.getAttribute('data-i18n-title');
            if (key) el.setAttribute('title', t(key));
        });
        scope.querySelectorAll('[data-i18n-equipped]').forEach(function (el) {
            el.setAttribute('data-equipped-label', t('inventory.equipped'));
        });
        document.documentElement.lang = lang;
        document.documentElement.setAttribute('data-lang', lang);
        var sel = document.getElementById('ot-lang-select');
        if (sel && sel.value !== lang) sel.value = lang;
        try {
            document.dispatchEvent(new CustomEvent('ot-lang-change', { detail: { lang: lang } }));
        } catch (e) {}
    }

    function setCatalog(next, nextLang) {
        catalog = next || {};
        lang = nextLang;
        global.OT_I18N = catalog;
        global.OT_LANG = lang;
        persist(lang);
        apply();
    }

    function setLang(code) {
        if (LANGS.indexOf(code) < 0) code = 'en';
        if (code === lang && catalog && Object.keys(catalog).length) {
            persist(code);
            apply();
            return Promise.resolve(code);
        }
        return fetch('/static/i18n/' + code + '.json', { credentials: 'same-origin' })
            .then(function (r) { return r.json(); })
            .then(function (data) {
                setCatalog(data, code);
                return code;
            })
            .catch(function () {
                persist(code);
                lang = code;
                apply();
                return code;
            });
    }

    global.OTI18n = {
        t: t,
        apply: apply,
        setLang: setLang,
        getLang: function () { return lang; },
        langs: LANGS.slice()
    };

    lang = readStored();
    if (LANGS.indexOf(lang) < 0) lang = 'en';
    document.documentElement.lang = lang;

    function boot() {
        if (global.OT_LANG === lang && catalog && Object.keys(catalog).length) {
            persist(lang);
            apply();
            return;
        }
        setLang(lang);
    }

    if (document.readyState === 'loading') {
        document.addEventListener('DOMContentLoaded', boot);
    } else {
        boot();
    }

    document.addEventListener('change', function (e) {
        var el = e.target;
        if (!el || el.id !== 'ot-lang-select') return;
        e.stopPropagation();
        setLang(el.value);
    });
})(window);
