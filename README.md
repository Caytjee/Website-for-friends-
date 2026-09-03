# OreTime

**Community gaming hub for Saturday nights with friends.**

Live site: **[https://oretimers.de/](https://oretimers.de/)**

Discord login, weekly game votes, a cosmetics shop with OreCoins, Battle Pass, WatchOut beacons, Steam library checks, and a live activity feed — all in one place for the OreTimers crew.

> Started as a tiny “website for friends.” Grew into a full Flask app. Same crew energy, bigger toolkit.

---

## What’s inside

| Area | Features |
|------|----------|
| **Saturday Command** | Vote for the next session game, radar (IN / MAYBE / OUT), Game of the Week hero |
| **Shop & economy** | OreCoins, avatar borders, custom banners, crates, Flip Pit, trade, Daily Ore |
| **Battle Pass** | Season XP track, exclusive cosmetics, claimable rewards |
| **Community** | WatchOut LFG beacons, wishlist / requests, armory PC setups, highlights |
| **Steam** | Library ownership, rivals playtime pit, game stack |
| **Live** | Socket activity feed, notifications, Discord webhooks for session pings |
| **Polish** | Themes, 7 languages (EN / DE / PL / CS / HR / FR / JA), admin panel, changelog |

---

## Stack

- **Backend:** Python, Flask, Flask-SocketIO, SQLite
- **Frontend:** Jinja templates, vanilla JS, CSS (no heavy SPA framework)
- **Auth:** Discord OAuth2
- **Integrations:** Steam Web API, Discord webhooks

---

## Quick start

### 1. Clone & install

```bash
git clone https://github.com/Caytjee/Website-for-friends-.git
cd Website-for-friends-
python -m venv .venv

# Windows
.venv\Scripts\activate
# macOS / Linux
source .venv/bin/activate

pip install -r requirements.txt
```

### 2. Environment

```bash
cp .env.example .env
```

Fill in at least:

| Variable | Purpose |
|----------|---------|
| `SECRET_KEY` | Flask session secret |
| `STEAM_API_KEY` | Steam Web API |
| `DISCORD_CLIENT_ID` / `DISCORD_CLIENT_SECRET` | Discord OAuth app |
| `DISCORD_REDIRECT_URI` | Must match Discord Developer Portal, e.g. `https://oretimers.de/callback` |
| `PORT` | Listen port (default `46281`) |
| `PUBLIC_SITE_URL` | Public URL, e.g. `https://oretimers.de` |
| `ADMINS` | Comma-separated Discord usernames with admin access |

Optional: webhook URL, ping role ID, founder / host display names, etc. — see `.env.example`.

**Never commit `.env`.** Keep secrets only on the host.

### 3. Discord app

1. [Discord Developer Portal](https://discord.com/developers/applications) → your app → OAuth2  
2. Add redirect: `https://your-domain/callback` (same as `DISCORD_REDIRECT_URI`)  
3. Scopes used: `identify`

### 4. Run

```bash
python flask_app.py
```

Open `http://127.0.0.1:46281/` (or your `PORT`). First visit creates `database.db` automatically.

---

## Project layout

```
flask_app.py          # App, routes, shop, votes, webhooks, SocketIO
templates/            # Jinja pages (home, shop, events, pass, …)
static/i18n/          # Language packs + i18n.js
static/img/           # Static images
.env.example          # Env template (safe to commit)
requirements.txt
```

SQLite file `database.db` is created at runtime and should stay out of git.

---

## Deploy notes

- Public domain for production: **https://oretimers.de/**  
- App still listens on the configured `PORT` behind the host / reverse proxy  
- Set `DISCORD_REDIRECT_URI` and Discord redirects to the **HTTPS domain**, not the raw host IP  
- Private hoster — host name is not public by design  

---

## Version

Current UI version: **2.8** (see in-app Changelog).

---

## License / vibe

Built for friends. Fork it, break it, make your own Saturday protocol.
