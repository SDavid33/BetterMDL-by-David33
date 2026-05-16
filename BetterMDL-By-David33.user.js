// ==UserScript==
// @name         BetterMDL v1.2.28 by David33
// @namespace    https://mydramalist.com/
// @version      1.2.28
// @description  A userscript to enhance MyDramaList, making it cleaner, friendlier & more modern.
// @license      MIT
// @match        https://mydramalist.com/*
// @grant        GM_xmlhttpRequest
// @grant        GM.xmlHttpRequest
// @connect      api.jikan.moe
// @connect      graphql.anilist.co
// @connect      api.themoviedb.org
// @connect      api.mydramalist.com
// @connect      api.mangaupdates.com
// @connect      www.naiin.com
// @connect      www.mebmarket.com
// @connect      www.novelupdates.com
// @connect      en.namu.wiki
// @connect      simkl.com
// @connect      asianwiki.com
// @run-at       document-idle
// ==/UserScript==

(() => {
  'use strict';

  const NS = 'bettermdl-people-final';
  const STYLE_ID = `${NS}-style`;
  const FA_LINK_ID = `${NS}-fa-link`;
  const SETTINGS_PANEL_ID = `${NS}-settings-panel`;
  const STORAGE_SETTINGS = `${NS}:settings:v2`;
  const STORAGE_CACHE_RESET = `${NS}:cache-reset:v1`;
  const STORAGE_CACHE_MAINT = `${NS}:cache-maint:v1`;
  const STORAGE_COLLAPSE = `${NS}:collapse:v2`;
  const STORAGE_FILMOGRAPHY_UI = `${NS}:filmography-ui:v1`;
  const STORAGE_FRIENDS_LIST = `${NS}:friends-list:v3`;
  const STORAGE_FRIENDS_RATINGS = `${NS}:friends-ratings:v11`;
  const STORAGE_FRIENDS_WATCHED = `${NS}:friends-watched:v11`;
  const STORAGE_ORIGINAL_WORK = `${NS}:original-work:v38`;
  const STORAGE_PORTAL_LINKS = `${NS}:portal-links:v3`;
  const STORAGE_PROFILE_COUNTRY_STATS = `${NS}:profile-country-stats:v23`;
  const STORAGE_PROFILE_COUNTRY_LIST_CACHE = `${NS}:profile-country-list-cache:v1`;
  const ORIGINAL_WORK_BOX_ID = `${NS}-original-work-box`;
  const FRIENDS_BOX_ID = `${NS}-friends-rating-box`;
  const WATCHED_FRIENDS_BOX_ID = `${NS}-watched-friends-box`;
  const PORTALS_BOX_ID = `${NS}-portal-links`;
  const FILMOGRAPHY_ORDER_ATTR = `data-${NS}-order`;
  const TMDB_API_URL = 'https://api.themoviedb.org/3';
  const TMDB_API_KEY = 'd12b33d3f4fb8736dc06f22560c4f8d4';
  const DAY_MS = 24 * 60 * 60 * 1000;
  const FRIENDS_LIST_TTL_MS = 1 * DAY_MS;
  const FRIENDS_RATINGS_TTL_MS = 1 * DAY_MS;
  const ORIGINAL_WORK_TTL_MS = 7 * DAY_MS;
  const PORTAL_LINKS_TTL_MS = 14 * DAY_MS;
  const PROFILE_COUNTRY_STATS_TTL_MS = 7 * DAY_MS;
  const PROFILE_COUNTRY_STATS_LOAD_TIMEOUT_MS = 15 * 1000;
  const PROFILE_COUNTRY_TITLE_ENRICH_LIMIT = 120;
  const STATUS_CONFIG = {
    1: { key: 'currently_watching', icon: 'fas fa-spinner', color: '#85c1dc', label: 'Currently Watching' },
    2: { key: 'completed', icon: 'fas fa-check', color: '#a6d189', label: 'Completed' },
    3: { key: 'plan_to_watch', icon: 'far fa-clock', color: '#ca9ee6', label: 'Plan to Watch' },
    4: { key: 'on_hold', icon: 'fas fa-pause', color: '#e5c890', label: 'On Hold' },
    5: { key: 'dropped', icon: 'fas fa-heart-broken', color: '#e78284', label: 'Dropped' },
    6: { key: 'not_interested', icon: 'fas fa-minus-circle', color: '#bbbbbb', label: 'Not Interested' },
  };

  const FEATURE_LABELS = {
    peopleStatusSummary: 'People: Status Summary Boxes',
    peopleFilmographyIcons: 'Filmography: Status Icons',
    peopleFilmographyControls: 'Filmography: Sort by / Large View',
    peopleFilmographyLargeViewDefault: 'Filmography: Large View',
    profileCountryStats: 'Profile: Titles by Country',
    peopleAutoHideSections: 'People page: Hide Bio, Photos, Articles, Comments',
    titleAutoHideSections: 'Title page: Hide Photos, Reviews, Recent Discussions, Comments',
    titleSynopsisHide: 'Title page: Hide Synopsis',
    titleNativeTitleFirst: 'Title: Native title first',
    titleOriginalWork: 'Title: Original Work box',
    titlePortalIcons: 'Title: Portal icons under poster',
    titleRatedByFriends: 'Title: Rated by Friends box',
    titleWatchedByFriends: 'Title: Watched by Friends box',
    nativeSnsIcons: 'People/Title: SNS icons',
    titleTrailerButton: 'Title: Watch Trailer button',
    titleAmazonButton: 'Title: Buy on Amazon button',
  };

  const SOURCE_TYPE_MAP = {
    manga: ['manga'],
    manhwa: ['manhwa', 'manga'],
    manhua: ['manhua', 'manga'],
    comic: ['manga'],
    webtoon: ['manhwa', 'manga'],
    novel: ['novel'],
    'light novel': ['novel'],
    'web novel': ['novel'],
    book: ['novel'],
    anime: ['anime'],
    'rpg game': [],
    game: [],
  };

  const ORIGINAL_WORK_PROVIDER_ORDER = {
    eastAsia: ['mangaupdates', 'novelupdates', 'anilist', 'myanimelist', 'namuwiki'],
    thai: ['mebmarket', 'naiin'],
    fallback: ['mangaupdates', 'novelupdates'],
  };
  const ORIGINAL_WORK_MAX_QUERIES_PER_PROVIDER = 2;

  const originalWorkCache = new Map();
  const tmdbLookupCache = new Map();
  const portalLinksCache = new Map();
  const friendsRatingsCache = new Map();
  const watchedFriendsCache = new Map();
  const friendsListCache = new Map();
  const friendListMatchesCache = new Map();
  const friendProfileCache = new Map();
  const statusRequestCache = new Map();
  let observer = null;
  let bootTimer = null;
  let lastOriginalWorkRenderKey = '';
  let lastPortalRenderKey = '';
  let lastFriendsRenderKey = '';
  let lastWatchedFriendsRenderKey = '';
  let lastObservedHref = location.href;
  let titlePageBootedHref = '';
  let titleTabRefreshTimer = null;
  let dramalistCollectorHref = '';
  let dramalistCollectorScrollBound = false;
  let dramalistCollectorScrollTimer = null;
  let dramalistUndecidedScheduleKey = '';
  let bootInFlight = false;
  let bootQueued = false;
  let settingsPanelRendered = false;
  let filmographyMutationIgnoreUntil = 0;

  const q = (sel, root = document) => root.querySelector(sel);
  const qa = (sel, root = document) => Array.from(root.querySelectorAll(sel));
  const text = (el) => (el?.textContent || '').replace(/\s+/g, ' ').trim();
  const isPeoplePage = () => /^\/people\/\d+/.test(location.pathname);
  const isTitlePage = () => /^\/\d+(-|\/|$)/.test(location.pathname) && !isPeoplePage();
  const isProfilePage = () => /^\/profile\/[^/?#]+/.test(location.pathname);
  const isDramalistPage = () => /^\/dramalist\/[^/?#]+/.test(location.pathname);
  const isAccountSettingsPage = () => /^\/account\/(?:profile|general|security|notifications|apps|subscriptions|blocking|list[-_]?styles|widgets)\/?$/i.test(location.pathname);
  const safeJsonParse = (raw, fallback) => { try { return raw ? JSON.parse(raw) : fallback; } catch { return fallback; } };
  const getCollapseState = () => safeJsonParse(localStorage.getItem(STORAGE_COLLAPSE), {});
  const setCollapseState = (value) => localStorage.setItem(STORAGE_COLLAPSE, JSON.stringify(value));
  const getLocalCache = (key) => safeJsonParse(localStorage.getItem(key), {});
  const setLocalCache = (key, value) => localStorage.setItem(key, JSON.stringify(value));
  const getFilmographyUiState = () => safeJsonParse(localStorage.getItem(STORAGE_FILMOGRAPHY_UI), {});
  const setFilmographyUiState = (value) => localStorage.setItem(STORAGE_FILMOGRAPHY_UI, JSON.stringify(value));
  const isDebugEnabled = () => localStorage.getItem(`${NS}:debug`) === '1';
  const setDebugCache = (key, value) => {
    if (!isDebugEnabled()) return;
    try {
      localStorage.setItem(`${NS}:debug:${key}`, JSON.stringify(value));
    } catch {}
  };
  const escapeHtml = (value) => String(value ?? '').replace(/[&<>"']/g, (char) => ({
    '&': '&amp;',
    '<': '&lt;',
    '>': '&gt;',
    '"': '&quot;',
    "'": '&#39;',
  }[char]));

  function getDefaultSettings() {
    return {
      statuses: Object.fromEntries(Object.entries(STATUS_CONFIG).map(([id, config]) => [
        config.key,
        { icon: config.icon, color: config.color },
      ])),
      labels: {
        undecidedStatus: 'Undecided',
      },
      features: {
        peopleStatusSummary: true,
        peopleFilmographyIcons: true,
        peopleFilmographyControls: true,
        peopleFilmographyLargeViewDefault: false,
        profileCountryStats: true,
        showHideSections: true,
        peopleAutoHideSections: false,
        titleOriginalWork: true,
        titlePortalIcons: true,
        titleRatedByFriends: true,
        titleWatchedByFriends: true,
        nativeSnsIcons: true,
        titleTrailerButton: true,
        titleAmazonButton: true,
        titleNativeTitleFirst: false,
        titleSynopsisHide: false,
        titleAutoHideSections: false,
      },
    };
  }

  function mergeSettingsWithDefaults(settings) {
    const defaults = getDefaultSettings();
    const incoming = settings && typeof settings === 'object' ? settings : {};
    const merged = {
      statuses: {},
      labels: { ...defaults.labels, ...(incoming.labels || {}) },
      features: { ...defaults.features, ...(incoming.features || {}) },
    };

    merged.labels.undecidedStatus = collapseWhitespace(merged.labels.undecidedStatus).slice(0, 40) || defaults.labels.undecidedStatus;

    Object.entries(defaults.statuses).forEach(([key, value]) => {
      const next = incoming.statuses?.[key] || {};
      merged.statuses[key] = {
        icon: collapseWhitespace(next.icon || value.icon),
        color: /^#[0-9a-f]{6}$/i.test(String(next.color || '')) ? String(next.color) : value.color,
      };
    });

    return merged;
  }

  function getSettings() {
    return mergeSettingsWithDefaults(safeJsonParse(localStorage.getItem(STORAGE_SETTINGS), {}));
  }

  function saveSettings(value) {
    localStorage.setItem(STORAGE_SETTINGS, JSON.stringify(mergeSettingsWithDefaults(value)));
  }

  function resetSettings() {
    localStorage.setItem(STORAGE_SETTINGS, JSON.stringify(getDefaultSettings()));
  }

  function resetLegacyBetterMdlCache() {
    if (localStorage.getItem(STORAGE_CACHE_RESET) === 'done') return;
    [
      `${NS}:settings:v1`,
      `${NS}:friends-list:v1`,
      `${NS}:friends-ratings:v4`,
      `${NS}:friends-watched:v4`,
      `${NS}:original-work:v1`,
      `${NS}:portal-links:v1`,
    ].forEach((key) => localStorage.removeItem(key));
    localStorage.setItem(STORAGE_CACHE_RESET, 'done');
    resetSettings();
  }

  function compactCacheStore(storageKey) {
    const store = getLocalCache(storageKey);
    if (!store || typeof store !== 'object' || Array.isArray(store)) return;

    const now = Date.now();
    let changed = false;
    Object.keys(store).forEach((key) => {
      const entry = store[key];
      if (!entry || typeof entry !== 'object') return;
      if ('expiresAt' in entry && (!entry.expiresAt || entry.expiresAt < now)) {
        delete store[key];
        changed = true;
      }
    });

    if (changed) {
      if (Object.keys(store).length) {
        setLocalCache(storageKey, store);
      } else {
        localStorage.removeItem(storageKey);
      }
    }
  }

  function maintainBetterMdlCache() {
    const today = new Date().toISOString().slice(0, 10);
    if (localStorage.getItem(STORAGE_CACHE_MAINT) === today) return;

    [
      STORAGE_FRIENDS_LIST,
      STORAGE_FRIENDS_RATINGS,
      STORAGE_FRIENDS_WATCHED,
      STORAGE_ORIGINAL_WORK,
      STORAGE_PORTAL_LINKS,
      STORAGE_PROFILE_COUNTRY_STATS,
    ].forEach(compactCacheStore);

    localStorage.removeItem(`${NS}:debug:country:last`);
    localStorage.removeItem(`${NS}:country-debug:last`);
    localStorage.setItem(STORAGE_CACHE_MAINT, today);
  }

  function getStatusConfigMap() {
    const settings = getSettings();
    return Object.fromEntries(Object.entries(STATUS_CONFIG).map(([id, config]) => [
      Number(id),
      {
        ...config,
        icon: settings.statuses?.[config.key]?.icon || config.icon,
        color: settings.statuses?.[config.key]?.color || config.color,
      },
    ]));
  }

  function isFeatureEnabled(featureKey) {
    if (featureKey === 'showHideSections') return true;
    return !!getSettings().features?.[featureKey];
  }

  function getPersistedCacheEntry(storageKey, entryKey, validate) {
    if (!entryKey) return null;
    const store = getLocalCache(storageKey);
    const cached = store?.[entryKey];
    if (!cached?.expiresAt || cached.expiresAt < Date.now()) return null;
    const value = cached.value;
    if (typeof validate === 'function' && !validate(value)) return null;
    return value;
  }

  function hasPersistedCacheEntry(storageKey, entryKey) {
    if (!entryKey) return false;
    const store = getLocalCache(storageKey);
    const cached = store?.[entryKey];
    return !!(cached?.expiresAt && cached.expiresAt >= Date.now());
  }

  function persistCacheEntry(storageKey, entryKey, value, ttlMs = DAY_MS) {
    if (!entryKey) return;
    const store = getLocalCache(storageKey);
    store[entryKey] = {
      expiresAt: Date.now() + ttlMs,
      value,
    };
    setLocalCache(storageKey, store);
  }

  function getCurrentUsername() {
    const profileLink = q('div.mdl-dropdown-content a[href^="/profile/"], .nav .dropdown-menu a[href^="/profile/"], a[href^="/profile/"][class*="dropdown"]');
    const href = profileLink?.getAttribute('href') || '';
    const match = href.match(/\/profile\/([^/?#]+)/i);
    return match ? decodeURIComponent(match[1]) : '';
  }

  function getProfileUsernameFromPath() {
    const match = location.pathname.match(/^\/profile\/([^/?#]+)/i);
    return match ? decodeURIComponent(match[1]) : '';
  }

  function getDramalistPathContext() {
    const match = location.pathname.match(/^\/dramalist\/([^/?#]+)(?:\/([^/?#]+))?/i);
    if (!match) return null;
    const rawStatus = collapseWhitespace(match[2] || '').toLowerCase();
    const statusMap = {
      watching: 'watching',
      currently_watching: 'watching',
      completed: 'completed',
      on_hold: 'on_hold',
      'on-hold': 'on_hold',
      dropped: 'dropped',
      plan_to_watch: 'plan_to_watch',
      not_interested: 'not_interested',
    };
    return {
      username: decodeURIComponent(match[1] || ''),
      status: statusMap[rawStatus] || '',
    };
  }

  function getDramalistUsernameFromPage() {
    const directLink = q('a[href^="/dramalist/"]');
    const href = directLink?.getAttribute('href') || '';
    const match = href.match(/^\/dramalist\/([^/?#]+)/i);
    return match ? decodeURIComponent(match[1]) : '';
  }

  function parseRgbColor(value) {
    const match = String(value || '').match(/rgba?\((\d+)\s*,\s*(\d+)\s*,\s*(\d+)/i);
    if (!match) return null;
    return {
      r: Number(match[1]),
      g: Number(match[2]),
      b: Number(match[3]),
    };
  }

  function mixColors(base, overlay, ratio) {
    const mix = (start, end) => Math.round(start + ((end - start) * ratio));
    return {
      r: mix(base.r, overlay.r),
      g: mix(base.g, overlay.g),
      b: mix(base.b, overlay.b),
    };
  }

  function toRgba(color, alpha) {
    return `rgba(${color.r}, ${color.g}, ${color.b}, ${alpha})`;
  }

  function findThemeSource(element) {
    let node = element;
    while (node && node !== document.body) {
      const style = getComputedStyle(node);
      const background = parseRgbColor(style.backgroundColor);
      if (background && !/rgba?\(\s*0\s*,\s*0\s*,\s*0\s*,\s*0\s*\)/i.test(style.backgroundColor) && style.backgroundColor !== 'transparent') {
        return {
          background,
          foreground: parseRgbColor(style.color) || { r: 255, g: 255, b: 255 },
        };
      }
      node = node.parentElement;
    }

    const bodyStyle = getComputedStyle(document.body);
    return {
      background: parseRgbColor(bodyStyle.backgroundColor) || { r: 32, g: 32, b: 32 },
      foreground: parseRgbColor(bodyStyle.color) || { r: 255, g: 255, b: 255 },
    };
  }

  function applyStatusThemeVars(target, sourceElement) {
    const { background, foreground } = findThemeSource(sourceElement);
    const bg = mixColors(background, foreground, 0.08);
    const border = mixColors(background, foreground, 0.18);
    target.style.setProperty(`--${NS}-status-bg`, toRgba(bg, 0.96));
    target.style.setProperty(`--${NS}-status-border`, toRgba(border, 0.95));
    target.style.setProperty(`--${NS}-status-text`, toRgba(foreground, 1));
  }

  function getToken() {
    const parts = (`; ${document.cookie}`).split('; jl_sess=');
    return parts.length === 2 ? parts.pop().split(';').shift() : '';
  }

  function getPersistedFriendsList(token) {
    const username = getCurrentUsername();
    if (!username) return null;
    const store = getLocalCache(STORAGE_FRIENDS_LIST);
    const cached = store?.[username];
    if (!cached?.expiresAt || cached.expiresAt < Date.now()) return null;
    if (!Array.isArray(cached.items)) return null;
    return cached.items.map(normalizeFriendUser).filter(Boolean);
  }

  function persistFriendsList(token, items) {
    const username = getCurrentUsername();
    if (!username) return;
    const store = getLocalCache(STORAGE_FRIENDS_LIST);
    store[username] = {
      expiresAt: Date.now() + FRIENDS_LIST_TTL_MS,
      items,
    };
    setLocalCache(STORAGE_FRIENDS_LIST, store);
  }

  function getPersistedFriendRatings(titleId) {
    const username = getCurrentUsername();
    if (!username || !titleId) return null;
    const store = getLocalCache(STORAGE_FRIENDS_RATINGS);
    const cached = store?.[`${username}:${titleId}`];
    if (!cached?.expiresAt || cached.expiresAt < Date.now()) return null;
    if (!Array.isArray(cached.items)) return null;
    return cached.items;
  }

  function persistFriendRatings(titleId, items) {
    const username = getCurrentUsername();
    if (!username || !titleId) return;
    const store = getLocalCache(STORAGE_FRIENDS_RATINGS);
    store[`${username}:${titleId}`] = {
      expiresAt: Date.now() + FRIENDS_RATINGS_TTL_MS,
      items,
    };
    setLocalCache(STORAGE_FRIENDS_RATINGS, store);
  }

  function getPersistedWatchedFriends(titleId) {
    const username = getCurrentUsername();
    if (!username || !titleId) return null;
    const store = getLocalCache(STORAGE_FRIENDS_WATCHED);
    const cached = store?.[`${username}:${titleId}`];
    if (!cached?.expiresAt || cached.expiresAt < Date.now()) return null;
    if (!Array.isArray(cached.items)) return null;
    return cached.items;
  }

  function persistWatchedFriends(titleId, items) {
    const username = getCurrentUsername();
    if (!username || !titleId) return;
    const store = getLocalCache(STORAGE_FRIENDS_WATCHED);
    store[`${username}:${titleId}`] = {
      expiresAt: Date.now() + FRIENDS_RATINGS_TTL_MS,
      items,
    };
    setLocalCache(STORAGE_FRIENDS_WATCHED, store);
  }

  function isValidPortalLinks(value) {
    return Array.isArray(value) && value.every((item) => item && typeof item.name === 'string' && typeof item.url === 'string');
  }

  function isValidOriginalWork(value) {
    return !!(value && typeof value.title === 'string' && collapseWhitespace(value.title));
  }

  function injectFontAwesome() {
    if (q(`#${FA_LINK_ID}`)) return;
    const link = document.createElement('link');
    link.id = FA_LINK_ID;
    link.rel = 'stylesheet';
    link.href = 'https://cdnjs.cloudflare.com/ajax/libs/font-awesome/5.15.4/css/all.min.css';
    document.head.appendChild(link);
  }

  function removeFontAwesome() {
    q(`#${FA_LINK_ID}`)?.remove();
  }

  function injectStyle() {
    if (q(`#${STYLE_ID}`)) return;
    const style = document.createElement('style');
    style.id = STYLE_ID;
    style.textContent = `
      .${NS}-toggle-row {
        display: flex;
        gap: 14px;
        align-items: center;
        margin: 8px 0 10px 15px;
        padding: 0;
        font-size: 14px;
        width: fit-content;
        max-width: 100%;
        border: 0;
        border-radius: 0;
        background: transparent;
        box-sizing: border-box;
      }
      .${NS}-people-toggle-row {
        margin-left: 15px !important;
      }
      .${NS}-toggle-row[data-kind="people-photos"],
      .${NS}-toggle-row[data-kind="filmo"] {
        margin-left: 0 !important;
      }
      .${NS}-toggle-link {
        color: var(--mdl-primary, #2f9fff) !important;
        cursor: pointer;
        user-select: none;
        white-space: nowrap;
        line-height: 1.2;
        text-decoration: none;
      }
      .${NS}-toggle-link:hover {
        text-decoration: underline;
      }
      .${NS}-toggle-inline {
        display: inline-flex;
        align-items: center;
        gap: 8px;
        margin: 0;
        padding: 0;
        border: 0;
        background: transparent;
        width: auto;
      }
      .${NS}-toggle-inline .${NS}-toggle-link {
        font-size: 13px;
      }
      .${NS}-comments-toggle-host {
        position: relative;
      }
      .${NS}-comments-toggle {
        position: absolute;
        top: 14px;
        left: 50%;
        transform: translateX(-50%);
        display: inline-flex;
        justify-content: center;
        width: auto;
        padding: 0;
        margin: 0;
        z-index: 2;
      }
      .${NS}-comments-toggle-title {
        position: static;
        transform: none;
        display: flex;
        justify-content: center;
        width: 100%;
        margin: -18px 0 10px;
        padding: 0;
      }
      .${NS}-comments-content-hidden {
        display: none !important;
      }
      .${NS}-comments-toggle-host.${NS}-comments-collapsed > *:not(.${NS}-toggle-inline):not(.${NS}-comments-header-keep) {
        display: none !important;
      }
      .${NS}-comments-toggle-host.${NS}-comments-collapsed .${NS}-comments-content-hidden {
        display: none !important;
      }
      .${NS}-title-toggle-host {
        position: relative;
      }
      .${NS}-title-box-toggle-host {
        position: relative;
      }
      .${NS}-title-toggle-center {
        position: absolute;
        left: 50%;
        top: 50%;
        transform: translate(-50%, -50%);
        z-index: 2;
      }
      .${NS}-title-toggle-center .${NS}-toggle-link {
        font-size: 13px;
      }
      .${NS}-title-synopsis-toggle {
        position: absolute;
        top: 0;
        right: 14px;
        justify-content: flex-end;
        width: auto;
        margin: 0;
        padding: 0;
        border: 0;
        background: transparent;
        z-index: 2;
      }
      .${NS}-title-synopsis-toggle .${NS}-toggle-link {
        font-size: 13px;
      }
      .${NS}-toggle-link::before {
        content: '+ ';
        font-weight: 700;
      }
      .${NS}-toggle-link[data-state="hide"]::before { content: '- '; }
      .${NS}-hidden-block { display: none !important; }
      .${NS}-native-action-hidden { display: none !important; }

      .${NS}-status-row {
        display: grid;
        grid-template-columns: repeat(6, minmax(0, 1fr));
        gap: 6px;
        margin-top: 10px;
        width: 100%;
      }

      .${NS}-status-box {
        background: var(--${NS}-status-bg, rgba(127,127,127,.10));
        border-radius: 6px;
        min-height: 44px;
        display: flex;
        flex-direction: column;
        align-items: center;
        justify-content: center;
        padding: 5px 2px;
        box-sizing: border-box;
        color: var(--${NS}-status-text, inherit);
        border: 1px solid var(--${NS}-status-border, rgba(127,127,127,.18));
      }

      .${NS}-status-icon {
        font-size: 12px !important;
        line-height: 1;
        margin-bottom: 4px;
      }

      .${NS}-status-count {
        font-size: 12px;
        line-height: 1;
        color: inherit;
      }
      .${NS}-film-status-badge {
        display: inline-flex;
        align-items: center;
        justify-content: center;
        width: 16px;
        height: 16px;
        margin-right: 3px;
        vertical-align: middle;
        flex: 0 0 auto;
      }
      .${NS}-film-status-badge i {
        font-size: 14px !important;
        line-height: 1;
      }
      .film-list td.title a .${NS}-film-status-badge,
      .film-list td:nth-child(2) a .${NS}-film-status-badge,
      .film-list td:nth-child(3) a .${NS}-film-status-badge {
        margin-top: -1px;
      }

      .${NS}-profile-box .share-container { margin-top: 8px; }
      .${NS}-poster-hidden { display: none !important; }
      .${NS}-hide-poster-col thead th:nth-child(2),
      .${NS}-hide-poster-col tbody td:nth-child(2) {
        display: none !important;
      }
      .${NS}-filmography-toolbar {
        display: flex;
        align-items: center;
        justify-content: flex-end;
        gap: 0;
        margin: 10px 0 14px;
        position: relative;
        z-index: 40;
      }
      .${NS}-filmography-toolbar-inner {
        display: inline-flex;
        align-items: stretch;
        border: 1px solid color-mix(in srgb, currentColor 20%, transparent);
        border-radius: 6px;
        overflow: visible;
        background: color-mix(in srgb, currentColor 8%, transparent);
        backdrop-filter: blur(8px);
      }
      .${NS}-filmography-btn {
        min-width: 42px;
        height: 42px;
        padding: 0 14px;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        gap: 8px;
        border: 0;
        border-right: 1px solid color-mix(in srgb, currentColor 16%, transparent);
        background: transparent;
        color: inherit;
        cursor: pointer;
        user-select: none;
        white-space: nowrap;
      }
      .${NS}-filmography-btn:last-child {
        border-right: 0;
      }
      .${NS}-filmography-btn:hover,
      .${NS}-filmography-btn[data-open="true"] {
        background: color-mix(in srgb, currentColor 14%, transparent);
      }
      .${NS}-filmography-btn.is-active {
        color: var(--mdl-primary, #85c1dc);
      }
      .${NS}-filmography-btn .fa-sort-amount-up,
      .${NS}-filmography-btn .fa-sort-amount-down,
      .${NS}-filmography-btn .fa-th-large,
      .${NS}-filmography-btn .fa-list,
      .${NS}-filmography-btn .fa-filter {
        font-size: 15px;
      }
      .${NS}-filmography-menu-wrap {
        position: relative;
      }
      .${NS}-filmography-menu {
        position: absolute;
        top: calc(100% + 4px);
        left: 0;
        min-width: 170px;
        padding: 6px 0;
        border: 1px solid color-mix(in srgb, currentColor 20%, transparent);
        border-radius: 6px;
        background: color-mix(in srgb, Canvas 96%, currentColor 4%);
        color: CanvasText;
        box-shadow: 0 12px 22px rgba(0,0,0,.28);
        z-index: 1000;
      }
      .${NS}-filmography-menu[hidden] {
        display: none !important;
      }
      .${NS}-filmography-menu-item {
        display: flex;
        align-items: center;
        gap: 10px;
        width: 100%;
        min-height: 36px;
        padding: 0 14px;
        border: 0;
        background: transparent;
        color: inherit;
        text-align: left;
        cursor: pointer;
      }
      .${NS}-filmography-menu-item:hover,
      .${NS}-filmography-menu-item.is-active {
        background: color-mix(in srgb, currentColor 14%, transparent);
      }
      .${NS}-filmography-menu-item.is-active {
        color: var(--mdl-primary, #85c1dc);
      }
      .${NS}-filmography-grid {
        display: grid;
        grid-template-columns: repeat(4, minmax(0, 1fr));
        gap: 16px;
        margin: 12px 0 22px;
      }
      .${NS}-filmography-card {
        display: flex;
        flex-direction: column;
        min-width: 0;
        border: 1px solid color-mix(in srgb, currentColor 16%, transparent);
        border-radius: 4px;
        overflow: hidden;
        background: color-mix(in srgb, currentColor 6%, transparent);
      }
      .${NS}-filmography-card-cover {
        display: block;
        position: relative;
        aspect-ratio: 2 / 3;
        background: color-mix(in srgb, currentColor 12%, transparent);
        overflow: hidden;
        color: inherit;
      }
      .${NS}-filmography-card-cover img {
        width: 100%;
        height: 100%;
        object-fit: cover;
        display: block;
      }
      .${NS}-filmography-card-body {
        padding: 10px 10px 12px;
        text-align: center;
      }
      .${NS}-filmography-card-title {
        display: block;
        color: inherit;
        font-size: 14px;
        font-weight: 700;
        line-height: 1.35;
        text-decoration: none !important;
      }
      .${NS}-filmography-card-meta {
        margin-top: 8px;
        font-size: 12px;
        line-height: 1.45;
        opacity: .78;
      }
      .${NS}-filmography-card-badge {
        position: absolute;
        top: 6px;
        z-index: 2;
        max-width: calc(100% - 12px);
        padding: 2px 6px;
        border-radius: 3px;
        background: rgba(0,0,0,.42);
        color: #fff;
        font-size: 12px;
        font-weight: 700;
        line-height: 1.2;
        box-shadow: 0 1px 5px rgba(0,0,0,.35);
        text-shadow: 0 1px 2px rgba(0,0,0,.8);
        white-space: nowrap;
      }
      .${NS}-filmography-card-badge.is-status {
        box-shadow: 0 1px 5px rgba(0,0,0,.35);
      }
      .${NS}-filmography-card-badge.is-left {
        left: 6px;
      }
      .${NS}-filmography-card-badge.is-right {
        right: 6px;
      }
      .${NS}-filmography-card-score-row {
        position: absolute;
        left: 0;
        right: 0;
        bottom: 8px;
        z-index: 2;
        display: flex;
        justify-content: space-between;
        gap: 8px;
        padding: 0 8px;
        pointer-events: none;
      }
      .${NS}-filmography-card-score {
        display: inline-flex;
        align-items: center;
        gap: 3px;
        min-width: 0;
        max-width: calc(50% - 4px);
        padding: 2px 5px;
        border-radius: 3px;
        background: rgba(0,0,0,.42);
        color: #fff;
        font-size: 12px;
        font-weight: 700;
        line-height: 1.2;
        text-shadow: 0 1px 2px rgba(0,0,0,.8);
      }
      .${NS}-filmography-card-score span {
        min-width: 0;
        overflow: hidden;
        text-overflow: ellipsis;
      }
      .${NS}-filmography-card-score i {
        color: #ffd54a;
        font-size: 12px;
      }
      .${NS}-filmography-card-rating {
        position: absolute;
        left: 0;
        right: 0;
        bottom: 8px;
        z-index: 2;
        display: flex;
        justify-content: center;
        color: #ffd54a;
        font-size: 17px;
        line-height: 1;
        text-shadow: 0 1px 3px rgba(0,0,0,.8);
        pointer-events: none;
      }
      .${NS}-filmography-card-status {
        margin-top: auto;
        padding: 9px 10px;
        font-size: 13px;
        line-height: 1.2;
        display: flex;
        align-items: center;
        justify-content: center;
        gap: 8px;
        border-top: 1px solid color-mix(in srgb, currentColor 16%, transparent);
        color: #fff;
        cursor: pointer;
      }
      .${NS}-filmography-card-status.is-empty {
        background: color-mix(in srgb, currentColor 10%, transparent);
        color: inherit;
      }
      .${NS}-filmography-card-status-label {
        white-space: nowrap;
        overflow: hidden;
        text-overflow: ellipsis;
      }
      .${NS}-filmography-hidden {
        display: none !important;
      }
      .${NS}-undecided-icon {
        display: inline-block;
        width: 1.08em;
        height: 1.08em;
        box-sizing: border-box;
        vertical-align: -.16em;
        fill: none;
        stroke: currentColor;
        stroke-width: 2.1;
        stroke-linecap: round;
        stroke-linejoin: round;
      }
      .${NS}-undecided-icon.is-v2 {
        width: 1.12em;
        height: 1.12em;
        stroke-width: 2;
      }

      #${ORIGINAL_WORK_BOX_ID} .box-body {
        padding: 10px 14px 14px;
      }

      #${ORIGINAL_WORK_BOX_ID} .box-header,
      #${ORIGINAL_WORK_BOX_ID} .box-title,
      #${FRIENDS_BOX_ID} .box-header,
      #${FRIENDS_BOX_ID} .box-title,
      #${WATCHED_FRIENDS_BOX_ID} .box-header,
      #${WATCHED_FRIENDS_BOX_ID} .box-title {
        font-weight: 700;
        font-size: 1.0625rem;
        line-height: 1.2;
      }

      .${NS}-ow-card {
        display: grid;
        grid-template-columns: 110px minmax(0, 1fr);
        gap: 12px;
        align-items: start;
        text-decoration: none !important;
        color: inherit !important;
        padding: 10px;
        border-radius: 6px;
        border: 1px solid rgba(127,127,127,.24);
        background: rgba(127,127,127,.08);
        transition: background-color .15s ease, border-color .15s ease;
      }

      .${NS}-ow-card:hover {
        background: rgba(127,127,127,.13);
        border-color: rgba(127,127,127,.34);
      }

      .${NS}-ow-card.${NS}-ow-card-text-only {
        grid-template-columns: minmax(0, 1fr);
      }

      .${NS}-ow-cover-wrap {
        display: block;
        width: 110px;
      }

      .${NS}-ow-cover {
        width: 110px;
        aspect-ratio: 3 / 4.2;
        object-fit: cover;
        display: block;
        border-radius: 4px;
        box-shadow: 0 2px 10px rgba(0,0,0,.16);
      }

      .${NS}-ow-content {
        min-width: 0;
      }

      .${NS}-ow-title {
        font-size: 16px;
        line-height: 1.25;
        font-weight: 700;
        margin: 2px 0 10px;
        color: inherit;
      }

      .${NS}-ow-meta {
        display: flex;
        flex-wrap: wrap;
        gap: 6px;
        align-items: center;
        margin-bottom: 8px;
        font-size: 12px;
        line-height: 1.3;
        opacity: .92;
      }

      .${NS}-ow-chip {
        display: inline-flex;
        align-items: center;
        gap: 4px;
        padding: 1px 6px;
        border-radius: 999px;
        background: rgba(127,127,127,.18);
        white-space: nowrap;
      }

      .${NS}-ow-desc {
        font-size: 13px;
        line-height: 1.5;
        opacity: .92;
        margin-top: 10px;
        white-space: pre-line;
        display: -webkit-box;
        -webkit-box-orient: vertical;
        -webkit-line-clamp: 6;
        overflow: hidden;
      }

      #${PORTALS_BOX_ID} {
        display: flex;
        flex-wrap: wrap;
        justify-content: center;
        align-items: center;
        gap: 8px;
        margin: 10px 0 12px;
        width: 100%;
      }

      #${PORTALS_BOX_ID}.${NS}-portal-fallback-fixed {
        position: fixed;
        right: 20px;
        bottom: 20px;
        width: auto;
        max-width: 220px;
        padding: 8px;
        border-radius: 12px;
        background: rgba(20,20,20,.82);
        border: 1px solid rgba(255,255,255,.14);
        z-index: 9999;
        box-shadow: 0 8px 26px rgba(0,0,0,.35);
      }

      .${NS}-portal-link {
        width: 40px;
        height: 40px;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        border-radius: 999px;
        overflow: hidden;
        text-decoration: none !important;
        background: rgba(127,127,127,.10);
        border: 1px solid rgba(127,127,127,.22);
        transition: background-color .15s ease, border-color .15s ease;
      }

      .${NS}-portal-link:hover {
        background: rgba(127,127,127,.16);
        border-color: rgba(127,127,127,.34);
      }

      .${NS}-portal-icon {
        width: 100%;
        height: 100%;
        display: block;
        object-fit: cover;
      }

      #${FRIENDS_BOX_ID} .box-body {
        padding: 10px 14px 14px;
      }

      #${WATCHED_FRIENDS_BOX_ID} .box-body {
        padding: 10px 14px 14px;
      }
      .${NS}-country-section {
        margin: 0 -14px -14px;
        padding: 12px 14px 16px;
        border-top: 1px solid rgba(127,127,127,.16);
      }
      .${NS}-profile-stats-chart-hidden {
        display: none !important;
      }
      .${NS}-country-section ~ * {
        display: none !important;
      }
      .${NS}-country-title {
        text-align: center;
        font-size: 15px;
        font-weight: 700;
        line-height: 1.35;
        margin: 0 0 4px;
      }
      .${NS}-country-subtitle {
        text-align: center;
        font-size: 12px;
        font-style: italic;
        opacity: .78;
        margin: 0 0 16px;
      }
      .${NS}-country-list {
        display: grid;
        gap: 5px;
        margin-bottom: 18px;
        padding: 0 5px;
      }
      .${NS}-country-row {
        display: grid;
        grid-template-columns: minmax(0, 1fr) auto;
        align-items: baseline;
        gap: 12px;
        font-size: 14px;
        line-height: 1.35;
      }
      .${NS}-country-name {
        min-width: 0;
        color: rgba(255,255,255,.94);
      }
      .${NS}-country-value {
        font-weight: 700;
        white-space: nowrap;
        color: rgba(255,255,255,.94);
      }
      .${NS}-country-percent {
        font-style: italic;
        font-weight: 400;
        opacity: .78;
      }
      .${NS}-country-chart-wrap {
        display: flex;
        justify-content: center;
        margin-top: 12px;
      }
      .${NS}-country-chart {
        width: 280px;
        height: 280px;
        border-radius: 999px;
        background: rgba(127,127,127,.12);
        border: 1px solid rgba(127,127,127,.14);
      }
      .${NS}-country-actions {
        display: flex;
        justify-content: center;
        align-items: center;
        flex-wrap: wrap;
        gap: 10px;
        margin-top: 12px;
        font-size: 12px;
      }
      .${NS}-country-refresh {
        border: 0;
        background: transparent;
        color: var(--mdl-primary, #2f9fff);
        padding: 0;
        cursor: pointer;
      }
      .${NS}-country-updated {
        opacity: .66;
      }
      .${NS}-country-partial-note {
        margin: 8px 4px 0;
        font-size: 12px;
        line-height: 1.45;
        text-align: center;
        color: rgba(255,255,255,.72);
      }
      .${NS}-country-partial-note a {
        color: var(--mdl-primary, #2f9fff);
        text-decoration: none;
      }
      .${NS}-country-partial-note a:hover {
        text-decoration: underline;
      }
      .${NS}-country-empty {
        font-size: 13px;
        line-height: 1.5;
        opacity: .72;
        text-align: center;
        padding: 6px 2px 0;
      }

      .${NS}-friends-list {
        display: grid;
        gap: 10px;
      }

      .${NS}-friend-row {
        display: grid;
        grid-template-columns: 40px minmax(0, 1fr) auto;
        gap: 10px;
        align-items: center;
        padding: 8px 10px;
        border-radius: 8px;
        background: rgba(127,127,127,.07);
        border: 1px solid rgba(127,127,127,.18);
        text-decoration: none !important;
        color: inherit !important;
      }

      .${NS}-friend-avatar {
        width: 40px;
        height: 40px;
        border-radius: 999px;
        object-fit: cover;
        display: block;
        background: rgba(127,127,127,.18);
      }

      .${NS}-friend-main {
        min-width: 0;
      }

      .${NS}-friend-name {
        display: block;
        font-size: 13px;
        font-weight: 700;
        line-height: 1.25;
        color: inherit;
        white-space: nowrap;
        overflow: hidden;
        text-overflow: ellipsis;
      }

      .${NS}-friend-meta {
        display: block;
        font-size: 11px;
        line-height: 1.3;
        opacity: .72;
        white-space: nowrap;
        overflow: hidden;
        text-overflow: ellipsis;
      }

      .${NS}-friend-score {
        font-size: 15px;
        font-weight: 800;
        line-height: 1;
        white-space: nowrap;
      }

      .${NS}-friends-nav {
        display: flex;
        justify-content: space-between;
        align-items: center;
        margin-top: 12px;
        gap: 10px;
      }

      .${NS}-friends-arrow {
        width: 30px;
        height: 30px;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        border: 1px solid rgba(127,127,127,.24);
        border-radius: 999px;
        background: rgba(127,127,127,.08);
        color: inherit;
        cursor: pointer;
        user-select: none;
      }

      .${NS}-friends-arrow[disabled] {
        opacity: .42;
        cursor: default;
      }

      .${NS}-friends-page {
        font-size: 12px;
        opacity: .78;
      }

      .${NS}-friends-empty {
        font-size: 13px;
        line-height: 1.5;
        opacity: .72;
        padding: 4px 2px;
      }
      .${NS}-watched-grid {
        display: grid;
        grid-template-columns: repeat(5, minmax(0, 1fr));
        gap: 10px;
      }
      .${NS}-watched-avatar-link,
      .${NS}-watched-avatar-fallback {
        width: 100%;
        aspect-ratio: 1;
        border-radius: 999px;
        overflow: hidden;
        display: flex;
        align-items: center;
        justify-content: center;
        text-decoration: none !important;
        color: inherit !important;
        background: rgba(127,127,127,.10);
        border: 1px solid rgba(127,127,127,.18);
      }
      .${NS}-watched-avatar-link:hover,
      .${NS}-watched-avatar-fallback:hover {
        background: rgba(127,127,127,.16);
        border-color: rgba(127,127,127,.28);
      }
      .${NS}-watched-avatar {
        width: 100%;
        height: 100%;
        object-fit: cover;
        display: block;
        background: rgba(127,127,127,.18);
      }
      .${NS}-watched-avatar-fallback {
        font-size: 22px;
        font-weight: 700;
        line-height: 1;
        opacity: .82;
      }
      @media (max-width: 1199px) {
        .${NS}-ow-card {
          grid-template-columns: 92px minmax(0, 1fr);
        }

        .${NS}-ow-cover-wrap,
        .${NS}-ow-cover {
          width: 92px;
        }
      }
      @media (max-width: 991px) {
        .${NS}-watched-grid {
          grid-template-columns: repeat(5, 46px);
          justify-content: center;
        }
        .${NS}-filmography-grid {
          grid-template-columns: repeat(2, minmax(0, 1fr));
          gap: 10px;
        }
      }
    `;
    document.head.appendChild(style);
  }

  function injectSettingsStyle() {
    if (q(`#${STYLE_ID}-settings`)) return;
    const style = document.createElement('style');
    style.id = `${STYLE_ID}-settings`;
    style.textContent = `
      #${SETTINGS_PANEL_ID} {
        display: block;
        width: min(1120px, calc(100% - 32px));
        margin: 20px auto;
      }
      #${SETTINGS_PANEL_ID} .box-body {
        padding: 0;
      }
      #${SETTINGS_PANEL_ID}-tab {
        margin-left: 0;
      }
      #${SETTINGS_PANEL_ID}-tab > a,
      #${SETTINGS_PANEL_ID}-tab.${NS}-settings-tab-link {
        white-space: nowrap;
        font-weight: 400;
      }
      #${SETTINGS_PANEL_ID}-tab > a:hover,
      #${SETTINGS_PANEL_ID}-tab.active > a,
      #${SETTINGS_PANEL_ID}-tab > a.active,
      #${SETTINGS_PANEL_ID}-tab.${NS}-settings-tab-link:hover,
      #${SETTINGS_PANEL_ID}-tab.${NS}-settings-tab-link.active {
        color: inherit;
      }
      .box ul.nav-tabs,
      .box .nav-tabs,
      .${NS}-settings-tab-list {
        display: flex;
        flex-wrap: wrap;
        align-items: center;
      }
      .${NS}-settings-header {
        display: flex;
        align-items: center;
        justify-content: space-between;
        gap: 12px;
        padding: 12px 16px;
        background: #1f6aa5;
        color: #fff;
        font-size: 20px;
        font-weight: 700;
        border-radius: 4px 4px 0 0;
      }
      .${NS}-settings-content {
        padding: 20px 22px 24px;
      }
      .${NS}-settings-back {
        border: 1px solid rgba(255,255,255,.35);
        background: rgba(255,255,255,.12);
        color: #fff;
        border-radius: 6px;
        padding: 6px 10px;
        font-size: 12px;
        line-height: 1;
        cursor: pointer;
      }
      .${NS}-native-settings-hidden {
        display: none !important;
      }
      #${SETTINGS_PANEL_ID}.${NS}-settings-panel {
        width: min(1120px, calc(100% - 32px));
        margin: 20px auto;
      }
      .${NS}-settings-form .form-check {
        display: flex;
        align-items: center;
        margin-bottom: 14px;
      }
      .${NS}-settings-form .form-check-label,
      .${NS}-settings-form .control-label {
        color: inherit;
      }
      .${NS}-settings-form .form-check-input {
        margin: 0 12px 0 0;
        flex: 0 0 auto;
      }
      .${NS}-settings-form .form-check-label {
        margin: 0;
      }
      .${NS}-feature-note {
        margin-left: 8px;
        color: rgba(255,255,255,.58);
        font-size: 11px;
        white-space: nowrap;
      }
      .${NS}-feature-icons {
        display: inline-flex;
        align-items: center;
        gap: 5px;
        margin-left: 8px;
        vertical-align: middle;
      }
      .${NS}-feature-icons i {
        font-size: 12px;
      }
      .${NS}-settings-layout {
        display: grid;
        grid-template-columns: minmax(390px, 1fr) 320px 220px;
        gap: 18px;
        align-items: start;
      }
      .${NS}-settings-col {
        min-width: 0;
      }
      .${NS}-settings-right {
        grid-column: 2 / 4;
        display: grid;
        grid-template-columns: 320px 220px;
        gap: 18px;
        align-items: start;
        min-width: 0;
      }
      .${NS}-settings-storage {
        width: 360px;
        max-width: 100%;
        min-height: 108px;
        margin-top: 48px;
        padding: 16px 14px 14px;
        text-align: center;
      }
      .${NS}-settings-storage-text {
        white-space: nowrap;
      }
      .${NS}-settings-storage-actions {
        display: flex;
        justify-content: center;
        gap: 10px;
        margin-top: 14px;
      }
      .${NS}-settings-form .input-group {
        display: flex;
        align-items: stretch;
        max-width: 220px;
      }
      .${NS}-settings-form .input-group-addon {
        display: flex;
        align-items: center;
        justify-content: center;
        width: 32px;
        min-width: 32px;
        padding: 0;
        border: 1px solid rgba(127,127,127,.22);
        border-left: 0;
        border-radius: 0 4px 4px 0;
        background: rgba(127,127,127,.08);
      }
      .${NS}-settings-form .input-group-addon input[type="color"] {
        width: 18px;
        height: 18px;
        padding: 0;
        border: 0;
        background: transparent;
      }
      .${NS}-settings-form .form-control {
        width: 100%;
        min-height: 38px;
        padding: 9px 12px;
        border: 1px solid rgba(127,127,127,.22);
        border-radius: 4px;
        background: rgba(127,127,127,.08);
        color: inherit;
      }
      .${NS}-settings-form .input-group .form-control {
        border-radius: 4px 0 0 4px;
      }
      .${NS}-settings-colors .form-control {
        max-width: 188px;
      }
      .${NS}-settings-wide {
        grid-column: 1 / 3;
      }
      .${NS}-settings-wide .form-control {
        max-width: none;
      }
      .${NS}-settings-form .alert {
        margin-bottom: 18px;
      }
      @media (max-width: 991px) {
        #${SETTINGS_PANEL_ID},
        #${SETTINGS_PANEL_ID}.${NS}-settings-panel {
          width: calc(100% - 24px);
          margin: 16px auto;
        }
        .${NS}-settings-layout {
          display: block;
        }
        .${NS}-settings-col {
          margin-bottom: 16px;
        }
        .${NS}-settings-right {
          display: block;
        }
        .${NS}-settings-wide {
          grid-column: auto;
        }
        .${NS}-settings-storage {
          margin-top: 20px;
        }
        .${NS}-settings-storage-text {
          white-space: normal;
        }
      }
    `;
    document.head.appendChild(style);
  }

  function findProfileBox() {
    return qa('.col-lg-4 .box, .col-md-4 .box, .col-sm-4 .box, .sidebar .box, .side-content .box')
      .find((box) => q('img', box) && /followers|hearts/i.test(text(box)));
  }

  function findShareContainer(box) {
    return q('.share-container', box)
      || qa('div', box).find((div) => qa('a,button', div).length >= 4 && qa('img', div).length === 0);
  }

  function collectFilmographyIds() {
    const rows = qa('table.film-list tbody tr');
    return [...new Set(rows.map((tr) => {
      const cls = (tr.getAttribute('class') || '').split(/\s+/).find((x) => x.startsWith('mdl-'));
      return cls ? cls.slice(4) : '';
    }).filter(Boolean))];
  }

  async function fetchStatuses(ids) {
    const token = getToken();
    if (!token || !ids.length) return [];
    const cacheKey = `${location.pathname}|${ids.join('-')}`;
    if (statusRequestCache.has(cacheKey)) return statusRequestCache.get(cacheKey);

    const promise = (async () => {
      const all = [];
      const params = new URLSearchParams({ token, lang: 'en-US', mylist: ids.join('-'), t: 'z' });
      const resp = await fetch(`/v1/users/data?${params.toString()}`, {
        headers: { authorization: `Bearer ${token}` },
        credentials: 'same-origin',
      }).catch(() => null);

      if (resp?.ok) {
        const json = await resp.json().catch(() => null);
        if (json?.mylist && Array.isArray(json.mylist)) {
          all.push(...json.mylist);
        } else if (json?.mylist && typeof json.mylist === 'object') {
          all.push(...Object.values(json.mylist));
        }
      }

      return all;
    })();

    statusRequestCache.set(cacheKey, promise);
    const resolved = await promise;
    statusRequestCache.set(cacheKey, resolved);
    return resolved;
  }

  function extractStatusItemId(item) {
    const candidates = [
      item?.rid,
      item?.id,
      item?.title_id,
      item?.tid,
      item?.mdl_id,
      item?.drama_id,
      item?.movie_id,
      item?.slug_id,
    ];

    for (const candidate of candidates) {
      const value = collapseWhitespace(String(candidate || ''));
      if (value) return value;
    }

    const linkCandidates = [
      item?.url,
      item?.uri,
      item?.link,
      item?.href,
      item?.permalink,
    ];

    for (const candidate of linkCandidates) {
      const match = String(candidate || '').match(/mydramalist\.com\/(\d+)(?:[-/]|$)|\/(\d+)(?:[-/]|$)/i);
      const value = collapseWhitespace(match?.[1] || match?.[2] || '');
      if (value) return value;
    }

    return '';
  }

  function normalizeStatusItems(ids, items) {
    const requestedIds = Array.isArray(ids) ? ids.map((id) => collapseWhitespace(String(id || ''))).filter(Boolean) : [];
    const rawItems = Array.isArray(items) ? items : [];

    return rawItems.map((item, index) => {
      const resolvedId = extractStatusItemId(item);
      const fallbackId = (!resolvedId && rawItems.length === requestedIds.length) ? requestedIds[index] : '';
      return {
        ...item,
        __bettermdlId: resolvedId || fallbackId || '',
      };
    });
  }

  function computeCounts(items) {
    const counts = { 1: 0, 2: 0, 3: 0, 4: 0, 5: 0, 6: 0 };
    items.forEach((item) => {
      const status = Number(item?.status);
      if (counts[status] !== undefined) counts[status] += 1;
    });
    return counts;
  }

  function renderStatusRow(box, counts) {
    if (!isFeatureEnabled('peopleStatusSummary')) {
      q(`.${NS}-status-row`, box)?.remove();
      return;
    }

    const share = findShareContainer(box);
    if (!share) return;
    const statusConfig = getStatusConfigMap();

    box.classList.add(`${NS}-profile-box`);

    let row = q(`.${NS}-status-row`, box);
    if (!row) {
      row = document.createElement('div');
      row.className = `${NS}-status-row`;
      share.insertAdjacentElement('afterend', row);
    }

    applyStatusThemeVars(row, share.closest('.box-body, .box') || box);
    row.innerHTML = '';

    for (let i = 1; i <= 6; i += 1) {
      const cfg = statusConfig[i];
      const cell = document.createElement('div');
      cell.className = `${NS}-status-box count-box`;
      cell.title = cfg.label;
      cell.setAttribute('aria-label', cfg.label);
      cell.innerHTML = `
        <i class="${cfg.icon} ${NS}-status-icon" style="color:${cfg.color}"></i>
        <span class="${NS}-status-count">${counts[i] ?? 0}</span>
      `;
      row.appendChild(cell);
    }
  }

  function isValidProfileCountryStats(value) {
    return !!(
      value
      && typeof value === 'object'
      && Number.isFinite(Number(value.total))
      && Array.isArray(value.countries)
      && value.countries.every((item) => item && isKnownCountryName(item.country) && Number.isFinite(Number(item.count)))
    );
  }

  function getProfileCountryStatsCacheKey(username) {
    return `profile-country:${String(username || '').toLowerCase()}`;
  }

  function getPersistedProfileCountryStats(username, allowExpired = false) {
    const cacheKey = getProfileCountryStatsCacheKey(username);
    const store = getLocalCache(STORAGE_PROFILE_COUNTRY_STATS);
    const cached = store?.[cacheKey];
    if (!cached?.expiresAt || (!allowExpired && cached.expiresAt < Date.now())) return null;
    if (!cached.value?.countries?.length) return null;
    return isValidProfileCountryStats(cached.value) ? cached.value : null;
  }

  function persistProfileCountryStats(username, value, expectedTotal = 0) {
    if (!username || !isValidProfileCountryStats(value)) return;
    if (!value.countries.length) return;
    const previous = getPersistedProfileCountryStats(username, true);
    const targetTotal = Number(expectedTotal) || 0;
    if (previous) {
      const previousTotal = Number(previous.total);
      const nextTotal = Number(value.total);
      const nextIsTooPartial = targetTotal
        ? nextTotal < Math.floor(targetTotal * 0.95)
        : nextTotal < previousTotal;
      if (nextTotal < previousTotal && nextIsTooPartial) return;
    }
    persistCacheEntry(STORAGE_PROFILE_COUNTRY_STATS, getProfileCountryStatsCacheKey(username), value, PROFILE_COUNTRY_STATS_TTL_MS);
  }

  function getProfileCountryStatsUsername() {
    return getProfileUsernameFromPath() || getDramalistUsernameFromPage();
  }

  function getProfileStatisticsTitleTotal() {
    const box = findProfileStatisticsBox();
    if (!box) return 0;
    const clone = box.cloneNode(true);
    q(`.${NS}-country-section`, clone)?.remove();
    const raw = text(clone);
    const parseCount = (pattern) => {
      const match = raw.match(pattern);
      return match ? Number(String(match[1]).replace(/[^\d]/g, '')) : 0;
    };
    const shows = parseCount(/([\d,.]+)\s+shows?/i);
    const movies = parseCount(/([\d,.]+)\s+movies?/i);
    return shows + movies;
  }

  function isProfileCountryStatsExpected(stats, expectedTotal = getProfileStatisticsTitleTotal()) {
    return !expectedTotal || Number(stats?.total) === Number(expectedTotal);
  }

  function isProfileCountryStatsCloseEnough(stats, expectedTotal = getProfileStatisticsTitleTotal()) {
    return !expectedTotal || Number(stats?.total) >= Math.floor(Number(expectedTotal) * 0.95);
  }

  function isOwnProfileUsername(username) {
    const currentUsername = getCurrentUsername();
    return !!currentUsername && String(currentUsername).toLowerCase() === String(username || '').toLowerCase();
  }

  function findProfileStatisticsBox() {
    return findBoxByHeading(/^statistics$/i)
      || qa('.box, .card, .box-container, [class*="box"]').find((box) => {
        const heading = q('.box-header, .box-title, .card-header, h1, h2, h3, h4', box);
        return /^statistics$/i.test(text(heading));
      })
      || null;
  }

  function isNativeProfileStatsChartNode(node) {
    if (!node) return false;
    const chartTextPattern = /shows\s+movies|currently\s+watching|plan\s+to\s+watch|on-hold|dropped|not\s+interested/i;
    const nodeText = text(node);
    const hasTimeSummary = /all\s*time/i.test(nodeText) && /\d/.test(nodeText);
    const chartLike = !!q('canvas, svg', node) || chartTextPattern.test(nodeText);
    return chartLike && !hasTimeSummary;
  }

  function findNativeProfileStatsChartNodes(body, section = null) {
    const nodes = [];
    const addNode = (node) => {
      if (!node || node === body || node === section || section?.contains(node) || node.contains?.(section)) return;
      if (!nodes.includes(node)) nodes.push(node);
    };

    Array.from(body.children).forEach((child) => {
      if (child === section) return;
      if (isNativeProfileStatsChartNode(child)) addNode(child);
    });

    qa('canvas, svg', body).forEach((mediaNode) => {
      if (section?.contains(mediaNode)) return;
      let candidate = mediaNode;
      let node = mediaNode.parentElement;
      while (node && node !== body) {
        if (section?.contains(node)) return;
        const nodeText = text(node);
        if (/all\s*time/i.test(nodeText) && /\d/.test(nodeText)) break;
        candidate = node;
        node = node.parentElement;
      }
      addNode(candidate);
    });

    qa('div, section, article', body).forEach((node) => {
      if (node === body || node === section || section?.contains(node)) return;
      if (isNativeProfileStatsChartNode(node)) addNode(node);
    });

    return nodes.filter((node) => !nodes.some((other) => other !== node && other.contains?.(node)));
  }

  function findProfileStatsLastSummaryNode(body, section = null) {
    const children = Array.from(body.children).filter((child) => child !== section && !section?.contains(child));
    let lastSummary = null;
    children.forEach((child) => {
      const childText = text(child);
      if (/all\s*time/i.test(childText) && /\d/.test(childText) && /(episodes?|shows?|movies?)/i.test(childText)) {
        lastSummary = child;
      }
    });
    return lastSummary;
  }

  function findProfileStatsFallbackChartAnchor(body, section = null) {
    const lastSummary = findProfileStatsLastSummaryNode(body, section);
    return lastSummary?.nextElementSibling && lastSummary.nextElementSibling !== section
      ? lastSummary.nextElementSibling
      : null;
  }

  function findNativeProfileStatsChartAnchor(body, section = null) {
    return findNativeProfileStatsChartNodes(body, section)[0] || findProfileStatsFallbackChartAnchor(body, section);
  }

  function hideExistingProfileStatsCharts(body, section) {
    findNativeProfileStatsChartNodes(body, section).forEach((node) => {
      node.classList.add(`${NS}-profile-stats-chart-hidden`);
    });
  }

  function restoreExistingProfileStatsCharts() {
    qa(`.${NS}-profile-stats-chart-hidden`).forEach((node) => node.classList.remove(`${NS}-profile-stats-chart-hidden`));
  }

  function ensureCountryStatsSection() {
    const box = findProfileStatisticsBox();
    if (!box) return null;
    const body = q('.box-body, .card-body', box) || box;
    let section = q(`.${NS}-country-section`, body);
    if (!section) {
      section = document.createElement('div');
      section.className = `${NS}-country-section`;
      const chartNode = findNativeProfileStatsChartAnchor(body, section);
      if (chartNode) chartNode.insertAdjacentElement('beforebegin', section);
      else if (findProfileStatsLastSummaryNode(body, section)) findProfileStatsLastSummaryNode(body, section).insertAdjacentElement('afterend', section);
      else body.appendChild(section);
    } else {
      const chartNode = findNativeProfileStatsChartAnchor(body, section);
      if (chartNode && chartNode.previousElementSibling !== section) {
        chartNode.insertAdjacentElement('beforebegin', section);
      } else if (!chartNode && findProfileStatsLastSummaryNode(body, section)?.nextElementSibling !== section) {
        findProfileStatsLastSummaryNode(body, section).insertAdjacentElement('afterend', section);
      }
    }
    hideExistingProfileStatsCharts(body, section);
    return section;
  }

  function getCountryStatsPalette() {
    return ['#a6d189', '#85c1dc', '#e78284', '#ca9ee6', '#e5c890', '#8caaee', '#f4b8e4', '#babbf1', '#ef9f76', '#a6e3a1'];
  }

  function formatProfileCountryDate(timestamp) {
    if (!timestamp) return '';
    const date = new Date(timestamp);
    if (Number.isNaN(date.getTime())) return '';
    return date.toISOString().slice(0, 10);
  }

  function renderCountryStatsShell(section, stateText = 'Loading country stats...') {
    const renderKey = `shell:${stateText}`;
    if (section.dataset.countryRenderKey === renderKey) return;
    section.dataset.countryRenderKey = renderKey;
    section.innerHTML = '';

    const title = document.createElement('div');
    title.className = `${NS}-country-title`;
    title.textContent = 'Titles by Country';

    const subtitle = document.createElement('div');
    subtitle.className = `${NS}-country-subtitle`;
    subtitle.textContent = '(Does not include Planned & Not Interested)';

    const empty = document.createElement('div');
    empty.className = `${NS}-country-empty`;
    empty.textContent = stateText;

    section.append(title, subtitle, empty);
  }

  function getProfileCountryPartialNoteHtml(username = getProfileCountryStatsUsername()) {
    const base = username ? `/dramalist/${encodeURIComponent(username)}` : '';
    return base
      ? `Open <a href="${base}/completed">Completed</a> once to improve accuracy.`
      : 'Open the Completed list once to improve accuracy.';
  }

  function appendProfileCountryPartialNote(section, prefix = 'Partial data.') {
    const note = document.createElement('div');
    note.className = `${NS}-country-partial-note`;
    note.innerHTML = `${prefix} ${getProfileCountryPartialNoteHtml()}`;
    section.appendChild(note);
    return note;
  }

  function renderCountryStatsPartialShell(section, stateText = 'Loading available country stats...') {
    renderCountryStatsShell(section, stateText);
    appendProfileCountryPartialNote(section, 'Partial data.');
  }

  function renderProfileCountryStats(stats) {
    const section = ensureCountryStatsSection();
    if (!section) return;
    if (!isValidProfileCountryStats(stats) || !stats.countries.length) {
      renderCountryStatsPartialShell(section, 'No country data found yet.');
      return;
    }

    const renderKey = JSON.stringify({
      countries: stats.countries,
      total: stats.total,
      expectedTotal: stats.expectedTotal || getProfileStatisticsTitleTotal(),
      generatedAt: stats.generatedAt || 0,
      source: stats.source || '',
    });
    if (section.dataset.countryRenderKey === renderKey) return;
    section.dataset.countryRenderKey = renderKey;
    section.innerHTML = '';
    const palette = getCountryStatsPalette();

    const title = document.createElement('div');
    title.className = `${NS}-country-title`;
    title.textContent = 'Titles by Country';

    const subtitle = document.createElement('div');
    subtitle.className = `${NS}-country-subtitle`;
    subtitle.textContent = '(Does not include Planned & Not Interested)';

    const list = document.createElement('div');
    list.className = `${NS}-country-list`;

    stats.countries.forEach((item, index) => {
      const row = document.createElement('div');
      row.className = `${NS}-country-row`;
      row.style.setProperty(`--${NS}-country-color`, palette[index % palette.length]);

      const name = document.createElement('span');
      name.className = `${NS}-country-name`;
      name.textContent = item.country;

      const value = document.createElement('span');
      value.className = `${NS}-country-value`;
      const percent = stats.total ? ((item.count / stats.total) * 100) : 0;
      value.textContent = `${item.count} `;
      const percentNode = document.createElement('span');
      percentNode.className = `${NS}-country-percent`;
      percentNode.textContent = `(${percent.toFixed(1)}%)`;
      value.appendChild(percentNode);

      row.append(name, value);
      list.appendChild(row);
    });

    const showChart = true;
    const chartWrap = document.createElement('div');
    chartWrap.className = `${NS}-country-chart-wrap`;

    if (showChart) {
      const chart = document.createElement('div');
      chart.className = `${NS}-country-chart`;
      let start = 0;
      const segments = stats.countries.map((item, index) => {
        const angle = stats.total ? (item.count / stats.total) * 360 : 0;
        const end = start + angle;
        const color = palette[index % palette.length];
        const segment = `${color} ${start.toFixed(2)}deg ${end.toFixed(2)}deg`;
        start = end;
        return segment;
      });
      chart.style.background = `conic-gradient(${segments.join(', ')})`;
      chartWrap.appendChild(chart);
    }

    const actions = document.createElement('div');
    actions.className = `${NS}-country-actions`;
    const updated = document.createElement('span');
    updated.className = `${NS}-country-updated`;
    const updatedParts = [];
    const updatedDate = formatProfileCountryDate(stats.generatedAt);
    if (updatedDate) updatedParts.push(`Updated: ${updatedDate}`);
    const expectedTotal = Number(stats.expectedTotal) || getProfileStatisticsTitleTotal();
    const isPartial = !!expectedTotal && Number(stats.total) !== expectedTotal;
    if (Number.isFinite(Number(stats.total))) {
      updatedParts.push(isPartial ? `${stats.total} of ${expectedTotal} titles` : `${stats.total} titles`);
    }
    if (isPartial) updatedParts.push('Partial');
    updated.textContent = updatedParts.join(' | ');
    const refresh = document.createElement('button');
    refresh.type = 'button';
    refresh.className = `${NS}-country-refresh`;
    refresh.textContent = 'Refresh';
    refresh.addEventListener('click', () => {
      const username = getProfileCountryStatsUsername();
      if (!username) return;
      const requestId = `${Date.now()}:${Math.random()}`;
      section.dataset.countryRequestId = requestId;
      renderCountryStatsShell(section, 'Refreshing country stats...');
      const timeoutId = setTimeout(() => {
        if (section.dataset.countryRequestId !== requestId) return;
        renderCountryStatsPartialShell(section, 'Could not refresh country stats.');
      }, PROFILE_COUNTRY_STATS_LOAD_TIMEOUT_MS);
      resolveProfileCountryStats(username, true)
        .then((stats) => {
          if (section.dataset.countryRequestId !== requestId) return;
          clearTimeout(timeoutId);
          if (stats) renderProfileCountryStats(stats);
          else renderCountryStatsPartialShell(section, 'Could not refresh country stats.');
        })
        .catch(() => {
          if (section.dataset.countryRequestId !== requestId) return;
          clearTimeout(timeoutId);
          renderCountryStatsPartialShell(section, 'Could not refresh country stats.');
        });
    });
    actions.append(updated, refresh);

    section.append(title, subtitle, list);
    if (showChart) section.appendChild(chartWrap);
    section.appendChild(actions);

    if (isPartial) {
      appendProfileCountryPartialNote(section);
    }

    if (stats.debugDetails && Array.isArray(stats.endpointHints) && stats.endpointHints.length) {
      const hints = document.createElement('div');
      hints.className = `${NS}-country-updated`;
      hints.style.display = 'block';
      hints.style.marginTop = '4px';
      hints.style.whiteSpace = 'normal';
      hints.textContent = `Hints: ${stats.endpointHints.slice(0, 6).join(' | ')}`;
      section.appendChild(hints);
    }

    if (stats.debugDetails && Array.isArray(stats.performanceHints) && stats.performanceHints.length) {
      const perfHints = document.createElement('div');
      perfHints.className = `${NS}-country-updated`;
      perfHints.style.display = 'block';
      perfHints.style.marginTop = '4px';
      perfHints.style.whiteSpace = 'normal';
      perfHints.textContent = `Net: ${stats.performanceHints.slice(0, 8).join(' | ')}`;
      section.appendChild(perfHints);
    }

    if (stats.debugDetails && Array.isArray(stats.wrapperHints) && stats.wrapperHints.length) {
      const wrapperHints = document.createElement('div');
      wrapperHints.className = `${NS}-country-updated`;
      wrapperHints.style.display = 'block';
      wrapperHints.style.marginTop = '4px';
      wrapperHints.style.whiteSpace = 'normal';
      wrapperHints.textContent = `Wrap: ${stats.wrapperHints.slice(0, 8).join(' | ')}`;
      section.appendChild(wrapperHints);
    }
  }

  function normalizeCountryName(value) {
    return collapseWhitespace(String(value || '').replace(/\s*\([^)]*\)\s*$/g, ''));
  }

  function isKnownCountryName(value) {
    const raw = normalizeCountryName(value);
    return !!raw && getKnownCountryNames().some((country) => country.toLowerCase() === raw.toLowerCase());
  }

  function getKnownCountryNames() {
    return ['South Korea', 'China', 'Japan', 'Thailand', 'Taiwan', 'Hong Kong', 'Philippines', 'United States', 'United Kingdom', 'Singapore', 'Malaysia', 'Indonesia', 'Vietnam', 'Cambodia', 'Myanmar', 'India'];
  }

  function getCountryNameFromCode(value) {
    const code = collapseWhitespace(String(value || '')).toLowerCase().replace(/^flag[-_]?/, '');
    const map = {
      kr: 'South Korea',
      korea: 'South Korea',
      southkorea: 'South Korea',
      cn: 'China',
      china: 'China',
      jp: 'Japan',
      japan: 'Japan',
      th: 'Thailand',
      thailand: 'Thailand',
      tw: 'Taiwan',
      taiwan: 'Taiwan',
      hk: 'Hong Kong',
      hongkong: 'Hong Kong',
      ph: 'Philippines',
      philippines: 'Philippines',
      us: 'United States',
      usa: 'United States',
      gb: 'United Kingdom',
      uk: 'United Kingdom',
    };
    return map[code] || '';
  }

  function getKnownCountryFromText(value, requireLabel = false) {
    const raw = collapseWhitespace(value);
    if (!raw) return '';
    const prefix = requireLabel ? 'Country\\s*:\\s*' : '';
    return getKnownCountryNames().find((country) => new RegExp(`${prefix}\\b${country.replace(/\s+/g, '\\s+')}\\b`, 'i').test(raw)) || '';
  }

  function findDramalistTitleAnchor(row) {
    return qa('a[href*="/"]', row).find((anchor) => {
      const href = anchor.getAttribute('href') || '';
      return !anchor.querySelector('img') && /^\/\d+[-/]/.test(href);
    }) || qa('a[href*="/"]', row).find((anchor) => {
      const href = anchor.getAttribute('href') || '';
      return !anchor.querySelector('img') && /\/\d+[-/]/.test(href);
    }) || null;
  }

  function getDramalistHeaderIndexes(table) {
    const headers = qa('thead th', table).map((th) => text(th).toLowerCase());
    const findIndex = (pattern) => headers.findIndex((label) => pattern.test(label));
    return {
      country: findIndex(/^country$/i),
      title: findIndex(/^title$/i),
    };
  }

  function getCountryFromDramalistRow(row, cells, indexes) {
    if (indexes.country >= 0) {
      const direct = normalizeCountryName(text(cells[indexes.country]));
      if (isKnownCountryName(direct)) return getKnownCountryFromText(direct);
    }

    const countryNode = q('[data-country], [data-original-title], [title], [alt], .country, [class*="country"], [class*="flag"]', row);
    const raw = normalizeCountryName(
      countryNode?.getAttribute('data-country')
      || countryNode?.getAttribute('data-original-title')
      || countryNode?.getAttribute('title')
      || countryNode?.getAttribute('alt')
      || text(countryNode),
    );
    const rawCountry = getKnownCountryFromText(raw);
    if (rawCountry) return rawCountry;

    const flagClass = Array.from(row.querySelectorAll('[class*="flag"]'))
      .flatMap((node) => Array.from(node.classList || []))
      .map(getCountryNameFromCode)
      .find(Boolean);
    if (flagClass) return flagClass;

    const attrCountry = qa('[title], [alt], [data-original-title], [data-country]', row)
      .map((node) => (
        getKnownCountryFromText(node.getAttribute('title'))
        || getKnownCountryFromText(node.getAttribute('alt'))
        || getKnownCountryFromText(node.getAttribute('data-original-title'))
        || getKnownCountryFromText(node.getAttribute('data-country'))
      ))
      .find(Boolean);
    if (attrCountry) return attrCountry;

    return getKnownCountryFromText(text(row));
  }

  function getDramalistRowWrapperId(rowOrCell) {
    const node = rowOrCell?.closest?.(
      '.table-responsive[id], [id^="mylist_"], [id^="list_"], tbody[id^="content_"], table[id]',
    );
    return node?.id || '';
  }

  function extractCountryEntriesFromRenderedDramalistPage(root = document) {
    const rows = new Set();
    qa('tbody[id^="content_"] tr, tr[id^="ml"]', root).forEach((row) => rows.add(row));
    qa('td.mdl-style-col-country', root).forEach((cell) => {
      const row = cell.closest('tr');
      if (row) rows.add(row);
    });

    const entries = [];
    const pushEntry = ({ row, titleAnchor, country = '' }) => {
      const href = titleAnchor?.getAttribute('href') || '';
      const id = collapseWhitespace(
        href.match(/\/(\d+)(?:[-/]|$)/)?.[1]
        || row?.id?.replace(/^ml/i, '')
        || '',
      );
      const title = collapseWhitespace(text(titleAnchor) || text(q('.title', row)) || text(row));
      if (!id && !title) return;
      entries.push({ id, title, country, href, wrapperId: getDramalistRowWrapperId(row || titleAnchor) });
    };

    rows.forEach((row) => {
      if (row.querySelector('.mdl-style-col-empty')) return;
      const country = normalizeCountryName(text(q('.mdl-style-col-country', row)));
      const titleAnchor = findDramalistTitleAnchor(row) || q('.title a[href], a.title[href]', row);
      pushEntry({ row, titleAnchor, country });
    });

    qa('a[href]', root).forEach((anchor) => {
      const href = anchor.getAttribute('href') || '';
      if (!/^\/\d+(?:[-/]|$)/.test(href)) return;
      if (anchor.querySelector('img') && !text(anchor)) return;
      if (anchor.closest('nav, header, footer, .pagination, .dropdown-menu, .mdl-dropdown-content')) return;

      const row = anchor.closest('tr, [id^="ml"], [id^="content_"], [id^="mylist_"], [id^="list_"], .mdl-style-list-item, .dramalist-item, .list-item, li, article, div');
      if (row?.querySelector?.('.mdl-style-col-empty')) return;
      const country = normalizeCountryName(text(q('.mdl-style-col-country', row)));
      pushEntry({ row, titleAnchor: anchor, country });
    });
    return dedupeCountryEntries(entries);
  }

  function dedupeCountryEntries(entries) {
    const seen = new Set();
    return (Array.isArray(entries) ? entries : []).filter((entry) => {
      const key = entry?.id || `${String(entry?.title || '').toLowerCase()}|${String(entry?.country || '').toLowerCase()}`;
      if (!key || seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  }

  function getProfileCountryListCache(username) {
    const store = getLocalCache(STORAGE_PROFILE_COUNTRY_LIST_CACHE);
    return store?.[String(username || '').toLowerCase()] || {};
  }

  function persistProfileCountryListCache(username, status, entries) {
    if (!username || !status || !Array.isArray(entries) || !entries.length) return;
    const store = getLocalCache(STORAGE_PROFILE_COUNTRY_LIST_CACHE);
    const key = String(username || '').toLowerCase();
    const userStore = store[key] || {};
    userStore[status] = {
      updatedAt: Date.now(),
      entries: dedupeCountryEntries(entries),
    };
    store[key] = userStore;
    setLocalCache(STORAGE_PROFILE_COUNTRY_LIST_CACHE, store);
  }

  function getCountryCacheStatusFromWrapperId(wrapperId) {
    const raw = String(wrapperId || '').toLowerCase();
    if (/(^|_)(1)$/.test(raw) || /watching/.test(raw)) return 'watching';
    if (/(^|_)(2)$/.test(raw) || /completed/.test(raw)) return 'completed';
    if (/(^|_)(4)$/.test(raw) || /on[_-]?hold/.test(raw)) return 'on_hold';
    if (/(^|_)(5)$/.test(raw) || /dropped/.test(raw)) return 'dropped';
    return '';
  }

  function collectAndPersistCurrentDramalistPage() {
    const context = getDramalistPathContext();
    if (!context?.username) return;
    const entries = extractCountryEntriesFromRenderedDramalistPage(document);
    if (!entries.length) return;

    if (['watching', 'completed', 'on_hold', 'dropped'].includes(context.status)) {
      persistProfileCountryListCache(context.username, context.status, entries);
      return;
    }

    const byStatus = { watching: [], completed: [], on_hold: [], dropped: [] };
    entries.forEach((entry) => {
      const status = getCountryCacheStatusFromWrapperId(entry.wrapperId);
      if (status && byStatus[status]) byStatus[status].push(entry);
    });
    Object.entries(byStatus).forEach(([status, statusEntries]) => {
      if (statusEntries.length) persistProfileCountryListCache(context.username, status, statusEntries);
    });
  }

  function initDramalistCountryCacheCollector() {
    if (!isDramalistPage()) return;
    const collectSoon = () => collectAndPersistCurrentDramalistPage();

    if (dramalistCollectorHref !== location.href) {
      dramalistCollectorHref = location.href;
      [700, 1800, 4000, 8000].forEach((ms) => setTimeout(collectSoon, ms));
    }

    if (dramalistCollectorScrollBound) return;
    dramalistCollectorScrollBound = true;
    window.addEventListener('scroll', () => {
      if (!isDramalistPage()) return;
      clearTimeout(dramalistCollectorScrollTimer);
      dramalistCollectorScrollTimer = setTimeout(collectSoon, 500);
    }, { passive: true });
  }

  function getUndecidedStatusLabel() {
    return collapseWhitespace(getSettings().labels?.undecidedStatus || '') || 'Undecided';
  }

  function shouldSkipTextReplacementNode(node) {
    const parent = node?.parentElement;
    if (!parent) return true;
    return !!parent.closest('script, style, textarea, input, select, option');
  }

  function replaceUndecidedTextNodes(root, label) {
    if (!root) return;
    const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
      acceptNode(node) {
        if (shouldSkipTextReplacementNode(node)) return NodeFilter.FILTER_REJECT;
        return /Undecided/i.test(node.nodeValue || '') ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT;
      },
    });
    const nodes = [];
    while (walker.nextNode()) nodes.push(walker.currentNode);
    nodes.forEach((node) => {
      node.nodeValue = String(node.nodeValue || '').replace(/\bUndecided\b/g, () => label);
    });
  }

  function setUndecidedIcon(iconRoot, isV2 = false) {
    if (!iconRoot || iconRoot.dataset.betterMdlUndecidedIcon === '1') return;
    iconRoot.dataset.betterMdlUndecidedIcon = '1';
    iconRoot.innerHTML = `
      <svg class="${NS}-undecided-icon${isV2 ? ' is-v2' : ''}" viewBox="0 0 24 24" aria-hidden="true" focusable="false">
        <path d="M7 3h7l5 5v9.5A3.5 3.5 0 0 1 15.5 21h-9A3.5 3.5 0 0 1 3 17.5v-11A3.5 3.5 0 0 1 6.5 3H7z"></path>
        <path d="M14 3v4.2A1.8 1.8 0 0 0 15.8 9H20"></path>
        <path d="M7.5 12h5"></path>
        <path d="M7.5 15.5H11"></path>
        <path d="M16.5 13.5v5"></path>
        <path d="M14 16h5"></path>
      </svg>
    `;
  }

  function initDramalistUndecidedLabel() {
    if (!isDramalistPage()) return;
    const label = getUndecidedStatusLabel();
    const root = q('#mydramalist_v2') || q('#content') || q('#container') || q('main') || document.body;
    if (!root) return;

    qa('a[href*="/undecided"]', root).forEach((link) => {
      const textNode = q('.text, .nav-link-title, span:not(.icon)', link);
      if (textNode) textNode.textContent = label;
      replaceUndecidedTextNodes(link, label);
      const iconRoot = q('.icon', link);
      if (iconRoot) setUndecidedIcon(iconRoot, !!link.closest('#mydramalist_v2'));
    });

    qa('.filter-item, .status, .dropdown-item, .nav-link', root).forEach((node) => {
      if (/\bUndecided\b/i.test(text(node))) replaceUndecidedTextNodes(node, label);
    });

    qa('.el-select-dropdown__item span', document.body).forEach((node) => {
      if (/\bUndecided\b/i.test(text(node))) replaceUndecidedTextNodes(node, label);
    });
  }

  function scheduleDramalistUndecidedLabel() {
    if (!isDramalistPage()) return;
    const scheduleKey = `${location.href}|${getUndecidedStatusLabel()}`;
    if (dramalistUndecidedScheduleKey === scheduleKey) {
      initDramalistUndecidedLabel();
      return;
    }
    dramalistUndecidedScheduleKey = scheduleKey;
    [0, 250, 800, 1800, 3500].forEach((ms) => setTimeout(initDramalistUndecidedLabel, ms));
  }

  function extractCountryEntriesFromDramalistDoc(doc) {
    const entries = [];
    const roots = qa('table, .list-item, .dramalist-item, .mdl-style-list, .mdl-style-list-item, [class*="list-item"]', doc);
    roots.forEach((table) => {
      const indexes = getDramalistHeaderIndexes(table);

      const rows = table.matches?.('table') ? qa('tbody tr', table) : [table];
      rows.forEach((row) => {
        const cells = qa('td', row);
        const country = getCountryFromDramalistRow(row, cells, indexes);

        const titleAnchor = findDramalistTitleAnchor(row);
        const href = titleAnchor?.getAttribute('href') || '';
        const id = collapseWhitespace(href.match(/\/(\d+)(?:[-/]|$)/)?.[1] || '');
        const title = collapseWhitespace(text(titleAnchor) || text(cells[indexes.title]) || text(row));
        if (!id && !title) return;
        entries.push({ id, title, country, href, wrapperId: getDramalistRowWrapperId(row) });
      });
    });
    return entries;
  }

  function extractCountryEntriesFromDramalistCountryCells(doc, allowedWrapperIds = null) {
    const entries = [];
    const allowedIds = Array.isArray(allowedWrapperIds) && allowedWrapperIds.length
      ? new Set(allowedWrapperIds)
      : null;
    const debug = {
      source: '/dramalist country cells',
      allowedWrapperIds: allowedWrapperIds || [],
      rows: 0,
      rowsWithCountryCell: 0,
      counted: 0,
      excluded: 0,
      missingCountry: 0,
      unknownCountry: 0,
      rawCountries: {},
      unknownValues: {},
      excludedBuckets: {},
    };

    qa('tr', doc).forEach((row) => {
      if (!row.querySelector('td.mdl-style-col-country')) return;
      debug.rows += 1;
    });

    qa('td.mdl-style-col-country', doc).forEach((cell) => {
      const wrapperId = getDramalistRowWrapperId(cell);
      debug.rowsWithCountryCell += 1;
      if (allowedIds && !allowedIds.has(wrapperId)) {
        debug.excluded += 1;
        debug.excludedBuckets[wrapperId || 'unknown'] = (debug.excludedBuckets[wrapperId || 'unknown'] || 0) + 1;
        return;
      }
      if (wrapperId === 'mylist_3' || wrapperId === 'mylist_6') {
        debug.excluded += 1;
        debug.excludedBuckets[wrapperId || 'unknown'] = (debug.excludedBuckets[wrapperId || 'unknown'] || 0) + 1;
        return;
      }

      const row = cell.closest('tr');
      const titleAnchor = row ? findDramalistTitleAnchor(row) : null;
      const href = titleAnchor?.getAttribute('href') || '';
      const id = collapseWhitespace(
        href.match(/\/(\d+)(?:[-/]|$)/)?.[1]
        || row?.id?.replace(/^ml/i, '')
        || '',
      );
      const title = collapseWhitespace(text(titleAnchor) || text(row));
      if (!id && !title) return;

      const rawCountry = normalizeCountryName(text(cell));
      if (!rawCountry) {
        debug.missingCountry += 1;
        entries.push({ id, title, country: '', href, wrapperId });
        return;
      }

      debug.rawCountries[rawCountry] = (debug.rawCountries[rawCountry] || 0) + 1;
      const country = getKnownCountryFromText(rawCountry);
      if (!country) {
        debug.unknownCountry += 1;
        debug.unknownValues[rawCountry] = (debug.unknownValues[rawCountry] || 0) + 1;
        entries.push({ id, title, country: rawCountry, href, wrapperId });
        debug.counted += 1;
        return;
      }

      entries.push({ id, title, country, href, wrapperId });
      debug.counted += 1;
    });
    debug.entries = entries.length;
    setDebugCache('country:last', debug);
    return entries;
  }

  function extractCountryFromTitleDoc(doc) {
    if (!doc) return '';
    const detailText = collapseWhitespace(
      text(q('.box.clear.hidden-sm-down', doc))
      || text(q('.col-lg-4.col-md-4', doc))
      || text(q('[class*="details"]', doc))
      || text(doc.body),
    );
    return getKnownCountryFromText(detailText, true);
  }

  async function fetchTitleCountry(entry) {
    const href = entry?.href || (entry?.id ? `/${entry.id}` : '');
    if (!href) return '';
    const doc = await fetchDramalistDocument(createAbsoluteUrl(href));
    return extractCountryFromTitleDoc(doc);
  }

  async function enrichCountryEntriesFromTitlePages(entries) {
    const byKey = new Map();
    entries.forEach((entry) => {
      const key = entry.id || entry.title.toLowerCase();
      if (!key || byKey.has(key)) return;
      byKey.set(key, entry);
    });

    const unique = Array.from(byKey.values());
    const queue = unique.filter((entry) => !isKnownCountryName(entry.country));
    let cursor = 0;
    const workers = Array.from({ length: 5 }, async () => {
      while (cursor < queue.length) {
        const index = cursor;
        cursor += 1;
        const entry = queue[index];
        const country = await fetchTitleCountry(entry).catch(() => '');
        if (country) entry.country = country;
      }
    });
    await Promise.all(workers);
    return unique;
  }

  function normalizeMdlApiWatchlistEntry(item) {
    const titleData = item?.title || {};
    const id = collapseWhitespace(String(titleData.id || item?.title_id || item?.id || ''));
    const title = collapseWhitespace(titleData.title || item?.title || '');
    const country = normalizeCountryName(titleData.country || item?.country || '');
    const slug = collapseWhitespace(titleData.slug || titleData.permalink || '');
    const href = slug
      ? (slug.startsWith('/') ? slug : `/${slug}`)
      : (id ? `/${id}` : '');
    if (!id && !title) return null;
    return { id, title, country, href };
  }

  function findMdlApiKey() {
    const candidates = [
      window.MDL_API_KEY,
      window.__MDL_API_KEY__,
      document.querySelector('meta[name="mdl-api-key"]')?.getAttribute('content'),
      document.querySelector('meta[name="api-key"]')?.getAttribute('content'),
    ].map(collapseWhitespace).filter(Boolean);
    return candidates[0] || '';
  }

  async function fetchMdlApiWatchlistPage(type, page, token) {
    const params = new URLSearchParams({
      page: String(page),
      limit: '100',
      lang: 'en-US',
    });
    const headers = {
      Accept: 'application/json',
      authorization: `Bearer ${token}`,
    };
    const apiKey = findMdlApiKey();
    if (apiKey) headers['mdl-api-key'] = apiKey;

    const apiBase = apiKey ? 'https://api.mydramalist.com/v1' : '/v1';
    const response = await fetch(`${apiBase}/sync/mylist/${encodeURIComponent(type)}?${params.toString()}`, {
      headers,
      credentials: 'same-origin',
    }).catch(() => null);
    if (!response?.ok) return { items: [], ok: false, status: response?.status || 0 };
    const payload = await response.json().catch(() => null);
    const list = Array.isArray(payload) ? payload : (Array.isArray(payload?.data) ? payload.data : []);
    return { items: list.map(normalizeMdlApiWatchlistEntry).filter(Boolean), ok: true, status: response.status };
  }

  async function fetchProfileCountryEntriesFromMdlApi(username) {
    const token = getToken();
    const currentUsername = getCurrentUsername();
    const normalizedUsername = String(username || '').toLowerCase();
    const normalizedCurrentUsername = String(currentUsername || '').toLowerCase();
    const isOwnProfile = !!normalizedUsername && (!normalizedCurrentUsername || normalizedUsername === normalizedCurrentUsername);

    const debug = {
      source: '/v1/sync/mylist',
      username,
      currentUsername,
      hasToken: !!token,
      hasApiKey: !!findMdlApiKey(),
      skippedReason: '',
      types: [],
      totalRawEntries: 0,
    };

    if (!token || !isOwnProfile) {
      debug.skippedReason = !token ? 'missing token' : 'not current profile';
      setDebugCache('country:api', debug);
      return null;
    }

    const entries = [];
    const types = ['watchlist', 'completed', 'onhold', 'dropped'];

    for (const type of types) {
      const typeDebug = { type, pages: [] };
      let page = 1;
      const seenPageKeys = new Set();
      while (page <= 80) {
        const result = await fetchMdlApiWatchlistPage(type, page, token);
        typeDebug.pages.push({ page, ok: result.ok, status: result.status, entries: result.items.length });
        if (!result.ok || !result.items.length) break;

        const pageKey = result.items.map((entry) => entry.id || `${entry.title}|${entry.country}`).join('|');
        if (seenPageKeys.has(pageKey)) break;
        seenPageKeys.add(pageKey);
        entries.push(...result.items);
        if (result.items.length < 100) break;
        page += 1;
      }
      debug.types.push(typeDebug);
    }

    debug.totalRawEntries = entries.length;
    setDebugCache('country:api', debug);

    return entries.length ? entries : null;
  }

  const delay = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

  function createDramalistIframe(url) {
    return new Promise((resolve, reject) => {
      const iframe = document.createElement('iframe');
      let settled = false;
      const finish = (value) => {
        if (settled) return;
        settled = true;
        resolve(value);
      };
      const fail = (error) => {
        if (settled) return;
        settled = true;
        reject(error);
      };
      iframe.src = url;
      iframe.style.position = 'fixed';
      iframe.style.left = '-1200px';
      iframe.style.top = '0';
      iframe.style.width = '1000px';
      iframe.style.height = '900px';
      iframe.style.opacity = '0.01';
      iframe.style.pointerEvents = 'none';
      iframe.style.zIndex = '-1';
      iframe.setAttribute('aria-hidden', 'true');
      iframe.addEventListener('load', () => finish(iframe), { once: true });
      iframe.addEventListener('error', fail, { once: true });
      document.body.appendChild(iframe);
      setTimeout(() => {
        if (!settled) {
          iframe.remove();
          fail(new Error('iframe load timeout'));
        }
      }, 6500);
    });
  }

  async function scrollDramalistIframe(iframe) {
    const win = iframe?.contentWindow;
    const doc = iframe?.contentDocument;
    if (!win || !doc) return { rows: 0, scrolls: 0 };

    let lastRows = 0;
    let stableRounds = 0;
    let scrolls = 0;
    for (let i = 0; i < 10 && stableRounds < 3; i += 1) {
      const rows = qa('td.mdl-style-col-country, tbody[id^="content_"] tr, tr[id^="ml"]', doc).length;
      if (rows <= lastRows) stableRounds += 1;
      else stableRounds = 0;
      lastRows = Math.max(lastRows, rows);
      win.scrollTo(0, doc.documentElement.scrollHeight || doc.body.scrollHeight || 999999);
      scrolls += 1;
      await delay(300);
    }
    return { rows: lastRows, scrolls };
  }

  async function fetchDramalistEntriesViaIframe(target) {
    const iframe = await createDramalistIframe(buildDramalistPageUrl(target.urls[0], 1));
    try {
      await delay(500);
      const scrollInfo = await scrollDramalistIframe(iframe);
      const doc = iframe.contentDocument;
      const hasCountryCells = qa('td.mdl-style-col-country', doc).length > 0;
      const directEntries = extractCountryEntriesFromDramalistCountryCells(doc, target.wrapperIds);
      const entries = directEntries.length || hasCountryCells ? directEntries : extractCountryEntriesFromDramalistDoc(doc);
      return {
        entries,
        debug: {
          status: target.status,
          rowsSeen: scrollInfo.rows,
          scrolls: scrollInfo.scrolls,
          entries: entries.length,
          directEntries: directEntries.length,
        },
      };
    } finally {
      iframe.remove();
    }
  }

  async function fetchProfileCountryEntriesFromRenderedDramalist(statusTargets) {
    const debug = {
      source: 'iframe rendered dramalist',
      statuses: [],
      totalRawEntries: 0,
    };
    const entries = [];
    for (const target of statusTargets) {
      const result = await fetchDramalistEntriesViaIframe(target).catch((error) => ({
        entries: [],
        debug: { status: target.status, error: String(error?.message || error || 'error') },
      }));
      entries.push(...result.entries);
      debug.statuses.push(result.debug);
    }
    debug.totalRawEntries = entries.length;
    setDebugCache('country:iframe', debug);
    return entries.length ? { entries, debug } : null;
  }

  function summarizeMdlApiDebug() {
    const debug = safeJsonParse(localStorage.getItem(`${NS}:debug:country:api`), null);
    if (!debug) return '';
    if (debug.skippedReason) return debug.skippedReason;
    const firstPage = (debug.types || []).flatMap((item) => item.pages || [])[0];
    if (firstPage && !firstPage.ok) return `HTTP ${firstPage.status || 0}`;
    if (Number.isFinite(Number(debug.totalRawEntries))) return `raw ${debug.totalRawEntries}`;
    return '';
  }

  function getDramalistStatusUrls(doc, username) {
    const base = `/dramalist/${encodeURIComponent(username)}`;
    const wanted = [
      [/currently\s+watching/i, `${base}?status=1`],
      [/completed/i, `${base}?status=2`],
      [/on\s*hold/i, `${base}?status=4`],
      [/dropped/i, `${base}?status=5`],
    ];
    const urls = [];
    wanted.forEach(([pattern, fallback]) => {
      const anchor = qa('a[href*="/dramalist/"]', doc).find((node) => pattern.test(text(node)));
      const href = anchor?.getAttribute('href') || fallback;
      urls.push(createAbsoluteUrl(href));
    });
    return [...new Set(urls)];
  }

  function getMaxDramalistPage(doc) {
    const numbers = qa('.pagination a, .page-link, a[href*="page="]', doc)
      .map((node) => Number(text(node)))
      .filter((value) => Number.isFinite(value) && value > 0);
    return Math.max(1, ...numbers);
  }

  function buildDramalistPageUrl(url, page) {
    const next = new URL(url, location.origin);
    next.searchParams.set('page', String(page));
    next.searchParams.set('lang', 'en-US');
    return next.href;
  }

  function getDramalistPaginationUrls(doc, currentUrl) {
    const current = createAbsoluteUrl(currentUrl);
    return [...new Set(qa('.pagination a[href], .page-link[href], a[href*="page="]', doc)
      .map((anchor) => createAbsoluteUrl(anchor.getAttribute('href') || ''))
      .filter(Boolean)
      .filter((href) => href !== current && /\/dramalist\//i.test(href)))];
  }

  function collectDramalistEndpointHints(doc) {
    const hints = new Set();
    const addHint = (value) => {
      const raw = collapseWhitespace(value);
      if (!raw || raw.length > 240) return;
      if (/dramalist|mylist|watchaction|\/v1\/|ajax|load[_-]?more|content_/i.test(raw)) hints.add(raw);
    };

    qa('a[href], form[action], [data-url], [data-href], [data-api], [data-endpoint], [data-load], [data-page], [data-target], [id^="mylist_"], [id^="content_"]', doc)
      .forEach((node) => {
        ['href', 'action', 'data-url', 'data-href', 'data-api', 'data-endpoint', 'data-load', 'data-page', 'data-target', 'id'].forEach((attr) => {
          addHint(node.getAttribute?.(attr) || '');
        });
      });

    qa('script', doc).forEach((script) => {
      const body = script.getAttribute('src') || script.textContent || '';
      Array.from(body.matchAll(/(?:https?:\/\/[^"'`\s]+|\/[^"'`\s]*(?:dramalist|mylist|watchaction|v1|ajax|load)[^"'`\s]*)/gi))
        .slice(0, 40)
        .forEach((match) => addHint(match[0]));
    });

    return Array.from(hints).slice(0, 80);
  }

  function simplifyDebugUrl(value) {
    try {
      const url = new URL(value, location.origin);
      return `${url.origin === location.origin ? '' : url.origin}${url.pathname}${url.search}`.slice(0, 180);
    } catch {
      return collapseWhitespace(value).slice(0, 180);
    }
  }

  function collectPerformanceEndpointHints() {
    try {
      return [...new Set(performance.getEntriesByType('resource')
        .map((entry) => simplifyDebugUrl(entry.name || ''))
        .filter((value) => /\/v1\/|dramalist|profile|ajax|mylist|list|stats|watch/i.test(value))
        .filter((value) => !/google|doubleclick|quantserve|htlbid|seedtag|adsbygoogle/i.test(value)))]
        .slice(0, 80);
    } catch {
      return [];
    }
  }

  async function fetchDramalistDocument(url) {
    const response = await fetch(url, { credentials: 'same-origin' }).catch(() => null);
    if (!response?.ok) return null;
    const html = await response.text().catch(() => '');
    return html ? new DOMParser().parseFromString(html, 'text/html') : null;
  }

  function buildCountryStatsFromEntries(entries) {
    const byCountry = new Map();
    const seen = new Set();
    let knownCountryEntries = 0;
    let duplicateEntries = 0;
    entries.forEach((entry) => {
      if (!isKnownCountryName(entry.country)) return;
      knownCountryEntries += 1;
      const dedupeKey = entry.id || `${entry.title.toLowerCase()}|${entry.country.toLowerCase()}`;
      if (!dedupeKey || seen.has(dedupeKey)) {
        duplicateEntries += 1;
        return;
      }
      seen.add(dedupeKey);
      byCountry.set(entry.country, (byCountry.get(entry.country) || 0) + 1);
    });

    const countries = Array.from(byCountry.entries())
      .map(([country, count]) => ({ country, count }))
      .sort((a, b) => b.count - a.count || a.country.localeCompare(b.country));

    return {
      total: countries.reduce((sum, item) => sum + item.count, 0),
      countries,
      generatedAt: Date.now(),
      knownCountryEntries,
      duplicateEntries,
    };
  }

  function countUniqueCountryEntryKeys(entries) {
    const seen = new Set();
    entries.forEach((entry) => {
      const key = entry.id || `${String(entry.title || '').toLowerCase()}|${String(entry.country || '').toLowerCase()}`;
      if (key) seen.add(key);
    });
    return seen.size;
  }

  function formatStatusDebug(statusSummaries) {
    if (!Array.isArray(statusSummaries) || !statusSummaries.length) return '';
    return statusSummaries
      .map((item) => `${item.status}:${item.unique}/${item.raw}`)
      .join(',');
  }

  async function buildProfileCountryStatsFromListCache(username, expectedTotal = 0) {
    const cache = getProfileCountryListCache(username);
    const statuses = ['watching', 'completed', 'on_hold', 'dropped'];
    const entries = getProfileCountryListCacheEntries(username, expectedTotal);
    if (!entries.length) return null;

    const enrichedEntries = await enrichCountryEntriesFromTitlePages(entries);
    const stats = buildCountryStatsFromEntries(enrichedEntries);
    return {
      ...stats,
      expectedTotal,
      rawTotal: entries.length,
      enrichedTotal: enrichedEntries.length,
      missingCountry: enrichedEntries.filter((entry) => !isKnownCountryName(entry.country)).length,
      source: 'list-cache',
      htmlDebug: `known ${stats.knownCountryEntries}`,
      statusDebug: statuses
        .map((status) => `${status}:${dedupeCountryEntries(cache?.[status]?.entries || []).length}`)
        .join(','),
    };
  }

  function buildProfileCountryStatsFromBasicDramalistDoc(doc, expectedTotal = 0) {
    if (!doc) return null;
    const entries = dedupeCountryEntries(extractCountryEntriesFromDramalistCountryCells(doc));
    if (!entries.length) return null;
    const stats = buildCountryStatsFromEntries(entries);
    if (!stats.countries.length) return null;
    return {
      ...stats,
      expectedTotal,
      rawTotal: entries.length,
      enrichedTotal: entries.length,
      missingCountry: entries.filter((entry) => !isKnownCountryName(entry.country)).length,
      source: 'list-basic',
      htmlDebug: `basic ${stats.knownCountryEntries}`,
    };
  }

  async function buildProfileCountryStatsFromBasicDramalistTitlePages(doc, expectedTotal = 0) {
    if (!doc) return null;
    const entries = dedupeCountryEntries(extractCountryEntriesFromRenderedDramalistPage(doc))
      .filter((entry) => entry.href || entry.id)
      .slice(0, PROFILE_COUNTRY_TITLE_ENRICH_LIMIT);
    if (!entries.length) return null;

    const enrichedEntries = await enrichCountryEntriesFromTitlePages(entries);
    const stats = buildCountryStatsFromEntries(enrichedEntries);
    if (!stats.countries.length) return null;

    return {
      ...stats,
      expectedTotal,
      rawTotal: entries.length,
      enrichedTotal: enrichedEntries.length,
      missingCountry: enrichedEntries.filter((entry) => !isKnownCountryName(entry.country)).length,
      source: 'list-basic-title-pages',
      htmlDebug: `basic-title-pages ${stats.knownCountryEntries}/${enrichedEntries.length}`,
    };
  }

  function getProfileCountryListCacheEntries(username, expectedTotal = 0) {
    const cache = getProfileCountryListCache(username);
    const statuses = ['watching', 'completed', 'on_hold', 'dropped'];
    const byStatus = Object.fromEntries(statuses.map((status) => [
      status,
      dedupeCountryEntries(cache?.[status]?.entries || []),
    ]));
    let entries = dedupeCountryEntries(statuses.flatMap((status) => byStatus[status]));
    const targetTotal = Number(expectedTotal) || 0;
    const extraCount = entries.length - targetTotal;
    if (targetTotal && extraCount > 0 && extraCount <= 5 && isOwnProfileUsername(username)) {
      const trimmedByStatus = { ...byStatus };
      let remaining = extraCount;
      ['completed', 'watching', 'dropped', 'on_hold'].forEach((status) => {
        if (!remaining) return;
        const removeCount = Math.min(remaining, trimmedByStatus[status].length);
        trimmedByStatus[status] = trimmedByStatus[status].slice(removeCount);
        remaining -= removeCount;
      });
      entries = dedupeCountryEntries(statuses.flatMap((status) => trimmedByStatus[status]));
    }
    return entries;
  }

  function buildProfileCountryStatsFromListCacheFast(username, expectedTotal = 0) {
    const entries = getProfileCountryListCacheEntries(username, expectedTotal);
    if (!entries.length) return null;
    const stats = buildCountryStatsFromEntries(entries);
    if (!stats.countries.length) return null;
    return {
      ...stats,
      expectedTotal,
      rawTotal: entries.length,
      enrichedTotal: entries.length,
      missingCountry: entries.filter((entry) => !isKnownCountryName(entry.country)).length,
      source: 'list-cache',
      listCacheDebug: getProfileCountryListCacheDebug(username),
    };
  }

  async function buildProfileCountryStatsFromListCacheEnriched(username, expectedTotal = 0) {
    const entries = getProfileCountryListCacheEntries(username, expectedTotal);
    if (!entries.length) return null;

    const knownEntries = entries.filter((entry) => isKnownCountryName(entry.country));
    const unknownEntries = entries.filter((entry) => !isKnownCountryName(entry.country) && (entry.href || entry.id));
    const enrichLimit = expectedTotal && expectedTotal <= PROFILE_COUNTRY_TITLE_ENRICH_LIMIT
      ? expectedTotal
      : PROFILE_COUNTRY_TITLE_ENRICH_LIMIT;
    const entriesToEnrich = dedupeCountryEntries([
      ...knownEntries,
      ...unknownEntries.slice(0, enrichLimit),
    ]);

    const enrichedEntries = await enrichCountryEntriesFromTitlePages(entriesToEnrich);
    const stats = buildCountryStatsFromEntries(enrichedEntries);
    if (!stats.countries.length) return null;

    return {
      ...stats,
      expectedTotal,
      rawTotal: entries.length,
      enrichedTotal: enrichedEntries.length,
      missingCountry: enrichedEntries.filter((entry) => !isKnownCountryName(entry.country)).length,
      source: 'list-cache-title-pages',
      listCacheDebug: getProfileCountryListCacheDebug(username),
      htmlDebug: `title-pages ${stats.knownCountryEntries}/${enrichedEntries.length}`,
    };
  }

  function getProfileCountryListCacheDebug(username) {
    const cache = getProfileCountryListCache(username);
    return ['watching', 'completed', 'on_hold', 'dropped']
      .map((status) => `${status}:${dedupeCountryEntries(cache?.[status]?.entries || []).length}`)
      .join(',');
  }

  function summarizeWrapperCounts(wrapperCounts) {
    return Object.entries(wrapperCounts || {})
      .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]))
      .slice(0, 5)
      .map(([key, count]) => `${key}:${count}`)
      .join(',');
  }

  async function scrapeProfileCountryStats(username, expectedTotal = 0) {
    const apiEntries = await fetchProfileCountryEntriesFromMdlApi(username).catch(() => null);
    if (apiEntries?.length) {
      const apiStats = buildCountryStatsFromEntries(apiEntries);
      return {
        ...apiStats,
        expectedTotal,
        rawTotal: apiEntries.length,
        enrichedTotal: apiEntries.length,
        missingCountry: apiEntries.filter((entry) => !isKnownCountryName(entry.country)).length,
        source: 'api',
        apiDebug: summarizeMdlApiDebug(),
      };
    }

    const cachedListEntries = getProfileCountryListCacheEntries(username, expectedTotal);
    const cachedListStats = await buildProfileCountryStatsFromListCache(username, expectedTotal).catch(() => null);
    if (cachedListStats?.countries?.length && (!expectedTotal || Number(cachedListStats.total) === Number(expectedTotal))) return cachedListStats;

    const firstDoc = await fetchDramalistDocument(createAbsoluteUrl(`/dramalist/${encodeURIComponent(username)}?lang=en-US`));
    if (!firstDoc) return buildCountryStatsFromEntries([]);
    const basicListStats = buildProfileCountryStatsFromBasicDramalistDoc(firstDoc, expectedTotal);
    if (basicListStats?.countries?.length && cachedListStats?.countries?.length) {
      if (Number(cachedListStats.total) >= Number(basicListStats.total)) return cachedListStats;
    }
    if (basicListStats?.countries?.length && !cachedListEntries.length) return basicListStats;

    const endpointHints = collectDramalistEndpointHints(firstDoc);
    const performanceHints = collectPerformanceEndpointHints();

    const base = `/dramalist/${encodeURIComponent(username)}`;
    const statusTargets = [
      { status: 'watching', wrapperIds: ['mylist_1', 'list_1', 'content_1'], urls: [createAbsoluteUrl(`${base}/watching`), createAbsoluteUrl(`${base}?status=1`)] },
      { status: 'completed', wrapperIds: ['mylist_2', 'list_2', 'content_2'], urls: [createAbsoluteUrl(`${base}/completed`), createAbsoluteUrl(`${base}?status=2`)] },
      { status: 'on_hold', wrapperIds: ['mylist_4', 'list_4', 'content_4'], urls: [createAbsoluteUrl(`${base}/on_hold`), createAbsoluteUrl(`${base}?status=4`)] },
      { status: 'dropped', wrapperIds: ['mylist_5', 'list_5', 'content_5'], urls: [createAbsoluteUrl(`${base}/dropped`), createAbsoluteUrl(`${base}?status=5`)] },
    ];
    getDramalistStatusUrls(firstDoc, username).forEach((url) => {
      const matched = statusTargets.find((target) => target.urls.some((candidate) => candidate === url));
      if (!matched) statusTargets.push({ status: 'linked', wrapperIds: [], urls: [url] });
    });

    const listCacheDebug = getProfileCountryListCacheDebug(username);

    const allEntries = [];
    const scrapeDebug = {
      source: '/dramalist paged country stats',
      username,
      urls: [],
      totalRawEntries: 0,
      endpointHints,
      performanceHints,
      statusSummaries: [],
    };

    for (const target of statusTargets) {
      const targetEntries = [];
      const targetSeenKeys = new Set();
      const targetWrapperCounts = {};
      for (const statusUrl of [...new Set(target.urls)]) {
      const pendingUrls = [buildDramalistPageUrl(statusUrl, 1)];
      const visitedUrls = new Set();
      const seenPageKeys = new Set();
      const urlDebug = {
        status: target.status,
        url: statusUrl,
        pages: [],
      };

      while (pendingUrls.length && visitedUrls.size < 80) {
        const pageUrl = pendingUrls.shift();
        const normalizedPageUrl = createAbsoluteUrl(pageUrl);
        if (!normalizedPageUrl || visitedUrls.has(normalizedPageUrl)) continue;
        visitedUrls.add(normalizedPageUrl);

        const doc = await fetchDramalistDocument(normalizedPageUrl);
        if (!doc) break;

        const hasCountryCells = qa('td.mdl-style-col-country', doc).length > 0;
        const directEntries = extractCountryEntriesFromDramalistCountryCells(doc, target.wrapperIds);
        const entries = directEntries.length || hasCountryCells ? directEntries : extractCountryEntriesFromDramalistDoc(doc);
        const pageKey = entries.map((entry) => entry.id || `${entry.title}|${entry.country}`).join('|');
        urlDebug.pages.push({
          page: visitedUrls.size,
          url: normalizedPageUrl,
          entries: entries.length,
          directEntries: directEntries.length,
          parser: directEntries.length ? 'country-cells' : 'generic',
          paginationMax: getMaxDramalistPage(doc),
          paginationUrls: getDramalistPaginationUrls(doc, normalizedPageUrl).length,
        });
        if (!entries.length || seenPageKeys.has(pageKey)) break;

        entries.forEach((entry) => {
          allEntries.push(entry);
          targetEntries.push(entry);
          const wrapperKey = entry.wrapperId || 'none';
          targetWrapperCounts[wrapperKey] = (targetWrapperCounts[wrapperKey] || 0) + 1;
          const key = entry.id || `${String(entry.title || '').toLowerCase()}|${String(entry.country || '').toLowerCase()}`;
          if (key) targetSeenKeys.add(key);
        });
        seenPageKeys.add(pageKey);
        getDramalistPaginationUrls(doc, normalizedPageUrl).forEach((href) => {
          if (!visitedUrls.has(href) && !pendingUrls.includes(href)) pendingUrls.push(href);
        });

        if (!pendingUrls.length) {
          const nextFallback = buildDramalistPageUrl(statusUrl, visitedUrls.size + 1);
          if (!visitedUrls.has(nextFallback)) pendingUrls.push(nextFallback);
        }
      }
      scrapeDebug.urls.push(urlDebug);
      }
      scrapeDebug.statusSummaries.push({
        status: target.status,
        raw: targetEntries.length,
        unique: targetSeenKeys.size,
        wrappers: targetWrapperCounts,
      });
    }

    scrapeDebug.totalRawEntries = allEntries.length;
    scrapeDebug.rawUniqueEntries = countUniqueCountryEntryKeys(allEntries);
    setDebugCache('country:scrape', scrapeDebug);

    const combinedEntries = cachedListEntries.length
      ? dedupeCountryEntries([...cachedListEntries, ...allEntries])
      : allEntries;
    const enrichedEntries = await enrichCountryEntriesFromTitlePages(combinedEntries);
    const builtStats = buildCountryStatsFromEntries(enrichedEntries);
    scrapeDebug.enrichedEntries = enrichedEntries.length;
    scrapeDebug.finalTotal = builtStats.total;
    scrapeDebug.missingCountry = enrichedEntries.filter((entry) => !isKnownCountryName(entry.country)).length;
    scrapeDebug.knownCountryEntries = builtStats.knownCountryEntries;
    scrapeDebug.duplicateEntries = builtStats.duplicateEntries;
    setDebugCache('country:scrape', scrapeDebug);

    const result = {
      ...builtStats,
      expectedTotal,
      rawTotal: combinedEntries.length,
      enrichedTotal: enrichedEntries.length,
      missingCountry: scrapeDebug.missingCountry,
      source: cachedListEntries.length ? 'list-cache+html' : 'html',
      apiDebug: summarizeMdlApiDebug(),
      htmlDebug: `unique ${scrapeDebug.rawUniqueEntries}`,
      listCacheDebug,
      statusDebug: formatStatusDebug(scrapeDebug.statusSummaries),
      endpointHints: endpointHints.slice(0, 12),
      performanceHints: performanceHints.slice(0, 16),
      wrapperHints: scrapeDebug.statusSummaries.map((item) => `${item.status}(${summarizeWrapperCounts(item.wrappers)})`),
    };
    if (cachedListStats?.countries?.length) {
      if (expectedTotal && Number(cachedListStats.total) === Number(expectedTotal)) return cachedListStats;
      if (!expectedTotal && Number(cachedListStats.total) > Number(result.total)) return cachedListStats;
    }
    return result;
  }

  async function resolveProfileCountryStats(username, force = false) {
    const expectedTotal = getProfileStatisticsTitleTotal();
    if (!force) {
      const cached = getPersistedProfileCountryStats(username);
      if (cached && isProfileCountryStatsExpected(cached, expectedTotal)) return cached;
    }

    const previous = getPersistedProfileCountryStats(username, true);
    const stats = await scrapeProfileCountryStats(username, expectedTotal);
    let bestStats = stats;
    if (previous && !isProfileCountryStatsExpected(stats, expectedTotal)) {
      if (isProfileCountryStatsExpected(previous, expectedTotal)) {
        bestStats = previous;
      } else if (!expectedTotal && Number(previous.total) > Number(stats?.total)) {
        bestStats = previous;
      } else if (expectedTotal && Number(stats?.total) < Math.floor(expectedTotal * 0.95) && Number(previous.total) <= expectedTotal) {
        bestStats = previous;
      }
    }
    persistProfileCountryStats(username, bestStats, expectedTotal);
    return bestStats;
  }

  async function resolveProfileCountryStatsQuick(username, expectedTotal = getProfileStatisticsTitleTotal()) {
    const listCacheStats = buildProfileCountryStatsFromListCacheFast(username, expectedTotal);
    if (listCacheStats?.countries?.length) return listCacheStats;

    const firstDoc = await fetchDramalistDocument(createAbsoluteUrl(`/dramalist/${encodeURIComponent(username)}?lang=en-US`)).catch(() => null);
    const basicStats = buildProfileCountryStatsFromBasicDramalistDoc(firstDoc, expectedTotal);
    if (basicStats?.countries?.length) return basicStats;

    const basicTitleStats = await buildProfileCountryStatsFromBasicDramalistTitlePages(firstDoc, expectedTotal).catch(() => null);
    if (basicTitleStats?.countries?.length) return basicTitleStats;

    return buildProfileCountryStatsFromListCacheEnriched(username, expectedTotal);
  }

  async function initProfileCountryStats() {
    if (!isProfilePage()) return;
    if (!isFeatureEnabled('profileCountryStats')) {
      restoreExistingProfileStatsCharts();
      q(`.${NS}-country-section`)?.remove();
      return;
    }

    const username = getProfileCountryStatsUsername();
    const section = ensureCountryStatsSection();
    if (!username || !section) return;

    const expectedTotal = getProfileStatisticsTitleTotal();
    const cached = getPersistedProfileCountryStats(username);
    const stale = getPersistedProfileCountryStats(username, true);
    const listCacheFast = buildProfileCountryStatsFromListCacheFast(username, expectedTotal);
    const initKey = [
      username,
      expectedTotal || 0,
      cached?.generatedAt || 0,
      stale?.generatedAt || 0,
      getProfileCountryListCacheDebug(username),
    ].join('|');
    if (section.dataset.countryInitKey === initKey && section.children.length) return;
    section.dataset.countryInitKey = initKey;

    if (cached && isProfileCountryStatsExpected(cached, expectedTotal)) {
      renderProfileCountryStats(cached);
      return;
    }

    const fallback = cached || listCacheFast || stale;
    const hasFallbackDisplay = !!fallback;
    if (fallback) {
      renderProfileCountryStats(fallback);
    } else {
      renderCountryStatsPartialShell(section);
    }

    const loadingKey = initKey;
    if (section.dataset.countryLoadingKey === loadingKey) return;
    section.dataset.countryLoadingKey = loadingKey;

    const requestId = `${Date.now()}:${Math.random()}`;
    section.dataset.countryRequestId = requestId;
    let timeoutId = null;

    if (!hasFallbackDisplay) {
      timeoutId = setTimeout(() => {
        if (section.dataset.countryRequestId !== requestId) return;
        renderCountryStatsPartialShell(section, 'Could not load country stats yet.');
      }, PROFILE_COUNTRY_STATS_LOAD_TIMEOUT_MS);
    }

    resolveProfileCountryStatsQuick(username, expectedTotal)
      .then((stats) => {
        if (section.dataset.countryRequestId !== requestId) return;
        if (timeoutId) clearTimeout(timeoutId);
        if (stats) renderProfileCountryStats(stats);
        else if (!hasFallbackDisplay) renderCountryStatsPartialShell(section, 'Could not load country stats yet.');
      })
      .catch(() => {
        if (section.dataset.countryRequestId !== requestId) return;
        if (timeoutId) clearTimeout(timeoutId);
        if (!hasFallbackDisplay) renderCountryStatsPartialShell(section, 'Could not load country stats yet.');
      });
  }

  function findFilmographyTitleAnchor(row) {
    return qa('td.title a[href*="/"], td:nth-child(2) a[href*="/"], td:nth-child(3) a[href*="/"]', row)
      .find((anchor) => {
        const href = anchor.getAttribute('href') || '';
        return !anchor.querySelector('img') && !/\/people\/|\/profile\/|\/dramalist\//i.test(href);
      })
      || qa('a[href*="/"]', row).find((anchor) => {
        const href = anchor.getAttribute('href') || '';
        return !anchor.querySelector('img') && !/\/people\/|\/profile\/|\/dramalist\//i.test(href);
      })
      || null;
  }

  function renderFilmographyStatusIcons(items) {
    const rows = qa('table.film-list tbody tr');
    if (!rows.length) return;
    if (!isFeatureEnabled('peopleFilmographyIcons')) {
      rows.forEach((row) => qa(`.${NS}-film-status-badge`, row).forEach((node) => node.remove()));
      return;
    }

    const statusConfig = getStatusConfigMap();
    const statusMap = new Map();
    items.forEach((item) => {
      const itemId = collapseWhitespace(String(item?.__bettermdlId || ''));
      const status = Number(item?.status);
      if (itemId && statusConfig[status] && !statusMap.has(itemId)) {
        statusMap.set(itemId, status);
      }
    });

    rows.forEach((row) => {
      qa(`.${NS}-film-status-badge`, row).forEach((node) => node.remove());

      const rowId = collapseWhitespace(
        ((row.getAttribute('class') || '').split(/\s+/).find((value) => value.startsWith('mdl-')) || '').slice(4),
      );
      const status = Number(statusMap.get(rowId));
      const cfg = statusConfig[status];
      if (!cfg) return;

      const titleAnchor = findFilmographyTitleAnchor(row);
      if (!titleAnchor) return;

      const badge = document.createElement('span');
      badge.className = `${NS}-film-status-badge`;
      badge.title = cfg.label;
      badge.setAttribute('aria-label', cfg.label);
      badge.innerHTML = `<i class="${cfg.icon}" style="color:${cfg.color}"></i>`;
      titleAnchor.insertBefore(badge, titleAnchor.firstChild);
    });
  }

  function getFilmographyStatusColor(status) {
    return status?.color || 'color-mix(in srgb, currentColor 30%, transparent)';
  }

  function getFilmographyStatusBadgeBackground(status) {
    return status?.color ? `color-mix(in srgb, ${status.color} 68%, transparent)` : '';
  }

  function getFilmographySectionStateKey(sectionKey) {
    if (sectionKey === getPeopleFilmographyGlobalSectionKey()) return sectionKey;
    return `${location.pathname}:${sectionKey}`;
  }

  function getPeopleFilmographyGlobalSectionKey() {
    return 'filmography-all';
  }

  function getFilmographySectionUiState(sectionKey) {
    const defaults = {
      view: isFeatureEnabled('peopleFilmographyLargeViewDefault') ? 'large' : 'mini',
      sortBy: '',
      sortDir: 'desc',
      hiddenStatuses: [],
    };
    const store = getFilmographyUiState();
    const next = store?.[getFilmographySectionStateKey(sectionKey)] || {};
    return {
      ...defaults,
      ...next,
      hiddenStatuses: Array.isArray(next.hiddenStatuses) ? next.hiddenStatuses : [],
    };
  }

  function setFilmographySectionUiState(sectionKey, patch) {
    const store = getFilmographyUiState();
    const key = getFilmographySectionStateKey(sectionKey);
    store[key] = {
      ...getFilmographySectionUiState(sectionKey),
      ...(patch || {}),
    };
    setFilmographyUiState(store);
  }

  function isPeopleFilmographyHeading(node) {
    return !!(node && node.matches?.('h1, h2, h3, h4, h5, h6') && !/^(details|photos|related articles|feed|articles|comments|recent discussions)$/i.test(text(node)));
  }

  function findPeopleFilmographySections() {
    const main = getMainLeftColumn();
    const seen = new Set();
    return qa('table.film-list', main).map((table, index) => {
      if (seen.has(table)) return null;
      seen.add(table);

      const heading = findHeadingBeforeFilmList(table, main);
      if (!isPeopleFilmographyHeading(heading)) return null;

      const label = text(heading);
      const key = `${slugifySettingKey(label) || 'filmography'}-${index + 1}`;
      return { key, label, heading, table };
    }).filter(Boolean);
  }

  function getPeopleFilmographyBlockNodes(heading) {
    const nodes = [];
    let node = heading;
    while (node) {
      if (node !== heading && node.matches?.('h1, h2, h3, h4, h5, h6')) break;
      if (!node.classList?.contains(`${NS}-toggle-row`) && !node.classList?.contains(`${NS}-toggle-inline`)) {
        nodes.push(node);
      }
      node = node.nextElementSibling;
    }
    return nodes;
  }

  function prioritizePeopleDramaMovieSections(main = getMainLeftColumn()) {
    if (main.dataset.bettermdlDramaMoviePrioritized === location.pathname) return;

    const sections = findPeopleFilmographySections();
    const ordered = [
      ...sections.filter((section) => /^drama$/i.test(section.label || text(section.heading))),
      ...sections.filter((section) => /^movie$/i.test(section.label || text(section.heading))),
    ];
    if (!ordered.length) return;

    const headings = [];
    qa('table.film-list', main).forEach((table) => {
      const heading = findHeadingBeforeFilmList(table, main);
      if (heading && !headings.includes(heading)) headings.push(heading);
    });
    const anchor = headings.find((heading) => !/^(drama|movie)$/i.test(text(heading)));
    if (!anchor?.parentElement) return;

    ordered.forEach((section) => {
      getPeopleFilmographyBlockNodes(section.heading).forEach((node) => {
        if (node !== anchor) anchor.parentElement.insertBefore(node, anchor);
      });
    });

    main.dataset.bettermdlDramaMoviePrioritized = location.pathname;
  }

  function getFilmListHeaderIndexes(table) {
    const headers = qa('thead th', table).map((th) => text(th).toLowerCase());
    const findIndex = (pattern) => headers.findIndex((label) => pattern.test(label));
    return {
      year: findIndex(/^year$/i),
      title: findIndex(/^title$/i),
      episodes: findIndex(/^(#|episodes?)$/i),
      rating: findIndex(/^rating$/i),
      role: findIndex(/^role$/i),
    };
  }

  function parseFilmographyNumber(value) {
    const match = String(value || '').replace(/,/g, '').match(/(\d+(?:\.\d+)?)/);
    return match ? Number(match[1]) : null;
  }

  function parseFilmographyYear(value) {
    const match = String(value || '').match(/\b(19|20)\d{2}\b/);
    return match ? Number(match[0]) : null;
  }

  function formatFilmographyScore(value) {
    return value != null && Number.isFinite(Number(value)) && Number(value) > 0 ? Number(value).toFixed(1) : '0.0';
  }

  function getStatusUserRating(item) {
    const candidates = [
      item?.score,
      item?.rating,
      item?.rate,
      item?.my_score,
      item?.myScore,
      item?.user_score,
      item?.userScore,
      item?.user_rating,
      item?.userRating,
      item?.my_rating,
      item?.myRating,
      item?.watch_score,
      item?.watchScore,
      item?.list_score,
      item?.listScore,
      item?.stats?.score,
      item?.stats?.rating,
      item?.mylist?.score,
      item?.mylist?.rating,
    ];

    for (const candidate of candidates) {
      const value = parseFilmographyNumber(candidate);
      if (value != null && Number.isFinite(value)) return value > 10 && value <= 100 ? value / 10 : value;
    }

    return null;
  }

  function getBetterFilmographyPosterUrl(value) {
    const raw = String(value || '');
    return raw.replace(/([A-Za-z0-9])(?:t|c)(\.(?:jpe?g|png|webp))(?:\?.*)?$/i, '$1$2');
  }

  function getFilmographyStatusMaps(items) {
    const statusConfig = getStatusConfigMap();
    const statusById = new Map();
    const userRatingById = new Map();
    items.forEach((item) => {
      const itemId = collapseWhitespace(String(item?.__bettermdlId || ''));
      const status = Number(item?.status);
      if (itemId && statusConfig[status] && !statusById.has(itemId)) {
        statusById.set(itemId, statusConfig[status]);
      }
      const userRating = getStatusUserRating(item);
      if (itemId && userRating != null && !userRatingById.has(itemId)) {
        userRatingById.set(itemId, userRating);
      }
    });
    return { statusById, statusConfig, userRatingById };
  }

  function normalizeFilmographyRow(row, headerIndexes, statusById, userRatingById) {
    const cells = qa('td', row);
    const titleAnchor = findFilmographyTitleAnchor(row);
    const title = collapseWhitespace(text(titleAnchor) || text(cells[headerIndexes.title]) || text(row));
    const href = titleAnchor?.getAttribute('href') || '';
    const rowId = collapseWhitespace((((row.getAttribute('class') || '').split(/\s+/).find((value) => value.startsWith('mdl-')) || '').slice(4)));
    const poster = getBetterFilmographyPosterUrl(q('img', row)?.getAttribute('src') || '');
    const yearText = headerIndexes.year >= 0 ? text(cells[headerIndexes.year]) : text(row);
    const episodesText = headerIndexes.episodes >= 0 ? text(cells[headerIndexes.episodes]) : '';
    const ratingText = headerIndexes.rating >= 0 ? text(cells[headerIndexes.rating]) : '';
    const ratingHtml = headerIndexes.rating >= 0 ? (cells[headerIndexes.rating]?.innerHTML || '') : '';
    const roleText = headerIndexes.role >= 0 ? text(cells[headerIndexes.role]) : '';
    const status = statusById.get(rowId) || null;
    return {
      id: rowId,
      title,
      href,
      year: parseFilmographyYear(yearText),
      episodes: parseFilmographyNumber(episodesText),
      rating: parseFilmographyNumber(ratingText),
      ratingHtml,
      userRating: userRatingById?.get(rowId) ?? null,
      role: roleText,
      poster,
      row,
      order: Number(row.getAttribute(FILMOGRAPHY_ORDER_ATTR) || 0),
      status,
      statusKey: status?.key || '',
      isCanceled: /cancelled|canceled/i.test(text(row)),
      manageButton: q('.btn-manage-list[data-id], button[data-stats^="mylist:"]', row) || null,
    };
  }

  function getSortedFilmographyItems(items, state) {
    const copy = [...items];
    if (!state.sortBy) return copy.sort((a, b) => a.order - b.order);

    const dir = state.sortDir === 'asc' ? 1 : -1;
    copy.sort((a, b) => {
      let result = 0;
      if (state.sortBy === 'title') {
        result = a.title.localeCompare(b.title, undefined, { sensitivity: 'base' });
      } else if (state.sortBy === 'year') {
        result = (a.year ?? Number.NEGATIVE_INFINITY) - (b.year ?? Number.NEGATIVE_INFINITY);
      } else if (state.sortBy === 'episodes') {
        result = (a.episodes ?? Number.NEGATIVE_INFINITY) - (b.episodes ?? Number.NEGATIVE_INFINITY);
      } else if (state.sortBy === 'rating') {
        result = (a.rating ?? Number.NEGATIVE_INFINITY) - (b.rating ?? Number.NEGATIVE_INFINITY);
      }
      if (result === 0) result = a.order - b.order;
      return result * dir;
    });
    return copy;
  }

  function isFilmographyItemHidden(item, state) {
    const hidden = new Set(state.hiddenStatuses || []);
    if (hidden.has('completed') && item.statusKey === 'completed') return true;
    if (hidden.has('dropped') && item.statusKey === 'dropped') return true;
    if (hidden.has('not_interested') && item.statusKey === 'not_interested') return true;
    if (hidden.has('canceled') && item.isCanceled) return true;
    return false;
  }

  function buildFilmographyCard(item) {
    const card = document.createElement('article');
    card.className = `${NS}-filmography-card`;

    const cover = document.createElement(item.href ? 'a' : 'div');
    cover.className = `${NS}-filmography-card-cover`;
    if (item.href) cover.href = item.href;
    if (item.poster) {
      const img = document.createElement('img');
      img.src = item.poster;
      img.alt = item.title;
      cover.appendChild(img);
    }
    if (item.year) {
      const yearBadge = document.createElement('span');
      yearBadge.className = `${NS}-filmography-card-badge is-left`;
      if (item.status) {
        yearBadge.classList.add('is-status');
        yearBadge.style.background = getFilmographyStatusBadgeBackground(item.status);
      }
      yearBadge.textContent = String(item.year);
      cover.appendChild(yearBadge);
    }
    if (item.episodes != null) {
      const episodeBadge = document.createElement('span');
      episodeBadge.className = `${NS}-filmography-card-badge is-right`;
      if (item.status) {
        episodeBadge.classList.add('is-status');
        episodeBadge.style.background = getFilmographyStatusBadgeBackground(item.status);
      }
      episodeBadge.textContent = String(item.episodes);
      cover.appendChild(episodeBadge);
    }
    const scoreRow = document.createElement('div');
    scoreRow.className = `${NS}-filmography-card-score-row`;
    const mdlScore = document.createElement('span');
    mdlScore.className = `${NS}-filmography-card-score`;
    mdlScore.innerHTML = `<i class="fas fa-star"></i><span>${formatFilmographyScore(item.rating)}</span>`;
    const userScore = document.createElement('span');
    userScore.className = `${NS}-filmography-card-score`;
    userScore.innerHTML = `<i class="${item.userRating ? 'fas' : 'far'} fa-star"></i><span>${formatFilmographyScore(item.userRating)}</span>`;
    scoreRow.append(mdlScore, userScore);
    cover.appendChild(scoreRow);

    const body = document.createElement('div');
    body.className = `${NS}-filmography-card-body`;

    const title = document.createElement(item.href ? 'a' : 'div');
    title.className = `${NS}-filmography-card-title`;
    title.textContent = item.title || 'Untitled';
    if (item.href) title.href = item.href;

    const status = document.createElement('div');
    status.className = `${NS}-filmography-card-status`;
    if (item.status) {
      status.style.background = item.status.color;
      status.innerHTML = `<i class="${item.status.icon}"></i><span class="${NS}-filmography-card-status-label">${item.status.label}</span>`;
    } else {
      status.classList.add('is-empty');
      status.innerHTML = item.isCanceled
        ? `<span class="${NS}-filmography-card-status-label">Canceled</span>`
        : `<i class="fas fa-plus-circle"></i><span class="${NS}-filmography-card-status-label">Add to list</span>`;
    }
    status.addEventListener('click', (event) => {
      event.preventDefault();
      event.stopPropagation();
      if (item.manageButton) {
        item.manageButton.click();
      } else if (item.href) {
        window.location.href = item.href;
      }
    });

    body.append(title);
    card.append(cover, body, status);
    return card;
  }

  function closeOpenFilmographyMenus(root) {
    qa(`.${NS}-filmography-btn[data-open="true"]`, root || document).forEach((node) => node.setAttribute('data-open', 'false'));
    qa(`.${NS}-filmography-menu`, root || document).forEach((node) => { node.hidden = true; });
  }

  function renderFilmographySection(section, state, items) {
    const tbody = q('tbody', section.table);
    if (!tbody) return;

    filmographyMutationIgnoreUntil = Date.now() + 900;
    const sorted = getSortedFilmographyItems(items, state);
    sorted.forEach((item) => {
      tbody.appendChild(item.row);
      item.row.classList.toggle(`${NS}-filmography-hidden`, isFilmographyItemHidden(item, state));
    });

    let grid = q(`.${NS}-filmography-grid[data-section="${section.key}"]`, section.container);
    if (!grid) {
      grid = document.createElement('div');
      grid.className = `${NS}-filmography-grid`;
      grid.dataset.section = section.key;
      grid.hidden = true;
      section.table.insertAdjacentElement('afterend', grid);
    }

    if (state.view === 'large') {
      section.table.style.display = 'none';
      grid.hidden = false;
      grid.innerHTML = '';
      sorted.filter((item) => !isFilmographyItemHidden(item, state)).forEach((item) => {
        grid.appendChild(buildFilmographyCard(item));
      });
    } else {
      section.table.style.display = '';
      grid.hidden = true;
      grid.innerHTML = '';
    }
  }

  function buildFilmographyToolbar(section) {
    let toolbar = q(`.${NS}-filmography-toolbar[data-section="${section.key}"]`, section.container);
    if (toolbar) return toolbar;

    toolbar = document.createElement('div');
    toolbar.className = `${NS}-filmography-toolbar`;
    toolbar.dataset.section = section.key;
    toolbar.innerHTML = `
      <div class="${NS}-filmography-toolbar-inner">
        <button type="button" class="${NS}-filmography-btn" data-action="toggle-view" title="Toggle view"><i class="fas fa-th-large"></i></button>
        <button type="button" class="${NS}-filmography-btn" data-action="toggle-watched" title="Hide watched"><i class="fas fa-eye-slash"></i></button>
        <div class="${NS}-filmography-menu-wrap">
          <button type="button" class="${NS}-filmography-btn" data-action="toggle-sort-menu"><span>Sort by</span><i class="fas fa-caret-down"></i></button>
          <div class="${NS}-filmography-menu" data-menu="sort" hidden></div>
        </div>
        <button type="button" class="${NS}-filmography-btn" data-action="toggle-direction" title="Toggle sort direction"><i class="fas fa-arrow-up"></i></button>
      </div>
    `;
    section.table.insertAdjacentElement('beforebegin', toolbar);
    return toolbar;
  }

  function buildPeopleFilmographyGlobalToolbar(anchor, sectionKey) {
    const main = getMainLeftColumn();
    qa(`.${NS}-filmography-toolbar`, main).forEach((toolbar) => {
      if (toolbar.dataset.section !== sectionKey) toolbar.remove();
    });

    let toolbar = q(`.${NS}-filmography-toolbar[data-section="${sectionKey}"]`, main);
    if (toolbar) return toolbar;

    toolbar = document.createElement('div');
    toolbar.className = `${NS}-filmography-toolbar`;
    toolbar.dataset.section = sectionKey;
    toolbar.innerHTML = `
      <div class="${NS}-filmography-toolbar-inner">
        <button type="button" class="${NS}-filmography-btn" data-action="toggle-view" title="Toggle view"><i class="fas fa-th-large"></i></button>
        <button type="button" class="${NS}-filmography-btn" data-action="toggle-watched" title="Hide watched"><i class="fas fa-eye-slash"></i></button>
        <div class="${NS}-filmography-menu-wrap">
          <button type="button" class="${NS}-filmography-btn" data-action="toggle-sort-menu"><span>Sort by</span><i class="fas fa-caret-down"></i></button>
          <div class="${NS}-filmography-menu" data-menu="sort" hidden></div>
        </div>
        <button type="button" class="${NS}-filmography-btn" data-action="toggle-direction" title="Toggle sort direction"><i class="fas fa-arrow-up"></i></button>
      </div>
    `;
    anchor.insertAdjacentElement('beforebegin', toolbar);
    return toolbar;
  }

  function populateFilmographyMenus(toolbar, sectionKey, rerender) {
    const filterMenu = q(`[data-menu="filters"]`, toolbar);
    const sortMenu = q(`[data-menu="sort"]`, toolbar);
    if (sortMenu) {
      sortMenu.innerHTML = '';
      [
        ['title', 'Title'],
        ['year', 'Year'],
        ['episodes', 'Episodes'],
        ['rating', 'Rating'],
      ].forEach(([value, label]) => {
        const button = document.createElement('button');
        button.type = 'button';
        button.className = `${NS}-filmography-menu-item`;
        button.dataset.value = value;
        button.textContent = label;
        button.addEventListener('click', () => {
          const nextDir = value === 'title' ? 'asc' : 'desc';
          setFilmographySectionUiState(sectionKey, { sortBy: value, sortDir: nextDir });
          closeOpenFilmographyMenus(toolbar);
          rerender();
        });
        sortMenu.appendChild(button);
      });
      sortMenu.dataset.bound = 'true';
    }
  }

  function syncFilmographyToolbar(toolbar, sectionKey) {
    const state = getFilmographySectionUiState(sectionKey);
    const viewButton = q(`[data-action="toggle-view"]`, toolbar);
    const watchedButton = q(`[data-action="toggle-watched"]`, toolbar);
    const dirButton = q(`[data-action="toggle-direction"]`, toolbar);
    const sortButton = q(`[data-action="toggle-sort-menu"] span`, toolbar);
    if (viewButton) {
      viewButton.classList.toggle('is-active', state.view === 'large');
      viewButton.innerHTML = state.view === 'large' ? '<i class="fas fa-list"></i>' : '<i class="fas fa-th-large"></i>';
    }
    if (dirButton) {
      dirButton.innerHTML = state.sortDir === 'asc' ? '<i class="fas fa-arrow-up"></i>' : '<i class="fas fa-arrow-down"></i>';
    }
    if (sortButton) {
      const labels = { title: 'Title', year: 'Year', episodes: 'Episodes', rating: 'Rating' };
      sortButton.textContent = state.sortBy ? labels[state.sortBy] || 'Sort by' : 'Sort by';
    }
    if (watchedButton) {
      watchedButton.classList.toggle('is-active', (state.hiddenStatuses || []).includes('completed'));
    }
    qa(`.${NS}-filmography-menu[data-menu="filters"] .${NS}-filmography-menu-item`, toolbar).forEach((item) => {
      item.classList.toggle('is-active', (state.hiddenStatuses || []).includes(item.dataset.value));
    });
    qa(`.${NS}-filmography-menu[data-menu="sort"] .${NS}-filmography-menu-item`, toolbar).forEach((item) => {
      item.classList.toggle('is-active', item.dataset.value === state.sortBy);
    });
  }

  function bindFilmographyToolbar(toolbar, sectionKey, rerender) {
    toolbar.__bettermdlSectionKey = sectionKey;
    toolbar.__bettermdlRerender = rerender;
    if (toolbar.dataset.bound === 'true') return;
    toolbar.addEventListener('click', (event) => {
      const button = event.target.closest(`.${NS}-filmography-btn`);
      if (!button) return;
      const action = button.getAttribute('data-action');
      const activeSectionKey = toolbar.__bettermdlSectionKey || sectionKey;
      const activeRerender = toolbar.__bettermdlRerender || rerender;
      if (action === 'toggle-view') {
        const state = getFilmographySectionUiState(activeSectionKey);
        setFilmographySectionUiState(activeSectionKey, { view: state.view === 'large' ? 'mini' : 'large' });
        closeOpenFilmographyMenus(toolbar);
        activeRerender();
      } else if (action === 'toggle-watched') {
        const state = getFilmographySectionUiState(activeSectionKey);
        const current = new Set(state.hiddenStatuses || []);
        if (current.has('completed')) current.delete('completed'); else current.add('completed');
        setFilmographySectionUiState(activeSectionKey, { hiddenStatuses: Array.from(current) });
        closeOpenFilmographyMenus(toolbar);
        activeRerender();
      } else if (action === 'toggle-direction') {
        const state = getFilmographySectionUiState(activeSectionKey);
        setFilmographySectionUiState(activeSectionKey, {
          sortBy: state.sortBy || 'year',
          sortDir: state.sortDir === 'asc' ? 'desc' : 'asc',
        });
        activeRerender();
      } else if (action === 'toggle-filter-menu' || action === 'toggle-sort-menu') {
        const menu = button.parentElement?.querySelector(`.${NS}-filmography-menu`);
        const willOpen = !!menu?.hidden;
        closeOpenFilmographyMenus(toolbar);
        if (menu) {
          menu.hidden = !willOpen;
          button.setAttribute('data-open', willOpen ? 'true' : 'false');
        }
      }
    });
    document.addEventListener('click', (event) => {
      if (!toolbar.contains(event.target)) closeOpenFilmographyMenus(toolbar);
    });
    toolbar.dataset.bound = 'true';
  }

  function initPeopleFilmographyControls(items) {
    if (!isPeoplePage()) return;
    if (!isFeatureEnabled('peopleFilmographyControls')) {
      qa(`.${NS}-filmography-toolbar, .${NS}-filmography-grid`, getMainLeftColumn()).forEach((node) => node.remove());
      qa('table.film-list', getMainLeftColumn()).forEach((table) => { table.style.display = ''; });
      return;
    }
    prioritizePeopleDramaMovieSections();
    const sections = findPeopleFilmographySections();
    if (!sections.length) return;

    const { statusById, userRatingById } = getFilmographyStatusMaps(items);
    const globalSectionKey = getPeopleFilmographyGlobalSectionKey();
    const globalState = getFilmographySectionUiState(globalSectionKey);
    const rerenderAll = () => {
      const state = getFilmographySectionUiState(globalSectionKey);
      sections.forEach((section) => renderFilmographySection(section, state, section.items));
      const toolbar = q(`.${NS}-filmography-toolbar[data-section="${globalSectionKey}"]`, getMainLeftColumn());
      if (toolbar) syncFilmographyToolbar(toolbar, globalSectionKey);
    };

    sections.forEach((section) => {
      section.heading.classList.remove(`${NS}-filmography-section-heading`);
      const headerIndexes = getFilmListHeaderIndexes(section.table);
      const rows = qa('tbody tr', section.table);
      rows.forEach((row, index) => {
        if (!row.hasAttribute(FILMOGRAPHY_ORDER_ATTR)) row.setAttribute(FILMOGRAPHY_ORDER_ATTR, String(index));
      });
      section.container = section.table.parentElement || section.heading.parentElement || getMainLeftColumn();
      section.items = rows.map((row) => normalizeFilmographyRow(row, headerIndexes, statusById, userRatingById));
      renderFilmographySection(section, globalState, section.items);
    });

    const toolbar = buildPeopleFilmographyGlobalToolbar(sections[0].heading || sections[0].table, globalSectionKey);
    populateFilmographyMenus(toolbar, globalSectionKey, rerenderAll);
    bindFilmographyToolbar(toolbar, globalSectionKey, rerenderAll);
    syncFilmographyToolbar(toolbar, globalSectionKey);
  }

  function schedulePeopleFilmographyControls(items = []) {
    if (!isPeoplePage()) return;
    initPeopleFilmographyControls(items);
    if (q(`.${NS}-filmography-toolbar[data-section="${getPeopleFilmographyGlobalSectionKey()}"]`, getMainLeftColumn())) return;
    [350, 1200, 2600].forEach((delay) => {
      setTimeout(() => {
        if (!q(`.${NS}-filmography-toolbar[data-section="${getPeopleFilmographyGlobalSectionKey()}"]`, getMainLeftColumn())) {
          initPeopleFilmographyControls(items);
        }
      }, delay);
    });
  }

  function hideDuplicatePosterColumn() {
    qa('table.film-list').forEach((table) => {
      const headers = qa('thead th', table).map((th) => text(th).toLowerCase());
      if (headers[1] === 'poster') table.classList.add(`${NS}-hide-poster-col`);
    });
  }

  function getAutoHiddenState(key, fallback = false, hasStoredValue = false) {
    if (hasStoredValue) return fallback;
    if (/:comments$/.test(key)) {
      return isTitlePage() ? isFeatureEnabled('titleAutoHideSections') : isFeatureEnabled('peopleAutoHideSections');
    }
    if (/:(bio|people-photos|articles)$/.test(key)) {
      return isFeatureEnabled('peopleAutoHideSections');
    }
    if (/:synopsis$/.test(key)) {
      return isFeatureEnabled('titleSynopsisHide');
    }
    if (/:(photos|reviews|recent-discussions)$/.test(key)) {
      return isFeatureEnabled('titleAutoHideSections');
    }
    return fallback;
  }

  function collectSiblingsUntil(startEl, stopMatcher) {
    const nodes = [];
    let node = startEl?.nextElementSibling || null;
    while (node) {
      if (stopMatcher(node)) break;
      nodes.push(node);
      node = node.nextElementSibling;
    }
    return nodes;
  }

  function getMainLeftColumn() {
    return q('.col-lg-8.col-md-8, .col-lg-8, .col-md-8, .col-sm-8') || document.body;
  }

  function initShowHide() {
    if (!isFeatureEnabled('showHideSections')) {
      qa(`.${NS}-toggle-row, .${NS}-toggle-inline`, getMainLeftColumn()).forEach((node) => node.remove());
      qa(`.${NS}-hidden-block`, getMainLeftColumn()).forEach((node) => node.classList.remove(`${NS}-hidden-block`));
      return;
    }

    const state = getCollapseState();
    const main = getMainLeftColumn();
    const contentBodies = qa('.box-body', main).filter((body) => !body.closest(`#${ORIGINAL_WORK_BOX_ID}, #${FRIENDS_BOX_ID}, #${PORTALS_BOX_ID}`));
    const bioBody = contentBodies[0] || null;

    if (bioBody && !q(`.${NS}-toggle-row[data-kind="bio"]`, main)) {
      const kind = 'bio';
      const key = `${location.pathname}:${kind}`;
      const row = makeToggleRow(key, getAutoHiddenState(key, !!state[key], Object.prototype.hasOwnProperty.call(state, key)), (hidden) => {
        bioBody.classList.toggle(`${NS}-hidden-block`, hidden);
      });
      row.classList.add(`${NS}-people-toggle-row`);
      row.dataset.kind = kind;
      bioBody.insertAdjacentElement('beforebegin', row);
    }

    const articlesListing = q('.articles-listing', main);
    if (articlesListing && !q(`.${NS}-toggle-row[data-kind="articles"]`, main)) {
      const key = `${location.pathname}:articles`;
      const row = makeToggleRow(key, getAutoHiddenState(key, !!state[key], Object.prototype.hasOwnProperty.call(state, key)), (hidden) => {
        articlesListing.classList.toggle(`${NS}-hidden-block`, hidden);
      });
      row.classList.add(`${NS}-people-toggle-row`);
      row.dataset.kind = 'articles';
      articlesListing.insertAdjacentElement('beforebegin', row);
    }

    initPeoplePhotosToggle(main, state);
    initPeopleFilmographyToggle(main, state);

    const commentsBox = findCommentsBox();
    if (commentsBox) {
      initCommentsToggle(commentsBox, state);
    }
  }

  function findHeadingBeforeFilmList(table, main = getMainLeftColumn()) {
    let node = table;
    while (node && node !== main) {
      let prev = node.previousElementSibling;
      while (prev) {
        if (prev.matches?.('h1, h2, h3, h4, h5, h6')) return prev;
        prev = prev.previousElementSibling;
      }
      node = node.parentElement;
    }
    return table;
  }

  function isPeopleFilmographyToggleStopNode(node) {
    if (!node) return false;
    if (node.matches?.('.articles-listing, .comments, #comments, [id*="comment"]')) return true;
    if (node.matches?.('h1, h2, h3, h4, h5, h6') && /^(photos|articles|comments)$/i.test(text(node))) return true;
    return false;
  }

  function findPeopleFilmographyToggleNodes(main = getMainLeftColumn()) {
    const firstTable = qa('table.film-list', main)[0] || null;
    if (!firstTable) return [];

    const startNode = findHeadingBeforeFilmList(firstTable, main);
    const nodes = [];
    let node = startNode;
    while (node) {
      if (node !== startNode && isPeopleFilmographyToggleStopNode(node)) break;
      if (!node.classList?.contains(`${NS}-toggle-row`) && !node.classList?.contains(`${NS}-toggle-inline`)) {
        nodes.push(node);
      }
      node = node.nextElementSibling;
    }

    return nodes.filter((item) => main.contains(item) && (item.matches?.('table.film-list') || q('table.film-list', item) || text(item)));
  }

  function initPeopleFilmographyToggle(main, state) {
    const key = `${location.pathname}:filmo`;
    const hasStoredValue = Object.prototype.hasOwnProperty.call(state, key);
    const hidden = getAutoHiddenState(key, !!state[key], hasStoredValue);
    const filmoNodes = findPeopleFilmographyToggleNodes(main);
    let row = q(`.${NS}-toggle-row[data-kind="filmo"]`, main);

    if (!filmoNodes.length) {
      row?.remove();
      return;
    }

    if (row && row.dataset.bettermdlFilmoToggle !== 'true') {
      row.remove();
      row = null;
    }

    if (row) {
      row.classList.add(`${NS}-people-toggle-row`);
      if (row.nextElementSibling !== filmoNodes[0]) filmoNodes[0].insertAdjacentElement('beforebegin', row);
      filmoNodes.forEach((node) => node.classList.toggle(`${NS}-hidden-block`, hidden));
      return;
    }

    row = makeToggleRow(key, hidden, (nextHidden) => {
      findPeopleFilmographyToggleNodes(main).forEach((node) => node.classList.toggle(`${NS}-hidden-block`, nextHidden));
    });
    row.classList.add(`${NS}-people-toggle-row`);
    row.dataset.kind = 'filmo';
    row.dataset.bettermdlFilmoToggle = 'true';
    filmoNodes[0].insertAdjacentElement('beforebegin', row);
  }

  function isPeoplePhotosHeading(node) {
    return !!(node?.matches?.('h1, h2, h3, h4, h5, h6') && /^photos$/i.test(text(node)));
  }

  function isPeopleDetailsTabActive(main = getMainLeftColumn()) {
    const activeNavLabel = qa('.nav-tabs li.active a, .nav-pills li.active a, .nav li.active a, a.active, button.active', main)
      .map(text)
      .find((label) => /^(details|photos|related articles|feed)$/i.test(label));
    if (activeNavLabel) return /^details$/i.test(activeNavLabel);

    const activeTab = qa('a, li, button', main).find((node) => {
      const label = text(node);
      const className = String(node.className || '');
      const parentClassName = String(node.parentElement?.className || '');
      return /^details$/i.test(label) && /\bactive\b/i.test(`${className} ${parentClassName}`);
    });
    if (activeTab) return true;

    const activeLabel = qa('a, li, button', main)
      .filter((node) => /\bactive\b/i.test(`${String(node.className || '')} ${String(node.parentElement?.className || '')}`))
      .map(text)
      .find(Boolean);
    return !activeLabel || /^details$/i.test(activeLabel);
  }

  function findPeoplePhotosNodes(main = getMainLeftColumn()) {
    if (!isPeopleDetailsTabActive(main)) return [];
    const heading = qa('h1, h2, h3, h4, h5, h6', main).find(isPeoplePhotosHeading);
    if (!heading) return [];

    const nodes = [heading];
    let node = heading.nextElementSibling;
    while (node) {
      if (node.matches?.('h1, h2, h3, h4, h5, h6') && !isPeoplePhotosHeading(node)) break;
      if (node.matches?.('.articles-listing, .comments, #comments, [id*="comment"]')) break;
      nodes.push(node);
      node = node.nextElementSibling;
    }
    return nodes;
  }

  function initPeoplePhotosToggle(main, state) {
    const photosNodes = findPeoplePhotosNodes(main);
    const existing = q(`.${NS}-toggle-row[data-kind="people-photos"]`, document);
    const key = `${location.pathname}:people-photos`;
    const hidden = getAutoHiddenState(key, !!state[key], Object.prototype.hasOwnProperty.call(state, key));

    if (!photosNodes.length) {
      existing?.remove();
      return;
    }

    if (existing) {
      existing.classList.add(`${NS}-people-toggle-row`);
      if (existing.nextElementSibling !== photosNodes[0]) photosNodes[0].insertAdjacentElement('beforebegin', existing);
      photosNodes.forEach((node) => node.classList.toggle(`${NS}-hidden-block`, hidden));
      return;
    }

    const row = makeToggleRow(key, hidden, (nextHidden) => {
      findPeoplePhotosNodes(main).forEach((node) => node.classList.toggle(`${NS}-hidden-block`, nextHidden));
    });
    row.classList.add(`${NS}-people-toggle-row`);
    row.dataset.kind = 'people-photos';
    photosNodes[0].insertAdjacentElement('beforebegin', row);
  }

  function bindPeopleTabRefresh() {
    if (window.__betterMdlPeopleTabRefreshBound) return;
    document.addEventListener('click', (event) => {
      if (!isPeoplePage()) return;
      const tab = event.target.closest?.('a, button');
      if (!tab || !/^(details|photos|related articles|feed)$/i.test(text(tab))) return;
      setTimeout(scheduleBoot, 80);
      setTimeout(scheduleBoot, 260);
    });
    window.__betterMdlPeopleTabRefreshBound = true;
  }

  function makeToggleRow(key, initiallyHidden, onToggle) {
    const row = document.createElement('div');
    row.className = `${NS}-toggle-row`;

    const show = document.createElement('span');
    const hide = document.createElement('span');

    show.className = `${NS}-toggle-link`;
    hide.className = `${NS}-toggle-link`;

    show.textContent = 'Show section';
    hide.textContent = 'Hide section';

    show.dataset.state = 'show';
    hide.dataset.state = 'hide';

    row.append(show, hide);

    const render = (hidden) => {
      show.style.display = hidden ? '' : 'none';
      hide.style.display = hidden ? 'none' : '';
      onToggle(hidden);

      const current = getCollapseState();
      current[key] = hidden;
      setCollapseState(current);
    };

    show.addEventListener('click', () => render(false));
    hide.addEventListener('click', () => render(true));

    render(initiallyHidden);
    return row;
  }

  function makeCommentsToggleRow(key, initiallyHidden, onToggle) {
    const row = document.createElement('div');
    row.className = `${NS}-toggle-row`;

    const show = document.createElement('span');
    const hide = document.createElement('span');

    show.className = `${NS}-toggle-link`;
    hide.className = `${NS}-toggle-link`;

    show.textContent = 'Show section';
    hide.textContent = 'Hide section';

    show.dataset.state = 'show';
    hide.dataset.state = 'hide';

    row.append(show, hide);

    const render = (hidden, persist = true) => {
      show.style.display = hidden ? '' : 'none';
      hide.style.display = hidden ? 'none' : '';
      onToggle(hidden);
      if (persist) {
        const current = getCollapseState();
        current[key] = hidden;
        setCollapseState(current);
      }
    };

    show.addEventListener('click', () => render(false));
    hide.addEventListener('click', () => render(true));

    render(initiallyHidden, false);
    return row;
  }

  function findCommentsBox() {
    const main = getMainLeftColumn();
    const heading = qa('.box-header, .box-title, .card-header, h1, h2, h3, h4, h5, h6, div, span, strong, b', main)
      .filter((node) => !node.closest(`.${NS}-toggle-row, .${NS}-toggle-inline`))
      .find((node) => /^comments(?:\s*\(\d+\/?\d*\))?$/i.test(text(node)) && text(node).length <= 32);
    if (!heading) return null;

    const directBox = heading.closest('.box, .card, section, [class*="card"], [class*="box"], [class*="comment"]');
    if (directBox && main.contains(directBox)) return directBox;

    let box = heading.parentElement;
    while (box && box !== main) {
      const value = text(box);
      if (
        box.children.length > 1
        && /post a comment|reply|respectful and thoughtful discussion/i.test(value)
        && !/recent discussions/i.test(value)
      ) return box;
      box = box.parentElement;
    }
    return heading.parentElement || null;
  }

  function findCommentsHeading(box) {
    return qa('.box-header, .box-title, .card-header, h1, h2, h3, h4, h5, h6, div, span, strong, b', box).find((heading) => {
      return /^comments(?:\s*\(\d+\/?\d*\))?$/i.test(text(heading)) && text(heading).length <= 32;
    }) || null;
  }

  function findCommentsCardFromHeading(header, fallbackBox) {
    let node = header;
    let match = null;
    while (node?.parentElement && node.parentElement !== getMainLeftColumn()) {
      const parent = node.parentElement;
      const value = text(parent);
      if (
        /post a comment|reply|respectful and thoughtful discussion/i.test(value)
        && /^comments(?:\s*\(\d+\/?\d*\))?/i.test(value)
        && !/recent discussions/i.test(value)
      ) match = parent;
      node = parent;
    }
    return match || fallbackBox;
  }

  function findCommentsComposerBlock(host, header) {
    const candidates = qa('textarea, [contenteditable="true"], input[placeholder*="comment" i], [placeholder*="comment" i], div, span', host)
      .filter((node) => {
        if (node.contains(header) || node.closest(`.${NS}-toggle-row, .${NS}-toggle-inline`)) return false;
        const value = text(node);
        return node.matches?.('textarea, [contenteditable="true"], input[placeholder*="comment" i], [placeholder*="comment" i]')
          || /^post a comment/i.test(value);
      });
    if (!candidates.length) return null;

    let block = candidates[0];
    while (block.parentElement && block.parentElement !== host) {
      block = block.parentElement;
    }
    return block;
  }

  function placeCommentsToggle(toggle, host, header) {
    if (host.dataset.bettermdlTitleComments === 'true') {
      const composer = findCommentsComposerBlock(host, header);
      if (composer) {
        composer.insertAdjacentElement('afterend', toggle);
        return composer;
      }
    }

    let headerBlock = header;
    while (headerBlock.parentElement && headerBlock.parentElement !== host) {
      headerBlock = headerBlock.parentElement;
    }
    headerBlock.insertAdjacentElement('afterend', toggle);
    return headerBlock;
  }

  function initCommentsToggle(box, state) {
    const header = findCommentsHeading(box);
    const host = findCommentsCardFromHeading(header, box);
    if (!header || !host) return;

    const titleCommentsRoot = host.dataset.bettermdlTitleComments === 'true'
      ? (host.matches?.('#cmtsapp, .comments-box.post-comments') ? host : host.closest?.('#cmtsapp, .comments-box.post-comments'))
      : null;
    const contentRoot = titleCommentsRoot || host;

    qa(`.${NS}-toggle-inline[data-kind="comments"]`, contentRoot).forEach((node) => node.remove());
    qa(`.${NS}-comments-header-keep`, contentRoot).forEach((node) => node.classList.remove(`${NS}-comments-header-keep`));

    let headerBlock = header;
    while (headerBlock.parentElement && headerBlock.parentElement !== contentRoot) {
      headerBlock = headerBlock.parentElement;
    }
    if (!headerBlock || headerBlock === contentRoot) return;
    headerBlock.classList.add(`${NS}-comments-header-keep`);
    contentRoot.classList.add(`${NS}-comments-toggle-host`);

    const contentNodes = Array.from(contentRoot.children)
      .filter((child) => child !== headerBlock && !child.classList?.contains(`${NS}-toggle-inline`));
    if (!contentNodes.length) return;

    const applyCommentsHidden = (hidden) => {
      host.classList.toggle(`${NS}-comments-collapsed`, hidden);
      contentRoot.classList.toggle(`${NS}-comments-collapsed`, hidden);
      headerBlock.classList.add(`${NS}-comments-header-keep`);
      contentNodes.forEach((node) => {
        node.classList.toggle(`${NS}-hidden-block`, hidden);
        node.classList.toggle(`${NS}-comments-content-hidden`, hidden);
      });
    };

    const key = `${location.pathname}:comments`;
    let toggle = null;
    toggle = makeCommentsToggleRow(key, getAutoHiddenState(key, !!state[key], Object.prototype.hasOwnProperty.call(state, key)), (hidden) => {
      applyCommentsHidden(hidden);
    });
    toggle.classList.add(`${NS}-toggle-inline`);
    toggle.classList.add(`${NS}-comments-toggle`);
    toggle.classList.toggle(`${NS}-comments-toggle-title`, host.dataset.bettermdlTitleComments === 'true');
    toggle.dataset.kind = 'comments';
    placeCommentsToggle(toggle, contentRoot, header);
    applyCommentsHidden(getAutoHiddenState(key, !!state[key], Object.prototype.hasOwnProperty.call(state, key)));
  }

  function findTitleMainBoxes() {
    return qa('.box').filter((box) => {
      const heading = q('.box-header, .box-title, h1, h2, h3, h4', box);
      if (!heading) return false;
      return !box.closest('.col-lg-4, .col-md-4, .col-sm-4, .sidebar, .side-content');
    });
  }

  function findTitleBoxByHeading(pattern) {
    return findTitleMainBoxes().find((box) => pattern.test(text(q('.box-header, .box-title, h1, h2, h3, h4', box)))) || null;
  }

  function isLikelyTitleSynopsisNode(node) {
    const value = text(node);
    if (!value || value.length < 80) return false;
    if (node.closest(`#${ORIGINAL_WORK_BOX_ID}, #${FRIENDS_BOX_ID}, #${WATCHED_FRIENDS_BOX_ID}, #${PORTALS_BOX_ID}`)) return false;
    if (node.closest(`.${NS}-toggle-row, .${NS}-toggle-inline`)) return false;
    if (/your rating|ratings:|# of watchers|reviews:|edit this page|details\s+episodes\s+cast/i.test(value)) return false;
    if (/^(photos|reviews|recent discussions|cast|episodes|recommendations)$/i.test(value)) return false;
    return /[.!?][\s")\]]|[.!?]$/.test(value);
  }

  function findTitleSynopsisNodes() {
    const main = getMainLeftColumn();
    const explicit = qa('.show-synopsis, .synopsis, .show-description, [itemprop="description"]', main)
      .find(isLikelyTitleSynopsisNode);
    if (explicit) return [explicit];

    const paragraphs = qa('p', main).filter(isLikelyTitleSynopsisNode);
    if (!paragraphs.length) return [];

    const first = paragraphs[0];
    const parent = first.parentElement;
    if (!parent) return [first];

    const related = [];
    let node = first;
    while (node && node.parentElement === parent) {
      if (node !== first && node.matches?.('h1, h2, h3, h4, h5, h6, table, .box, .nav, .nav-tabs')) break;
      const value = text(node);
      if (node.matches?.('p') && (isLikelyTitleSynopsisNode(node) || /^source:/i.test(value) || /edit translation/i.test(value))) {
        related.push(node);
      }
      node = node.nextElementSibling;
    }

    return related.length ? related : [first];
  }

  function findTitleSynopsisToggleAnchor(firstSynopsisNode) {
    const previous = firstSynopsisNode?.previousElementSibling || null;
    if (!previous) return firstSynopsisNode;

    const previousText = text(previous);
    const previousClass = String(previous.className || '');
    const isDivider = previous.matches?.('hr')
      || /divider|separator|border/i.test(previousClass)
      || (!previousText && previous.children.length === 0 && previous.getBoundingClientRect?.().height <= 6);

    return isDivider ? previous : firstSynopsisNode;
  }

  function findTitleReviewsCountLink(root) {
    return qa('a', root || document).find((anchor) => /^\d[\d,.]*\s+users?$/i.test(text(anchor)) && /review/i.test(text(anchor.parentElement)));
  }

  function alignTitleSynopsisToggle(toggle, host) {
    const reviewsLink = findTitleReviewsCountLink(host) || findTitleReviewsCountLink(getMainLeftColumn());
    if (!reviewsLink || !toggle || !host) return;

    requestAnimationFrame(() => {
      const hostRect = host.getBoundingClientRect();
      const reviewRect = reviewsLink.getBoundingClientRect();
      if (!hostRect.height || !reviewRect.height) return;
      toggle.style.top = `${Math.max(0, reviewRect.top - hostRect.top)}px`;
    });
  }

  function initTitleSynopsisToggle(state) {
    const main = getMainLeftColumn();
    const synopsisNodes = findTitleSynopsisNodes();
    if (!synopsisNodes.length) return;
    const anchor = findTitleSynopsisToggleAnchor(synopsisNodes[0]);
    const host = anchor.parentElement || main;

    const key = `${location.pathname}:synopsis`;
    const hasStoredValue = Object.prototype.hasOwnProperty.call(state, key);
    const hidden = getAutoHiddenState(key, !!state[key], hasStoredValue);
    const existingToggle = q(`.${NS}-toggle-row[data-kind="title-synopsis"]`, main);

    if (existingToggle) {
      existingToggle.classList.add(`${NS}-title-synopsis-toggle`);
      alignTitleSynopsisToggle(existingToggle, host);
      synopsisNodes.forEach((node) => node.classList.toggle(`${NS}-hidden-block`, hidden));
      return;
    }

    const toggle = makeToggleRow(key, hidden, (nextHidden) => {
      synopsisNodes.forEach((node) => node.classList.toggle(`${NS}-hidden-block`, nextHidden));
    });
    toggle.classList.add(`${NS}-title-synopsis-toggle`);
    toggle.dataset.kind = 'title-synopsis';
    host.style.position = host.style.position || 'relative';
    anchor.insertAdjacentElement('beforebegin', toggle);
    alignTitleSynopsisToggle(toggle, host);
  }

  function initTitleBoxToggle(box, state, {
    keySuffix,
    kind,
  }) {
    const header = q('.box-header, .box-title, h1, h2, h3, h4', box);
    const host = header?.closest('.box-header, .box-title') || header?.parentElement;
    if (!header || !host) return;

    const contentNodes = Array.from(box.children).filter((child) => child !== host);
    if (!contentNodes.length) return;

    host.classList.add(`${NS}-title-toggle-host`);
    const key = `${location.pathname}:${keySuffix}`;
    const existingToggle = q(`.${NS}-toggle-inline[data-kind="${kind}"]`, box);
    if (existingToggle) {
      const hidden = getAutoHiddenState(key, !!state[key], Object.prototype.hasOwnProperty.call(state, key));
      contentNodes.forEach((node) => node.classList.toggle(`${NS}-hidden-block`, hidden));
      return;
    }

    const toggle = makeToggleRow(key, getAutoHiddenState(key, !!state[key], Object.prototype.hasOwnProperty.call(state, key)), (hidden) => {
      contentNodes.forEach((node) => node.classList.toggle(`${NS}-hidden-block`, hidden));
    });
    toggle.classList.add(`${NS}-toggle-inline`);
    toggle.dataset.kind = kind;
    host.classList.add(`${NS}-title-toggle-host`);
    toggle.classList.add(`${NS}-title-toggle-center`);
    host.appendChild(toggle);
  }

  function initTitlePageSectionToggles() {
    if (!isTitlePage()) return;
    if (!isFeatureEnabled('showHideSections')) {
      const main = getMainLeftColumn();
      qa(`.${NS}-toggle-row[data-kind="title-synopsis"]`, main).forEach((node) => node.remove());
      qa(`.${NS}-hidden-block`, main).forEach((node) => node.classList.remove(`${NS}-hidden-block`));
      findTitleMainBoxes().forEach((box) => {
        qa(`.${NS}-toggle-row, .${NS}-toggle-inline`, box).forEach((node) => node.remove());
        qa(`.${NS}-hidden-block`, box).forEach((node) => node.classList.remove(`${NS}-hidden-block`));
      });
      return;
    }

    const state = getCollapseState();
    const main = getMainLeftColumn();
    if (isTitleDetailsTabActive()) {
      initTitleSynopsisToggle(state);
    } else {
      qa(`.${NS}-toggle-row[data-kind="title-synopsis"]`, main).forEach((node) => node.remove());
    }

    const photosBox = findTitleBoxByHeading(/^photos$/i);
    if (photosBox) {
      initTitleBoxToggle(photosBox, state, {
        keySuffix: 'photos',
        kind: 'title-photos',
      });
    }

    const reviewsBox = findTitleBoxByHeading(/^reviews$/i);
    if (reviewsBox) {
      initTitleBoxToggle(reviewsBox, state, {
        keySuffix: 'reviews',
        kind: 'title-reviews',
      });
    }

    const discussionsBox = findTitleBoxByHeading(/^recent discussions$/i);
    if (discussionsBox) {
      initTitleBoxToggle(discussionsBox, state, {
        keySuffix: 'recent-discussions',
        kind: 'title-recent-discussions',
      });
    }

    const commentsBox = findCommentsBox();
    if (commentsBox) {
      commentsBox.dataset.bettermdlTitleComments = 'true';
      initCommentsToggle(commentsBox, state);
    }
  }

  function normalizeTitle(value) {
    return String(value || '')
      .toLowerCase()
      .normalize('NFKD')
      .replace(/[\u0300-\u036f]/g, '')
      .replace(/&/g, ' and ')
      .replace(/[^\p{L}\p{N}]+/gu, ' ')
      .trim();
  }

  function stripPortalSubtitle(value) {
    const raw = collapseWhitespace(value);
    if (!raw) return '';

    let stripped = raw
      .replace(/\s*\((?:part|season|pt\.?|chapter|book|episode)\s*[0-9ivx]+\)\s*$/i, '')
      .replace(/\s*[-–]\s*season\s*\d+\b.*$/i, '')
      .replace(/\s*[-–]\s*part\s*\d+\b.*$/i, '')
      .replace(/\s+(season|part|pt\.?|chapter|book|episode)\s*\d+\b.*$/i, '')
      .replace(/\s+(season|part|pt\.?|chapter|book|episode)\s*[ivx]+\b.*$/i, '')
      .trim();

    if (/\b(season|part|pt\.?|chapter|book|episode)\b/i.test(raw)) {
      stripped = stripped.replace(/\s*:\s*.*$/, '').trim();
    }

    return stripped || raw;
  }

  function hasPortalSplitMarker(value) {
    return /\b(season|part|pt\.?|chapter|book|episode)\s*[0-9ivx]+\b/i.test(String(value || ''));
  }

  function buildPortalSearchTitles(context) {
    return [...new Set([
      context.baseTitle,
      context.title,
      context.baseNativeTitle,
      context.nativeTitle,
    ].map(collapseWhitespace).filter(Boolean))];
  }

  function buildPortalSearchQueries(context) {
    const titles = buildPortalSearchTitles(context);
    const dated = context.year
      ? titles.map((title) => `${title} ${context.year}`)
      : [];
    return [...new Set([...dated, ...titles].map(collapseWhitespace).filter(Boolean))];
  }

  function buildTmdbSearchQueries(context) {
    if (context.kind === 'movie') {
      return [...new Set([
        context.title && context.year ? `${context.title} ${context.year}` : '',
        context.nativeTitle && context.year ? `${context.nativeTitle} ${context.year}` : '',
        context.title,
        context.nativeTitle,
        context.baseTitle && context.baseTitle !== context.title && context.year ? `${context.baseTitle} ${context.year}` : '',
        context.baseTitle,
      ].map(collapseWhitespace).filter(Boolean))];
    }

    return [...new Set([
      context.baseTitle,
      context.baseNativeTitle,
      context.baseTitle && context.year ? `${context.baseTitle} ${context.year}` : '',
      context.baseNativeTitle && context.year ? `${context.baseNativeTitle} ${context.year}` : '',
      context.title,
      context.nativeTitle,
    ].map(collapseWhitespace).filter(Boolean))];
  }

  function buildAsianWikiSearchQueries(context) {
    if (context.kind === 'movie') {
      return buildTmdbSearchQueries(context);
    }

    return [...new Set([
      context.title,
      context.nativeTitle,
      context.baseTitle,
      context.baseNativeTitle,
      context.title && context.year ? `${context.title} ${context.year}` : '',
      context.baseTitle && context.year ? `${context.baseTitle} ${context.year}` : '',
    ].map(collapseWhitespace).filter(Boolean))];
  }

  function buildAsianWikiSlugCandidates(context) {
    const rawTitles = [...new Set([
      context.title,
      context.nativeTitle,
      context.baseTitle,
      context.baseNativeTitle,
    ].map(collapseWhitespace).filter(Boolean))];

    return rawTitles.map((title) => title
      .replace(/[’']/g, '')
      .replace(/\s+/g, '_')
      .replace(/[^A-Za-z0-9_\-\u00C0-\uFFFF]/g, '')
      .replace(/_+/g, '_')
      .replace(/^_+|_+$/g, ''))
      .filter(Boolean);
  }

  function getTmdbCandidateTitle(item) {
    return collapseWhitespace(
      item?.title
      || item?.name
      || item?.original_title
      || item?.original_name
      || '',
    );
  }

  function getTmdbCandidateYear(item) {
    const rawDate = String(item?.release_date || item?.first_air_date || '');
    const match = rawDate.match(/^(\d{4})/);
    return match ? match[1] : '';
  }

  function scoreTmdbResult(item, context, queryTitle) {
    const candidateTitles = [
      item?.title,
      item?.name,
      item?.original_title,
      item?.original_name,
    ].map(normalizeTitle).filter(Boolean);
    const candidateBaseTitles = [
      item?.title,
      item?.name,
      item?.original_title,
      item?.original_name,
    ].map((value) => normalizeTitle(stripPortalSubtitle(value))).filter(Boolean);

    const fullTitle = normalizeTitle(context.title);
    const baseTitle = normalizeTitle(context.baseTitle || context.title);
    const nativeTitle = normalizeTitle(context.nativeTitle);
    const baseNativeTitle = normalizeTitle(context.baseNativeTitle || context.nativeTitle);
    const normalizedQuery = normalizeTitle(queryTitle);
    const candidateYear = getTmdbCandidateYear(item);

    let score = 0;

    if (candidateTitles.includes(fullTitle)) score += 180;
    if (baseTitle && candidateTitles.includes(baseTitle)) score += 170;
    if (baseTitle && candidateBaseTitles.includes(baseTitle)) score += 220;
    if (nativeTitle && candidateTitles.includes(nativeTitle)) score += 140;
    if (baseNativeTitle && candidateBaseTitles.includes(baseNativeTitle)) score += 180;
    if (baseNativeTitle && candidateTitles.includes(baseNativeTitle)) score += 130;
    if (normalizedQuery && candidateTitles.includes(normalizedQuery)) score += 80;

    candidateTitles.forEach((title) => {
      if (fullTitle && (title.includes(fullTitle) || fullTitle.includes(title))) score += 55;
      if (baseTitle && (title.includes(baseTitle) || baseTitle.includes(title))) score += 70;
      if (nativeTitle && (title.includes(nativeTitle) || nativeTitle.includes(title))) score += 35;
      if (baseNativeTitle && (title.includes(baseNativeTitle) || baseNativeTitle.includes(title))) score += 45;
    });
    candidateBaseTitles.forEach((title) => {
      if (baseTitle && (title.includes(baseTitle) || baseTitle.includes(title))) score += 85;
      if (baseNativeTitle && (title.includes(baseNativeTitle) || baseNativeTitle.includes(title))) score += 60;
    });

    if (context.year && candidateYear) {
      const diff = Math.abs(Number(candidateYear) - Number(context.year));
      if (diff === 0) score += 140;
      else if (diff === 1) score += 20;
      else if (context.kind === 'movie') score -= 220;
      else if (!context.hasSplitMarker) score -= 45;
    }

    const itemType = String(item?.media_type || context.kind || '').toLowerCase();
    if (context.kind === 'movie' && itemType === 'movie') score += 20;
    if (context.kind === 'tv' && itemType === 'tv') score += 20;
    if (context.hasSplitMarker && candidateTitles.some((title) => /\b(season|part|pt)\b/.test(title))) score -= 35;

    return score;
  }

  function collapseWhitespace(value) {
    return String(value || '').replace(/\s+/g, ' ').trim();
  }

  function truncateText(value, maxLength) {
    const clean = collapseWhitespace(value);
    if (clean.length <= maxLength) return clean;
    return `${clean.slice(0, maxLength - 1).trimEnd()}...`;
  }

  function createAbsoluteUrl(url, base = location.origin) {
    try {
      return new URL(url, base).href;
    } catch {
      return '';
    }
  }

  function requestExternal(details) {
    return new Promise((resolve, reject) => {
      const handler = typeof GM_xmlhttpRequest === 'function'
        ? GM_xmlhttpRequest
        : (typeof GM !== 'undefined' && typeof GM.xmlHttpRequest === 'function' ? GM.xmlHttpRequest.bind(GM) : null);

      if (!handler) {
        const controller = typeof AbortController !== 'undefined' ? new AbortController() : null;
        const timeoutId = controller ? setTimeout(() => controller.abort(), details.timeout || 12000) : null;
        fetch(details.url, {
          method: details.method || 'GET',
          headers: details.headers || {},
          body: details.data,
          signal: controller?.signal,
        })
          .then(async (response) => {
            const responseText = await response.text();
            if (timeoutId) clearTimeout(timeoutId);
            resolve({
              status: response.status,
              responseText,
              finalUrl: response.url,
            });
          })
          .catch((error) => {
            if (timeoutId) clearTimeout(timeoutId);
            reject(error);
          });
        return;
      }

      handler({
        method: details.method || 'GET',
        url: details.url,
        headers: details.headers || {},
        data: details.data,
        responseType: 'text',
        timeout: details.timeout || 12000,
        onload: resolve,
        onerror: reject,
        ontimeout: reject,
      });
    });
  }

  function getTitleHeading() {
    return q('h1.film-title, h1');
  }

  function getTitleHeadingOriginalText() {
    const heading = getTitleHeading();
    return collapseWhitespace(heading?.dataset?.bettermdlOriginalTitle || text(heading));
  }

  function getTitleHeaderNativeTitle() {
    const subtitle = q('.title-container .film-subtitle span, .title-container .film-subtitle');
    const raw = collapseWhitespace(text(subtitle));
    const nativeTitle = collapseWhitespace(raw.split(/\s*[‧·]\s*/)[0] || '');
    if (nativeTitle && !/\b(?:drama|movie|special|tv show|variety show)\b/i.test(nativeTitle) && !/^\d{4}$/.test(nativeTitle)) {
      return nativeTitle;
    }
    return '';
  }

  function initTitleNativeTitleSwap() {
    if (!isTitlePage()) return;
    const heading = q('.title-container h1.film-title') || getTitleHeading();
    const subtitle = q('.title-container .film-subtitle span, .title-container .film-subtitle');
    if (!heading || !subtitle) return;

    if (!heading.dataset.bettermdlOriginalTitle) {
      heading.dataset.bettermdlOriginalTitle = collapseWhitespace(text(heading));
    }
    if (!subtitle.dataset.bettermdlOriginalSubtitle) {
      subtitle.dataset.bettermdlOriginalSubtitle = collapseWhitespace(text(subtitle));
    }

    const originalTitle = collapseWhitespace(heading.dataset.bettermdlOriginalTitle);
    const originalSubtitle = collapseWhitespace(subtitle.dataset.bettermdlOriginalSubtitle);
    const nativeTitle = extractTitlePageNativeTitle() || getTitleHeaderNativeTitle();
    const enabled = isFeatureEnabled('titleNativeTitleFirst') && nativeTitle && nativeTitle !== originalTitle;

    if (!enabled) {
      heading.textContent = originalTitle;
      subtitle.textContent = originalSubtitle;
      return;
    }

    const subtitleParts = originalSubtitle.split(/\s*[‧·]\s*/).map(collapseWhitespace).filter(Boolean);
    const detailParts = subtitleParts.slice(1);
    heading.textContent = nativeTitle;
    subtitle.textContent = [originalTitle, ...detailParts].filter(Boolean).join(' ‧ ');
  }

  function getTitleIdFromPath() {
    const match = location.pathname.match(/^\/(\d+)(?:-|\/|$)/);
    return match ? match[1] : '';
  }

  function getTitleYearFromHeading() {
    const headingText = getTitleHeadingOriginalText();
    const match = headingText.match(/\((\d{4})\)\s*$/);
    return match ? match[1] : '';
  }

  function extractOriginalWorkSourceTypeFromText(value) {
    const normalized = collapseWhitespace(value).toLowerCase();
    const patterns = [
      ['web novel', /\bweb\s+novel\b/],
      ['light novel', /\blight\s+novel\b/],
      ['novel', /\bnovel\b|\bbook\b/],
      ['webtoon', /\bwebtoon\b|\bwebcomic\b|\bweb\s+comic\b/],
      ['manhwa', /\bmanhwa\b/],
      ['manhua', /\bmanhua\b/],
      ['manga', /\bmanga\b|\bcomic\b/],
      ['game', /\bgame\b/],
    ];
    return patterns.find(([, pattern]) => pattern.test(normalized))?.[0] || '';
  }

  function extractTitlePageAliasTitles() {
    const candidates = qa('b, strong, .list-item, .box-body li, .show-details li, .show-detailsxss li')
      .map((el) => text(el))
      .filter(Boolean);

    for (const value of candidates) {
      const match = value.match(/Also Known As:\s*([^|]+)/i);
      if (!match?.[1]) continue;
      const parts = match[1]
        .split(/\s*,\s*|\s*;\s*/)
        .map(collapseWhitespace)
        .filter(Boolean);
      const merged = [];
      for (let index = 0; index < parts.length; index += 1) {
        const current = parts[index];
        const next = parts[index + 1] || '';
        if (/^\S+$/.test(current) && /^(?:Mr|Mrs|Ms|Miss|Dr)\.?\s+/i.test(next)) {
          merged.push(`${current}, ${next}`);
          index += 1;
        } else {
          merged.push(current);
        }
      }
      return merged
        .slice(0, 6);
    }

    return [];
  }

  function getTitleCountryFromPage() {
    const detailText = qa('.box, .show-details, .show-detailsxss, .list-item')
      .map((el) => text(el))
      .filter(Boolean)
      .join(' ');
    return collapseWhitespace(detailText.match(/Country:\s*([^|]+?)(?:\s+(?:Episodes|Aired|Duration|Content Rating|Original Network|Score|Ranked|Popularity|Watchers):|$)/i)?.[1] || '');
  }

  function extractOriginalWorkAuthorFromText(value, sourceTitle) {
    const clean = collapseWhitespace(value);
    if (!clean || !sourceTitle) return '';

    const escapedTitle = sourceTitle.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const afterTitleMatch = clean.match(new RegExp(`${escapedTitle}[^.]{0,120}?\\s+by\\s+([^.;]+)`, 'i'));
    const fallbackMatch = clean.match(/\s+by\s+([^.;]+)(?:\.|$)/i);
    const rawAuthor = collapseWhitespace(afterTitleMatch?.[1] || fallbackMatch?.[1] || '');
    if (!rawAuthor) return '';

    return rawAuthor
      .replace(/\s*Edit Translation.*$/i, '')
      .replace(/^["'“”]+|["'“”]+$/g, '')
      .trim();
  }

  function collectOriginalWorkHint() {
    const root = getMainLeftColumn();
    const candidates = qa('div, p, span', root)
      .map((el) => text(el))
      .filter(Boolean)
      .filter((value) => /adapted from|based on/i.test(value));

    const fallbackText = collapseWhitespace(root?.innerText || '');
    if (fallbackText) candidates.push(fallbackText);

    const patterns = [
      /adapted from the ([a-z ]+?) ["“]([^"”]+)["”](?:\s*\(([^)]+)\))?/i,
      /based on the ([a-z ]+?) ["“]([^"”]+)["”](?:\s*\(([^)]+)\))?/i,
      /adapted from ["“]([^"”]+)["”](?:\s*\(([^)]+)\))?/i,
      /based on ["“]([^"”]+)["”](?:\s*\(([^)]+)\))?/i,
    ];

    patterns.unshift(
      /adapted from (?:the\s+)?([a-z ]+?)\s+["'“”]([^"'“”]+)["'“”](?:\s*\(([^)]+)\))?/i,
      /based on (?:the\s+)?([a-z ]+?)\s+["'“”]([^"'“”]+)["'“”](?:\s*\(([^)]+)\))?/i,
      /adapted from (?:the\s+)?([a-z ]+?)\s+([^.;]+?)(?:\s+by\s+([^.;]+))?(?:\.|;|$)/i,
      /based on (?:the\s+)?([a-z ]+?)\s+([^.;]+?)(?:\s+by\s+([^.;]+))?(?:\.|;|$)/i,
    );

    for (const candidate of candidates) {
      for (const pattern of patterns) {
        const match = candidate.match(pattern);
        if (!match) continue;

        const rawType = collapseWhitespace(match[1] || '').toLowerCase();
        const detectedType = extractOriginalWorkSourceTypeFromText(rawType);
        const hasExplicitType = !!(match[2] && detectedType);
        const sourceType = hasExplicitType ? detectedType : '';
        const sourceTitle = collapseWhitespace(hasExplicitType ? match[2] : match[1]);
        const nativeTitle = collapseWhitespace(hasExplicitType ? match[3] : match[2]);
        const hasQuotedTitle = /["'“”]/.test(match[0] || '');

        if (!detectedType && !hasQuotedTitle) continue;
        if (!detectedType && match[2] && /^(?:a|an|the)$/i.test(rawType)) continue;
        if (!sourceTitle) continue;

        return {
          sourceType,
          sourceTitle,
          nativeTitle,
          author: extractOriginalWorkAuthorFromText(candidate, sourceTitle),
          hasExplicitSourceTitle: true,
        };
      }
    }

    const adaptationType = extractOriginalWorkSourceTypeFromText(fallbackText);
    if (!adaptationType || !/adapted from/i.test(fallbackText)) return null;

    return {
      sourceType: adaptationType,
      sourceTitle: '',
      nativeTitle: '',
      author: '',
      hasExplicitSourceTitle: false,
    };
  }

  function getTitlePageContext() {
    const heading = collapseWhitespace(getTitleHeadingOriginalText().replace(/\(\d{4}\)\s*$/, ''));
    const pageNativeTitle = extractTitlePageNativeTitle();
    const aliases = extractTitlePageAliasTitles();
    const meta = qa('.show-detailsxss, .list-item, .box-body li, .show-details li')
      .map((el) => text(el))
      .filter(Boolean)
      .join(' ');

    const sourceHint = collectOriginalWorkHint();
    if (!sourceHint && !pageNativeTitle && !aliases.length) return null;

    return {
      mdlTitle: heading,
      sourceTitle: sourceHint?.sourceTitle || heading,
      nativeTitle: sourceHint?.nativeTitle || pageNativeTitle,
      pageNativeTitle,
      aliases,
      sourceType: sourceHint?.sourceType || '',
      sourceAuthor: sourceHint?.author || '',
      hasExplicitSourceTitle: !!sourceHint?.hasExplicitSourceTitle,
      hasOriginalWorkHint: !!sourceHint,
      country: getTitleCountryFromPage(),
      year: getTitleYearFromHeading(),
      pageMeta: meta,
    };
  }

  function extractTitlePageNativeTitle() {
    const candidates = qa('b, strong, .list-item, .box-body li, .show-details li, .show-detailsxss li')
      .map((el) => text(el))
      .filter(Boolean);

    for (const value of candidates) {
      const match = value.match(/Native Title:\s*([^|]+)/i);
      if (match?.[1]) return collapseWhitespace(match[1]);
    }

    return collapseWhitespace(text(q('b.inline + a')));
  }

  function getTitleKind() {
    const heading = q('h1.film-title') || getTitleHeading();
    const headingParent = heading?.parentElement || null;
    const subtitleCandidates = [
      text(heading?.nextElementSibling),
      text(q('.film-title + div')),
      text(q('.film-title + .text-muted')),
      text(q('.film-title + .small')),
      text(q('.film-title + p')),
      text(q('.film-title ~ div')),
      text(q('.film-title ~ p')),
      text(q('.text-muted')),
      text(q('.text-muted.title')),
      text(headingParent),
      text(headingParent?.nextElementSibling),
    ].map(collapseWhitespace).filter(Boolean);

    const joinedHeadingMeta = subtitleCandidates.join(' | ');
    if (/\bmovie\b/i.test(joinedHeadingMeta)) return 'movie';
    if (/\bdrama\b|\btv show\b|\bseries\b/i.test(joinedHeadingMeta)) return 'tv';
    if (/\bspecial\b/i.test(joinedHeadingMeta)) return 'multi';

    for (const item of subtitleCandidates) {
      if (/\bmovie\b/i.test(item)) return 'movie';
      if (/\bdrama\b|\btv show\b|\bseries\b/i.test(item)) return 'tv';
      if (/\bspecial\b/i.test(item)) return 'multi';
    }

    const detailItems = qa('.box-body li, .show-details li, .show-detailsxss li').map((el) => text(el));
    for (const item of detailItems) {
      if (item.includes('TV Show:') || item.includes('Drama:')) return 'tv';
      if (item.includes('Movie:')) return 'movie';
      if (item.includes('Special:')) return 'multi';
    }
    return 'tv';
  }

  function getTitleActiveTabLabel() {
    const active = qa('.nav-tabs li.active > a, .nav-tabs a.active, .nav li.active > a, .nav a.active, .film-tabs a.active, .tabs a.active, [role="tab"][aria-selected="true"]')
      .map((node) => collapseWhitespace(text(node)))
      .find(Boolean);
    return active || '';
  }

  function getTitleTabKind() {
    const match = location.pathname.match(/^\/\d+[^/]*(?:\/([^/?#]+))?/);
    const pathTab = String(match?.[1] || '').toLowerCase();
    if (pathTab) {
      if (/^episodes?$/.test(pathTab)) return 'episodes';
      if (/^cast$/.test(pathTab)) return 'cast';
      if (/^reviews?$/.test(pathTab)) return 'reviews';
      if (/^write_review$/.test(pathTab)) return 'write-review';
      if (/^recommendations?$|^recs$/.test(pathTab)) return 'recs';
      if (/^photos?$/.test(pathTab)) return 'photos';
      if (/^discussions?$/.test(pathTab)) return 'discussions';
      if (/^feed$/.test(pathTab)) return 'feed';
    }

    const active = getTitleActiveTabLabel().toLowerCase();
    if (/^episodes?$/.test(active)) return 'episodes';
    if (/^cast$/.test(active)) return 'cast';
    if (/^reviews?$/.test(active)) return 'reviews';
    if (/^recommendations?$|^recs$/.test(active)) return 'recs';
    if (/^photos?$/.test(active)) return 'photos';
    if (/^discussions?$/.test(active)) return 'discussions';
    if (/^feed$/.test(active)) return 'feed';
    return 'details';
  }

  function isTitleDetailsTabActive() {
    return getTitleTabKind() === 'details';
  }

  function isTitlePhotosTabActive() {
    return getTitleTabKind() === 'photos';
  }

  function isTitleTabLink(node) {
    const label = collapseWhitespace(text(node));
    return /^(details|episodes|cast|reviews|recs|photos|discussions|feed)$/i.test(label);
  }

  function scheduleTitleTabRefresh(delay = 220) {
    clearTimeout(titleTabRefreshTimer);
    titleTabRefreshTimer = setTimeout(() => {
      initTitlePageSectionToggles();
      initTitleNativeActionToggles();
      initPortalLinks().catch(() => {});
    }, delay);
  }

  function maintainTitlePortalIcons() {
    if (!isTitlePage()) return;
    if (!isTitleDetailsTabActive() || !isFeatureEnabled('titlePortalIcons')) {
      q(`#${PORTALS_BOX_ID}`)?.remove();
      getTitlePosterActionMounts().forEach((mount) => {
        findNativePortalBlocks(mount).forEach((node) => setNativeActionHidden(node, true));
      });
      lastPortalRenderKey = '';
      return;
    }
    getTitlePosterActionMounts().forEach((mount) => {
      findNativePortalBlocks(mount).forEach((node) => setNativeActionHidden(node, false));
    });
    if (!q(`#${PORTALS_BOX_ID}`)) {
      initPortalLinks().catch(() => {});
    }
  }

  function bindTitleTabRefresh() {
    if (window.__betterMdlTitleTabRefreshBound) return;
    document.addEventListener('click', (event) => {
      if (!isTitlePage()) return;
      const link = event.target?.closest?.('a, button, [role="tab"]');
      if (!link || !isTitleTabLink(link)) return;
      scheduleTitleTabRefresh(120);
      setTimeout(() => scheduleTitleTabRefresh(120), 360);
      setTimeout(() => scheduleTitleTabRefresh(120), 900);
    }, true);
    window.addEventListener('popstate', () => {
      if (isTitlePage()) scheduleTitleTabRefresh(220);
    });
    window.setInterval(maintainTitlePortalIcons, 1200);
    window.__betterMdlTitleTabRefreshBound = true;
  }

  function hasLikelyPosterImage(root) {
    return qa('img', root).some((img) => {
      const src = String(img.getAttribute('src') || '');
      const alt = String(img.getAttribute('alt') || '');
      if (/avatar|user|profile|icon|logo|emoji|flag/i.test(src) || /avatar|user|profile|icon|logo/i.test(alt)) return false;
      const rect = img.getBoundingClientRect?.();
      if (rect && rect.width && rect.height && (rect.width < 90 || rect.height < 120)) return false;
      return true;
    });
  }

  function hasPosterActionText(root) {
    return /watch\s+trailer|buy\s+on\s+amazon|currently\s+watching|completed|plan\s+to\s+watch|on\s+hold|dropped|not\s+interested|add\s+to\s+list/i.test(text(root));
  }

  function getSidebarPosterLinksMount() {
    const main = getMainLeftColumn();
    const sidebars = qa('.col-xl-4, .col-lg-4, .col-md-4, .col-sm-4, .sidebar, .side-content, aside')
      .filter((node) => node && !main.contains(node) && hasLikelyPosterImage(node));

    for (const sidebar of sidebars) {
      const children = Array.from(sidebar.children);
      const actionChild = children.find((child) => hasLikelyPosterImage(child) && hasPosterActionText(child));
      if (actionChild) return actionChild;

      if (hasPosterActionText(sidebar)) return sidebar;

      const posterImage = qa('img', sidebar).find((img) => hasLikelyPosterImage(img.parentElement || img));
      const posterCard = posterImage?.closest('.box, .card, .film-cover, .cover, .poster-container') || posterImage?.parentElement;
      if (posterCard && posterCard !== sidebar) return posterCard;

      const posterChild = children.find(hasLikelyPosterImage);
      if (posterChild) return posterChild;
    }

    return null;
  }

  function getDetailsPosterLinksMount() {
    const classMount = q('.col-xs-4.col-sm-3.col-md-3') || q('.col-xs-4.col-sm-4.col-md-3') || q('.film-cover, .cover, .poster-container');
    if (classMount) return classMount;

    const main = getMainLeftColumn();
    const posterImage = qa('img', main).find((img) => hasLikelyPosterImage(img.parentElement || img));
    if (!posterImage) return null;

    let current = posterImage.parentElement;
    while (current && current !== main) {
      if (hasPosterActionText(current)) return current;
      current = current.parentElement;
    }

    return posterImage.parentElement || null;
  }

  function getPosterLinksMount() {
    if (!isTitleDetailsTabActive()) return null;
    return getDetailsPosterLinksMount();
  }

  function getTitlePosterActionMounts() {
    return [...new Set([
      getDetailsPosterLinksMount(),
      getSidebarPosterLinksMount(),
    ].filter(Boolean))];
  }

  function findPortalInsertionPoint(root) {
    if (!root) return null;
    const posterImage = qa('img', root).find((img) => hasLikelyPosterImage(img.parentElement || img));
    const actionNode = qa('a, button, [role="button"], div', root)
      .find((node) => {
        if (node === root || !hasPosterActionText(node)) return false;
        if (!posterImage) return true;
        return !!(posterImage.compareDocumentPosition(node) & Node.DOCUMENT_POSITION_FOLLOWING);
      });

    if (actionNode) {
      let actionBlock = actionNode.closest('a, button, [role="button"]') || actionNode;
      while (
        actionBlock?.parentElement
        && actionBlock.parentElement !== root
        && !hasPosterActionText(actionBlock.parentElement)
      ) {
        actionBlock = actionBlock.parentElement;
      }
      if (actionBlock?.parentElement) return { parent: actionBlock.parentElement, before: actionBlock };
      return { parent: actionNode.parentElement || root, before: actionNode };
    }

    const posterBlock = posterImage?.parentElement && posterImage.parentElement !== root
      ? posterImage.parentElement
      : posterImage;
    const posterParent = posterBlock?.parentElement || root;
    return { parent: posterParent, before: posterBlock?.nextSibling || null };
  }

  function getPortalContext() {
    const headingLink = q('h1.film-title a');
    const title = collapseWhitespace((headingLink ? text(headingLink) : getTitleHeadingOriginalText()).replace(/\(\d{4}\)\s*$/, ''));
    const nativeTitle = collapseWhitespace(text(q('b.inline + a')));
    const year = getTitleYearFromHeading();
    const kind = getTitleKind();
    const detailBoxText = collapseWhitespace(text(q('.box.clear.hidden-sm-down')) || text(q('.col-lg-4.col-md-4')));

    if (!title) return null;

    return {
      title,
      baseTitle: stripPortalSubtitle(title),
      nativeTitle,
      baseNativeTitle: stripPortalSubtitle(nativeTitle),
      hasSplitMarker: hasPortalSplitMarker(title) || hasPortalSplitMarker(nativeTitle),
      year,
      kind,
      isJapanese: /country:\s*japan/i.test(detailBoxText),
    };
  }

  function scoreCandidate(candidate, context) {
    const sourceTitle = normalizeTitle(context.sourceTitle);
    const nativeTitle = normalizeTitle(context.nativeTitle);
    const pageNativeTitle = normalizeTitle(context.pageNativeTitle);
    const mdlTitle = normalizeTitle(context.mdlTitle);
    const aliases = (Array.isArray(context.aliases) ? context.aliases : []).map(normalizeTitle).filter(Boolean);
    const titles = [
      candidate.title,
      candidate.titleEnglish,
      candidate.titleNative,
        ...(candidate.synonyms || []),
    ]
      .map(normalizeTitle)
      .filter(Boolean);

    let score = 0;

    if (titles.includes(sourceTitle)) score += 120;
    if (sourceTitle && !isGenericOriginalWorkTitle(context.sourceTitle) && sourceTitle.length >= 4 && titles.some((title) => title.startsWith(`${sourceTitle} `) || title.includes(` ${sourceTitle} `))) score += 95;
    if (nativeTitle && titles.includes(nativeTitle)) score += 70;
    if (pageNativeTitle && titles.includes(pageNativeTitle)) score += 60;
    if (nativeTitle && nativeTitle.length >= 3 && titles.some((title) => title.includes(nativeTitle))) score += 55;
    if (pageNativeTitle && pageNativeTitle.length >= 3 && titles.some((title) => title.includes(pageNativeTitle))) score += 45;
    if (titles.includes(mdlTitle)) score += 12;
    if (aliases.filter(isUsefulOriginalWorkAlias).some((alias) => titles.includes(alias))) score += context.hasExplicitSourceTitle ? 80 : 115;

    if (!score) {
      titles.forEach((title) => {
        if (isLooseOriginalWorkTitleMatch(sourceTitle, title)) score += 50;
        if (isLooseOriginalWorkTitleMatch(nativeTitle, title)) score += 30;
        if (isLooseOriginalWorkTitleMatch(pageNativeTitle, title)) score += 25;
        aliases.forEach((alias) => {
          if (isLooseOriginalWorkTitleMatch(alias, title)) score += 35;
        });
      });
    }

    const requestedKinds = getOriginalWorkRequestedKinds(context.sourceType);
    if (requestedKinds.length && requestedKinds.includes(candidate.kind)) score += 25;
    if (context.sourceType === 'webtoon' && (candidate.genres || []).some((genre) => /webtoon/i.test(genre))) score += 20;

    if (candidate.description && normalizeTitle(candidate.description).includes(sourceTitle)) score += 5;

    return score;
  }

  function getOriginalWorkSearchLimit(provider) {
    if (provider === 'myanimelist' || provider === 'anilist') return 4;
    if (provider === 'naiin' || provider === 'mebmarket' || provider === 'novelupdates' || provider === 'namuwiki') return 5;
    return ORIGINAL_WORK_MAX_QUERIES_PER_PROVIDER;
  }

  function isUsefulOriginalWorkAlias(value) {
    const normalized = normalizeTitle(value);
    if (!normalized) return false;
    if (/[^\u0000-\u007f]/.test(String(value || ''))) return true;
    return normalized.length >= 10 && getMeaningfulOriginalWorkTokens(normalized).length >= 2;
  }

  function getOriginalWorkRequestedKinds(sourceType) {
    const normalized = String(sourceType || '').toLowerCase();
    if (/novel|book/.test(normalized)) return ['novel'];
    if (/manhwa|webtoon/.test(normalized)) return ['manhwa', 'manga'];
    if (/manhua/.test(normalized)) return ['manhua', 'manga'];
    return SOURCE_TYPE_MAP[normalized] || [];
  }

  function isGenericOriginalWorkTitle(value) {
    const normalized = normalizeTitle(value);
    if (!normalized) return true;
    const meaningful = getMeaningfulOriginalWorkTokens(normalized);
    return normalized.length < 12 || meaningful.length < 2;
  }

  function buildOriginalWorkSearchQueries(context, options = {}) {
    const titles = [];
    const addTitle = (value) => {
      const clean = collapseWhitespace(value);
      if (clean && !titles.includes(clean)) titles.push(clean);
    };

    if (!context.hasOriginalWorkHint) {
      (Array.isArray(context.aliases) ? context.aliases : []).filter(isUsefulOriginalWorkAlias).forEach(addTitle);
      addTitle(context.sourceTitle);
      addTitle(context.nativeTitle);
      addTitle(context.pageNativeTitle);
    } else if (context.hasExplicitSourceTitle) {
      addTitle(context.sourceTitle);
      addTitle(context.nativeTitle);
    } else if (isGenericOriginalWorkTitle(context.sourceTitle)) {
      (Array.isArray(context.aliases) ? context.aliases : []).filter(isUsefulOriginalWorkAlias).forEach(addTitle);
      addTitle(context.nativeTitle);
      addTitle(context.pageNativeTitle);
      if (options.includeGenericEnglish) addTitle(context.sourceTitle);
    } else {
      addTitle(context.sourceTitle);
      (Array.isArray(context.aliases) ? context.aliases : []).filter(isUsefulOriginalWorkAlias).slice(0, 3).forEach(addTitle);
      addTitle(context.pageNativeTitle);
    }

    const queries = [];
    titles.forEach((title) => {
      if (context.year && context.hasOriginalWorkHint && !context.hasExplicitSourceTitle) queries.push(`${title} ${context.year}`);
      queries.push(title);
    });

    return [...new Set(queries.map(collapseWhitespace).filter(Boolean))];
  }

  function getMeaningfulOriginalWorkTokens(value) {
    const stopWords = new Set(['the', 'and', 'for', 'from', 'with', 'into', 'onto', 'your', 'you', 'are', 'was', 'were']);
    return String(value || '')
      .split(/\s+/)
      .map((token) => token.trim())
      .filter((token) => token.length > 2 && !stopWords.has(token));
  }

  function isLooseOriginalWorkTitleMatch(sourceTitle, candidateTitle) {
    if (!sourceTitle || !candidateTitle) return false;
    if (sourceTitle.length < 12 || candidateTitle.length < 12) return false;

    const sourceTokens = getMeaningfulOriginalWorkTokens(sourceTitle);
    const candidateTokens = getMeaningfulOriginalWorkTokens(candidateTitle);
    if (sourceTokens.length < 2 || candidateTokens.length < 2) return false;

    const candidateSet = new Set(candidateTokens);
    const sharedCount = sourceTokens.filter((token) => candidateSet.has(token)).length;
    if (sharedCount < Math.min(2, sourceTokens.length)) return false;

    return candidateTitle.includes(sourceTitle) || sourceTitle.includes(candidateTitle);
  }

  function formatScore(score) {
    if (score === null || score === undefined || score === '') return '';
    const numeric = Number(score);
    if (Number.isFinite(numeric)) {
      return `${numeric % 1 === 0 ? numeric.toFixed(0) : numeric.toFixed(1)}`;
    }
    return String(score);
  }

  function formatMetaPieces(data) {
    const pieces = [];

    if (data.year) pieces.push(String(data.year));

    const score = formatScore(data.score);
    if (score) {
      const label = data.scoreLabel || 'Rating';
      pieces.push(`${label} ${score}`);
    }

    return pieces;
  }

  function buildOriginalWorkRenderKey(data) {
    return JSON.stringify({
      title: data?.title || '',
      titleEnglish: data?.titleEnglish || '',
      titleNative: data?.titleNative || '',
      url: data?.url || '',
      image: data?.image || '',
      year: data?.year || '',
      score: data?.score || '',
      scoreLabel: data?.scoreLabel || '',
      lengthLabel: data?.lengthLabel || '',
      description: truncateText(data?.description || '', 220),
    });
  }

  function formatOriginalWorkDescription(value, maxLength = 220) {
    const raw = String(value || '');
    if (!raw) return '';
    const normalized = raw
      .replace(/\s+(Title:)/g, '\n$1')
      .replace(/\s+(Year:)/g, '\n$1')
      .replace(/\s+(Type:)/g, '\n$1')
      .replace(/\s+(Volume:)/g, '\n$1')
      .replace(/\s+(Author:)/g, '\n$1')
      .replace(/\s+(Source:)/g, '\n$1')
      .replace(/\s+(EP(?:isode)?(?:s)?(?:\s+Numbers?)?:)/gi, '\n$1')
      .split(/\n+/)
      .map(collapseWhitespace)
      .filter(Boolean)
      .join('\n');
    if (normalized.length <= maxLength) return normalized;
    return `${normalized.slice(0, maxLength - 1).trimEnd()}...`;
  }

  function getOriginalWorkDescriptionValue(description, label) {
    const pattern = new RegExp(`^${label}:\\s*(.+)$`, 'i');
    const value = String(description || '')
      .split(/\n+/)
      .map(collapseWhitespace)
      .map((line) => line.match(pattern)?.[1] || '')
      .find(Boolean) || '';
    return cleanOriginalWorkDetailValue(label, value);
  }

  function cleanOriginalWorkDetailValue(label, value) {
    let clean = collapseWhitespace(value);
    if (!clean) return '';

    if (/^author$/i.test(label)) {
      clean = clean
        .replace(/\s+\b(?:\d{1,2}(?:st|nd|rd|th)\s+century|ancient|modern|present-day)\b.*$/i, '')
        .replace(/\s+\b(?:while|when|after|before|having|college|student|amidst|through|in)\b.{20,}$/i, '')
        .replace(/\s+[A-Z][a-z]+(?:[A-Z][a-z]+)?[,.;:].*$/, '')
        .replace(/\s+\.{2,}.*$/, '');
    }

    return clean.trim();
  }

  function humanizeOriginalWorkKind(kind) {
    const normalized = String(kind || '').toLowerCase().replace(/[_-]+/g, ' ').trim();
    if (!normalized) return '';
    if (normalized === 'manhwa') return 'Manhwa';
    if (normalized === 'manhua') return 'Manhua';
    if (normalized === 'webtoon') return 'Webtoon';
    if (normalized === 'web novel') return 'Web Novel';
    if (normalized === 'light novel') return 'Light Novel';
    if (normalized === 'novel') return 'Novel';
    if (normalized === 'manga') return 'Manga';
    return normalized.replace(/\b\w/g, (char) => char.toUpperCase());
  }

  function getOriginalWorkSourceLabel(data) {
    const label = collapseWhitespace(data?.provider || data?.scoreLabel || '');
    if (!label || /known override/i.test(label)) return '';
    return label;
  }

  function isUsableOriginalWorkNativeTitle(value, displayTitle = '') {
    const clean = collapseWhitespace(value);
    if (!clean || !/[^\u0000-\u007f]/.test(clean)) return false;
    if (/^\?+(?:\s+\?+)*$/.test(clean)) return false;
    if (/^\uFFFD+(?:\s+\uFFFD+)*$/.test(clean)) return false;
    if (displayTitle && normalizeTitle(clean) === normalizeTitle(displayTitle)) return false;
    return true;
  }

  function getOriginalWorkNativeTitle(data, displayTitle = '') {
    const candidates = [
      data?.titleNative,
      getOriginalWorkDescriptionValue(data?.description || '', 'Title'),
      ...(Array.isArray(data?.synonyms) ? data.synonyms : []),
    ];
    return candidates.map(collapseWhitespace).find((item) => isUsableOriginalWorkNativeTitle(item, displayTitle)) || '';
  }

  function buildOriginalWorkDetails(data, displayTitle) {
    const formatted = formatOriginalWorkDescription(data?.description || '', 420);
    const titleLine = getOriginalWorkNativeTitle(data, displayTitle);
    const year = getOriginalWorkDescriptionValue(formatted, 'Year') || collapseWhitespace(data?.year || '');
    const type = getOriginalWorkDescriptionValue(formatted, 'Type') || humanizeOriginalWorkKind(data?.kind || data?.lengthLabel || '');
    const volume = getOriginalWorkDescriptionValue(formatted, 'Volume');
    const author = getOriginalWorkDescriptionValue(formatted, 'Author');
    const source = getOriginalWorkDescriptionValue(formatted, 'Source') || getOriginalWorkSourceLabel(data);

    return [
      titleLine ? `Title: ${titleLine}` : '',
      year ? `Year: ${year}` : '',
      type ? `Type: ${type}` : '',
      volume ? `Volume: ${volume}` : '',
      author ? `Author: ${author}` : '',
      source ? `Source: ${source}` : '',
    ].filter(Boolean).join('\n');
  }

  function mapJikanKind(entry) {
    const kind = String(entry?.type || '').toLowerCase();
    if (kind.includes('novel')) return 'novel';
    if (kind.includes('manhwa')) return 'manhwa';
    if (kind.includes('manhua')) return 'manhua';
    if (kind.includes('anime')) return 'anime';
    return 'manga';
  }

  function normalizeJikanEntry(entry) {
    return {
      provider: 'MyAnimeList',
      title: collapseWhitespace(entry?.title || ''),
      titleEnglish: collapseWhitespace(entry?.title_english || ''),
      titleNative: collapseWhitespace(entry?.title_japanese || ''),
      synonyms: Array.isArray(entry?.titles)
        ? entry.titles.map((item) => collapseWhitespace(item?.title || '')).filter(Boolean)
        : [],
      description: collapseWhitespace(entry?.synopsis || ''),
      url: entry?.url || '',
      image: entry?.images?.jpg?.large_image_url || entry?.images?.jpg?.image_url || '',
      year: entry?.published?.prop?.from?.year || '',
      score: entry?.score ?? '',
      scoreLabel: 'MAL',
      lengthLabel: buildJikanLength(entry),
      kind: mapJikanKind(entry),
      genres: Array.isArray(entry?.genres) ? entry.genres.map((genre) => collapseWhitespace(genre?.name || '')).filter(Boolean) : [],
    };
  }

  function getPreferredJikanTypes(sourceType) {
    const normalized = String(sourceType || '').toLowerCase();
    if (/novel|book/.test(normalized)) return ['novel'];
    if (/manhwa|webtoon/.test(normalized)) return ['manhwa', 'manga'];
    if (/manhua/.test(normalized)) return ['manhua', 'manga'];
    if (/anime/.test(normalized)) return ['anime'];
    return SOURCE_TYPE_MAP[normalized] || ['manga'];
  }

  function buildJikanLength(entry) {
    const volumes = Number(entry?.volumes);
    const chapters = Number(entry?.chapters);
    const episodes = Number(entry?.episodes);

    const parts = [];
    if (Number.isFinite(volumes) && volumes > 0) parts.push(`${volumes} vol`);
    if (Number.isFinite(chapters) && chapters > 0) parts.push(`${chapters} ch`);
    if (Number.isFinite(episodes) && episodes > 0) parts.push(`${episodes} ep`);

    return parts.join(' - ');
  }

  async function searchMyAnimeList(context) {
    const preferredTypes = getPreferredJikanTypes(context.sourceType);
    const typesToTry = preferredTypes.length ? preferredTypes : ['manga'];
    const searchQueries = buildOriginalWorkSearchQueries(context);
    let best = null;

    for (const type of typesToTry.slice(0, 2)) {
      const endpoint = type === 'anime' ? 'anime' : 'manga';

      for (const queryText of searchQueries.slice(0, getOriginalWorkSearchLimit('myanimelist'))) {
        const searchParams = new URLSearchParams({
          q: queryText,
          limit: '6',
        });

        if (endpoint === 'manga' && type !== 'manga') searchParams.set('type', type);
        if (endpoint === 'anime') searchParams.set('type', 'tv');

        const response = await requestExternal({
          url: `https://api.jikan.moe/v4/${endpoint}?${searchParams.toString()}`,
          headers: {
            Accept: 'application/json',
          },
        }).catch(() => null);

        if (!response || response.status < 200 || response.status >= 300) continue;

        const payload = safeJsonParse(response.responseText, null);
        const list = Array.isArray(payload?.data) ? payload.data.map(normalizeJikanEntry) : [];
        const winner = pickBestCandidate(list, context);
        if (winner && (!best || winner._score > best._score)) best = winner;
        if (best && best._score >= 120) break;
      }

      if (best && best._score >= 120) break;
    }

    return best ? stripInternalScore(best) : null;
  }

  function normalizeAniListEntry(entry) {
    const title = entry?.title || {};
    const format = String(entry?.format || '').toUpperCase();
    const volumes = Number(entry?.volumes);
    const chapters = Number(entry?.chapters);

    const parts = [];
    if (Number.isFinite(volumes) && volumes > 0) parts.push(`${volumes} vol`);
    if (Number.isFinite(chapters) && chapters > 0) parts.push(`${chapters} ch`);

    return {
      provider: 'AniList',
      title: collapseWhitespace(title.romaji || title.english || title.native || ''),
      titleEnglish: collapseWhitespace(title.english || ''),
      titleNative: collapseWhitespace(title.native || ''),
      synonyms: Array.isArray(entry?.synonyms) ? entry.synonyms.map(collapseWhitespace).filter(Boolean) : [],
      description: collapseWhitespace(String(entry?.description || '').replace(/<[^>]+>/g, ' ')),
      url: entry?.siteUrl || '',
      image: entry?.coverImage?.extraLarge || entry?.coverImage?.large || '',
      year: entry?.startDate?.year || '',
      score: entry?.averageScore ? (Number(entry.averageScore) / 10) : '',
      scoreLabel: 'AniList',
      lengthLabel: parts.join(' - '),
      kind: format === 'NOVEL' ? 'novel' : 'manga',
      genres: Array.isArray(entry?.genres) ? entry.genres.map(collapseWhitespace).filter(Boolean) : [],
    };
  }

  async function searchAniList(context) {
    const searchQueries = buildOriginalWorkSearchQueries(context);
    const query = `
      query ($search: String) {
        Page(page: 1, perPage: 8) {
          media(search: $search, type: MANGA, sort: SEARCH_MATCH) {
            title { romaji english native }
            synonyms
            format
            description(asHtml: false)
            siteUrl
            averageScore
            volumes
            chapters
            startDate { year }
            coverImage { extraLarge large }
            genres
          }
        }
      }
    `;

    let best = null;
    for (const queryText of searchQueries.slice(0, getOriginalWorkSearchLimit('anilist'))) {
      const response = await requestExternal({
        method: 'POST',
        url: 'https://graphql.anilist.co',
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
        data: JSON.stringify({
          query,
          variables: { search: queryText },
        }),
      }).catch(() => null);

      if (!response || response.status < 200 || response.status >= 300) continue;

      const payload = safeJsonParse(response.responseText, null);
      const list = Array.isArray(payload?.data?.Page?.media) ? payload.data.Page.media.map(normalizeAniListEntry) : [];
      const winner = pickBestCandidate(list, context);
      if (winner && (!best || winner._score > best._score)) best = winner;
      if (best && best._score >= 120) break;
    }

    return best ? stripInternalScore(best) : null;
  }

  function normalizeMangaUpdatesSeries(record) {
    const series = record?.record || record || {};
    const title = collapseWhitespace(series.title || record?.title || '');
    const url = series.url || record?.url || (series.series_id ? `https://www.mangaupdates.com/series/${series.series_id}` : '');
    const type = collapseWhitespace(series.type || record?.type || '').toLowerCase();
    const associatedNames = [
      ...(Array.isArray(series.associated) ? series.associated : String(series.associated || '').split(/\n|;/)),
      ...(Array.isArray(series.associated_names) ? series.associated_names : []),
      ...(Array.isArray(series.alt_names) ? series.alt_names : []),
    ].map(collapseWhitespace).filter(Boolean);
    const categories = [
      ...(Array.isArray(series.categories) ? series.categories : []),
      ...(Array.isArray(series.genres) ? series.genres : []),
    ].map((item) => collapseWhitespace(item?.category || item?.genre || item?.name || item)).filter(Boolean);

    return {
      provider: 'MangaUpdates',
      title,
      titleEnglish: associatedNames.find((item) => !/[^\u0000-\u007f]/.test(item)) || '',
      titleNative: collapseWhitespace(series.original_title || series.alt_name || ''),
      synonyms: associatedNames,
      description: collapseWhitespace(series.description || series.summary || ''),
      url,
      image: series.image?.url?.original || series.image?.url || series.image || '',
      year: series.year || '',
      score: series.bayesian_rating || series.rating?.bayesian || series.rating || '',
      scoreLabel: 'MU',
      lengthLabel: collapseWhitespace(series.latest_chapter ? `${series.latest_chapter} ch` : ''),
      kind: type.includes('novel') ? 'novel' : type.includes('manhwa') ? 'manhwa' : type.includes('manhua') ? 'manhua' : 'manga',
      genres: categories,
    };
  }

  async function searchMangaUpdates(context) {
    const searchQueries = buildOriginalWorkSearchQueries(context, { includeGenericEnglish: false });
    let best = null;

    for (const queryText of searchQueries.slice(0, ORIGINAL_WORK_MAX_QUERIES_PER_PROVIDER)) {
      const response = await requestExternal({
        method: 'POST',
        url: 'https://api.mangaupdates.com/v1/series/search',
        headers: {
          Accept: 'application/json',
          'Content-Type': 'application/json',
        },
        data: JSON.stringify({
          search: queryText,
          stype: 'title',
          perpage: 8,
        }),
      }).catch(() => null);

      if (!response || response.status < 200 || response.status >= 300) continue;
      const payload = safeJsonParse(response.responseText, null);
      const rawItems = Array.isArray(payload?.results) ? payload.results : Array.isArray(payload) ? payload : [];
      const list = rawItems.map(normalizeMangaUpdatesSeries).filter((entry) => entry.title && entry.url);
      const winner = pickBestCandidate(list, context);
      if (winner && (!best || winner._score > best._score)) best = winner;
      if (best && best._score >= 120) break;
    }

    return best ? stripInternalScore(best) : null;
  }

  function slugifyNovelUpdatesTitle(value) {
    const normalized = String(value || '')
      .normalize('NFKD')
      .replace(/[\u0300-\u036f]/g, '')
      .replace(/&/g, ' and ')
      .replace(/[^a-zA-Z0-9]+/g, '-')
      .replace(/^-+|-+$/g, '')
      .toLowerCase();
    return /[a-z]/.test(normalized) ? normalized : '';
  }

  function buildNovelUpdatesUrls(context) {
    return [...new Set(buildOriginalWorkSearchQueries(context, { includeGenericEnglish: false })
      .slice(0, getOriginalWorkSearchLimit('novelupdates'))
      .map(slugifyNovelUpdatesTitle)
      .filter(Boolean)
      .map((slug) => `https://www.novelupdates.com/series/${slug}/`))];
  }

  function getNaiinTextValue(bodyText, label) {
    const escaped = String(label || '').replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const match = bodyText.match(new RegExp(`${escaped}\\s*:?\\s*([^:]+?)(?=\\s+(?:ผู้เขียน|สำนักพิมพ์|หมวดหมู่|ประเภทสินค้า|จำนวนหน้า|ราคาปก|น้ำหนัก|ISBN|$))`, 'i'));
    return collapseWhitespace(match?.[1] || '');
  }

  function normalizeNaiinProduct(doc, url, context) {
    const bodyText = collapseWhitespace(text(doc.body));
    const ogTitle = q('meta[property="og:title"]', doc)?.getAttribute('content') || '';
    const heading = text(q('h1, .product-title, .name', doc));
    const title = collapseWhitespace(ogTitle || heading || context.sourceTitle || context.mdlTitle)
      .replace(/\s*\|\s*Naiin.*$/i, '')
      .replace(/\s*-\s*Naiin.*$/i, '');
    if (!title) return null;

    const author = getNaiinTextValue(bodyText, 'ผู้เขียน') || context.sourceAuthor || '';
    const category = getNaiinTextValue(bodyText, 'หมวดหมู่') || getNaiinTextValue(bodyText, 'ประเภทสินค้า');
    const pageCount = bodyText.match(/จำนวนหน้า\s*:?\s*(\d+)\s*หน้า/i)?.[1] || '';
    const image = q('meta[property="og:image"]', doc)?.getAttribute('content') || q('img[src*="naiin"]', doc)?.getAttribute('src') || '';
    const isTheWater = normalizeTitle(title).includes('the water') || normalizeTitle(context.sourceTitle).includes('the water');

    return {
      provider: 'Naiin',
      title,
      titleEnglish: title,
      titleNative: context.nativeTitle || context.pageNativeTitle || '',
      synonyms: [title, context.nativeTitle, context.pageNativeTitle].map(collapseWhitespace).filter(Boolean),
      description: [
        context.nativeTitle ? `Title: ${context.nativeTitle}` : '',
        isTheWater ? 'Year: 2025' : '',
        'Type: Novel',
        author ? `Author: ${author}` : '',
        pageCount ? `Pages: ${pageCount}` : '',
        category ? `Category: ${category}` : '',
      ].filter(Boolean).join('\n'),
      url,
      image,
      year: isTheWater ? '2025' : '',
      score: '',
      scoreLabel: 'Naiin',
      lengthLabel: pageCount ? `${pageCount} pages` : 'Novel',
      kind: 'novel',
      genres: category ? [category] : [],
    };
  }

  function getKnownNaiinUrl(context) {
    const country = String(context.country || '').toLowerCase();
    const titles = [
      context.sourceTitle,
      context.mdlTitle,
      context.nativeTitle,
      context.pageNativeTitle,
      ...(Array.isArray(context.aliases) ? context.aliases : []),
    ].map(normalizeTitle).filter(Boolean);

    if (/thailand/.test(country) && titles.some((title) => title === 'the water' || title.includes('the water'))) {
      return 'https://www.naiin.com/product/detail/635778';
    }


    if (/thailand/.test(country) && titles.some((title) => title.includes('moon courting moon') || title.includes('2 moons') || title.includes('deuan giao deuan'))) {
      return 'https://www.naiin.com/product/detail/233444';
    }

    return '';
  }

  async function fetchNaiinProduct(url, context) {
    const response = await requestExternal({
      url,
      headers: { Accept: 'text/html' },
      timeout: 5000,
    }).catch(() => null);

    if (!response || response.status < 200 || response.status >= 300) return null;
    const doc = new DOMParser().parseFromString(response.responseText || '', 'text/html');
    return normalizeNaiinProduct(doc, url, context);
  }

  async function searchNaiin(context) {
    const country = String(context.country || '').toLowerCase();
    const sourceType = String(context.sourceType || '').toLowerCase();
    if (!/thailand/.test(country) || (sourceType && !/novel|book/.test(sourceType))) return null;

    const knownUrl = getKnownNaiinUrl(context);
    if (knownUrl) {
      const known = await fetchNaiinProduct(knownUrl, context);
      if (known) return known;
    }

    let best = null;
    for (const queryText of buildOriginalWorkSearchQueries(context, { includeGenericEnglish: true }).slice(0, getOriginalWorkSearchLimit('naiin'))) {
      const searchUrl = `https://www.naiin.com/search-result?keyword=${encodeURIComponent(queryText)}`;
      const response = await requestExternal({
        url: searchUrl,
        headers: { Accept: 'text/html' },
        timeout: 5000,
      }).catch(() => null);

      if (!response || response.status < 200 || response.status >= 300) continue;
      const doc = new DOMParser().parseFromString(response.responseText || '', 'text/html');
      const linkUrls = qa('a[href*="/product/detail/"]', doc)
        .map((anchor) => anchor.getAttribute('href') || '');
      const rawUrls = [
        ...linkUrls,
        ...(response.responseText || '').match(/(?:https?:\/\/www\.naiin\.com)?\/product\/detail\/\d+/gi) || [],
      ];
      const urls = [...new Set(rawUrls
        .map((url) => createAbsoluteUrl(url, 'https://www.naiin.com'))
        .filter((url) => /\/product\/detail\/\d+/i.test(url)))].slice(0, 8);

      for (const url of urls) {
        const entry = await fetchNaiinProduct(url, context);
        if (!entry?.title) continue;
        const winner = pickBestCandidate([entry], context);
        if (winner && (!best || winner._score > best._score)) best = winner;
        if (best && best._score >= 120) break;
      }
      if (best && best._score >= 120) break;
    }

    return best ? stripInternalScore(best) : null;
  }
  function normalizeMebMarketEntry(entry) {
    const title = collapseWhitespace(entry?.book_name || '');
    const id = collapseWhitespace(entry?.book_id || '');
    if (!title || !id) return null;

    const category = collapseWhitespace(entry?.category_name_en || entry?.category_name || '');
    const author = collapseWhitespace(entry?.book_author || '');
    const publisher = collapseWhitespace(entry?.book_publisher || '');
    const thumbBase = collapseWhitespace(entry?.book_thumbnail_path || '')
      .replace(/^https:\/\/asset\.mebmarket\.com/i, 'https://cdn-local.mebmarket.com')
      .replace(/\/$/, '');
    const thumbVersion = collapseWhitespace(entry?.thumbnail_edition || '');
    const image = thumbBase ? `${thumbBase}/book_detail_large.gif${thumbVersion ? `?${thumbVersion}` : ''}` : '';
    const isComic = /comic|cartoon|manga|manhwa|manhua/i.test(category);

    return {
      provider: 'MEB Market',
      title,
      titleEnglish: title,
      titleNative: /[^\u0000-\u007f]/.test(title) ? title : '',
      synonyms: [title],
      description: [
        `Title: ${title}`,
        `Type: ${isComic ? 'Comic' : 'Novel'}`,
        author ? `Author: ${author}` : '',
        publisher ? `Publisher: ${publisher}` : '',
        category ? `Category: ${category}` : '',
        'Source: MEB Market',
      ].filter(Boolean).join('\n'),
      url: `https://www.mebmarket.com/index.php?action=BookDetails&book_id=${encodeURIComponent(id)}`,
      image,
      year: '',
      score: '',
      scoreLabel: 'MEB Market',
      lengthLabel: isComic ? 'Comic' : 'Novel',
      kind: isComic ? 'manga' : 'novel',
      genres: category ? [category] : [],
    };
  }

  async function searchMebMarket(context) {
    const country = String(context.country || '').toLowerCase();
    if (!/thailand/.test(country)) return null;

    const queries = buildOriginalWorkSearchQueries(context, { includeGenericEnglish: false })
      .filter((query) => /[^\u0000-\u007f]/.test(query) || !isGenericOriginalWorkTitle(query))
      .slice(0, getOriginalWorkSearchLimit('mebmarket'));

    let best = null;
    for (const queryText of queries) {
      const payload = {
        token: '',
        filter: { type: 'all', value: queryText },
        sort: { by: 'date', type: 'desc' },
        exact_keyword: '',
        price: 'all',
        is_mag: '',
        category_id: '',
        series_id: '',
        from_book_price: '',
        bundle_type: '',
        to_book_price: '',
        result_per_page: 8,
        page_no: 1,
        app_id: 'ASK',
        app_platform: 'WEB',
        content_type_list: null,
        debug_elastic: 1,
        category_group_id: '',
        book_language_id: '',
        rating_count: '',
        book_rating: '',
      };
      const form = new URLSearchParams();
      form.set('api', 'Store');
      form.set('method', 'userSearchBooks2');
      form.set('data', JSON.stringify(payload));

      const response = await requestExternal({
        method: 'POST',
        url: 'https://www.mebmarket.com/ajax.php',
        headers: {
          Accept: 'application/json, text/plain, */*',
          'Content-Type': 'application/x-www-form-urlencoded; charset=UTF-8',
        },
        data: form.toString(),
        timeout: 6000,
      }).catch(() => null);

      if (!response || response.status < 200 || response.status >= 300) continue;
      const payloadJson = safeJsonParse(response.responseText, null);
      const list = Array.isArray(payloadJson?.data?.book_list)
        ? payloadJson.data.book_list.map(normalizeMebMarketEntry).filter((entry) => entry?.title)
        : [];
      const winner = pickBestCandidate(list, context);
      if (winner && (!best || winner._score > best._score)) best = winner;
      if (best && best._score >= 120) break;
    }

    return best ? stripInternalScore(best) : null;
  }


  function getNovelUpdatesMetaText(doc, label) {
    const normalizedLabel = String(label || '').toLowerCase();
    const item = qa('.seriesother, .seriesgenre, .seriesstatus, .seriesna, .genre', doc).find((node) => {
      const value = collapseWhitespace(text(node)).toLowerCase();
      return value.startsWith(normalizedLabel) || value.includes(`${normalizedLabel}:`);
    });
    return item ? collapseWhitespace(text(item).replace(new RegExp(`^${label}\\s*:?\\s*`, 'i'), '')) : '';
  }

  function normalizeNovelUpdatesEntry(doc, url) {
    const title = collapseWhitespace(text(q('.seriestitlenu, h1.entry-title, h1', doc)) || String(doc.title || '').replace(/\s*-\s*Novel Updates.*$/i, ''));
    if (!title) return null;

    const associatedNames = collapseWhitespace(text(q('#editassociated, .seriesother', doc)));
    const synonyms = associatedNames
      ? associatedNames.split(/\n|;|\||,/).map(collapseWhitespace).filter(Boolean)
      : [];
    const author = collapseWhitespace(text(q('#showauthors, a[href*="/nauthor/"]', doc)));
    const image = q('.seriesimg img, img[src*="novelupdates"]', doc)?.getAttribute('src') || '';
    const descriptionText = collapseWhitespace(text(q('#editdescription, .seriesdesc, .entry-content', doc)));
    const year = String(descriptionText || '').match(/\b(19|20)\d{2}\b/)?.[0] || '';

    return {
      provider: 'NovelUpdates',
      title,
      titleEnglish: '',
      titleNative: synonyms.find((item) => /[^\u0000-\u007f]/.test(item)) || '',
      synonyms,
      description: collapseWhitespace([
        year ? `Year: ${year}` : '',
        'Type: Novel',
        author ? `Author: ${author}` : '',
        'Source: NovelUpdates',
      ].filter(Boolean).join('\n')),
      url,
      image,
      year,
      score: '',
      scoreLabel: 'NovelUpdates',
      lengthLabel: '',
      kind: 'novel',
      genres: [],
    };
  }

  async function searchNovelUpdates(context) {
    let best = null;

    for (const url of buildNovelUpdatesUrls(context)) {
      const response = await requestExternal({
        url,
        headers: { Accept: 'text/html' },
        timeout: 5000,
      }).catch(() => null);

      if (!response || response.status < 200 || response.status >= 300) continue;
      const html = response.responseText || '';
      if (!html || /Just a moment|Cloudflare|Checking your browser/i.test(html)) continue;

      const doc = new DOMParser().parseFromString(html, 'text/html');
      const entry = normalizeNovelUpdatesEntry(doc, url);
      if (!entry?.title) continue;

      const winner = pickBestCandidate([entry], context);
      if (winner && (!best || winner._score > best._score)) best = winner;
      if (best && best._score >= 120) break;
    }

    return best ? stripInternalScore(best) : null;
  }

  function buildNamuWikiUrls(context) {
    const titles = [
      context.pageNativeTitle,
      context.nativeTitle,
      ...(Array.isArray(context.aliases) ? context.aliases : []),
      context.sourceTitle,
      context.mdlTitle,
    ].map(collapseWhitespace).filter(Boolean);

    return [...new Set(titles.slice(0, 5).map((title) => `https://en.namu.wiki/w/${encodeURIComponent(title)}`))];
  }

  async function searchNamuWikiOriginalWork(context) {
    const country = String(context.country || '').toLowerCase();
    if (!/south korea|korea/.test(country)) return null;
    if (!context?.hasOriginalWorkHint) return null;

    for (const url of buildNamuWikiUrls(context)) {
      const response = await requestExternal({
        url,
        headers: { Accept: 'text/html' },
        timeout: 5000,
      }).catch(() => null);

      if (!response || response.status < 200 || response.status >= 300) continue;
      const doc = new DOMParser().parseFromString(response.responseText || '', 'text/html');
      const bodyText = collapseWhitespace(text(doc.body));
      if (!/original work|based on|adapted from/i.test(bodyText)) continue;

      const data = buildOriginalWorkFromText(bodyText, context, 'NamuWiki', url);
      if (data && scoreCandidate(data, context) >= 95) return data;
    }

    return null;
  }

  function cleanOriginalWorkPhrase(value) {
    return collapseWhitespace(String(value || '')
      .replace(/<[^>]+>/g, ' ')
      .replace(/\[[^\]]+\]/g, ' ')
      .replace(/\s+(?:Director|Screenwriter|Genres?|Tags?|Related Content|Cast|Synopsis|Notes?|External Links)\b.*$/i, '')
      .replace(/\s+(?:starring|directed by|written by|aired on|broadcast on)\b.*$/i, '')
      .replace(/^\s*(?:the\s+)?(?:original\s+)?(?:novel|web\s+novel|light\s+novel|webtoon|webcomic|web\s+comic|manga|manhwa|manhua|comic|book)\s*[:\-]?\s*/i, '')
      .replace(/^["'“”]+|["'“”]+$/g, ''));
  }

  function parseOriginalWorkTitleDetails(value, fallbackType = '') {
    let phrase = cleanOriginalWorkPhrase(value);
    if (!phrase) return null;

    let author = '';
    const authorMatch = phrase.match(/\s+by\s+([^.;|]+)$/i);
    if (authorMatch?.[1]) {
      author = collapseWhitespace(authorMatch[1]);
      phrase = collapseWhitespace(phrase.slice(0, authorMatch.index));
    }

    let titleNative = '';
    const nativeMatch = phrase.match(/\(([^)]*[^\u0000-\u007f][^)]*)\)/);
    if (nativeMatch?.[1]) {
      titleNative = collapseWhitespace(nativeMatch[1]);
      phrase = collapseWhitespace(phrase.replace(nativeMatch[0], ''));
    }

    const type = extractOriginalWorkSourceTypeFromText(`${fallbackType} ${value}`) || fallbackType;
    const title = collapseWhitespace(phrase.replace(/^["'“”]+|["'“”]+$/g, ''));
    if (!title || /^by$/i.test(title)) return null;
    if (/^(?:a|an|the)?\s*(?:novel|web\s+novel|light\s+novel|manga|webtoon|webcomic|web\s+comic|manhwa|manhua|comic|book)$/i.test(title)) return null;

    return {
      title,
      titleNative,
      author,
      type,
    };
  }

  function toTitleCaseLabel(value) {
    return collapseWhitespace(value)
      .replace(/_/g, ' ')
      .replace(/\b\w/g, (char) => char.toUpperCase());
  }

  function buildOriginalWorkFromContext(context) {
    if (!context?.hasExplicitSourceTitle || !collapseWhitespace(context.sourceTitle)) return null;

    const typeLabel = toTitleCaseLabel(context.sourceType || 'Original Work');
    const originalTitle = context.nativeTitle && context.nativeTitle !== context.sourceTitle
      ? `Title: ${context.nativeTitle}`
      : '';
    const description = [
      originalTitle,
      context.year ? `Year: ${context.year}` : '',
      typeLabel ? `Type: ${typeLabel}` : '',
      context.sourceAuthor ? `Author: ${context.sourceAuthor}` : '',
      'Source: MyDramaList',
    ].filter(Boolean).join('\n');

    return {
      provider: 'MyDramaList',
      title: context.sourceTitle,
      titleEnglish: '',
      titleNative: context.nativeTitle && context.nativeTitle !== context.sourceTitle ? context.nativeTitle : '',
      synonyms: context.nativeTitle ? [context.nativeTitle] : [],
      description,
      url: '',
      image: '',
      year: '',
      score: '',
      scoreLabel: '',
      lengthLabel: '',
      kind: context.sourceType || 'novel',
      genres: [],
    };
  }

  function getKnownOriginalWorkOverride(context) {
    const titles = [
      context?.mdlTitle,
      context?.sourceTitle,
      context?.nativeTitle,
      context?.pageNativeTitle,
      ...(Array.isArray(context?.aliases) ? context.aliases : []),
    ].map(normalizeTitle).filter(Boolean);
    const country = String(context?.country || '').toLowerCase();

    if (/south korea|korea/.test(country) && titles.some((title) => title === 'goodbye mr black' || title === 'good bye mr black')) {
      return {
        provider: 'Known Override',
        title: 'Goodbye Mr. Black',
        titleEnglish: '',
        titleNative: context?.pageNativeTitle || context?.nativeTitle || '',
        synonyms: ['Good-bye, Mr. Black'],
        description: [
          'Year: 1983',
          'Type: Manhwa',
          'Author: Hwang Mi Na',
          'Source: MangaUpdates',
        ].join('\n'),
        url: 'https://www.mangaupdates.com/series/c9isifh/goodbye-mr-black',
        image: 'https://cdn.mangaupdates.com/image/i396061.jpg',
        year: '1983',
        score: '',
        scoreLabel: 'MangaUpdates',
        lengthLabel: 'Manhwa',
        kind: 'manhwa',
        genres: [],
      };
    }

    if (/china|taiwan/.test(country) && titles.some((title) => title === 'chinese paladin' || title === 'xianjian qixia zhuan' || title === 'the legend of sword and fairy' || title === '?????' || title === '?????')) {
      return {
        provider: 'MyAnimeList',
        title: 'Chinese Paladin',
        titleEnglish: '',
        titleNative: context?.pageNativeTitle || context?.nativeTitle || '?????',
        synonyms: ['?????', '?????'],
        description: [
          'Type: Manhua',
          'Volume: 8',
          'Source: MyAnimeList',
        ].join('\n'),
        url: 'https://myanimelist.net/manga/14735/Chinese_Paladin',
        image: 'https://myanimelist.net/images/manga/2/21259l.jpg',
        year: '',
        score: '',
        scoreLabel: 'MyAnimeList',
        lengthLabel: 'Manhua',
        kind: 'manhua',
        genres: [],
      };
    }
    if (/south korea|korea/.test(country) && titles.some((title) => title === 'the story of park s marriage contract' || title === 'the tale of park yeon woo' || title === 'the tale of the contract marriage of the yeolnyeo park clan' || title === 'yeolnyeoparkssi gyeyakgyeolhondyeon' || title === '???? ?????')) {
      return {
        provider: 'Naver Webtoon',
        title: "The Story of Park's Marriage Contract",
        titleEnglish: '',
        titleNative: '???? ?????',
        synonyms: ['The Tale of Park Yeon Woo', 'Yeolnyeoparkssi Gyeyakgyeolhondyeon', '???? ?????'],
        description: [
          'Year: 2020',
          'Type: Webtoon',
          'Author: Kim Neo UI, Angelique',
          'Source: Naver Webtoon',
        ].join('\n'),
        url: 'https://comic.naver.com/webtoon/list?titleId=761601',
        image: 'https://shared-comic.pstatic.net/thumb/webtoon/761601/thumbnail/thumbnail_IMAG21_f7b0c713-9fb3-4b84-a266-448aebffeb53.jpg',
        year: '2020',
        score: '',
        scoreLabel: 'Naver Webtoon',
        lengthLabel: 'Webtoon',
        kind: 'webtoon',
        genres: [],
      };
    }
    if (/south korea|korea/.test(country) && titles.some((title) => title === 'love in the moonlight' || title === 'moonlight drawn by clouds' || title === 'gooreumi geurin dalbit' || title === '구르미 그린 달빛' || title === '??? ?? ??')) {
      return {
        provider: 'NovelUpdates',
        title: 'Moonlight Drawn by Clouds',
        titleEnglish: '',
        titleNative: '구르미 그린 달빛',
        synonyms: ['Love in the Moonlight', '구르미 그린 달빛', '??? ?? ??'],
        description: [
          'Year: 2013',
          'Type: Novel',
          'Author: Yoon Yi Soo',
          'Source: NovelUpdates',
        ].join('\n'),
        url: 'https://www.novelupdates.com/series/moonlight-drawn-by-clouds/',
        image: 'https://cdn.wuxiaworld.eu/original/Moonlight-Drawn-by-Clouds_eHr4x8G.jpg',
        year: '2013',
        score: '',
        scoreLabel: 'NovelUpdates',
        lengthLabel: 'Novel',
        kind: 'novel',
        genres: [],
      };
    }
    if (/thailand/.test(country) && titles.some((title) => title.includes('don t say no when hearts are close') || title === 'don t say no')) {
      return {
        provider: 'MyDramaList',
        title: "Don't Say No When Hearts Are Close",
        titleEnglish: '',
        titleNative: context?.nativeTitle || '',
        synonyms: context?.nativeTitle ? [context.nativeTitle] : [],
        description: [
          'Type: Novel',
          'Author: Mame',
          'Source: MyDramaList',
        ].join('\n'),
        url: '',
        image: '',
        year: '',
        score: '',
        scoreLabel: '',
        lengthLabel: 'Novel',
        kind: 'novel',
        genres: [],
      };
    }

    return null;
  }

  function buildOriginalWorkFromText(rawText, context, provider, url = '', image = '') {
    const clean = collapseWhitespace(rawText);
    if (!clean) return null;

    const patterns = [
      { type: '', pattern: /Original Writing:\s*(.{3,220})/i },
      { type: '', pattern: /Original (?:Work|Novel|Manga|Webtoon|Webcomic|Comic|Book):\s*(.{3,220})/i },
      { type: '', pattern: /Based on (?:the\s+)?(?:(novel|web\s+novel|light\s+novel|manga|webtoon|webcomic|web\s+comic|manhwa|manhua|comic|book)\s+)?["'“”]?([^"'“”.;]{2,160})["'“”]?(?:\s+by\s+([^.;]{2,90}))?/i },
      { type: '', pattern: /Adapted from (?:the\s+)?(?:(novel|web\s+novel|light\s+novel|manga|webtoon|webcomic|web\s+comic|manhwa|manhua|comic|book)\s+)?["'“”]?([^"'“”.;]{2,160})["'“”]?(?:\s+by\s+([^.;]{2,90}))?/i },
    ];

    for (const item of patterns) {
      const match = clean.match(item.pattern);
      if (!match) continue;

      const hasBasedType = /Based on|Adapted from/i.test(item.pattern.source) && match[2];
      const phrase = hasBasedType
        ? `${match[2]}${match[3] ? ` by ${match[3]}` : ''}`
        : match[1];
      const fallbackType = hasBasedType ? collapseWhitespace(match[1] || '') : context.sourceType;
      const parsed = parseOriginalWorkTitleDetails(phrase, fallbackType);
      if (!parsed?.title) continue;

      const description = [
        parsed.author ? `Author: ${parsed.author}` : '',
        provider ? `Source: ${provider}` : '',
      ].filter(Boolean).join('\n');

      return {
        provider,
        title: parsed.title,
        titleEnglish: '',
        titleNative: parsed.titleNative,
        synonyms: parsed.titleNative ? [parsed.titleNative] : [],
        description,
        url,
        image,
        year: '',
        score: '',
        scoreLabel: provider,
        lengthLabel: parsed.type ? parsed.type.replace(/\b\w/g, (char) => char.toUpperCase()) : '',
        kind: parsed.type || context.sourceType || 'novel',
        genres: [],
      };
    }

    return null;
  }

  function getTrustedOriginalWorkProviderOrder(context) {
    const country = String(context.country || '').toLowerCase();

    if (/thailand/.test(country)) return ORIGINAL_WORK_PROVIDER_ORDER.thai;

    if (/japan|south korea|korea|china/.test(country)) return ORIGINAL_WORK_PROVIDER_ORDER.eastAsia;

    return ORIGINAL_WORK_PROVIDER_ORDER.fallback;
  }

  function getOriginalWorkProviderOrder(context) {
    if (!context?.hasOriginalWorkHint) return [];
    return getTrustedOriginalWorkProviderOrder(context);
  }

  function enrichOriginalWorkNativeTitle(entry, context) {
    if (!isValidOriginalWork(entry)) return entry;
    if (isUsableOriginalWorkNativeTitle(entry.titleNative, entry.title || entry.titleEnglish)) return entry;

    const candidates = [
      context?.nativeTitle,
      context?.pageNativeTitle,
      context?.sourceTitle,
      ...(Array.isArray(context?.aliases) ? context.aliases : []),
    ];
    const nativeTitle = candidates
      .map(collapseWhitespace)
      .find((item) => isUsableOriginalWorkNativeTitle(item, entry.title || entry.titleEnglish));

    return nativeTitle
      ? {
          ...entry,
          titleNative: nativeTitle,
          synonyms: [...new Set([...(Array.isArray(entry.synonyms) ? entry.synonyms : []), nativeTitle].filter(Boolean))],
        }
      : entry;
  }

  async function searchOriginalWorkProvider(provider, context) {
    if (provider === 'myanimelist') return searchMyAnimeList(context);
    if (provider === 'anilist') return searchAniList(context);
    if (provider === 'mangaupdates') return searchMangaUpdates(context);
    if (provider === 'naiin') return searchNaiin(context);
    if (provider === 'mebmarket') return searchMebMarket(context);
    if (provider === 'novelupdates') return searchNovelUpdates(context);
    if (provider === 'namuwiki') return searchNamuWikiOriginalWork(context);
    return null;
  }

  function pickBestCandidate(entries, context) {
    let best = null;

    entries.forEach((entry) => {
      const score = scoreCandidate(entry, context);
      if (!best || score > best._score) {
        best = { ...entry, _score: score };
      }
    });

    if (!best || best._score < 95) return null;
    return best;
  }

  function stripInternalScore(entry) {
    const { _score, ...clean } = entry;
    return clean;
  }

  function buildPortalRenderKey(links) {
    return JSON.stringify(links.map((link) => ({
      name: link.name,
      url: link.url,
    })));
  }

  function getFaviconUrl(url) {
    return `https://www.google.com/s2/favicons?domain=${encodeURIComponent(url)}&sz=64`;
  }

  function getPortalIconUrl(link) {
    if (link?.name === 'SIMKL') return 'https://simkl.com/favicon.ico';
    return getFaviconUrl(link?.url || '');
  }

  function getPortalNameFromUrl(url) {
    const value = String(url || '');
    if (/imdb\.com/i.test(value)) return 'IMDb';
    if (/themoviedb\.org|tmdb\.org/i.test(value)) return 'TMDb';
    if (/simkl\.com/i.test(value)) return 'SIMKL';
    if (/asianwiki\.com/i.test(value)) return 'AsianWiki';
    return '';
  }

  function collectNativePortalLinks() {
    const linkMap = new Map();
    getTitlePosterActionMounts().forEach((mount) => {
      qa('a[href]', mount).forEach((anchor) => {
        const url = createAbsoluteUrl(anchor.getAttribute('href') || '');
        const name = getPortalNameFromUrl(url);
        if (name && url) linkMap.set(name, url);
      });
    });
    return ['IMDb', 'TMDb', 'SIMKL', 'AsianWiki']
      .filter((name) => linkMap.has(name))
      .map((name) => ({ name, url: linkMap.get(name) }));
  }

  function isNativePortalAnchor(anchor) {
    if (!anchor || anchor.closest?.(`#${PORTALS_BOX_ID}`)) return false;
    return !!getPortalNameFromUrl(createAbsoluteUrl(anchor.getAttribute?.('href') || ''));
  }

  function findNativePortalBlocks(root = document) {
    const blocks = new Set();
    qa('a[href]', root).forEach((anchor) => {
      if (!isNativePortalAnchor(anchor)) return;
      let block = anchor.parentElement;
      while (block && block !== root.parentElement) {
        const portalCount = qa('a[href]', block).filter(isNativePortalAnchor).length;
        if (portalCount >= 2) break;
        if (block === root) break;
        block = block.parentElement;
      }
      blocks.add(block || anchor);
    });
    return Array.from(blocks).filter(Boolean);
  }

  function addPortalSearchFallbackLinks(linkMap, context) {
    if (!linkMap || linkMap.size) return;
    const query = collapseWhitespace(context?.title || context?.baseTitle || '');
    if (!query) return;
    const encoded = encodeURIComponent(query);
    linkMap.set('IMDb', `https://www.imdb.com/find/?q=${encoded}`);
    linkMap.set('TMDb', `https://www.themoviedb.org/search?query=${encoded}`);
    linkMap.set('SIMKL', `https://simkl.com/search/?q=${encoded}`);
  }

  async function tmdbSearchPortalLinks(context) {
    const searchType = context.kind === 'movie' ? 'movie' : context.kind === 'tv' ? 'tv' : 'multi';
    const searchTitles = buildTmdbSearchQueries(context);
    const seenResults = new Set();
    const candidates = [];

    for (const queryTitle of searchTitles) {
      const params = new URLSearchParams({
        api_key: TMDB_API_KEY,
        query: queryTitle,
      });

      if (searchType === 'movie' && context.year) params.set('year', context.year);

      const response = await requestExternal({
        url: `${TMDB_API_URL}/search/${searchType}?${params.toString()}`,
        headers: { Accept: 'application/json' },
      }).catch(() => null);

      if (!response || response.status < 200 || response.status >= 300) continue;
      const payload = safeJsonParse(response.responseText, null);
      const results = Array.isArray(payload?.results) ? payload.results.filter((item) => !(item?.genre_ids || []).includes(16)) : [];

      results.forEach((item) => {
        const itemType = searchType === 'multi' ? String(item?.media_type || '').toLowerCase() : searchType;
        if (!['movie', 'tv'].includes(itemType)) return;
        const dedupeKey = `${itemType}:${item.id}`;
        if (seenResults.has(dedupeKey)) return;
        seenResults.add(dedupeKey);
        candidates.push({
          item,
          itemType,
          score: scoreTmdbResult({ ...item, media_type: itemType }, context, queryTitle),
        });
      });
    }

    if (!candidates.length) return null;
    candidates.sort((left, right) => right.score - left.score);

    const topCandidate = candidates[0];
    if (!topCandidate || topCandidate.score < 80) return null;

    const top = topCandidate.item;
    const tmdbType = searchType === 'multi' ? String(top.media_type || '').toLowerCase() : searchType;
    if (!['movie', 'tv'].includes(tmdbType)) return null;

    const links = [];
    const tmdbUrl = `https://www.themoviedb.org/${tmdbType}/${top.id}`;
    links.push({ name: 'TheMovieDB', url: tmdbUrl });

    const externalResponse = await requestExternal({
      url: `${TMDB_API_URL}/${tmdbType}/${top.id}/external_ids?api_key=${TMDB_API_KEY}`,
      headers: { Accept: 'application/json' },
    }).catch(() => null);

    const externalIds = externalResponse && externalResponse.status >= 200 && externalResponse.status < 300
      ? safeJsonParse(externalResponse.responseText, {})
      : {};

    if (externalIds?.imdb_id) {
      links.push({ name: 'IMDb', url: `https://www.imdb.com/title/${externalIds.imdb_id}` });
    }

    if (externalIds?.tvdb_id) {
      const tvdbUrl = tmdbType === 'movie'
        ? `https://www.thetvdb.com/movie/${externalIds.tvdb_id}`
        : `https://thetvdb.com/?tab=series&id=${externalIds.tvdb_id}`;
      links.push({ name: 'TVDB', url: tvdbUrl });
    }

    links.push({ name: 'TMDb', url: tmdbUrl });

    const simklUrl = buildSimklSearchUrl({
      tmdbId: top.id,
      tmdbType,
      imdbId: externalIds?.imdb_id || '',
      tvdbId: externalIds?.tvdb_id || '',
    });
    if (simklUrl) links.push({ name: 'SIMKL', url: simklUrl });

    return {
      tmdbId: top.id,
      tmdbType,
      tmdbUrl,
      voteAverage: top.vote_average ?? '',
      voteCount: top.vote_count ?? '',
      externalIds,
      links,
    };
  }

  async function resolveTmdbData(context) {
    const cacheKey = JSON.stringify(context);
    if (tmdbLookupCache.has(cacheKey)) return tmdbLookupCache.get(cacheKey);

    const promise = tmdbSearchPortalLinks(context).catch(() => null);
    tmdbLookupCache.set(cacheKey, promise);
    const result = await promise;
    tmdbLookupCache.set(cacheKey, result);
    return result;
  }

  function buildSimklSearchUrl({ tmdbId, tmdbType, imdbId, tvdbId }) {
    const type = tmdbType === 'movie' ? 'movies' : 'tv';
    const lookupUrl = imdbId
      ? `https://www.imdb.com/title/${imdbId}/`
      : tvdbId
        ? (tmdbType === 'movie'
            ? `https://www.thetvdb.com/movie/${tvdbId}`
            : `https://thetvdb.com/?tab=series&id=${tvdbId}`)
        : `https://www.themoviedb.org/${tmdbType === 'movie' ? 'movie' : 'tv'}/${tmdbId}`;

    return `https://simkl.com/search/?type=${type}&q=${encodeURIComponent(lookupUrl)}`;
  }

  function scoreAsianWikiCandidate(anchor, context) {
    const href = anchor?.getAttribute('href') || '';
    if (!href || /Special:|File:|Category:/i.test(href)) return -1;

    const linkText = collapseWhitespace(text(anchor));
    const hrefName = collapseWhitespace(decodeURIComponent(href.split('/').pop() || '').replace(/_/g, ' '));
    const normalizedText = normalizeTitle(linkText);
    const normalizedHref = normalizeTitle(stripPortalSubtitle(hrefName));
    const baseTitle = normalizeTitle(context.baseTitle || context.title);
    const baseNativeTitle = normalizeTitle(context.baseNativeTitle || context.nativeTitle);
    const fullTitle = normalizeTitle(context.title);
    const nativeTitle = normalizeTitle(context.nativeTitle);

    let score = 0;
    if (baseTitle && (normalizedText === baseTitle || normalizedHref === baseTitle)) score += 180;
    if (baseNativeTitle && (normalizedText === baseNativeTitle || normalizedHref === baseNativeTitle)) score += 150;
    if (fullTitle && normalizedText === fullTitle) score += 90;
    if (nativeTitle && normalizedText === nativeTitle) score += 70;
    if (baseTitle && (normalizedText.includes(baseTitle) || normalizedHref.includes(baseTitle))) score += 40;
    if (baseNativeTitle && (normalizedText.includes(baseNativeTitle) || normalizedHref.includes(baseNativeTitle))) score += 25;
    if (context.hasSplitMarker && /\b(actor|actress|director|writer)\b/i.test(linkText)) score -= 100;
    return score;
  }

  async function resolveAsianWikiUrl(queryTitles, context) {
    for (const slug of buildAsianWikiSlugCandidates(context)) {
      const directUrl = `https://asianwiki.com/${slug}`;
      const directResponse = await requestExternal({ url: directUrl }).catch(() => null);
      if (!directResponse || directResponse.status < 200 || directResponse.status >= 300) continue;

      const directDoc = new DOMParser().parseFromString(directResponse.responseText, 'text/html');
      const pageTitle = collapseWhitespace(text(directDoc.querySelector('#content h1, #firstHeading, h1')));
      const baseTitle = normalizeTitle(context.baseTitle || context.title);
      const baseNativeTitle = normalizeTitle(context.baseNativeTitle || context.nativeTitle);
      const normalizedPageTitle = normalizeTitle(stripPortalSubtitle(pageTitle));
      if (
        (baseTitle && (normalizedPageTitle === baseTitle || normalizedPageTitle.includes(baseTitle)))
        || (baseNativeTitle && (normalizedPageTitle === baseNativeTitle || normalizedPageTitle.includes(baseNativeTitle)))
      ) {
        return directUrl;
      }
    }

    for (const queryTitle of (Array.isArray(queryTitles) ? queryTitles : [queryTitles]).filter(Boolean)) {
      const searchUrl = `https://asianwiki.com/index.php?title=Special%253ASearch&search=${encodeURIComponent(queryTitle)}`;
      const response = await requestExternal({ url: searchUrl }).catch(() => null);
      if (!response || response.status < 200 || response.status >= 300) continue;

      const doc = new DOMParser().parseFromString(response.responseText, 'text/html');
      const matches = Array.from(doc.querySelectorAll('.searchresults a'));
      if (!matches.length) continue;
      const ranked = matches
        .map((anchor) => ({ anchor, score: scoreAsianWikiCandidate(anchor, context) }))
        .filter((item) => item.score >= 80)
        .sort((left, right) => right.score - left.score);
      if (!ranked.length) continue;
      return createAbsoluteUrl(`https://asianwiki.com${ranked[0].anchor.getAttribute('href')}`);
    }
    return '';
  }

  async function resolvePortalLinks(context) {
    const cacheKey = JSON.stringify(context);
    if (portalLinksCache.has(cacheKey)) return portalLinksCache.get(cacheKey);

    if (hasPersistedCacheEntry(STORAGE_PORTAL_LINKS, cacheKey)) {
      const persisted = getPersistedCacheEntry(STORAGE_PORTAL_LINKS, cacheKey, (value) => Array.isArray(value) && value.every((item) => item && typeof item.name === 'string' && typeof item.url === 'string'));
      portalLinksCache.set(cacheKey, persisted);
      return Array.isArray(persisted) ? persisted : [];
    }

    const promise = (async () => {
      const tmdbData = await resolveTmdbData(context);
      const linkMap = new Map();
      collectNativePortalLinks().forEach((link) => {
        if (link?.name && link?.url) linkMap.set(link.name, link.url);
      });
      (tmdbData?.links || []).forEach((link) => {
        if (link?.name && link?.url && !linkMap.has(link.name)) linkMap.set(link.name, link.url);
      });
      const asianWikiUrl = await resolveAsianWikiUrl(buildAsianWikiSearchQueries(context), context).catch(() => '');
      if (asianWikiUrl && !linkMap.has('AsianWiki')) linkMap.set('AsianWiki', asianWikiUrl);
      addPortalSearchFallbackLinks(linkMap, context);

      const orderedNames = ['IMDb', 'TMDb', 'SIMKL', 'AsianWiki'];
      return orderedNames
        .filter((name) => linkMap.has(name))
        .map((name) => ({ name, url: linkMap.get(name) }));
    })();

    portalLinksCache.set(cacheKey, promise);
    const result = await promise;
    persistCacheEntry(STORAGE_PORTAL_LINKS, cacheKey, Array.isArray(result) ? result : [], PORTAL_LINKS_TTL_MS);
    portalLinksCache.set(cacheKey, result);
    return result;
  }

  function ensurePortalLinksContainer() {
    let container = q(`#${PORTALS_BOX_ID}`);
    const mount = getPosterLinksMount();

    if (mount && container && (!mount.contains(container) || container.classList.contains(`${NS}-portal-fallback-fixed`))) {
      container.remove();
      container = null;
    }
    if (container) return container;

    container = document.createElement('div');
    container.id = PORTALS_BOX_ID;

    if (mount) {
      const insertion = findPortalInsertionPoint(mount);
      if (insertion?.parent) {
        insertion.parent.insertBefore(container, insertion.before || null);
      } else {
        mount.appendChild(container);
      }
    } else {
      container.classList.add(`${NS}-portal-fallback-fixed`);
      document.body.appendChild(container);
    }

    return container;
  }

  function setNativeActionHidden(node, hidden) {
    if (!node) return;
    node.classList.toggle(`${NS}-native-action-hidden`, !!hidden);
  }

  function isNativeSocialAnchor(anchor) {
    const raw = [
      anchor?.getAttribute?.('href') || '',
      anchor?.getAttribute?.('title') || '',
      anchor?.getAttribute?.('aria-label') || '',
      anchor?.className || '',
      text(anchor),
    ].join(' ');
    return /facebook|twitter|x\.com|reddit|pinterest|weibo|tumblr|share/i.test(raw);
  }

  function findNativeSocialBlocks(root = document) {
    const blocks = new Set();
    qa('a[href], button, [role="button"]', root).forEach((node) => {
      if (!isNativeSocialAnchor(node)) return;
      let block = node.closest('.share-container, .share-buttons, .social-share, .box-body > div, .film-cover + div');
      if (!block) {
        let current = node.parentElement;
        while (current && current !== root.parentElement) {
          const socialCount = qa('a[href], button, [role="button"]', current)
            .filter(isNativeSocialAnchor)
            .length;
          if (socialCount >= 2 || /share|social|sns/i.test(String(current.className || ''))) {
            block = current;
            break;
          }
          if (current === root) break;
          current = current.parentElement;
        }
      }
      blocks.add(block || node);
    });
    qa('.share-container, .share-buttons, .social-share', root).forEach((node) => blocks.add(node));
    return Array.from(blocks).filter(Boolean);
  }

  function initPeopleNativeActionToggles() {
    if (!isPeoplePage()) return;
    const profileBox = findProfileBox();
    if (!profileBox) return;
    const hidden = !isFeatureEnabled('nativeSnsIcons');
    const share = findShareContainer(profileBox);
    setNativeActionHidden(share, hidden);
  }

  function findTitleNativeActionNodes(pattern) {
    return getTitlePosterActionMounts().flatMap((mount) => qa('a, button, [role="button"]', mount).filter((node) => {
        const raw = [
          text(node),
          node.getAttribute('title') || '',
          node.getAttribute('aria-label') || '',
          node.getAttribute('href') || '',
        ].join(' ');
        return pattern.test(raw);
      }));
  }

  function initTitleNativeActionToggles() {
    if (!isTitlePage()) return;
    const hideSns = !isFeatureEnabled('nativeSnsIcons');
    const hideNativePortals = !isTitleDetailsTabActive();
    getTitlePosterActionMounts().forEach((mount) => {
      findNativeSocialBlocks(mount).forEach((node) => setNativeActionHidden(node, hideSns));
      findNativePortalBlocks(mount).forEach((node) => setNativeActionHidden(node, hideNativePortals));
    });
    findTitleNativeActionNodes(/watch\s+trailer|trailer/i)
      .forEach((node) => setNativeActionHidden(node, !isFeatureEnabled('titleTrailerButton')));
    findTitleNativeActionNodes(/buy\s+on\s+amazon|amazon/i)
      .forEach((node) => setNativeActionHidden(node, !isFeatureEnabled('titleAmazonButton')));
  }

  function renderPortalLinks(links) {
    const container = ensurePortalLinksContainer();
    if (!container) return;

    if (!Array.isArray(links) || !links.length) {
      container.remove();
      lastPortalRenderKey = '';
      return;
    }

    const renderKey = buildPortalRenderKey(links);
    if (container.dataset.renderKey === renderKey && lastPortalRenderKey === renderKey) return;

    container.innerHTML = '';

    links.forEach((link) => {
      const anchor = document.createElement('a');
      anchor.className = `${NS}-portal-link`;
      anchor.href = link.url;
      anchor.target = '_blank';
      anchor.rel = 'noopener noreferrer';
      anchor.title = link.name;
      anchor.setAttribute('aria-label', link.name);

      const icon = document.createElement('img');
      icon.className = `${NS}-portal-icon`;
      icon.src = getPortalIconUrl(link);
      icon.alt = link.name;
      icon.loading = 'lazy';

      anchor.appendChild(icon);
      container.appendChild(anchor);
    });

    container.dataset.renderKey = renderKey;
    lastPortalRenderKey = renderKey;
  }

  async function resolveOriginalWork(context) {
    const cacheKey = JSON.stringify(context);
    if (originalWorkCache.has(cacheKey)) return originalWorkCache.get(cacheKey);

    if (hasPersistedCacheEntry(STORAGE_ORIGINAL_WORK, cacheKey)) {
      const persisted = getPersistedCacheEntry(STORAGE_ORIGINAL_WORK, cacheKey, (value) => value === null || isValidOriginalWork(value));
      originalWorkCache.set(cacheKey, persisted);
      return persisted;
    }

    const promise = (async () => {
      const contextFallback = buildOriginalWorkFromContext(context);
      const knownOverride = getKnownOriginalWorkOverride(context);
      if (knownOverride && (knownOverride.provider !== 'MyDramaList' || knownOverride.url || knownOverride.image)) return enrichOriginalWorkNativeTitle(knownOverride, context);

      for (const provider of getOriginalWorkProviderOrder(context)) {
        const result = await searchOriginalWorkProvider(provider, context).catch(() => null);
        if (!isValidOriginalWork(result)) continue;
        return enrichOriginalWorkNativeTitle(result, context);
      }

      const fallback = enrichOriginalWorkNativeTitle(contextFallback, context);
      if (isValidOriginalWork(fallback)) return fallback;

      return null;
    })();

    originalWorkCache.set(cacheKey, promise);
    const result = await promise;
    persistCacheEntry(STORAGE_ORIGINAL_WORK, cacheKey, isValidOriginalWork(result) ? result : null, ORIGINAL_WORK_TTL_MS);
    originalWorkCache.set(cacheKey, result);
    return result;
  }

  function findSidebarBoxes() {
    return qa('.col-xl-4 .box, .col-lg-4 .box, .col-md-4 .box, .col-sm-4 .box, .col-xl-3 .box, .col-lg-3 .box, .col-md-3 .box, .col-sm-3 .box, .sidebar .box, .side-content .box, aside .box')
      .filter((box) => q('.box-header, .box-title, h1, h2, h3, h4', box));
  }

  function findBoxByHeading(pattern) {
    return findSidebarBoxes().find((box) => {
      const heading = q('.box-header, .box-title, h1, h2, h3, h4', box);
      return pattern.test(text(heading));
    }) || null;
  }

  function findMainBoxes() {
    return qa('.box').filter((box) => {
      const heading = q('.box-header, .box-title, h1, h2, h3, h4', box);
      if (!heading) return false;
      return !box.closest('.col-lg-4, .col-md-4, .col-sm-4, .sidebar, .side-content');
    });
  }

  function findMainBoxByHeading(pattern) {
    return findMainBoxes().find((box) => {
      const heading = q('.box-header, .box-title, h1, h2, h3, h4', box);
      return pattern.test(text(heading));
    }) || null;
  }

  function ensureOriginalWorkBoxShell() {
    let box = q(`#${ORIGINAL_WORK_BOX_ID}`);
    if (box) return box;

    const statisticsBox = findBoxByHeading(/^statistics$/i);
    const contributorsBox = findBoxByHeading(/^top contributors$/i);
    if (!statisticsBox || !contributorsBox || !contributorsBox.parentElement) return null;

    box = document.createElement('div');
    box.id = ORIGINAL_WORK_BOX_ID;
    box.className = statisticsBox.className;
    box.innerHTML = `
      <div class="${q('.box-header', statisticsBox)?.className || 'box-header'}">Check out the original work</div>
      <div class="${q('.box-body', statisticsBox)?.className || 'box-body'}"></div>
    `;

    contributorsBox.parentElement.insertBefore(box, contributorsBox);
    return box;
  }

  function ensureFriendsBoxShell() {
    let box = q(`#${FRIENDS_BOX_ID}`);
    if (box) return box;

    const originalWorkBox = q(`#${ORIGINAL_WORK_BOX_ID}`) || findBoxByHeading(/^check out the original work$/i);
    const statisticsBox = findBoxByHeading(/^statistics$/i);
    const contributorsBox = findBoxByHeading(/^top contributors$/i);
    const anchorParent = contributorsBox?.parentElement || originalWorkBox?.parentElement;
    if (!anchorParent || !contributorsBox) return null;

    const headerClassSource = q('.box-header', statisticsBox || originalWorkBox || contributorsBox)?.className || 'box-header';
    const normalizedHeaderClass = headerClassSource.includes('primary')
      ? headerClassSource
      : `${headerClassSource} primary`;

    box = document.createElement('div');
    box.id = FRIENDS_BOX_ID;
    box.className = contributorsBox.className;
    box.innerHTML = `
      <div class="${normalizedHeaderClass}">Rated by Friends</div>
      <div class="${q('.box-body', contributorsBox)?.className || 'box-body'}"></div>
    `;

    anchorParent.insertBefore(box, contributorsBox);
    return box;
  }

  function ensureWatchedFriendsBoxShell() {
    let box = q(`#${WATCHED_FRIENDS_BOX_ID}`);
    if (box) {
      const friendsBox = q(`#${FRIENDS_BOX_ID}`) || findBoxByHeading(/^(friends rating|rated by friends)$/i);
      if (friendsBox?.parentElement === box.parentElement && friendsBox.nextElementSibling !== box) {
        friendsBox.insertAdjacentElement('afterend', box);
      }
      return box;
    }

    const friendsBox = q(`#${FRIENDS_BOX_ID}`) || findBoxByHeading(/^(friends rating|rated by friends)$/i);
    const originalWorkBox = q(`#${ORIGINAL_WORK_BOX_ID}`) || findBoxByHeading(/^check out the original work$/i);
    const contributorsBox = findBoxByHeading(/^top contributors$/i);
    const anchorParent = contributorsBox?.parentElement || friendsBox?.parentElement || originalWorkBox?.parentElement;
    if (!anchorParent || !contributorsBox) return null;

    const headerClassSource = q('.box-header', friendsBox || originalWorkBox || contributorsBox)?.className || 'box-header';
    const normalizedHeaderClass = headerClassSource.includes('primary')
      ? headerClassSource
      : `${headerClassSource} primary`;

    box = document.createElement('div');
    box.id = WATCHED_FRIENDS_BOX_ID;
    box.className = contributorsBox.className;
    box.innerHTML = `
      <div class="${normalizedHeaderClass}">Watched by Friends</div>
      <div class="${q('.box-body', contributorsBox)?.className || 'box-body'}"></div>
    `;

    if (friendsBox?.parentElement === anchorParent) {
      friendsBox.insertAdjacentElement('afterend', box);
    } else {
      anchorParent.insertBefore(box, contributorsBox);
    }
    return box;
  }

  function renderOriginalWorkCard(data) {
    const box = ensureOriginalWorkBoxShell();
    if (!box) return;

    const body = q('.box-body', box) || box;
    const title = data.title || data.titleEnglish || data.titleNative;
    const description = buildOriginalWorkDetails(data, title);

    if (!title) {
      box.remove();
      lastOriginalWorkRenderKey = '';
      return;
    }

    const renderKey = buildOriginalWorkRenderKey(data);
    if (box.dataset.renderKey === renderKey && lastOriginalWorkRenderKey === renderKey) return;

    body.innerHTML = '';

    const card = document.createElement(data.url ? 'a' : 'div');
    card.className = `${NS}-ow-card`;
    if (data.url) {
      card.href = data.url;
      card.target = '_blank';
      card.rel = 'noopener noreferrer';
    }
    if (!data.image) card.classList.add(`${NS}-ow-card-text-only`);

    const content = document.createElement('span');
    content.className = `${NS}-ow-content`;

    const titleEl = document.createElement('span');
    titleEl.className = `${NS}-ow-title`;
    titleEl.textContent = title;
    content.appendChild(titleEl);

    if (description) {
      const descEl = document.createElement('span');
      descEl.className = `${NS}-ow-desc`;
      descEl.textContent = description;
      content.appendChild(descEl);
    }

    if (data.image) {
      const coverWrap = document.createElement('span');
      coverWrap.className = `${NS}-ow-cover-wrap`;
      const cover = document.createElement('img');
      cover.className = `${NS}-ow-cover`;
      cover.src = data.image;
      cover.alt = `${title} cover`;
      cover.loading = 'lazy';
      coverWrap.appendChild(cover);
      card.append(coverWrap);
    }

    card.append(content);
    body.appendChild(card);
    box.dataset.renderKey = renderKey;
    lastOriginalWorkRenderKey = renderKey;
  }

  async function initOriginalWorkBox() {
    if (!isTitlePage()) return;
    if (!isFeatureEnabled('titleOriginalWork')) {
      q(`#${ORIGINAL_WORK_BOX_ID}`)?.remove();
      lastOriginalWorkRenderKey = '';
      return;
    }

    const context = getTitlePageContext();
    if (!context?.sourceTitle) {
      q(`#${ORIGINAL_WORK_BOX_ID}`)?.remove();
      lastOriginalWorkRenderKey = '';
      return;
    }

    const data = await resolveOriginalWork(context).catch(() => null);
    if (!data) {
      q(`#${ORIGINAL_WORK_BOX_ID}`)?.remove();
      lastOriginalWorkRenderKey = '';
      return;
    }

    renderOriginalWorkCard(data);
  }

  function normalizeFriendUser(entry) {
    const username = collapseWhitespace(entry?.username || entry?.user_name || '');
    if (!username) return null;

    return {
      username,
      displayName: collapseWhitespace(entry?.display_name || entry?.name || entry?.username || ''),
      avatar: entry?.avatar_url || entry?.avatar || '',
    };
  }

  function getFriendDisplayLabel(entry) {
    return collapseWhitespace(entry?.displayName || entry?.username || '');
  }

  function isLikelyBadFriendLabel(value) {
    const normalized = collapseWhitespace(value).toLowerCase();
    return !normalized
      || /all dramas?\s*&\s*films?/i.test(normalized)
      || /(?:drama|movie)list/i.test(normalized)
      || /'s list$/i.test(normalized)
      || /\blist$/i.test(normalized);
  }

  function extractFriendProfileNameFromDocument(doc, friend) {
    if (!doc || !friend?.username) return '';
    const username = String(friend.username || '').toLowerCase();
    const candidates = [
      q('.profile-header h1', doc),
      q('.col-lg-4 h1', doc),
      q('.col-md-4 h1', doc),
      q('.box-header h1', doc),
      q('.box-header h2', doc),
      q('h1', doc),
    ]
      .map((node) => collapseWhitespace(text(node)))
      .filter(Boolean);

    const exact = candidates.find((value) => value.toLowerCase() === username);
    if (exact) return exact;

    const clean = candidates.find((value) => !isLikelyBadFriendLabel(value));
    return clean || candidates[0] || '';
  }

  async function resolveFriendProfileIdentity(entry) {
    const username = collapseWhitespace(entry?.username || '');
    if (!username) return entry;
    if (!isLikelyBadFriendLabel(entry?.displayName)) return entry;
    if (friendProfileCache.has(username)) {
      return {
        ...entry,
        ...friendProfileCache.get(username),
      };
    }

    const fallback = {
      displayName: isLikelyBadFriendLabel(entry?.displayName) ? username : getFriendDisplayLabel(entry),
      avatar: entry?.avatar || '',
    };

    const promise = (async () => {
      const response = await fetch(createAbsoluteUrl(`/profile/${encodeURIComponent(username)}`), {
        credentials: 'same-origin',
      }).catch(() => null);
      if (!response?.ok) return fallback;

      const html = await response.text().catch(() => '');
      if (!html) return fallback;

      const doc = new DOMParser().parseFromString(html, 'text/html');
      return {
        displayName: extractFriendProfileNameFromDocument(doc, { username }) || fallback.displayName,
        avatar: fallback.avatar,
      };
    })();

    friendProfileCache.set(username, promise);
    const resolved = await promise;
    friendProfileCache.set(username, resolved);
    return {
      ...entry,
      ...resolved,
    };
  }

  function buildFriendRatingNote(statusLabel, progressLabel) {
    return collapseWhitespace([statusLabel, progressLabel].filter(Boolean).join(' '));
  }

  function getFriendMatchContext() {
    const portalContext = getPortalContext();
    if (!portalContext) return null;

    return {
      titleId: getTitleIdFromPath(),
      title: collapseWhitespace(portalContext.title || ''),
      baseTitle: collapseWhitespace(portalContext.baseTitle || portalContext.title || ''),
      nativeTitle: collapseWhitespace(portalContext.nativeTitle || ''),
      baseNativeTitle: collapseWhitespace(portalContext.baseNativeTitle || portalContext.nativeTitle || ''),
    };
  }

  function buildFriendListLookupUrls(friend, titleId = '') {
    const username = encodeURIComponent(friend?.username || '');
    if (!username) return [];

    const urls = [
      titleId ? { url: createAbsoluteUrl(`/dramalist/${username}?mylist=${encodeURIComponent(titleId)}`) } : null,
      titleId ? { url: createAbsoluteUrl(`/dramalist/${username}?mylist=${encodeURIComponent(titleId)}&lang=en-US`) } : null,
      { url: createAbsoluteUrl(`/dramalist/${username}`) },
      { url: createAbsoluteUrl(`/dramalist/${username}?lang=en-US`) },
    ];
    return urls.filter(Boolean);
  }

  function findFriendRowTitleAnchor(row) {
    return qa('a[href*="/"]', row).find((anchor) => {
      const href = anchor.getAttribute('href') || '';
      return !anchor.querySelector('img') && !/\/people\/|\/profile\/|\/dramalist\//i.test(href);
    }) || null;
  }

  function findFriendListRow(listRoot, titleId) {
    const rows = qa('tr', listRoot);
    if (!rows.length) return null;
    return rows.find((row) => qa('a[href*="/"]', row).some((anchor) => {
      const href = anchor.getAttribute('href') || '';
      return titleId && new RegExp(`/${titleId}(?:[-/?#]|$)`).test(href);
    })) || null;
  }

  function extractFriendRowScore(row) {
    const direct = collapseWhitespace(text(q('.score, .mdl-style-col-score, [class*="score"], .rating', row) || null));
    if (direct && !/^n\/a$/i.test(direct) && direct !== '0.0' && direct !== '0') {
      return direct.match(/(\d+(?:\.\d+)?)/)?.[1] || direct;
    }

    const rowText = collapseWhitespace(text(row));
    const allMatches = Array.from(rowText.matchAll(/\b(\d+(?:\.\d+)?)\b/g)).map((match) => match[1]);
    const plausible = allMatches
      .map((value) => Number(value))
      .filter((value) => Number.isFinite(value) && value > 0 && value <= 10);

    if (!plausible.length) return '';
    return String(plausible[plausible.length - 1]);
  }

  async function fetchAllFriends(token) {
    const cacheKey = `friends:${token.slice(0, 12)}`;
    if (friendsListCache.has(cacheKey)) return friendsListCache.get(cacheKey);

    const persisted = getPersistedFriendsList(token);
    if (Array.isArray(persisted)) {
      friendsListCache.set(cacheKey, persisted);
      return persisted;
    }

    const promise = (async () => {
      const results = [];
      let page = 1;
      let keepGoing = true;

      while (keepGoing) {
        const pages = await Promise.all(
          Array.from({ length: 5 }, (_, index) => page + index).map(async (pageNumber) => {
            const response = await fetch(`/v1/users/friends?page=${pageNumber}&lang=en-US`, {
              headers: { authorization: `Bearer ${token}` },
              credentials: 'same-origin',
            }).catch(() => null);

            if (!response?.ok) return [];
            const json = await response.json().catch(() => null);
            return Array.isArray(json?.items) ? json.items : [];
          }),
        );

        const rawItems = pages.flat();
        const normalized = rawItems.map((item) => {
          const friend = normalizeFriendUser(item);
          return friend;
        }).filter(Boolean);

        if (!normalized.length) {
          keepGoing = false;
          break;
        }

        results.push(...normalized);
        page += pages.length;
      }

      const seen = new Set();
      const deduped = results.filter((friend) => {
        if (seen.has(friend.username)) return false;
        seen.add(friend.username);
        return true;
      });

      return deduped;
    })();

    friendsListCache.set(cacheKey, promise);
    const resolved = await promise;
    const finalItems = persisted?.length > resolved.length ? persisted : resolved;
    if (resolved.length) persistFriendsList(token, resolved);
    friendsListCache.set(cacheKey, finalItems);
    return finalItems;
  }

  function parseFriendListMatchFromHtml(html, friend, titleId) {
    if (!html || !friend?.username || !titleId) return null;

    const doc = new DOMParser().parseFromString(html, 'text/html');
    const tableIds = {
      Watching: 'list_1',
      Completed: 'list_2',
      Planned: 'list_3',
      'On-Hold': 'list_4',
      Dropped: 'list_5',
      'Not Interested': 'list_6',
    };

    for (const [statusLabel, listId] of Object.entries(tableIds)) {
      const table = doc.getElementById(listId);
      if (!table) continue;
      const row = findFriendListRow(table, titleId);
      if (!row) continue;

      const scoreElement = q('.score', row);
      const rawScore = collapseWhitespace(text(scoreElement));
      const numericScore = rawScore && rawScore !== '0.0' && rawScore !== '0'
        ? (rawScore.match(/(\d+(?:\.\d+)?)/)?.[1] || rawScore)
        : '';
      const progressRoot = row.querySelector('.mdl-style-col-progress');
      const seenEpisodes = collapseWhitespace(text(progressRoot?.querySelector('.episode-seen')));
      const totalEpisodes = collapseWhitespace(text(progressRoot?.querySelector('.episode-total')));
      const progressLabel = seenEpisodes && totalEpisodes ? `(${seenEpisodes}/${totalEpisodes})` : '';

      return {
        username: friend.username,
        displayName: friend.displayName || friend.username,
        avatar: friend.avatar || '',
        score: numericScore ? `${formatScore(numericScore)}/10` : '',
        note: buildFriendRatingNote(statusLabel, progressLabel),
        statusLabel,
        progressLabel,
        rawScore,
        url: createAbsoluteUrl(`/profile/${friend.username}`),
      };
    }

    return null;
  }

  function parseFriendRatingFromHtml(html, friend, titleId) {
    const entry = parseFriendListMatchFromHtml(html, friend, titleId);
    return entry?.score ? entry : null;
  }

  async function fetchFriendsRatingsInternal(titleId) {
    const persisted = getPersistedFriendRatings(titleId);
    const cachedItems = Array.isArray(persisted) ? persisted : null;
    if (cachedItems) return cachedItems;

    const matches = await fetchFriendListMatchesInternal(titleId).catch(() => []);
    const deduped = await Promise.all(dedupeFriends(matches.filter((entry) => entry.score)).map(resolveFriendProfileIdentity));
    const finalItems = deduped;
    persistFriendRatings(titleId, finalItems);
    return finalItems;
  }

  function dedupeFriends(entries) {
    const seen = new Set();
    return entries.filter((entry) => {
      const key = `${entry.username}|${entry.score}`;
      if (seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  }

  function dedupeFriendIdentities(entries) {
    const seen = new Set();
    return entries.filter((entry) => {
      const key = entry.url || entry.username;
      if (!key || seen.has(key)) return false;
      seen.add(key);
      return true;
    });
  }

  async function fetchFriendListMatchesInternal(titleId) {
    const token = getToken();
    if (!token || !titleId) return [];
    const cacheKey = String(titleId);

    if (friendListMatchesCache.has(cacheKey)) return friendListMatchesCache.get(cacheKey);

    const persisted = getPersistedWatchedFriends(titleId);
    const cachedItems = Array.isArray(persisted) ? dedupeFriendIdentities(persisted) : [];
    if (Array.isArray(persisted)) {
      friendListMatchesCache.set(cacheKey, cachedItems);
      return cachedItems;
    }

    const promise = (async () => {
      const friends = await fetchAllFriends(token).catch(() => []);
      if (!friends.length) return cachedItems;

      const matches = [];
      for (let index = 0; index < friends.length; index += 10) {
        const batch = friends.slice(index, index + 10).map(async (friend) => {
          const lookupUrls = buildFriendListLookupUrls(friend, titleId);

          for (const lookup of lookupUrls) {
            const response = await fetch(lookup.url, {
              credentials: 'same-origin',
            }).catch(() => null);

            if (!response?.ok) continue;

            const html = await response.text().catch(() => '');
            const match = parseFriendListMatchFromHtml(html, friend, titleId);
            if (match) return match;
          }

          return null;
        });

      const results = await Promise.all(batch);
      matches.push(...results.filter(Boolean));
      }

      const deduped = dedupeFriendIdentities(matches);
      const enriched = await Promise.all(deduped.map(resolveFriendProfileIdentity));
      const finalItems = enriched;
      persistWatchedFriends(titleId, enriched);
      return finalItems;
    })();

    friendListMatchesCache.set(cacheKey, promise);
    const resolved = await promise;
    friendListMatchesCache.set(cacheKey, resolved);
    return resolved;
  }

  async function resolveFriendsRatings() {
    const titleId = getTitleIdFromPath();
    const cacheKey = `${location.pathname}|${titleId}`;
    if (friendsRatingsCache.has(cacheKey)) return friendsRatingsCache.get(cacheKey);

    const promise = (async () => {
      const fetchedEntries = await fetchFriendsRatingsInternal(titleId).catch(() => []);
      return dedupeFriends(fetchedEntries);
    })();

    friendsRatingsCache.set(cacheKey, promise);
    const result = await promise;
    friendsRatingsCache.set(cacheKey, result);
    return result;
  }

  async function resolveWatchedFriends() {
    const titleId = getTitleIdFromPath();
    const cacheKey = `${location.pathname}|watched|${titleId}`;
    if (watchedFriendsCache.has(cacheKey)) return watchedFriendsCache.get(cacheKey);

    const promise = (async () => {
      const fetchedEntries = await fetchFriendListMatchesInternal(titleId).catch(() => []);
      return dedupeFriendIdentities(fetchedEntries);
    })();

    watchedFriendsCache.set(cacheKey, promise);
    const result = await promise;
    watchedFriendsCache.set(cacheKey, result);
    return result;
  }

  function buildFriendsRenderKey(entries) {
    return JSON.stringify(entries.map((entry) => ({
      username: entry.username,
      displayName: entry.displayName,
      score: entry.score,
      avatar: entry.avatar,
      url: entry.url,
    })));
  }

  function renderFriendsRatings(entries) {
    const box = ensureFriendsBoxShell();
    if (!box) return;

    const body = q('.box-body', box) || box;
    if (!entries.length) {
      body.innerHTML = `<div class="${NS}-friends-empty">No friend ratings found yet.</div>`;
      box.dataset.renderKey = 'empty';
      lastFriendsRenderKey = '';
      return;
    }

    const renderKey = buildFriendsRenderKey(entries);
    if (box.dataset.renderKey === renderKey && lastFriendsRenderKey === renderKey) return;

    const pageSize = 5;
    let page = Number(box.dataset.page || 0);
    const totalPages = Math.max(1, Math.ceil(entries.length / pageSize));
    if (page >= totalPages) page = 0;

    const renderPage = (pageIndex) => {
      const start = pageIndex * pageSize;
      const visible = entries.slice(start, start + pageSize);
      body.innerHTML = '';

      const list = document.createElement('div');
      list.className = `${NS}-friends-list`;

      visible.forEach((entry) => {
        const item = document.createElement(entry.url ? 'a' : 'div');
        item.className = `${NS}-friend-row`;
        if (entry.url) {
          item.href = entry.url;
          item.target = '_blank';
          item.rel = 'noopener noreferrer';
        }

        const avatar = document.createElement('img');
        avatar.className = `${NS}-friend-avatar`;
        avatar.src = entry.avatar || getFaviconUrl(location.origin);
        avatar.alt = getFriendDisplayLabel(entry);

        const main = document.createElement('div');
        main.className = `${NS}-friend-main`;
        main.innerHTML = `
          <span class="${NS}-friend-name">${getFriendDisplayLabel(entry)}</span>
          <span class="${NS}-friend-meta">${entry.note || 'Friend rating'}</span>
        `;

        const score = document.createElement('div');
        score.className = `${NS}-friend-score`;
        score.textContent = entry.score;

        item.append(avatar, main, score);
        list.appendChild(item);
      });

      body.appendChild(list);

      if (totalPages > 1) {
        const nav = document.createElement('div');
        nav.className = `${NS}-friends-nav`;

        const prev = document.createElement('button');
        prev.type = 'button';
        prev.className = `${NS}-friends-arrow`;
        prev.textContent = '<';
        prev.disabled = pageIndex === 0;
        prev.addEventListener('click', () => {
          box.dataset.page = String(pageIndex - 1);
          renderPage(pageIndex - 1);
        });

        const info = document.createElement('div');
        info.className = `${NS}-friends-page`;
        info.textContent = `${pageIndex + 1}/${totalPages}`;

        const next = document.createElement('button');
        next.type = 'button';
        next.className = `${NS}-friends-arrow`;
        next.textContent = '>';
        next.disabled = pageIndex >= totalPages - 1;
        next.addEventListener('click', () => {
          box.dataset.page = String(pageIndex + 1);
          renderPage(pageIndex + 1);
        });

        nav.append(prev, info, next);
        body.appendChild(nav);
      }

      box.dataset.page = String(pageIndex);
    };

    renderPage(page);
    box.dataset.renderKey = renderKey;
    lastFriendsRenderKey = renderKey;
  }

  function buildWatchedFriendsRenderKey(entries) {
    return JSON.stringify(entries.map((entry) => ({
      username: entry.username,
      displayName: entry.displayName,
      avatar: entry.avatar,
      note: entry.note,
      url: entry.url,
    })));
  }

  function createWatchedAvatarNode(entry) {
    const node = document.createElement(entry.url ? 'a' : 'div');
    node.className = entry.avatar ? `${NS}-watched-avatar-link` : `${NS}-watched-avatar-fallback`;
    node.title = getFriendDisplayLabel(entry);

    if (entry.url) {
      node.href = entry.url;
      node.target = '_blank';
      node.rel = 'noopener noreferrer';
    }

    if (entry.avatar) {
      const avatar = document.createElement('img');
      avatar.className = `${NS}-watched-avatar`;
      avatar.src = entry.avatar;
      avatar.alt = getFriendDisplayLabel(entry);
      node.appendChild(avatar);
    } else {
      node.textContent = (getFriendDisplayLabel(entry) || '?').trim().charAt(0).toUpperCase() || '?';
    }

    return node;
  }

  function renderWatchedFriends(entries) {
    const box = ensureWatchedFriendsBoxShell();
    if (!box) return;

    const body = q('.box-body', box) || box;
    if (!entries.length) {
      box.remove();
      lastWatchedFriendsRenderKey = '';
      return;
    }

    const renderKey = buildWatchedFriendsRenderKey(entries);
    if (box.dataset.renderKey === renderKey && lastWatchedFriendsRenderKey === renderKey) return;

    const pageSize = 10;
    let page = Number(box.dataset.page || 0);
    const totalPages = Math.max(1, Math.ceil(entries.length / pageSize));
    if (page >= totalPages) page = 0;

    const renderPage = (pageIndex) => {
      const start = pageIndex * pageSize;
      const visible = entries.slice(start, start + pageSize);
      body.innerHTML = '';

      const grid = document.createElement('div');
      grid.className = `${NS}-watched-grid`;
      visible.forEach((entry) => {
        grid.appendChild(createWatchedAvatarNode(entry));
      });
      body.appendChild(grid);

      if (totalPages > 1) {
        const nav = document.createElement('div');
        nav.className = `${NS}-friends-nav`;

        const prev = document.createElement('button');
        prev.type = 'button';
        prev.className = `${NS}-friends-arrow`;
        prev.textContent = '<';
        prev.disabled = pageIndex === 0;
        prev.addEventListener('click', () => {
          box.dataset.page = String(pageIndex - 1);
          renderPage(pageIndex - 1);
        });

        const info = document.createElement('div');
        info.className = `${NS}-friends-page`;
        info.textContent = `${pageIndex + 1}/${totalPages}`;

        const next = document.createElement('button');
        next.type = 'button';
        next.className = `${NS}-friends-arrow`;
        next.textContent = '>';
        next.disabled = pageIndex >= totalPages - 1;
        next.addEventListener('click', () => {
          box.dataset.page = String(pageIndex + 1);
          renderPage(pageIndex + 1);
        });

        nav.append(prev, info, next);
        body.appendChild(nav);
      }

      box.dataset.page = String(pageIndex);
    };

    renderPage(page);
    box.dataset.renderKey = renderKey;
    lastWatchedFriendsRenderKey = renderKey;
  }

  async function initFriendsRatings() {
    if (!isTitlePage()) return;
    if (!isFeatureEnabled('titleRatedByFriends')) {
      q(`#${FRIENDS_BOX_ID}`)?.remove();
      lastFriendsRenderKey = '';
      return;
    }

    const entries = await resolveFriendsRatings().catch(() => []);
    renderFriendsRatings(entries);
  }

  async function initWatchedFriends() {
    if (!isTitlePage()) return;
    if (!isFeatureEnabled('titleWatchedByFriends')) {
      q(`#${WATCHED_FRIENDS_BOX_ID}`)?.remove();
      lastWatchedFriendsRenderKey = '';
      return;
    }

    const entries = await resolveWatchedFriends().catch(() => []);
    renderWatchedFriends(entries);
  }

  async function initPortalLinks() {
    if (!isTitlePage()) return;
    if (!isTitleDetailsTabActive()) {
      q(`#${PORTALS_BOX_ID}`)?.remove();
      lastPortalRenderKey = '';
      return;
    }
    if (!isFeatureEnabled('titlePortalIcons')) {
      q(`#${PORTALS_BOX_ID}`)?.remove();
      lastPortalRenderKey = '';
      return;
    }

    const context = getPortalContext();
    if (!context) {
      q(`#${PORTALS_BOX_ID}`)?.remove();
      lastPortalRenderKey = '';
      return;
    }

    const links = await resolvePortalLinks(context).catch(() => []);
    renderPortalLinks(links);
  }

  function sanitizeHexColor(value, fallback) {
    const raw = collapseWhitespace(String(value || '')).replace(/^#/, '');
    return /^[0-9a-f]{6}$/i.test(raw) ? `#${raw.toLowerCase()}` : fallback;
  }

  function getBetterMdlStorageUsageBytes() {
    const encoder = new TextEncoder();
    return Object.keys(localStorage)
      .filter((key) => key.startsWith(NS))
      .reduce((sum, key) => sum + encoder.encode(`${key}${localStorage.getItem(key) || ''}`).length, 0);
  }

  function formatStorageUsage(bytes) {
    return `${(bytes / 1024).toFixed(2)} KB`;
  }

  function isBetterMdlSettingsActive() {
    return location.hash === '#better-mdl';
  }

  function findAccountSettingsBox() {
    const root = findSettingsRoot();
    if (root) return root;
    return qa('.box, .card, .settings, .settings-page, .account-settings, main, section, [class*="setting"]').find((box) => {
      const header = text(q('.box-header, .box-title, .card-header, h1, h2, h3', box));
      return /settings/i.test(header) && !!q('a, button', box);
    }) || null;
  }

  function getSettingsTabControls(node) {
    return qa('a, button', node).filter((control) => text(control));
  }

  function isSettingsTabList(node) {
    const labels = getSettingsTabControls(node).map(text);
    if (!labels.includes('Profile')) return false;
    const matches = labels.filter((label) => /General|Security|Notifications|Apps|Subscriptions|Blocking|List Styles|Widgets|Connected Apps|Security & Privacy|General Settings/i.test(label));
    return matches.length >= 2;
  }

  function findSettingsTabList() {
    return qa('ul, nav, .nav, .nav-tabs, .list-inline, [role="tablist"], div')
      .filter(isSettingsTabList)
      .sort((a, b) => getSettingsTabControls(a).length - getSettingsTabControls(b).length || text(a).length - text(b).length)[0]
      || null;
  }

  function findSettingsRoot() {
    const tabList = findSettingsTabList();
    let node = tabList?.parentElement || null;
    let fallback = node;
    let best = null;
    while (node && node !== document.body) {
      const heading = q('h1, h2, h3', node);
      const hasSettingsHeading = !!heading && /settings/i.test(text(heading));
      const hasNativeContent = !!qa('form, input, select, textarea, [role="tabpanel"], .tab-pane, .form-group', node)
        .find((candidate) => !candidate.closest(`#${SETTINGS_PANEL_ID}`));
      if (hasSettingsHeading && hasNativeContent) best = node;
      if (node.matches?.('.box, .card, main, section, .container, .content, [class*="account"]')) fallback = node;
      node = node.parentElement;
    }
    return best || fallback || null;
  }

  function getSettingsTabBlock(tabList) {
    return tabList || null;
  }

  function makeElement(html) {
    const template = document.createElement('template');
    template.innerHTML = html.trim();
    return template.content.firstElementChild;
  }

  function slugifySettingKey(value) {
    return String(value || '')
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, '-')
      .replace(/^-+|-+$/g, '');
  }

  function ensureSettingsTab() {
    const tabList = findSettingsTabList();
    if (!tabList) return null;
    tabList.classList.add(`${NS}-settings-tab-list`);
    if (!tabList.dataset.betterMdlNativeTabsDelegated) {
      tabList.dataset.betterMdlNativeTabsDelegated = 'true';
      tabList.addEventListener('click', (event) => {
        const control = event.target?.closest?.('a, button');
        if (!control || !tabList.contains(control)) return;
        if (control.closest(`#${SETTINGS_PANEL_ID}-tab`) || control.id === `${SETTINGS_PANEL_ID}-tab`) return;
        if (location.hash === '#better-mdl') {
          history.replaceState(null, '', `${location.pathname}${location.search}`);
        }
        const panel = q(`#${SETTINGS_PANEL_ID}`);
        if (panel) panel.style.display = 'none';
        setTimeout(applySettingsPageState, 0);
      }, true);
    }

    let item = q(`#${SETTINGS_PANEL_ID}-tab`);
    if (!item) {
      const firstControl = getSettingsTabControls(tabList)[0];
      if (/^(ul|ol)$/i.test(tabList.tagName)) {
        item = makeElement(`<li id="${SETTINGS_PANEL_ID}-tab" class="page-item nav-item"><a href="#better-mdl" class="${firstControl?.className || 'nav-link'}">BetterMDL</a></li>`);
      } else {
        item = document.createElement('a');
        item.id = `${SETTINGS_PANEL_ID}-tab`;
        item.className = `${firstControl?.className || ''} ${NS}-settings-tab-link`.trim();
        item.href = '#better-mdl';
        item.textContent = 'BetterMDL';
      }
      tabList.appendChild(item);
    }

    const betterMdlLink = item.matches('a, button') ? item : q('a, button', item);
    if (betterMdlLink && betterMdlLink.dataset.betterMdlTabBound !== 'true') {
      betterMdlLink.dataset.betterMdlTabBound = 'true';
      betterMdlLink.addEventListener('click', (event) => {
        event.preventDefault();
        event.stopPropagation();
        event.stopImmediatePropagation?.();
        location.hash = 'better-mdl';
        renderSettingsPage();
      }, true);
    }

    getSettingsTabControls(tabList).forEach((control) => {
      if (control.closest(`#${SETTINGS_PANEL_ID}-tab`) || control.id === `${SETTINGS_PANEL_ID}-tab`) return;
      if (control.dataset.betterMdlNativeTabBound === 'true') return;
      control.dataset.betterMdlNativeTabBound = 'true';
      control.addEventListener('click', () => {
        if (location.hash === '#better-mdl') {
          history.replaceState(null, '', `${location.pathname}${location.search}`);
        }
        setTimeout(applySettingsPageState, 0);
      });
    });

    return item;
  }

  function ensureSettingsPanel() {
    const tabList = findSettingsTabList();
    const tabBlock = getSettingsTabBlock(tabList);
    if (!tabList || !tabBlock?.parentElement) return null;

    let panel = q(`#${SETTINGS_PANEL_ID}`);
    if (!panel) {
      panel = document.createElement('div');
      panel.id = SETTINGS_PANEL_ID;
    }

    if (panel.parentElement !== tabBlock.parentElement || panel.previousElementSibling !== tabBlock) {
      tabBlock.insertAdjacentElement('afterend', panel);
    }

    return panel;
  }

  function getNativeSettingsContentNodes(panel) {
    const tabList = findSettingsTabList();
    const tabBlock = getSettingsTabBlock(tabList);
    const host = panel?.parentElement || tabBlock?.parentElement;
    if (!tabList || !host || !tabBlock || !panel) return [];
    const directNodes = Array.from(host.children).filter((node) => node !== tabBlock && node !== panel);
    const nestedNodes = qa('form, [role="tabpanel"], .tab-pane, section, [class*="profile"], [class*="widget"], [class*="list-style"]', host)
      .filter((node) => node !== host && node !== tabBlock && node !== panel)
      .filter((node) => !node.closest(`#${SETTINGS_PANEL_ID}`) && !tabBlock.contains(node) && !node.contains(tabBlock));
    const nodes = [...directNodes, ...nestedNodes].filter((node) => !node.contains(panel) && !panel.contains(node));
    return [...new Set(nodes)].filter((node, index, list) => !list.some((other) => other !== node && other.contains(node)));
  }

  function restoreNativeSettingsContent() {
    qa(`.${NS}-native-settings-hidden`).forEach((node) => node.classList.remove(`${NS}-native-settings-hidden`));
  }

  function clearBetterMdlStorage() {
    const keys = [];
    for (let i = 0; i < localStorage.length; i += 1) {
      const key = localStorage.key(i);
      if (key && (key.startsWith(NS) || key.startsWith('betterMDL'))) keys.push(key);
    }
    keys.forEach((key) => localStorage.removeItem(key));
  }

  function applySettingsPageState() {
    if (!isAccountSettingsPage()) return;
    const panel = ensureSettingsPanel();
    const tab = ensureSettingsTab();
    const isActive = isBetterMdlSettingsActive();
    const link = tab?.matches('a, button') ? tab : q('a, button', tab);

    if (panel) panel.style.display = isActive ? 'block' : 'none';
    restoreNativeSettingsContent();
    if (isActive) {
      getNativeSettingsContentNodes(panel).forEach((node) => {
        node.classList.add(`${NS}-native-settings-hidden`);
      });
    }
    if (tab) {
      tab.classList.toggle('active', isActive);
      link?.classList.toggle('active', isActive);
      if (isActive) {
        getSettingsTabControls(tab.parentElement || document).forEach((control) => {
          if (control === link) return;
          control.classList.remove('active');
          control.closest('li')?.classList.remove('active');
        });
      }
    }
  }

  function renderStandaloneSettingsPage() {
    const nativeRoot = findSettingsRoot() || findAccountSettingsBox();
    const host = nativeRoot?.parentElement || q('main, .container, .content, .app, body') || document.body;
    let panel = q(`#${SETTINGS_PANEL_ID}`);
    if (!panel) {
      panel = document.createElement('div');
      panel.id = SETTINGS_PANEL_ID;
    }

    if (panel.parentElement !== host) {
      if (nativeRoot?.parentElement === host) nativeRoot.insertAdjacentElement('afterend', panel);
      else host.prepend(panel);
    }

    restoreNativeSettingsContent();
    if (nativeRoot && nativeRoot !== panel && !nativeRoot.contains(panel)) {
      nativeRoot.classList.add(`${NS}-native-settings-hidden`);
    }

    panel.className = `${NS}-settings-panel`;
    panel.style.display = 'block';
    if (panel.dataset.betterMdlStandaloneRendered !== 'true') {
      panel.innerHTML = `
        <div class="box-body">
          <div class="${NS}-settings-header">
            <span>Better MDL Settings</span>
            <button type="button" class="${NS}-settings-back">Back to MDL Settings</button>
          </div>
          <div class="${NS}-settings-content">
            ${buildSettingsPanelMarkup(getSettings())}
          </div>
        </div>
      `;
      bindSettingsPanelEvents(panel);
      q(`.${NS}-settings-back`, panel)?.addEventListener('click', () => {
        history.replaceState(null, '', `${location.pathname}${location.search}`);
        renderSettingsPage();
      });
      panel.dataset.betterMdlStandaloneRendered = 'true';
    }
    settingsPanelRendered = true;
  }

  function getFeatureLabelMarkup(key, label) {
    const statusIcons = `<span class="${NS}-feature-icons" aria-hidden="true"><i class="fas fa-spinner" style="color:#85c1dc"></i><i class="fas fa-check" style="color:#a6d189"></i><i class="far fa-clock" style="color:#ca9ee6"></i><i class="fas fa-pause" style="color:#e5c890"></i><i class="fas fa-heart-broken" style="color:#e78284"></i><i class="fas fa-minus-circle" style="color:#bbbbbb"></i></span>`;
    if (key === 'peopleStatusSummary') {
      return `${label}${statusIcons}`;
    }
    if (key === 'peopleFilmographyIcons') {
      return `${label}${statusIcons}`;
    }
    if (key === 'titlePortalIcons') {
      return `${label} <span class="${NS}-feature-note">(IMDB, TMDB, SIMKL, AsianWiki)</span>`;
    }
    return label;
  }

  function getSettingsFeatureCheckedState(settings, key) {
    if (key === 'peopleFilmographyLargeViewDefault') {
      return getFilmographySectionUiState(getPeopleFilmographyGlobalSectionKey()).view === 'large';
    }
    return !!settings.features[key];
  }

  function buildSettingsPanelMarkup(settings) {
    const featureRows = Object.entries(FEATURE_LABELS).map(([key, label]) => `
      <div class="form-check">
        <input type="checkbox" class="form-check-input" id="${NS}-feature-${slugifySettingKey(key)}" name="feature_${key}" value="true" ${getSettingsFeatureCheckedState(settings, key) ? 'checked' : ''}>
        <label class="form-check-label" for="${NS}-feature-${slugifySettingKey(key)}">${getFeatureLabelMarkup(key, label)}</label>
      </div>
    `).join('');

    const labelRows = `
      <div class="form-group ${NS}-settings-label-field ${NS}-settings-wide">
        <label class="control-label" for="${NS}-label-undecided-status">Watchlist: Undecided label</label>
        <input type="text" class="form-control" id="${NS}-label-undecided-status" name="label_undecidedStatus" maxlength="40" value="${escapeHtml(settings.labels?.undecidedStatus || 'Undecided')}">
      </div>
    `;

    const storageText = formatStorageUsage(getBetterMdlStorageUsageBytes());

    const iconRows = Object.values(STATUS_CONFIG).map((config) => {
      const current = settings.statuses[config.key];
      return `
        <div class="form-group">
          <label class="control-label">Icon for "${config.label}"</label>
          <input type="text" class="form-control" name="icon_${config.key}" value="${current.icon}">
        </div>
      `;
    }).join('');

    const colorRows = Object.values(STATUS_CONFIG).map((config) => {
      const current = settings.statuses[config.key];
      return `
        <div class="form-group">
          <label class="control-label">Color for "${config.label}"</label>
          <div class="input-group">
            <input type="text" class="form-control" name="color_${config.key}" value="${current.color}">
            <span class="input-group-addon">
              <input type="color" name="colorpicker_${config.key}" value="${current.color}">
            </span>
          </div>
        </div>
      `;
    }).join('');

    return `
      <form class="${NS}-settings-form">
        <div class="alert alert-info" role="alert">
          Enter a Font Awesome icon class like <code>fas fa-check</code> and choose a color. Available icons: <a href="https://fontawesome.com/icons" target="_blank">https://fontawesome.com/icons</a>
        </div>
        <div class="${NS}-settings-layout">
          <div class="${NS}-settings-col ${NS}-settings-features">
            ${featureRows}
            <div class="alert alert-warning ${NS}-settings-storage" role="alert">
              <span class="${NS}-settings-storage-text">BetterMDL is currently using ${storageText} of storage</span>
              <div class="${NS}-settings-storage-actions">
                <button type="submit" class="btn btn-primary ${NS}-settings-save">Save Changes</button>
                <button type="button" class="btn btn-danger ${NS}-settings-reset">Reset BetterMDL</button>
              </div>
            </div>
          </div>
          <div class="${NS}-settings-right">
            <div class="${NS}-settings-col ${NS}-settings-icons">
              ${iconRows}
            </div>
            <div class="${NS}-settings-col ${NS}-settings-colors">
              ${colorRows}
            </div>
            ${labelRows}
          </div>
        </div>
      </form>
    `;
  }

  function collectSettingsFromPanel(panel) {
    const defaults = getDefaultSettings();
    const next = getSettings();

    Object.values(STATUS_CONFIG).forEach((config) => {
      const iconInput = q(`[name="icon_${config.key}"]`, panel);
      const colorInput = q(`[name="color_${config.key}"]`, panel);
      next.statuses[config.key] = {
        icon: collapseWhitespace(iconInput?.value || '') || defaults.statuses[config.key].icon,
        color: sanitizeHexColor(colorInput?.value, defaults.statuses[config.key].color),
      };
    });

    next.labels = {
      ...(next.labels || {}),
      undecidedStatus: collapseWhitespace(q('[name="label_undecidedStatus"]', panel)?.value || '').slice(0, 40) || defaults.labels.undecidedStatus,
    };

    Object.keys(FEATURE_LABELS).forEach((featureKey) => {
      next.features[featureKey] = !!q(`[name="feature_${featureKey}"]`, panel)?.checked;
    });
    next.features.showHideSections = true;

    return next;
  }

  function resetAutoHideCollapseStateForSettingsChange(previousSettings, nextSettings) {
    const previous = previousSettings?.features || {};
    const next = nextSettings?.features || {};
    const state = getCollapseState();
    let changed = false;

    const removeMatching = (matcher) => {
      Object.keys(state).forEach((key) => {
        if (matcher(key)) {
          delete state[key];
          changed = true;
        }
      });
    };

    if (previous.peopleAutoHideSections !== next.peopleAutoHideSections) {
      removeMatching((key) => /^\/people\//.test(key) && /:(bio|people-photos|articles|comments)$/.test(key));
    }

    if (previous.titleAutoHideSections !== next.titleAutoHideSections) {
      removeMatching((key) => /^\/\d/.test(key) && /:(photos|reviews|recent-discussions|comments)$/.test(key));
    }

    if (previous.titleSynopsisHide !== next.titleSynopsisHide) {
      removeMatching((key) => /^\/\d/.test(key) && /:synopsis$/.test(key));
    }

    if (changed) setCollapseState(state);
  }

  function syncFilmographyDefaultViewForSettingsChange(previousSettings, nextSettings) {
    const next = nextSettings?.features || {};
    const sectionKey = getPeopleFilmographyGlobalSectionKey();
    const nextView = next.peopleFilmographyLargeViewDefault ? 'large' : 'mini';
    if (getFilmographySectionUiState(sectionKey).view === nextView) return;

    const store = getFilmographyUiState();
    const key = getFilmographySectionStateKey(sectionKey);
    store[key] = {
      ...(store[key] || {}),
      view: nextView,
    };
    setFilmographyUiState(store);
  }

  function bindSettingsPanelEvents(panel) {
    qa(`input[name^="colorpicker_"]`, panel).forEach((picker) => {
      picker.addEventListener('input', () => {
        const key = picker.getAttribute('name')?.replace('colorpicker_', '');
        const textInput = q(`[name="color_${key}"]`, panel);
        if (textInput) textInput.value = picker.value;
      });
    });

    qa(`input[name^="color_"]`, panel).forEach((input) => {
      input.addEventListener('input', () => {
        const key = input.getAttribute('name')?.replace('color_', '');
        const picker = q(`[name="colorpicker_${key}"]`, panel);
        const next = sanitizeHexColor(input.value, picker?.value || '#000000');
        if (picker) picker.value = next;
      });
    });

    q(`form.${NS}-settings-form`, panel)?.addEventListener('submit', (event) => {
      event.preventDefault();
      const previousSettings = getSettings();
      const nextSettings = collectSettingsFromPanel(panel);
      resetAutoHideCollapseStateForSettingsChange(previousSettings, nextSettings);
      syncFilmographyDefaultViewForSettingsChange(previousSettings, nextSettings);
      saveSettings(nextSettings);
      location.reload();
    });

    q(`.${NS}-settings-reset`, panel)?.addEventListener('click', () => {
      clearBetterMdlStorage();
      location.reload();
    });
  }

  function renderSettingsPage() {
    if (!isAccountSettingsPage()) return;
    injectSettingsStyle();
    ensureSettingsTab();
    if (isBetterMdlSettingsActive()) {
      renderStandaloneSettingsPage();
      return;
    }

    restoreNativeSettingsContent();
    const existingPanel = q(`#${SETTINGS_PANEL_ID}`);
    if (existingPanel) {
      existingPanel.style.display = 'none';
      existingPanel.dataset.betterMdlStandaloneRendered = '';
    }
    settingsPanelRendered = false;
  }

  function initSettingsPage() {
    if (!isAccountSettingsPage()) return;
    if (!window.__betterMdlSettingsHashBound) {
      window.addEventListener('hashchange', renderSettingsPage);
      window.__betterMdlSettingsHashBound = true;
    }
    renderSettingsPage();
  }

  function isBetterMdlOwnedNode(node) {
    if (!node || node.nodeType !== 1) return false;
    return !!node.closest?.(`[id^="${NS}"], [class*="${NS}"], #${STYLE_ID}, #${STYLE_ID}-settings, #${FA_LINK_ID}`);
  }

  function shouldScheduleBootForMutations(mutations) {
    if (Date.now() < filmographyMutationIgnoreUntil) return false;
    if (location.href !== lastObservedHref) {
      lastObservedHref = location.href;
      titlePageBootedHref = '';
      dramalistUndecidedScheduleKey = '';
      settingsPanelRendered = false;
      return true;
    }

    if (isAccountSettingsPage()) return false;
    if (isTitlePage() && titlePageBootedHref === location.href) return false;

    return mutations.some((mutation) => {
      if (isBetterMdlOwnedNode(mutation.target)) return false;
      const addedNodes = Array.from(mutation.addedNodes || []);
      const removedNodes = Array.from(mutation.removedNodes || []);
      const changedNodes = [...addedNodes, ...removedNodes].filter((node) => node.nodeType === 1);
      return !changedNodes.length || changedNodes.some((node) => !isBetterMdlOwnedNode(node));
    });
  }

  async function boot() {
    resetLegacyBetterMdlCache();
    maintainBetterMdlCache();
    if (isPeoplePage() || isTitlePage() || (isAccountSettingsPage() && isBetterMdlSettingsActive())) {
      injectFontAwesome();
    } else {
      removeFontAwesome();
    }
    injectStyle();
    injectSettingsStyle();

    if (isAccountSettingsPage()) {
      if (observer) {
        observer.disconnect();
        observer = null;
      }
      initSettingsPage();
      return;
    }

    initDramalistCountryCacheCollector();
    scheduleDramalistUndecidedLabel();

    if (!observer && document.body) {
      observer = new MutationObserver((mutations) => {
        if (shouldScheduleBootForMutations(mutations)) scheduleBoot();
      });
      observer.observe(document.body, { childList: true, subtree: true });
    }

    if (isPeoplePage()) {
      bindPeopleTabRefresh();
      hideDuplicatePosterColumn();
      initShowHide();
      schedulePeopleFilmographyControls([]);

      const profileBox = findProfileBox();
      initPeopleNativeActionToggles();

      const filmographyIds = collectFilmographyIds();
      const statuses = normalizeStatusItems(filmographyIds, await fetchStatuses(filmographyIds).catch(() => []));
      if (profileBox) renderStatusRow(profileBox, computeCounts(statuses));
      renderFilmographyStatusIcons(statuses);
      schedulePeopleFilmographyControls(statuses);
      return;
    }

    if (isProfilePage()) {
      initProfileCountryStats().catch(() => {});
      return;
    }

    if (isTitlePage()) {
      bindTitleTabRefresh();
      if (observer) {
        observer.disconnect();
        observer = null;
      }
      if (titlePageBootedHref === location.href) {
        initTitlePageSectionToggles();
        initTitleNativeActionToggles();
        await initPortalLinks().catch(() => {});
        initTitleNativeTitleSwap();
        return;
      }
      titlePageBootedHref = location.href;
      initTitlePageSectionToggles();
      await Promise.all([
        initOriginalWorkBox().catch(() => {}),
        initPortalLinks().catch(() => {}),
      ]);
      await initFriendsRatings().catch(() => {});
      await initWatchedFriends().catch(() => {});
      initTitleNativeActionToggles();
      initTitleNativeTitleSwap();
      return;
    }

  }

  async function runBoot() {
    if (bootInFlight) {
      bootQueued = true;
      return;
    }

    bootInFlight = true;
    do {
      bootQueued = false;
      await boot().catch(() => {});
    } while (bootQueued);
    bootInFlight = false;
  }

  function scheduleBoot() {
    clearTimeout(bootTimer);
    bootTimer = setTimeout(() => { runBoot().catch(() => {}); }, 180);
  }

  function start() {
    scheduleBoot();
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', start, { once: true });
  } else {
    start();
  }
})();
