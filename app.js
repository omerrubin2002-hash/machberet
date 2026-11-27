'use strict';
(function () {
  // ===================== קבועים =====================
  const PAGE_W = 1000, PAGE_H0 = 1425, GRID = 25; // גובה = 57 משבצות שלמות
  let PAGE_H = PAGE_H0; // גובה העמוד הנוכחי (דף שגדל מתארך)
  const LINE_GAP = 35, LINE_TOP = 105, MARGIN_X = PAGE_W - 75; // דף שורות (קו שוליים מימין)
  const PAPER = {
    light: { page: '#ffffff', grid: '#d3deea', line: '#c5d3e3', margin: '#f0b4b4', desk: '#e9e7e2', engMinor: '#d6eadb', engMajor: '#9ccaa5', div: '#9fb3c8' },
    dark: { page: '#1f2023', grid: '#353d48', line: '#3b4656', margin: '#6b3c3c', desk: '#121214', engMinor: '#253229', engMajor: '#3e5c45', div: '#5a6b80' },
  };
  const PAPER_TYPES = ['blank', 'lines', 'grid', 'eng', 'cornell'];
  const ENG_MINOR = 12.5, ENG_MAJOR = 62.5;               // הנדסאי: משבצת קטנה, וקו עבה כל 5
  const CORNELL_X = PAGE_W - 280; // קורנל: עמודת הערות מימין, סיכום 270 מעל תחתית הדף
  const PEN_TYPES = ['felt', 'fountain', 'brush', 'pencil'];
  const PEN_SIZES = [1.5, 2.5, 3.5, 5, 7, 10];   // עובי בסיס ביחידות דף (דף = 1000 יחידות רוחב)
  const PEN_DOTS = [3, 4.5, 6, 8, 10.5, 13];     // גודל הנקודה בכפתור
  const PEN_DEFAULT_IDX = { felt: 2, fountain: 2, brush: 3, pencil: 2 };
  const HL_SIZES = [8, 12, 16, 22, 28, 36];
  const HL_DOTS = [6, 8, 10, 12, 14, 16];
  const HL_ALPHA = 0.42;
  const BASE_COLORS = ['#1a1a1a', '#1e4fd8', '#d32020', '#138a3a'];
  const HL_COLORS = ['#fdd835', '#7cd65a', '#ff8ac4', '#5ec8f2'];
  const MARGIN = 24;
  const MIN_DIST = 0.3;                    // מרחק מינימלי בין נקודות שנשמרות
  const ERASER_SIZES = [8, 16, 28];        // רדיוס המחק בפיקסלים של מסך: קטן, בינוני, גדול
  const ERASER_DOTS = [12, 20, 32];        // גודל העיגול בתפריט
  const ERASER_DYN_MAX = 40;               // מחק דינמי גדל עד כאן (יותר מהגדול), או לפחות פי 1.6
  const PALM_MS = 300;                     // כמה זמן אחרי הרמת העט מתעלמים ממגע חדש
  const HOVER_MS = 150;                    // ריחוף העט מעל המסך חוסם מגע רק לרגע קצר
  const TOUCH_SLOP = 12;                   // אצבע צריכה לזוז כך כדי להתחיל גלילה (כף יד שנחה לא תזיז)
  const PALM_SIZE = 50;                    // מגע רחב מזה = כף יד
  const TAP_MS = 350, TAP_SLOP = 18;       // הקשה בשתיים/שלוש אצבעות: קצרה ובלי תזוזה (אחרת זה זום)
  const SEL_BLUE = '#1e4fd8';
  const PALETTE = [
    '#000000', '#4a4a4a', '#8c8c8c', '#6d3b1f', '#a0522d', '#c98a4b',
    '#b71c1c', '#e53935', '#f06292', '#ad1457', '#8e24aa', '#5e35b1',
    '#1a237e', '#1e4fd8', '#039be5', '#00838f', '#00897b', '#2e7d32',
    '#7cb342', '#c0ca33', '#fdd835', '#ffb300', '#fb8c00', '#f4511e',
  ];

  const $ = (s) => document.querySelector(s);
  const stage = $('#stage'), mainC = $('#main'), overC = $('#over');
  let mctx, octx;

  let W = 0, H = 0, dpr = 1, stageLeft = 0, stageTop = 0;
  const view = { s: 1, ox: 0, oy: 0 };
  let rendered = { s: 1, ox: 0, oy: 0 };
  let lastRenderMs = 0, lastRenderAt = 0, raf = 0, firstLayout = true;
  let strokes = [];                        // ממוינים לפי id (= סדר יצירה)
  let images = [];                         // תמונות בעמוד (מצוירות מתחת לכתב), לפי סדר הוספה

  // מצבי עבודה (מוגדרים כאן כי הציור משתמש בהם)
  let live = null;        // הקו שנכתב עכשיו
  let eraseState = null;  // מחיקה בגרירה
  let lassoLive = null;   // לאסו שמצויר עכשיו
  let sel = null;         // בחירה פעילה
  let selDrag = null;     // הזזה / שינוי גודל של הבחירה
  let renderHide = null, renderExtra = null; // בזמן גרירת בחירה: מה להסתיר / להוסיף בדף
  let penIsDown = false, lastPenAt = -1e9;

  // מחברת ועמוד פתוחים
  let curNb = null, curPage = null, curType = 'grid', loading = true, pageDirty = false, viewOnly = false;
  const lib = { folders: new Map(), notebooks: new Map() };

  // ===================== הגדרות =====================
  const validIdx = (i) => Number.isInteger(i) && i >= 0 && i < 6;
  const settings = (() => {
    let s = {};
    try { s = JSON.parse(localStorage.getItem('machberet.settings')) || {}; } catch (e) { /* ignore */ }
    const oldIdx = [1, 2, 4][s.sizeIdx];
    const pens = {};
    for (const t of PEN_TYPES) {
      const o = (s.pens && s.pens[t]) || {};
      pens[t] = {
        color: typeof o.color === 'string' ? o.color : (t === 'fountain' && typeof s.color === 'string' ? s.color : BASE_COLORS[0]),
        sizeIdx: validIdx(o.sizeIdx) ? o.sizeIdx : (t === 'fountain' && oldIdx !== undefined ? oldIdx : PEN_DEFAULT_IDX[t]),
      };
    }
    const h = s.hl || {};
    const colors = (a) => (Array.isArray(a) ? a.filter((c) => typeof c === 'string').slice(0, 20) : []);
    const penColors = colors(s.penColors).length ? colors(s.penColors) : BASE_COLORS.concat(colors(s.custom)).slice(0, 20);
    const hlColors = colors(s.hlColors).length ? colors(s.hlColors) : HL_COLORS.slice();
    return {
      penColors, hlColors,
      lassoMode: s.lassoMode === 'whole' ? 'whole' : 'cut',
      tool: ['pen', 'hl', 'eraser', 'lasso'].includes(s.tool) ? s.tool : 'pen',
      lastInk: s.lastInk === 'hl' ? 'hl' : 'pen',
      penType: PEN_TYPES.includes(s.penType) ? s.penType : 'fountain',
      pens,
      hl: {
        color: typeof h.color === 'string' ? h.color : HL_COLORS[0],
        sizeIdx: validIdx(h.sizeIdx) ? h.sizeIdx : 3,
        mode: h.mode === 'smart' ? 'smart' : 'free',
      },
      fastInk: s.fastInk !== false,
      eraserMode: s.eraserMode === 'area' ? 'area' : 'stroke',
      eraserSize: [0, 1, 2].includes(s.eraserSize) ? s.eraserSize : 1,
      eraserDynamic: s.eraserDynamic !== false,
      dark: s.dark === true,
      barHidden: s.barHidden === true,
      nb: typeof s.nb === 'string' ? s.nb : '',
      page: typeof s.page === 'string' ? s.page : '',
      libSort: ['updated', 'name', 'created'].includes(s.libSort) ? s.libSort : 'updated',
      lastBackup: +s.lastBackup || 0,
      continuous: s.continuous === true,
    };
  })();
  mctx = settings.fastInk ? mainC.getContext('2d', { desynchronized: true }) : mainC.getContext('2d', { alpha: false });
  octx = overC.getContext('2d');
  function saveSettings() {
    try { localStorage.setItem('machberet.settings', JSON.stringify(settings)); } catch (e) { /* ignore */ }
  }
  // הכלי שהגדלים והצבעים בסרגל שייכים לו (עט או מדגש)
  function inkTool() { return settings.tool === 'pen' || settings.tool === 'hl' ? settings.tool : settings.lastInk; }
  function ink(k) { return k === 'hl' ? settings.hl : settings.pens[settings.penType]; }
  function colorList() { return inkTool() === 'hl' ? settings.hlColors : settings.penColors; }

  // ===================== אחסון (IndexedDB) =====================
  const DB = (() => {
    let dbp = null;
    function open() {
      if (!dbp) {
        dbp = new Promise((res, rej) => {
          const r = indexedDB.open('machberet', 3);
          r.onupgradeneeded = (ev) => {
            const db = r.result;
            if (ev.oldVersion < 1) db.createObjectStore('strokes', { keyPath: 'id' }).createIndex('page', 'page');
            if (ev.oldVersion < 2) {
              db.createObjectStore('folders', { keyPath: 'id' });
              db.createObjectStore('notebooks', { keyPath: 'id' });
              db.createObjectStore('thumbs', { keyPath: 'page' });
            }
            if (ev.oldVersion < 3) {
              db.createObjectStore('images', { keyPath: 'id' }).createIndex('page', 'page'); // תמונות בעמוד
              db.createObjectStore('files', { keyPath: 'id' });                              // קובצי PDF מיובאים
            }
          };
          r.onsuccess = () => res(r.result);
          r.onerror = () => rej(r.error);
        });
      }
      return dbp;
    }
    // טרנזקציה אחת; מחזיר את תוצאת הבקשה ש-fn מחזירה (אם יש), אחרי שהטרנזקציה הושלמה
    async function run(stores, mode, fn) {
      const db = await open();
      return new Promise((res, rej) => {
        let t;
        if (mode === 'readwrite') {
          try { t = db.transaction(stores, mode, { durability: 'strict' }); } catch (e) { t = db.transaction(stores, mode); }
        } else t = db.transaction(stores, mode);
        const out = fn((n) => t.objectStore(n));
        t.oncomplete = () => res(out instanceof IDBRequest ? out.result : out);
        t.onerror = () => rej(t.error);
        t.onabort = () => rej(t.error);
      });
    }
    const rec = (k) => ({ id: k.id, page: k.page, type: k.type, color: k.color, size: k.size, pts: k.pts });
    const store = (k) => (k.img ? 'images' : 'strokes');
    return {
      load: (page) => run('strokes', 'readonly', (s) => s('strokes').index('page').getAll(page)),
      loadImgs: (page) => run('images', 'readonly', (s) => s('images').index('page').getAll(page)),
      put: (list) => run(['strokes', 'images'], 'readwrite', (s) => list.forEach((k) => s(store(k)).put(k.img ? imgRec(k) : rec(k)))),
      del: (list) => run(['strokes', 'images'], 'readwrite', (s) => list.forEach((k) => s(store(k)).delete(k.id))),
      getFile: (id) => run('files', 'readonly', (s) => s('files').get(id)),
      putFile: (r) => run('files', 'readwrite', (s) => { s('files').put(r); }),
      fileIds: () => run('files', 'readonly', (s) => s('files').getAllKeys()),
      delFiles: (ids) => run('files', 'readwrite', (s) => ids.forEach((id) => s('files').delete(id))),
      putImgRecs: (list) => run('images', 'readwrite', (s) => list.forEach((r) => s('images').put(r))),
      all: (store) => run(store, 'readonly', (s) => s(store).getAll()),
      putRec: (store, r) => run(store, 'readwrite', (s) => { s(store).put(r); }),
      delRec: (store, key) => run(store, 'readwrite', (s) => { s(store).delete(key); }),
      getThumb: (page) => run('thumbs', 'readonly', (s) => s('thumbs').get(page)).then((r) => (r ? r.blob : null)),
      putThumb: (page, blob) => run('thumbs', 'readwrite', (s) => { s('thumbs').put({ page, blob }); }),
      delThumbs: (pages) => run('thumbs', 'readwrite', (s) => pages.forEach((p) => s('thumbs').delete(p))),
      // מחיקת עמודים: כל הקווים שלהם והתמונה המוקטנת
      delPages: (pages) => run(['strokes', 'images', 'thumbs'], 'readwrite', (s) => {
        for (const name of ['strokes', 'images']) {
          const st = s(name), idx = st.index('page');
          for (const p of pages) {
            const q = idx.getAllKeys(p);
            q.onsuccess = () => q.result.forEach((k) => st.delete(k));
          }
        }
        for (const p of pages) s('thumbs').delete(p);
      }),
      restoreAll: (folders, nbs, strokes, pages, imgs, files) => run(['folders', 'notebooks', 'strokes', 'thumbs', 'images', 'files'], 'readwrite', (s) => {
        folders.forEach((f) => s('folders').put(f));
        nbs.forEach((n) => s('notebooks').put(n));
        strokes.forEach((r) => s('strokes').put(r));
        imgs.forEach((r) => s('images').put(r));
        files.forEach((r) => s('files').put(r));
        pages.forEach((p) => s('thumbs').delete(p));
      }),
      putStrokeRecs: (list) => run('strokes', 'readwrite', (s) => list.forEach((r) => s('strokes').put(r))),
    };
  })();

  let saveChain = Promise.resolve();
  function persist(fn) {
    const p = saveChain.then(fn);
    saveChain = p.then(
      () => { if ($('#status').textContent.startsWith('⚠ השמירה')) setStatus(''); },
      (err) => { console.error(err); setStatus('⚠ השמירה נכשלה'); }
    );
    return p;
  }
  function setStatus(t) { $('#status').textContent = t; }

  // ===================== גאומטריית קו =====================
  // נקודות גולמיות: מערך שטוח [x, y, לחץ, ...]. הקו מצויר כאיחוד של עיגולים
  // ו"קפסולות" בין נקודות מוחלקות, כך שהעובי משתנה בצורה רציפה.
  // סוגי קו: felt (עובי אחיד), fountain (לפי לחץ), brush (לחץ + מתחדד בקצוות), pencil (מרקם), hl (מדגש)
  function brushTL(size) { return size * 6 + 6; } // אורך ההתחדדות בקצוות המכחול
  function baseRadius(st, p) {
    switch (st.type) {
      case 'felt': return st.size * 0.45;
      case 'hl': return st.size * 0.5;
      case 'pencil': return st.size * (0.5 + 0.6 * p) * 0.5;
      case 'brush': return st.size * (0.2 + 1.3 * p) * 0.5;
      default: return st.size * (0.35 + 0.95 * p) * 0.5;
    }
  }
  function radiusAt(st, p, s) {
    const r = baseRadius(st, p);
    if (st.type !== 'brush') return r;
    const tl = Math.max(0.5, Math.min(brushTL(st.size), st.total * 0.45));
    let f = Math.min(1, s / tl, (st.total - s) / tl);
    if (!(f > 0)) f = 0;
    f = f * (2 - f);
    return r * (0.08 + 0.92 * f);
  }

  const A = [0, 0, 0], B = [0, 0, 0], C = [0, 0, 0], D = [0, 0, 0];
  function sp(pts, n, i, o) { // נקודה מוחלקת i
    if (i <= 0 || i >= n - 1) {
      const j = (i <= 0 ? 0 : n - 1) * 3;
      o[0] = pts[j]; o[1] = pts[j + 1]; o[2] = pts[j + 2];
      return;
    }
    const a = (i - 1) * 3, b = i * 3, c = (i + 1) * 3;
    o[0] = 0.25 * pts[a] + 0.5 * pts[b] + 0.25 * pts[c];
    o[1] = 0.25 * pts[a + 1] + 0.5 * pts[b + 1] + 0.25 * pts[c + 1];
    o[2] = 0.25 * pts[a + 2] + 0.5 * pts[b + 2] + 0.25 * pts[c + 2];
  }

  function addDot(path, x, y, r) {
    path.moveTo(x + r, y);
    path.arc(x, y, r, 0, Math.PI * 2);
    path.closePath();
  }

  function addCapsule(path, x1, y1, r1, x2, y2, r2) {
    const dx = x2 - x1, dy = y2 - y1, d = Math.hypot(dx, dy);
    if (d > Math.abs(r1 - r2) + 1e-6) {
      const th = Math.atan2(dy, dx), al = Math.acos((r1 - r2) / d);
      const c1 = Math.cos(th + al), s1 = Math.sin(th + al), c2 = Math.cos(th - al), s2 = Math.sin(th - al);
      const ax1 = x1 + r1 * c1, ay1 = y1 + r1 * s1, bx1 = x2 + r2 * c1, by1 = y2 + r2 * s1;
      const bx2 = x2 + r2 * c2, by2 = y2 + r2 * s2, ax2 = x1 + r1 * c2, ay2 = y1 + r1 * s2;
      const area = (ax1 * by1 - bx1 * ay1) + (bx1 * by2 - bx2 * by1) + (bx2 * ay2 - ax2 * by2) + (ax2 * ay1 - ax1 * ay2);
      // כל תתי-המסלולים באותו כיוון סיבוב כדי שהמילוי יהיה איחוד בלי חורים
      if (area >= 0) { path.moveTo(ax1, ay1); path.lineTo(bx1, by1); path.lineTo(bx2, by2); path.lineTo(ax2, ay2); }
      else { path.moveTo(ax2, ay2); path.lineTo(bx2, by2); path.lineTo(bx1, by1); path.lineTo(ax1, ay1); }
      path.closePath();
    }
    addDot(path, x2, y2, r2);
  }

  // מקטע i: מנקודה מוחלקת i ל-i+1, בעקומת Catmull-Rom.
  // st = { type, size, arc (אורך מצטבר לכל נקודה, רק למכחול), total }
  function emitSegment(path, pts, n, i, st) {
    sp(pts, n, i - 1, A); sp(pts, n, i, B); sp(pts, n, i + 1, C); sp(pts, n, i + 2, D);
    const d = Math.hypot(C[0] - B[0], C[1] - B[1]);
    const steps = Math.max(1, Math.ceil(d / 2));
    const ar = st.arc;
    const s0 = ar ? ar[Math.min(i, n - 1)] : 0, s1 = ar ? ar[Math.min(i + 1, n - 1)] : 0;
    let px = B[0], py = B[1], pr = radiusAt(st, B[2], s0);
    for (let k = 1; k <= steps; k++) {
      const t = k / steps, t2 = t * t, t3 = t2 * t;
      const x = 0.5 * (2 * B[0] + (C[0] - A[0]) * t + (2 * A[0] - 5 * B[0] + 4 * C[0] - D[0]) * t2 + (3 * B[0] - A[0] - 3 * C[0] + D[0]) * t3);
      const y = 0.5 * (2 * B[1] + (C[1] - A[1]) * t + (2 * A[1] - 5 * B[1] + 4 * C[1] - D[1]) * t2 + (3 * B[1] - A[1] - 3 * C[1] + D[1]) * t3);
      const r = radiusAt(st, B[2] + (C[2] - B[2]) * t, s0 + (s1 - s0) * t);
      addCapsule(path, px, py, pr, x, y, r);
      px = x; py = y; pr = r;
    }
  }
  function startDot(path, pts, n, st) {
    sp(pts, n, 0, B);
    addDot(path, B[0], B[1], radiusAt(st, B[2], 0));
  }
  function buildPath(st) {
    const p = new Path2D();
    startDot(p, st.pts, st.n, st);
    for (let i = 0; i < st.n - 1; i++) emitSegment(p, st.pts, st.n, i, st);
    return p;
  }

  function makeStroke(rec) {
    const pts = rec.pts instanceof Float32Array ? rec.pts : Float32Array.from(rec.pts);
    const n = pts.length / 3;
    const type = rec.type || 'fountain';
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (let i = 0; i < pts.length; i += 3) {
      const x = pts[i], y = pts[i + 1];
      if (x < x0) x0 = x; if (x > x1) x1 = x;
      if (y < y0) y0 = y; if (y > y1) y1 = y;
    }
    let arc = null, total = 0;
    if (type === 'brush') {
      arc = new Float32Array(n);
      for (let i = 1; i < n; i++) arc[i] = arc[i - 1] + Math.hypot(pts[i * 3] - pts[i * 3 - 3], pts[i * 3 + 1] - pts[i * 3 - 2]);
      total = arc[n - 1];
    }
    const pad = rec.size * 1.5;
    return { id: rec.id, page: rec.page, type, color: rec.color, size: rec.size, pts, n, arc, total, bbox: [x0 - pad, y0 - pad, x1 + pad, y1 + pad], path: null };
  }

  // ===================== תמונות =====================
  // תמונה בעמוד: מלבן (x,y,w,h) כפי שמוצג, סיבוב ברבעים סביב המרכז,
  // וחיתוך [שמאל, עליון, ימין, תחתון] בשברים של התמונה המקורית. הקובץ עצמו (blob) נשמר ברשומה.
  function makeImg(r) {
    const crop = Array.isArray(r.crop) && r.crop.length === 4 ? r.crop.slice() : [0, 0, 1, 1];
    return {
      id: r.id, page: r.page, img: true, blob: r.blob, mime: r.mime || (r.blob && r.blob.type) || 'image/png',
      x: r.x, y: r.y, w: r.w, h: r.h, rot: (((r.rot || 0) % 360) + 360) % 360, crop, bbox: [r.x, r.y, r.x + r.w, r.y + r.h],
    };
  }
  function imgRec(k) { return { id: k.id, page: k.page, blob: k.blob, mime: k.mime, x: k.x, y: k.y, w: k.w, h: k.h, rot: k.rot, crop: k.crop }; }
  const bmpCache = new WeakMap(); // blob -> ImageBitmap / Promise / 'bad'
  function imgBitmap(im) { const v = im.blob && bmpCache.get(im.blob); return v && typeof v === 'object' && !(v instanceof Promise) ? v : null; }
  function decodeImg(im) {
    if (!im.blob) return Promise.resolve(null);
    let v = bmpCache.get(im.blob);
    if (!v) {
      v = createImageBitmap(im.blob).then(
        (b) => { bmpCache.set(im.blob, b); assetReady(); return b; },
        (err) => { console.error(err); bmpCache.set(im.blob, 'bad'); return null; });
      bmpCache.set(im.blob, v);
    }
    return v instanceof Promise ? v : Promise.resolve(v === 'bad' ? null : v);
  }
  function drawImg(ctx, im) {
    const b = imgBitmap(im);
    ctx.globalAlpha = 1;
    if (!b) { decodeImg(im); ctx.fillStyle = 'rgba(128,128,128,0.15)'; ctx.fillRect(im.x, im.y, im.w, im.h); return; }
    const c = im.crop, sx = c[0] * b.width, sy = c[1] * b.height, sw = (c[2] - c[0]) * b.width, sh = (c[3] - c[1]) * b.height;
    const odd = im.rot % 180 !== 0, dw = odd ? im.h : im.w, dh = odd ? im.w : im.h;
    ctx.save();
    ctx.translate(im.x + im.w / 2, im.y + im.h / 2);
    ctx.rotate(im.rot * Math.PI / 180);
    ctx.imageSmoothingEnabled = true;
    ctx.imageSmoothingQuality = 'medium';
    ctx.drawImage(b, sx, sy, sw, sh, -dw / 2, -dh / 2, dw, dh);
    ctx.restore();
  }
  function drawItem(ctx, it) { if (it.img) drawImg(ctx, it); else drawInk(ctx, it); }

  // ===================== רקע PDF (עמוד מיובא) =====================
  // העמוד שומר רק הפניה: { file, n (מספר עמוד), h (גובה ביחידות דף) }. הציור נעשה ב-pdf.js לתמונה
  // ברזולוציה שמתאימה לזום, אחת בכל פעם, ולא בזמן שהעט כותב.
  function baseH(pg) { return pg && pg.bg ? pg.bg.h : PAGE_H0; }
  function pageH(pg) { return (pg && pg.h) || baseH(pg); }
  let pdfjsP = null;
  function loadPdfjs() {
    if (!pdfjsP) {
      pdfjsP = import('./lib/pdf.min.js').then((m) => { m.GlobalWorkerOptions.workerSrc = 'lib/pdf.worker.min.js'; return m; });
      pdfjsP.catch(() => { pdfjsP = null; });
    }
    return pdfjsP;
  }
  async function fileBytes(id) {
    const r = await DB.getFile(id);
    if (!r || !r.blob) throw new Error('nofile');
    return new Uint8Array(await r.blob.arrayBuffer());
  }
  const pdfDocs = new Map(); // file id -> Promise<PDFDocumentProxy>
  function getPdf(id) {
    let p = pdfDocs.get(id);
    if (!p) {
      p = (async () => { const pdfjs = await loadPdfjs(); return pdfjs.getDocument({ data: await fileBytes(id), isEvalSupported: false }).promise; })();
      p.catch(() => pdfDocs.delete(id));
      pdfDocs.set(id, p);
    }
    return p;
  }
  const BG_KEEP = 10, bgCache = new Map(), bgQueue = [];
  let bgBusy = false, bgTimer = 0;
  function bgMaxPx(pg) { return Math.max(64, Math.min(4096, Math.sqrt(12e6 * PAGE_W / pg.bg.h))); }
  function bgEntry(pg) {
    const k = pg.bg.file + ':' + pg.bg.n;
    let e = bgCache.get(k);
    if (e) { bgCache.delete(k); bgCache.set(k, e); return e; }
    e = { pg, c: null, w: 0, want: 0, queued: false, err: false, waiters: [] };
    bgCache.set(k, e);
    for (const [kk, x] of bgCache) {
      if (bgCache.size <= BG_KEEP) break;
      if (x !== e && !x.queued && !x.waiters.length) { if (x.c) x.c.width = 0; bgCache.delete(kk); }
    }
    return e;
  }
  function bgKick(ms) { if (!bgTimer) bgTimer = setTimeout(() => { bgTimer = 0; bgPump(); }, ms); }
  function bgCanvas(pg, px) {
    const e = bgEntry(pg);
    px = Math.min(Math.ceil(px), bgMaxPx(pg));
    if (!e.err && e.w < px * 0.97 && e.want < px) {
      e.want = px;
      if (!e.queued) { e.queued = true; bgQueue.push(e); bgKick(e.c ? 150 : 0); }
    }
    return e.c;
  }
  function bgReady(pg, px) {
    const e = bgEntry(pg);
    bgCanvas(pg, px);
    if (e.err || (e.c && !e.queued)) return Promise.resolve();
    return new Promise((res) => e.waiters.push(res));
  }
  async function bgPump() {
    if (bgBusy || !bgQueue.length) return;
    if (live || penIsDown) { bgKick(300); return; }
    bgBusy = true;
    const e = bgQueue.shift();
    try {
      const doc = await getPdf(e.pg.bg.file);
      const page = await doc.getPage(e.pg.bg.n);
      const v1 = page.getViewport({ scale: 1 });
      const vp = page.getViewport({ scale: e.want / v1.width });
      const c = document.createElement('canvas');
      c.width = Math.max(1, Math.round(vp.width)); c.height = Math.max(1, Math.round(vp.height));
      const g = c.getContext('2d');
      g.fillStyle = '#fff'; g.fillRect(0, 0, c.width, c.height);
      await page.render({ canvasContext: g, viewport: vp }).promise;
      if (e.c) e.c.width = 0;
      e.c = c; e.w = c.width;
    } catch (err) { console.error(err); e.err = true; }
    e.queued = false;
    bgBusy = false;
    if (!e.err && e.w < e.want * 0.97) { e.queued = true; bgQueue.push(e); }
    else { const w = e.waiters; e.waiters = []; w.forEach((f) => f()); }
    assetReady();
    bgPump();
  }
  // vis: התחום הנראה במסך (רק בציור הראשי). אם התמונה של כל העמוד לא חדה מספיק לזום הזה,
  // מציירים מעליה את החלק שעל המסך ברזולוציה מלאה (bgDetail), אחרי שהתנועה נעצרת
  function drawBg(ctx, pg, vis) {
    if (!pg || !pg.bg) return;
    const a = Math.abs(ctx.getTransform().a), px = a * PAGE_W;
    const c = bgCanvas(pg, px);
    ctx.globalAlpha = 1;
    ctx.imageSmoothingEnabled = true;
    if (c) ctx.drawImage(c, 0, 0, PAGE_W, pg.bg.h);
    if (!vis) return;
    const e = bgEntry(pg);
    if (e.err || (c && e.w >= px * 0.97)) return; // התמונה המלאה מספיקה
    const key = pg.bg.file + ':' + pg.bg.n, y1 = Math.min(vis[3], pg.bg.h);
    if (y1 <= vis[1]) return;
    const D = bgDetail;
    if (D && D.key === key && Math.abs(D.a - a) < a * 0.01) {
      ctx.drawImage(D.c, D.x0, D.y0, D.x1 - D.x0, D.y1 - D.y0);
      if (D.x0 <= vis[0] + 1 && D.y0 <= vis[1] + 1 && D.x1 >= vis[2] - 1 && D.y1 >= y1 - 1) return; // מכסה את המסך
    }
    clearTimeout(detailTimer);
    detailTimer = setTimeout(() => renderDetail(pg, key, a, vis[0], vis[1], vis[2], y1), 250);
  }
  let bgDetail = null, detailTimer = 0, detailTask = null;
  async function renderDetail(pg, key, a, x0, y0, x1, y1) {
    if (live || penIsDown || gesture || inertia) { detailTimer = setTimeout(() => renderDetail(pg, key, a, x0, y0, x1, y1), 300); return; }
    if (curPg() !== pg || Math.abs(view.s * dpr - a) > a * 0.01) return; // התצוגה כבר השתנתה
    // קצת שוליים מסביב, כדי שגלילה קטנה לא תצריך ציור חדש
    const mx = (x1 - x0) * 0.15, my = (y1 - y0) * 0.15;
    x0 = Math.max(0, x0 - mx); y0 = Math.max(0, y0 - my); x1 = Math.min(PAGE_W, x1 + mx); y1 = Math.min(pg.bg.h, y1 + my);
    if (detailTask) { try { detailTask.cancel(); } catch (err) { /* ignore */ } }
    try {
      const doc = await getPdf(pg.bg.file), page = await doc.getPage(pg.bg.n);
      const v1 = page.getViewport({ scale: 1 }), vp = page.getViewport({ scale: a * PAGE_W / v1.width });
      const c = document.createElement('canvas');
      c.width = Math.max(1, Math.ceil((x1 - x0) * a)); c.height = Math.max(1, Math.ceil((y1 - y0) * a));
      const g = c.getContext('2d');
      g.fillStyle = '#fff'; g.fillRect(0, 0, c.width, c.height);
      const task = page.render({ canvasContext: g, viewport: vp, transform: [1, 0, 0, 1, -x0 * a, -y0 * a] });
      detailTask = task;
      await task.promise;
      if (detailTask !== task) return;
      detailTask = null;
      if (bgDetail) bgDetail.c.width = 0;
      bgDetail = { key, a, x0, y0, x1: x0 + c.width / a, y1: y0 + c.height / a, c };
      requestRender();
    } catch (err) { if (!err || err.name !== 'RenderingCancelledException') console.error(err); }
  }
  // רקע / תמונה מוכנים: מציירים מחדש
  let assetRaf = 0;
  function assetReady() {
    if (assetRaf) return;
    assetRaf = requestAnimationFrame(() => {
      assetRaf = 0;
      for (const o of others.values()) o.cache = null;
      invalidateCache(); requestRender();
    });
  }

  let lastId = 0;
  function newId() {
    let id = Date.now() * 100;
    if (id <= lastId) id = lastId + 1;
    lastId = id;
    return id;
  }

  // ===================== סגנון דיו =====================
  // עיפרון: מילוי במרקם גרגירי בצבע הקו (גרגר בגודל פיקסל מסך, לא תלוי בזום)
  const patCache = new WeakMap();
  function hexRgb(c) {
    const m = /^#?([0-9a-f]{6})$/i.exec(c);
    const v = m ? parseInt(m[1], 16) : 0;
    return [(v >> 16) & 255, (v >> 8) & 255, v & 255];
  }
  function pencilPattern(ctx, color) {
    let m = patCache.get(ctx);
    if (!m) { m = new Map(); patCache.set(ctx, m); }
    let pat = m.get(color);
    if (!pat) {
      const c = document.createElement('canvas');
      c.width = c.height = 64;
      const g = c.getContext('2d'), img = g.createImageData(64, 64), [r, gg, b] = hexRgb(color);
      let seed = 1234567;
      const rnd = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x7fffffff; };
      for (let i = 0; i < img.data.length; i += 4) {
        const v = rnd();
        img.data[i] = r; img.data[i + 1] = gg; img.data[i + 2] = b;
        img.data[i + 3] = v < 0.5 ? 235 : v < 0.75 ? 150 : v < 0.88 ? 70 : 0;
      }
      g.putImageData(img, 0, 0);
      pat = ctx.createPattern(c, 'repeat');
      m.set(color, pat);
    }
    const a = ctx.getTransform().a || 1, q = dpr / a;
    if (pat.setTransform) pat.setTransform(new DOMMatrix([q, 0, 0, q, 0, 0]));
    return pat;
  }
  // דף כהה: דיו שחור/אפור כהה מוצג בהיר (רק בתצוגה, הצבע השמור לא משתנה)
  let inkDark = false;
  const darkMap = new Map();
  function shownColor(c) {
    if (!inkDark) return c;
    let m = darkMap.get(c);
    if (m === undefined) {
      const [r, g, b] = hexRgb(c), mx = Math.max(r, g, b), mn = Math.min(r, g, b), l = (mx + mn) / 510;
      if (mx - mn < 48 && l < 0.45) {
        const v = Math.round(236 - l * 200).toString(16).padStart(2, '0');
        m = '#' + v + v + v;
      } else m = c;
      darkMap.set(c, m);
    }
    return m;
  }
  function applyInk(ctx, st) {
    const c = shownColor(st.color);
    if (st.type === 'hl') { ctx.globalAlpha = HL_ALPHA; ctx.fillStyle = c; }
    else { ctx.globalAlpha = 1; ctx.fillStyle = st.type === 'pencil' ? pencilPattern(ctx, c) : c; }
  }
  function drawInk(ctx, st) {
    if (!st.path) st.path = buildPath(st);
    applyInk(ctx, st);
    ctx.fill(st.path);
  }

  // ===================== ציור =====================
  function setWorld(ctx, v) { ctx.setTransform(dpr * v.s, 0, 0, dpr * v.s, dpr * v.ox, dpr * v.oy); }

  function fillWorld(ctx, path, st) {
    setWorld(ctx, rendered);
    ctx.save();
    ctx.beginPath(); ctx.rect(0, 0, PAGE_W, PAGE_H); ctx.clip();
    applyInk(ctx, st);
    ctx.fill(path);
    ctx.restore();
  }

  let overlayDirty = false;
  function clearOverlay() {
    if (!overlayDirty) return;
    octx.setTransform(1, 0, 0, 1, 0, 0);
    octx.clearRect(0, 0, overC.width, overC.height);
    overlayDirty = false;
  }

  // רקע הדף לפי הסוג (ריק / שורות / משבצות), בתחום הנראה בלבד
  function drawPaper(ctx, type, dark, lw, vx0, vy0, vx1, vy1) {
    const P = dark ? PAPER.dark : PAPER.light;
    ctx.globalAlpha = 1;
    ctx.fillStyle = P.page;
    ctx.fillRect(0, 0, PAGE_W, PAGE_H);
    if (type === 'blank') return;
    ctx.lineWidth = lw;
    ctx.beginPath();
    const x0 = Math.max(0, vx0), x1 = Math.min(PAGE_W, vx1), y0 = Math.max(0, vy0), y1 = Math.min(PAGE_H, vy1);
    if (type === 'eng') {
      const lines = (step, major) => {
        ctx.beginPath();
        for (let x = Math.ceil(x0 / step) * step; x <= x1; x += step) {
          if (x <= 0 || x >= PAGE_W || (!major && x % ENG_MAJOR === 0)) continue;
          ctx.moveTo(x, y0); ctx.lineTo(x, y1);
        }
        for (let y = Math.ceil(y0 / step) * step; y <= y1; y += step) {
          if (y <= 0 || y >= PAGE_H || (!major && y % ENG_MAJOR === 0)) continue;
          ctx.moveTo(x0, y); ctx.lineTo(x1, y);
        }
      };
      lines(ENG_MINOR, false); ctx.strokeStyle = P.engMinor; ctx.lineWidth = lw; ctx.stroke();
      lines(ENG_MAJOR, true); ctx.strokeStyle = P.engMajor; ctx.lineWidth = lw * 1.5; ctx.stroke();
      return;
    }
    if (type === 'cornell') {
      for (let y = LINE_TOP + Math.max(0, Math.ceil((vy0 - LINE_TOP) / LINE_GAP)) * LINE_GAP; y <= vy1 && y < PAGE_H - 30; y += LINE_GAP) {
        ctx.moveTo(x0, y); ctx.lineTo(x1, y);
      }
      ctx.strokeStyle = P.line;
      ctx.stroke();
      ctx.beginPath();
      ctx.moveTo(0, LINE_TOP - LINE_GAP); ctx.lineTo(PAGE_W, LINE_TOP - LINE_GAP); // כותרת
      ctx.moveTo(CORNELL_X, LINE_TOP - LINE_GAP); ctx.lineTo(CORNELL_X, PAGE_H - 270);  // עמודת הערות
      ctx.moveTo(0, PAGE_H - 270); ctx.lineTo(PAGE_W, PAGE_H - 270);                      // סיכום
      ctx.strokeStyle = P.div;
      ctx.lineWidth = lw * 2;
      ctx.stroke();
      return;
    }
    if (type === 'lines') {
      for (let y = LINE_TOP + Math.max(0, Math.ceil((vy0 - LINE_TOP) / LINE_GAP)) * LINE_GAP; y <= vy1 && y < PAGE_H - 30; y += LINE_GAP) {
        ctx.moveTo(x0, y); ctx.lineTo(x1, y);
      }
      ctx.strokeStyle = P.line;
      ctx.stroke();
      if (MARGIN_X >= vx0 && MARGIN_X <= vx1) {
        ctx.beginPath();
        ctx.moveTo(MARGIN_X, Math.max(0, vy0)); ctx.lineTo(MARGIN_X, Math.min(PAGE_H, vy1));
        ctx.strokeStyle = P.margin;
        ctx.stroke();
      }
      return;
    }
    for (let x = Math.ceil(vx0 / GRID) * GRID; x <= vx1; x += GRID) {
      if (x <= 0 || x >= PAGE_W) continue;
      ctx.moveTo(x, vy0); ctx.lineTo(x, vy1);
    }
    for (let y = Math.ceil(vy0 / GRID) * GRID; y <= vy1; y += GRID) {
      if (y <= 0 || y >= PAGE_H) continue;
      ctx.moveTo(vx0, y); ctx.lineTo(vx1, y);
    }
    ctx.strokeStyle = P.grid;
    ctx.stroke();
  }

  // דף + קווים, בתחום הנראה בלבד
  function drawPage(ctx, gridLW, vx0, vy0, vx1, vy1) {
    drawPaper(ctx, curType, settings.dark, gridLW, vx0, vy0, vx1, vy1);
    drawBg(ctx, curPg(), ctx === mctx ? [vx0, vy0, vx1, vy1] : null);
    ctx.save();
    ctx.beginPath(); ctx.rect(0, 0, PAGE_W, PAGE_H); ctx.clip();
    const vis = (b) => !(b[2] < vx0 || b[0] > vx1 || b[3] < vy0 || b[1] > vy1);
    for (const im of images) {
      if (renderHide && renderHide.has(im.id)) continue;
      if (vis(im.bbox)) drawImg(ctx, im);
    }
    for (const st of strokes) {
      if (renderHide && renderHide.has(st.id)) continue;
      if (vis(st.bbox)) drawInk(ctx, st);
    }
    if (renderExtra) for (const st of renderExtra) if (vis(st.bbox)) drawInk(ctx, st);
    ctx.restore();
  }

  function drawDesk(ctx, s) {
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.globalAlpha = 1;
    ctx.fillStyle = settings.dark ? PAPER.dark.desk : PAPER.light.desk;
    ctx.fillRect(0, 0, mainC.width, mainC.height);
    setWorld(ctx, view);
    ctx.fillStyle = 'rgba(0,0,0,0.10)';
    ctx.fillRect(2 / s, 3 / s, PAGE_W, PAGE_H);
  }

  // ===================== גלילה רציפה בין עמודים (אופציה בתפריט) =====================
  // העמוד הפעיל (curPage) נשאר במערכת הצירים הרגילה; שאר העמודים מצוירים מעליו/מתחתיו לקריאה,
  // ונגיעה בעט בעמוד אחר (או גלילה אליו) הופכת אותו לפעיל בלי שהמסך זז.
  const GAP = 30;
  const others = new Map(); // id -> { strokes, cache }
  const contOn = () => !!(settings.continuous && curNb && !loading);
  function withH(h, fn) { const sv = PAGE_H; PAGE_H = h; try { return fn(); } finally { PAGE_H = sv; } }
  function stackPages() {
    const out = [];
    let y = 0, cur = 0;
    for (const pg of curNb.pages) {
      const h = pg.id === curPage ? PAGE_H : pageH(pg);
      out.push({ pg, y, h });
      if (pg.id === curPage) cur = y;
      y += h + GAP;
    }
    for (const o of out) o.rel = o.y - cur;
    return out;
  }
  function loadOther(id) {
    if (others.has(id)) return;
    const info = { strokes: null, images: [], cache: null };
    others.set(id, info);
    saveChain.then(() => Promise.all([DB.load(id), DB.loadImgs(id)])).then(([recs, ims]) => {
      if (others.get(id) !== info) return;
      info.images = ims.map(makeImg);
      info.strokes = recs.map(makeStroke);
      requestRender();
    }).catch((err) => { console.error(err); others.delete(id); });
  }
  function otherCache(o, info) {
    if (info.cache) return info.cache;
    const cs = Math.min(1, 4096 / o.h), c = document.createElement('canvas');
    c.width = Math.ceil(PAGE_W * cs); c.height = Math.ceil(o.h * cs);
    const g = c.getContext('2d');
    g.setTransform(cs, 0, 0, cs, 0, 0);
    withH(o.h, () => {
      drawPaper(g, o.pg.type, settings.dark, dpr / cs, 0, 0, PAGE_W, o.h);
      drawBg(g, o.pg);
      g.save(); g.beginPath(); g.rect(0, 0, PAGE_W, o.h); g.clip();
      for (const im of info.images) drawImg(g, im);
      for (const st of info.strokes) drawInk(g, st);
      g.restore();
    });
    info.cache = c;
    return c;
  }
  function drawOthers(ctx, s, fast) {
    if (!contOn()) return;
    const vy0 = -view.oy / s, vy1 = (H - view.oy) / s;
    const vx0 = Math.max(0, -view.ox / s), vx1 = Math.min(PAGE_W, (W - view.ox) / s);
    for (const o of stackPages()) {
      if (o.pg.id === curPage || o.rel > vy1 || o.rel + o.h < vy0) continue;
      if (!others.has(o.pg.id)) loadOther(o.pg.id);
      const info = others.get(o.pg.id);
      setWorld(ctx, view);
      ctx.translate(0, o.rel);
      ctx.globalAlpha = 1;
      ctx.fillStyle = 'rgba(0,0,0,0.10)';
      ctx.fillRect(2 / s, 3 / s, PAGE_W, o.h);
      if (fast && info.strokes) { ctx.imageSmoothingEnabled = true; ctx.drawImage(otherCache(o, info), 0, 0, PAGE_W, o.h); continue; }
      const ly0 = Math.max(0, vy0 - o.rel), ly1 = Math.min(o.h, vy1 - o.rel);
      withH(o.h, () => {
        drawPaper(ctx, o.pg.type, settings.dark, 1 / s, vx0, ly0, vx1, ly1);
        drawBg(ctx, o.pg);
        if (!info.strokes) return;
        ctx.save(); ctx.beginPath(); ctx.rect(0, 0, PAGE_W, o.h); ctx.clip();
        for (const im of info.images) { const b = im.bbox; if (!(b[2] < vx0 || b[0] > vx1 || b[3] < ly0 || b[1] > ly1)) drawImg(ctx, im); }
        for (const st of info.strokes) { const b = st.bbox; if (!(b[2] < vx0 || b[0] > vx1 || b[3] < ly0 || b[1] > ly1)) drawInk(ctx, st); }
        ctx.restore();
      });
    }
    setWorld(ctx, view);
  }
  function pruneOthers() {
    const i = curNb.pages.findIndex((p) => p.id === curPage);
    for (const id of [...others.keys()]) {
      const j = curNb.pages.findIndex((p) => p.id === id);
      if (j < 0 || Math.abs(j - i) > 2) others.delete(id);
    }
  }
  // הופך עמוד אחר לפעיל; התצוגה מתוקנת כך שהמסך לא זז
  function setActive(id) {
    if (!contOn() || busy() || id === curPage) return false;
    const info = others.get(id), o = stackPages().find((x) => x.pg.id === id);
    if (!info || !info.strokes || !o) return false;
    clearSelection();
    saveCurThumb();
    others.set(curPage, { strokes, images, cache: null });
    others.delete(id);
    const pg = o.pg;
    curPage = pg.id; curType = pg.type; PAGE_H = pageH(pg); strokes = info.strokes; images = info.images; pageDirty = false;
    settings.page = pg.id; saveSettings();
    if (curNb.last !== pg.id) { curNb.last = pg.id; saveRec('notebooks', curNb); }
    let h = histories.get(pg.id);
    if (!h) { h = { u: [], r: [] }; histories.set(pg.id, h); }
    undoStack = h.u; redoStack = h.r;
    updateUndoUI();
    view.oy += o.rel * view.s;
    invalidateCache(); pruneOthers(); updatePageUI();
    if (!pagesPanel.hidden) renderPagesPanel();
    render();
    return true;
  }
  // בסוף גלילה: העמוד שבמרכז המסך הופך לפעיל (וגם מספר העמוד בסרגל מתעדכן)
  function followScroll() {
    if (!contOn() || busy()) return;
    const cy = (H / 2 - view.oy) / view.s;
    if (cy >= -GAP / 2 && cy <= PAGE_H + GAP / 2) return;
    for (const o of stackPages()) {
      if (o.pg.id !== curPage && cy >= o.rel - GAP / 2 && cy <= o.rel + o.h + GAP / 2) {
        if (!setActive(o.pg.id)) { loadOther(o.pg.id); setTimeout(followScroll, 300); }
        return;
      }
    }
  }

  // ציור מלא וחד של מה שעל המסך
  function render() {
    if (raf) { cancelAnimationFrame(raf); raf = 0; }
    if (fastRaf) { cancelAnimationFrame(fastRaf); fastRaf = 0; }
    const t0 = performance.now();
    const ctx = mctx, s = view.s, ox = view.ox, oy = view.oy;
    drawDesk(ctx, s);
    drawOthers(ctx, s, false);
    const vx0 = Math.max(0, -ox / s), vy0 = Math.max(0, -oy / s);
    const vx1 = Math.min(PAGE_W, (W - ox) / s), vy1 = Math.min(PAGE_H, (H - oy) / s);
    if (vx1 > vx0 && vy1 > vy0) {
      drawPage(ctx, 1 / s, vx0, vy0, vx1, vy1);
      if (live && live.n && live.type !== 'hl') { // מדגש בזמן כתיבה מצויר בשכבה העליונה
        const p = new Path2D();
        startDot(p, live.pts, live.n, live);
        for (let i = 0; i < live.next; i++) emitSegment(p, live.pts, live.n, i, live);
        ctx.save();
        ctx.beginPath(); ctx.rect(0, 0, PAGE_W, PAGE_H); ctx.clip();
        applyInk(ctx, live);
        ctx.fill(p);
        ctx.restore();
      }
    }
    rendered = { s, ox, oy };
    fromCache = false;
    lastRenderAt = performance.now();
    lastRenderMs = lastRenderAt - t0;
    if (sel) drawSelOverlay();
  }

  // תמונה של הדף כולו, להזזה וזום חלקים (מציירים ממנה בזמן תנועה, ובסוף ציור חד)
  let cache = null, cacheValid = false, cacheScale = 1, cacheTimer = 0, fromCache = false, fastRaf = 0;
  function buildCache() {
    const cs = Math.min(4096 / PAGE_H, Math.max(1, fitScale() * dpr * 1.25));
    if (!cache) cache = document.createElement('canvas');
    const w = Math.ceil(PAGE_W * cs), h = Math.ceil(PAGE_H * cs);
    if (cache.width !== w || cache.height !== h) { cache.width = w; cache.height = h; }
    cacheScale = cs;
    const c = cache.getContext('2d');
    c.setTransform(cs, 0, 0, cs, 0, 0);
    drawPage(c, dpr / cs, 0, 0, PAGE_W, PAGE_H);
    cacheValid = true;
  }
  function cacheAdd(st) {
    if (!cacheValid) return;
    const c = cache.getContext('2d');
    c.setTransform(cacheScale, 0, 0, cacheScale, 0, 0);
    c.save();
    c.beginPath(); c.rect(0, 0, PAGE_W, PAGE_H); c.clip();
    drawInk(c, st);
    c.restore();
  }
  function invalidateCache() { cacheValid = false; scheduleCache(); }
  function scheduleCache() {
    clearTimeout(cacheTimer);
    cacheTimer = setTimeout(() => {
      if (cacheValid) return;
      if (live || eraseState || lassoLive || selDrag || gesture || inertia) { scheduleCache(); return; }
      buildCache();
    }, 700);
  }
  function drawFromCache() {
    fastRaf = 0;
    if (!cacheValid) buildCache();
    const ctx = mctx, s = view.s;
    drawDesk(ctx, s);
    drawOthers(ctx, s, true);
    ctx.imageSmoothingEnabled = true;
    ctx.drawImage(cache, 0, 0, PAGE_W, PAGE_H);
    rendered = { s, ox: view.ox, oy: view.oy };
    fromCache = true;
    if (sel) drawSelOverlay();
  }

  function requestRender() {
    if (fastRaf) { cancelAnimationFrame(fastRaf); fastRaf = 0; }
    if (!raf) raf = requestAnimationFrame(() => { raf = 0; render(); });
  }
  function ensureRendered() {
    if (raf || fastRaf || fromCache || rendered.s !== view.s || rendered.ox !== view.ox || rendered.oy !== view.oy) render();
  }

  // בזמן גלילה/זום: אם ציור מלא מהיר, מציירים מלא כל פריים; אחרת מציירים מהתמונה השמורה
  function viewChanged() {
    if (lastRenderMs < 8) { requestRender(); return; }
    if (raf) { cancelAnimationFrame(raf); raf = 0; }
    if (!fastRaf) fastRaf = requestAnimationFrame(drawFromCache);
  }

  // ===================== תצוגה (זום וגלילה) =====================
  function fitScale() { return (W - 2 * MARGIN) / PAGE_W; }
  function minScale() { return Math.min(fitScale(), (H - 2 * MARGIN) / PAGE_H); }
  function maxScale() { return fitScale() * 6; }
  function clampScale(s) { return Math.max(minScale(), Math.min(maxScale(), s)); }
  function clampView() {
    const pw = PAGE_W * view.s, ph = PAGE_H * view.s;
    if (pw + 2 * MARGIN <= W) view.ox = (W - pw) / 2;
    else view.ox = Math.max(W - pw - MARGIN, Math.min(MARGIN, view.ox));
    // בגלילה רציפה הגבולות הם של כל העמודים יחד
    let top = 0, bottom = PAGE_H;
    if (contOn()) { const sp = stackPages(), l = sp[sp.length - 1]; top = sp[0].rel; bottom = l.rel + l.h; }
    const th = (bottom - top) * view.s;
    if (ph + 2 * MARGIN <= H && th === ph) view.oy = (H - ph) / 2;
    else if (th + 2 * MARGIN <= H) view.oy = (H - th) / 2 - top * view.s;
    else view.oy = Math.max(H - bottom * view.s - MARGIN, Math.min(MARGIN - top * view.s, view.oy));
  }
  function fitWidth() {
    view.s = fitScale(); view.ox = MARGIN; view.oy = MARGIN;
    clampView();
  }

  function resize() {
    const r = stage.getBoundingClientRect();
    let cx = 0, cy = 0;
    if (!firstLayout) { cx = (W / 2 - view.ox) / view.s; cy = (H / 2 - view.oy) / view.s; }
    W = r.width; H = r.height; stageLeft = r.left; stageTop = r.top;
    dpr = window.devicePixelRatio || 1;
    for (const c of [mainC, overC]) { c.width = Math.round(W * dpr); c.height = Math.round(H * dpr); }
    overlayDirty = false;
    invalidateCache();
    if (firstLayout) { fitWidth(); firstLayout = false; }
    else {
      view.s = clampScale(view.s);
      view.ox = W / 2 - cx * view.s; view.oy = H / 2 - cy * view.s;
      clampView();
    }
    render();
  }
  window.addEventListener('resize', resize);

  const wx = (cx) => (cx - stageLeft - view.ox) / view.s;
  const wy = (cy) => (cy - stageTop - view.oy) / view.s;

  // ===================== ביטול / שחזור =====================
  let undoStack = [], redoStack = [];     // לכל עמוד היסטוריה משלו (histories)
  const histories = new Map();
  function insertSorted(st) {
    let lo = 0, hi = strokes.length;
    while (lo < hi) { const m = (lo + hi) >> 1; if (strokes[m].id < st.id) lo = m + 1; else hi = m; }
    strokes.splice(lo, 0, st);
    return lo === strokes.length - 1;
  }
  // רשימות פעולה מכילות גם קווים וגם תמונות (it.img); תמונות נשמרות בנפרד ומצוירות מתחת לכתב
  function addStrokes(list, noRender) {
    if (!list.length) return;
    pageDirty = true;
    for (const st of list) {
      if (st.img) {
        let i = images.length;
        while (i > 0 && images[i - 1].id > st.id) i--;
        images.splice(i, 0, st);
        invalidateCache();
      } else if (insertSorted(st)) cacheAdd(st);
      else invalidateCache();
    }
    persist(() => DB.put(list));
    if (!noRender) requestRender();
  }
  function removeStrokes(list) {
    if (!list.length) return;
    pageDirty = true;
    const ids = new Set(list.map((s) => s.id));
    strokes = strokes.filter((s) => !ids.has(s.id));
    if (list.some((s) => s.img)) images = images.filter((s) => !ids.has(s.id));
    invalidateCache();
    persist(() => DB.del(list));
    requestRender();
  }
  function pushAction(a) {
    undoStack.push(a);
    if (undoStack.length > 500) undoStack.shift();
    redoStack.length = 0;
    updateUndoUI();
  }
  function commit(a, alreadyDrawn) {
    removeStrokes(a.remove);
    addStrokes(a.add, alreadyDrawn);
    pushAction(a);
    maybeGrow(a.add);
  }
  function busy() { return live || eraseState || lassoLive || selDrag; }
  function undo() {
    if (busy() || viewOnly || loading) return;
    const a = undoStack.pop(); if (!a) return;
    clearSelection();
    removeStrokes(a.add); addStrokes(a.remove);
    redoStack.push(a); updateUndoUI();
  }
  function redo() {
    if (busy() || viewOnly || loading) return;
    const a = redoStack.pop(); if (!a) return;
    clearSelection();
    removeStrokes(a.remove); addStrokes(a.add);
    undoStack.push(a); updateUndoUI();
  }
  function updateUndoUI() {
    $('#undo').disabled = !undoStack.length;
    $('#redo').disabled = !redoStack.length;
  }

  // ===================== עט ומדגש: כתיבה =====================
  function pressureOf(e) {
    if (e.pointerType === 'mouse') return 0.5;
    let p = e.pressure;
    if (!(p > 0)) p = live && live.n ? live.pts[live.n * 3 - 1] : 0.3;
    return Math.min(1, p);
  }

  function addLivePoint(x, y, p) {
    const L = live;
    if (L.n > 0) {
      const j = (L.n - 1) * 3, dx = x - L.pts[j], dy = y - L.pts[j + 1], d2 = dx * dx + dy * dy;
      if (d2 < MIN_DIST * MIN_DIST) return;
      L.arc.push(L.arc[L.n - 1] + Math.sqrt(d2));
    } else L.arc.push(0);
    L.pts.push(x, y, p);
    L.n++;
  }

  // מצייר על הקנבס הראשי רק מקטעים סופיים (שלא ישתנו), ואת "הזנב" על שכבה עליונה
  function liveDraw() {
    const L = live;
    if (L.type === 'hl') { liveDrawHL(); return; }
    const p = new Path2D();
    let any = false;
    const brush = L.type === 'brush', tl = brushTL(L.size);
    // במכחול: הקטע האחרון (באורך ההתחדדות) נשאר בשכבה העליונה עד הרמת העט
    while (L.next <= L.n - 4 && (!brush || L.arc[L.n - 1] - L.arc[L.next + 1] > tl)) {
      emitSegment(p, L.pts, L.n, L.next, L); L.next++; any = true;
    }
    if (any) fillWorld(mctx, p, L);

    clearOverlay();
    const k = Math.max(0, L.next - 2);
    const tail = L.pts.slice(k * 3);
    const tn = tail.length / 3;
    if (tn - 1 > L.next - k) {
      const tst = { type: L.type, size: L.size, color: L.color, arc: brush ? L.arc.slice(k) : null, total: Infinity };
      const t = new Path2D();
      for (let i = L.next - k; i < tn - 1; i++) emitSegment(t, tail, tn, i, tst);
      fillWorld(octx, t, L);
      overlayDirty = true;
    }
  }

  // מדגש חכם: פס ישר מההתחלה לסוף (כמעט אופקי = אופקי בדיוק)
  function smartPts(L) {
    const x0 = L.pts[0], y0 = L.pts[1], j = (L.n - 1) * 3;
    const x1 = L.pts[j];
    let y1 = L.pts[j + 1];
    if (Math.abs(y1 - y0) < Math.abs(x1 - x0) * Math.tan(10 * Math.PI / 180)) y1 = y0;
    return [x0, y0, 0.5, x1, y1, 0.5];
  }
  // מדגש שקוף: מציירים את כולו בכל פעם בשכבה העליונה (כדי שלא ייווצרו כתמים כהים בחפיפות)
  function liveDrawHL() {
    const L = live;
    let p;
    if (L.smart) {
      p = buildPath(makeStroke({ type: 'hl', size: L.size, pts: smartPts(L) }));
    } else {
      while (L.next <= L.n - 4) { emitSegment(L.hlPath, L.pts, L.n, L.next, L); L.next++; }
      p = new Path2D(L.hlPath);
      for (let i = L.next; i < L.n - 1; i++) emitSegment(p, L.pts, L.n, i, L);
    }
    overlayDirty = true;
    clearOverlay();
    fillWorld(octx, p, L);
    overlayDirty = true;
  }

  function startStroke(e, x, y) {
    const hl = settings.tool === 'hl';
    const k = ink(settings.tool);
    live = {
      pointerId: e.pointerId, pts: [], arc: [], n: 0, next: 0, total: Infinity,
      type: hl ? 'hl' : settings.penType, color: k.color,
      size: hl ? HL_SIZES[k.sizeIdx] : PEN_SIZES[k.sizeIdx],
      smart: hl && settings.hl.mode === 'smart',
      hlPath: null,
    };
    addLivePoint(x, y, pressureOf(e));
    const p = new Path2D();
    startDot(p, live.pts, live.n, live);
    if (hl) { live.hlPath = p; liveDrawHL(); }
    else fillWorld(mctx, p, live);
  }

  function finishStroke() {
    const L = live;
    live = null;
    if (L.type === 'hl') {
      // שרבוט הלוך-חזור במדגש מוחק, כמו בעט (לפי התנועה עצמה, גם במצב חכם)
      const raw = makeStroke({ type: 'hl', size: L.size, pts: L.pts });
      if (isScribble(raw)) {
        const hits = scribbleHits(raw).filter((s) => s.type === 'hl'); // מדגש מוחק רק מדגש, לא כתב
        if (hits.length) { overlayDirty = true; clearOverlay(); commit({ add: [], remove: hits }); requestRender(); return; }
      }
      const st = makeStroke({ id: newId(), page: curPage, type: 'hl', color: L.color, size: L.size, pts: Float32Array.from(L.smart ? smartPts(L) : L.pts) });
      overlayDirty = true; clearOverlay();
      fillWorld(mctx, (st.path = buildPath(st)), st);
      commit({ add: [st], remove: [] }, true);
      return;
    }
    const st = makeStroke({ id: newId(), page: curPage, type: L.type, color: L.color, size: L.size, pts: Float32Array.from(L.pts) });
    let p;
    if (st.type === 'brush' && st.total * 0.45 < brushTL(st.size)) p = buildPath(st); // קו קצר: ההתחדדות משתנה, מציירים מחדש
    else {
      p = new Path2D();
      for (let i = L.next; i < L.n - 1; i++) emitSegment(p, st.pts, st.n, i, st);
    }
    fillWorld(mctx, p, st);
    clearOverlay();
    if (isScribble(st)) {
      const hits = scribbleHits(st);
      if (hits.length) { commit({ add: [], remove: hits }); requestRender(); return; }
    }
    commit({ add: [st], remove: [] }, true);
  }

  // ===================== מחק =====================
  function ptSegDist(px, py, x1, y1, x2, y2) {
    const dx = x2 - x1, dy = y2 - y1, l2 = dx * dx + dy * dy;
    let t = l2 ? ((px - x1) * dx + (py - y1) * dy) / l2 : 0;
    t = Math.max(0, Math.min(1, t));
    return Math.hypot(px - x1 - t * dx, py - y1 - t * dy);
  }
  function cross(ax, ay, bx, by, cx, cy) { return (bx - ax) * (cy - ay) - (by - ay) * (cx - ax); }
  function segSegDist(ax, ay, bx, by, cx, cy, dx, dy) {
    const d1 = cross(ax, ay, bx, by, cx, cy), d2 = cross(ax, ay, bx, by, dx, dy);
    const d3 = cross(cx, cy, dx, dy, ax, ay), d4 = cross(cx, cy, dx, dy, bx, by);
    if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0))) return 0;
    return Math.min(ptSegDist(ax, ay, cx, cy, dx, dy), ptSegDist(bx, by, cx, cy, dx, dy),
      ptSegDist(cx, cy, ax, ay, bx, by), ptSegDist(dx, dy, ax, ay, bx, by));
  }
  function hitStrokeSeg(st, x1, y1, x2, y2, R) {
    const b = st.bbox;
    if (Math.max(x1, x2) + R < b[0] || Math.min(x1, x2) - R > b[2] || Math.max(y1, y2) + R < b[1] || Math.min(y1, y2) - R > b[3]) return false;
    const r = R + st.size * 0.65, p = st.pts;
    if (st.n === 1) return ptSegDist(p[0], p[1], x1, y1, x2, y2) < r;
    for (let i = 0; i < st.n - 1; i++) {
      const a = i * 3;
      if (segSegDist(p[a], p[a + 1], p[a + 3], p[a + 4], x1, y1, x2, y2) < r) return true;
    }
    return false;
  }
  // מעקב לביטול: קווים מקוריים שנמחקו, וחלקים חדשים שנוצרו מחיתוך (חלק שנמחק שוב פשוט נעלם)
  function eraseTrackRemoved(st) {
    if (eraseState.added.has(st.id)) eraseState.added.delete(st.id);
    else eraseState.removedOrig.set(st.id, st);
  }

  // מחיקת שטח: מחזיר את חלקי הקו שנשארים, או null אם לא נמחק ממנו כלום
  function cutStroke(st, x1, y1, x2, y2, R) {
    const p = st.pts, n = st.n, dense = [];
    const step = Math.max(0.5, R / 4);
    for (let i = 0; i < n; i++) {
      const a = i * 3;
      if (i > 0) {
        const b = a - 3, dx = p[a] - p[b], dy = p[a + 1] - p[b + 1], d = Math.hypot(dx, dy);
        // מוסיפים נקודות ביניים רק ליד המחק, כדי שהחיתוך יהיה מדויק
        if (d > step && segSegDist(p[b], p[b + 1], p[a], p[a + 1], x1, y1, x2, y2) < R + st.size * 2) {
          const k = Math.ceil(d / step);
          for (let j = 1; j < k; j++) {
            const t = j / k;
            dense.push(p[b] + dx * t, p[b + 1] + dy * t, p[b + 2] + (p[a + 2] - p[b + 2]) * t);
          }
        }
      }
      dense.push(p[a], p[a + 1], p[a + 2]);
    }
    const pieces = [];
    let cur = [], removedAny = false;
    for (let i = 0; i < dense.length; i += 3) {
      const r = baseRadius(st, dense[i + 2]);
      if (ptSegDist(dense[i], dense[i + 1], x1, y1, x2, y2) < R + r) {
        removedAny = true;
        if (cur.length) { pieces.push(cur); cur = []; }
      } else cur.push(dense[i], dense[i + 1], dense[i + 2]);
    }
    if (cur.length) pieces.push(cur);
    if (!removedAny) return null;
    return pieces.filter((pc) => pc.length >= 6).map((pc) =>
      makeStroke({ id: newId(), page: st.page, type: st.type, color: st.color, size: st.size, pts: Float32Array.from(pc) }));
  }

  function eraseSeg(x1, y1, x2, y2) {
    const R = eraseState.R / view.s, hits = [];
    for (const st of strokes) if (hitStrokeSeg(st, x1, y1, x2, y2, R)) hits.push(st);
    if (!hits.length) return;
    if (settings.eraserMode === 'stroke') {
      hits.forEach(eraseTrackRemoved);
      removeStrokes(hits);
      return;
    }
    const gone = [], pieces = [];
    for (const st of hits) {
      const res = cutStroke(st, x1, y1, x2, y2, R);
      if (res) { gone.push(st); pieces.push(...res); }
    }
    if (!gone.length) return;
    gone.forEach(eraseTrackRemoved);
    removeStrokes(gone);
    for (const pc of pieces) eraseState.added.set(pc.id, pc);
    addStrokes(pieces, true);
  }

  // מחק דינמי: בתנועה מהירה גדל, באיטית חוזר לגודל שנבחר
  function updateEraserRadius(e) {
    const E = eraseState, base = ERASER_SIZES[settings.eraserSize];
    const dt = e.timeStamp - E.lt;
    if (dt > 0) {
      const v = Math.hypot(e.clientX - E.lsx, e.clientY - E.lsy) / dt;
      E.v = E.v * 0.7 + v * 0.3;
    }
    E.lsx = e.clientX; E.lsy = e.clientY; E.lt = e.timeStamp;
    if (!settings.eraserDynamic) { E.R = base; return; }
    const max = Math.max(base * 1.6, ERASER_DYN_MAX);
    const k = Math.min(1, Math.max(0, (E.v - 0.3) / 1.0)); // 0 באיטי, 1 במהיר
    E.R = base + (max - base) * k;
  }

  function drawEraserCursor(cx, cy) {
    clearOverlay();
    octx.setTransform(dpr, 0, 0, dpr, 0, 0);
    octx.beginPath();
    octx.arc(cx - stageLeft, cy - stageTop, eraseState ? eraseState.R : ERASER_SIZES[settings.eraserSize], 0, Math.PI * 2);
    octx.lineWidth = 1.5;
    octx.strokeStyle = 'rgba(80,80,80,0.7)';
    octx.stroke();
    overlayDirty = true;
  }

  // ===================== שרבוט למחיקה =====================
  // שרבוט = תנועה הלוך-חזור (לפחות 4 שינויי כיוון) לאורך הציר הראשי של הקו
  function isScribble(st) {
    const n = st.n, p = st.pts;
    if (n < 10) return false;
    let mx = 0, my = 0;
    for (let i = 0; i < n; i++) { mx += p[i * 3]; my += p[i * 3 + 1]; }
    mx /= n; my /= n;
    let sxx = 0, syy = 0, sxy = 0;
    for (let i = 0; i < n; i++) {
      const dx = p[i * 3] - mx, dy = p[i * 3 + 1] - my;
      sxx += dx * dx; syy += dy * dy; sxy += dx * dy;
    }
    const th = 0.5 * Math.atan2(2 * sxy, sxx - syy), ux = Math.cos(th), uy = Math.sin(th);
    let lo = Infinity, hi = -Infinity;
    const proj = new Float32Array(n);
    for (let i = 0; i < n; i++) {
      const t = p[i * 3] * ux + p[i * 3 + 1] * uy;
      proj[i] = t; if (t < lo) lo = t; if (t > hi) hi = t;
    }
    const ext = hi - lo;
    if (ext < 8) return false;
    const h = ext * 0.35;
    let dir = 0, ex = proj[0], turns = 0;
    const start = proj[0];
    for (let i = 1; i < n; i++) {
      const t = proj[i];
      if (dir === 0) {
        if (t - start > h) { dir = 1; ex = t; } else if (start - t > h) { dir = -1; ex = t; }
      } else if (dir === 1) {
        if (t > ex) ex = t; else if (ex - t > h) { turns++; dir = -1; ex = t; }
      } else {
        if (t < ex) ex = t; else if (t - ex > h) { turns++; dir = 1; ex = t; }
      }
    }
    return turns >= 4;
  }
  function convexHull(p, n) {
    const pts = [];
    for (let i = 0; i < n; i++) pts.push([p[i * 3], p[i * 3 + 1]]);
    pts.sort((a, b) => a[0] - b[0] || a[1] - b[1]);
    const cr = (o, a, b) => (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0]);
    const lower = [], upper = [];
    for (const q of pts) { while (lower.length >= 2 && cr(lower[lower.length - 2], lower[lower.length - 1], q) <= 0) lower.pop(); lower.push(q); }
    for (let i = pts.length - 1; i >= 0; i--) { const q = pts[i]; while (upper.length >= 2 && cr(upper[upper.length - 2], upper[upper.length - 1], q) <= 0) upper.pop(); upper.push(q); }
    upper.pop(); lower.pop();
    return lower.concat(upper);
  }
  function inConvex(hull, x, y) {
    if (hull.length < 3) return false;
    let sign = 0;
    for (let i = 0; i < hull.length; i++) {
      const a = hull[i], b = hull[(i + 1) % hull.length];
      const c = (b[0] - a[0]) * (y - a[1]) - (b[1] - a[1]) * (x - a[0]);
      if (c !== 0) { const sg = c > 0 ? 1 : -1; if (!sign) sign = sg; else if (sg !== sign) return false; }
    }
    return true;
  }
  function scribbleHits(sc) {
    const hull = convexHull(sc.pts, sc.n), sb = sc.bbox;
    const diag = Math.hypot(sb[2] - sb[0], sb[3] - sb[1]);
    const hits = [];
    for (const st of strokes) {
      const b = st.bbox;
      if (b[2] < sb[0] || b[0] > sb[2] || b[3] < sb[1] || b[1] > sb[3]) continue;
      let inside = 0;
      for (let i = 0; i < st.n; i++) if (inConvex(hull, st.pts[i * 3], st.pts[i * 3 + 1])) inside++;
      if (inside / st.n >= 0.4) { hits.push(st); continue; }
      if (Math.hypot(b[2] - b[0], b[3] - b[1]) > diag * 2) continue; // לא מוחקים קו גדול שרק נגענו בקצהו
      let crossed = false;
      const r = (sc.size + st.size) * 0.5;
      for (let i = 0; i < sc.n - 1 && !crossed; i++) {
        const a = i * 3;
        if (hitStrokeSeg(st, sc.pts[a], sc.pts[a + 1], sc.pts[a + 3], sc.pts[a + 4], r * 0.5)) crossed = true;
      }
      if (crossed) hits.push(st);
    }
    return hits;
  }

  // ===================== לאסו =====================
  // המסגרת נשארת בדיוק בצורה שצוירה. נבחר רק מה שבתוכה; קו שחוצה את הגבול נחתך בגבול.
  // החיתוך מתבצע בפועל רק כשמזיזים/משנים גודל (בחירה בלי פעולה לא משנה כלום).
  function inPoly(poly, x, y) {
    let c = false;
    for (let i = 0, j = poly.length - 2; i < poly.length; j = i, i += 2) {
      const xi = poly[i], yi = poly[i + 1], xj = poly[j], yj = poly[j + 1];
      if ((yi > y) !== (yj > y) && x < (xj - xi) * (y - yi) / (yj - yi) + xi) c = !c;
    }
    return c;
  }
  function polyBox(poly) {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    for (let i = 0; i < poly.length; i += 2) {
      const x = poly[i], y = poly[i + 1];
      if (x < x0) x0 = x; if (x > x1) x1 = x;
      if (y < y0) y0 = y; if (y > y1) y1 = y;
    }
    return [x0, y0, x1, y1];
  }
  // קו שעובר דרך הלאסו בלי נקודה בפנים (למשל פס ישר של מדגש)
  function crossesPoly(st, poly) {
    const p = st.pts, m = poly.length;
    for (let i = 0; i < st.n - 1; i++) {
      const a = i * 3, ax = p[a], ay = p[a + 1], bx = p[a + 3], by = p[a + 4];
      for (let j = 0; j < m; j += 2) {
        const k = (j + 2) % m, cx = poly[j], cy = poly[j + 1], dx = poly[k], dy = poly[k + 1];
        const d1 = cross(ax, ay, bx, by, cx, cy), d2 = cross(ax, ay, bx, by, dx, dy);
        if ((d1 > 0) === (d2 > 0)) continue;
        const d3 = cross(cx, cy, dx, dy, ax, ay), d4 = cross(cx, cy, dx, dy, bx, by);
        if ((d3 > 0) !== (d4 > 0)) return true;
      }
    }
    return false;
  }
  function tPoly(poly, T) { return poly.map((v, i) => (i & 1 ? v * T.k + T.ty : v * T.k + T.tx)); }

  function computeSelection(poly) {
    const pb = polyBox(poly), items = [], whole = [], remove = [], keep = [];
    for (const st of strokes) {
      const b = st.bbox;
      if (b[2] < pb[0] || b[0] > pb[2] || b[3] < pb[1] || b[1] > pb[3]) continue;
      const p = st.pts, n = st.n, ins = new Uint8Array(n);
      let cnt = 0;
      for (let i = 0; i < n; i++) if (inPoly(poly, p[i * 3], p[i * 3 + 1])) { ins[i] = 1; cnt++; }
      if (settings.lassoMode === 'whole') { // קו שלם: כל קו שהלאסו נוגע בו נבחר כולו
        if (cnt || crossesPoly(st, poly)) { items.push(st); whole.push(st); }
        continue;
      }
      if (!cnt) continue;
      if (cnt === n) { items.push(st); whole.push(st); continue; }
      // חיתוך בגבול: נקודת המעבר נמצאת בחיפוש בינארי על המקטע
      const inRuns = [], outRuns = [];
      let cur = [p[0], p[1], p[2]], curIn = ins[0];
      for (let i = 1; i < n; i++) {
        const a = (i - 1) * 3, c = i * 3;
        if (ins[i] !== curIn) {
          let lo = 0, hi = 1;
          for (let it = 0; it < 12; it++) {
            const m = (lo + hi) / 2;
            const isIn = inPoly(poly, p[a] + (p[c] - p[a]) * m, p[a + 1] + (p[c + 1] - p[a + 1]) * m) ? 1 : 0;
            if (isIn === curIn) lo = m; else hi = m;
          }
          const t = (lo + hi) / 2;
          const bx = p[a] + (p[c] - p[a]) * t, by = p[a + 1] + (p[c + 1] - p[a + 1]) * t, bp = p[a + 2] + (p[c + 2] - p[a + 2]) * t;
          cur.push(bx, by, bp);
          (curIn ? inRuns : outRuns).push(cur);
          cur = [bx, by, bp];
          curIn = ins[i];
        }
        cur.push(p[c], p[c + 1], p[c + 2]);
      }
      (curIn ? inRuns : outRuns).push(cur);
      const mk = (pc) => makeStroke({ id: newId(), page: st.page, type: st.type, color: st.color, size: st.size, pts: Float32Array.from(pc) });
      remove.push(st);
      for (const r of inRuns) items.push(mk(r));
      for (const r of outRuns) keep.push(mk(r));
    }
    // תמונה נבחרת שלמה (לא נחתכת) אם המרכז שלה בתוך הלאסו; במצב "קו שלם" גם אם פינה בפנים
    for (const im of images) {
      const b = im.bbox;
      if (inPoly(poly, (b[0] + b[2]) / 2, (b[1] + b[3]) / 2) || (settings.lassoMode === 'whole' &&
        (inPoly(poly, b[0], b[1]) || inPoly(poly, b[2], b[1]) || inPoly(poly, b[2], b[3]) || inPoly(poly, b[0], b[3])))) {
        items.push(im); whole.push(im);
      }
    }
    return { poly, items, whole, remove, keep };
  }
  const rectPoly = (b) => [b[0], b[1], b[2], b[1], b[2], b[3], b[0], b[3]];
  // בחירה של פריטים שלמים; תמונה בודדת מקבלת מסגרת מלבנית וכפתורי חיתוך/סיבוב
  function makeSel(items, poly, crop) {
    const one = items.length === 1 && items[0].img ? items[0] : null;
    return { poly: one ? rectPoly(one.bbox) : poly, items, whole: items, remove: [], keep: [], img: one, crop: !!(one && crop) };
  }
  function imageAt(x, y) {
    for (let i = images.length - 1; i >= 0; i--) {
      const b = images[i].bbox;
      if (x >= b[0] && x <= b[2] && y >= b[1] && y <= b[3]) return images[i];
    }
    return null;
  }
  function selectImage(im) {
    clearSelection();
    sel = makeSel([im]);
    updateUI();
    drawSelOverlay();
  }

  function startLasso(e, x, y) {
    lassoLive = { pointerId: e.pointerId, pts: [x, y] };
    drawLassoLive();
  }
  function addLassoPoint(x, y) {
    const P = lassoLive.pts, n = P.length;
    if (Math.hypot(x - P[n - 2], y - P[n - 1]) * view.s < 2) return;
    P.push(x, y);
  }
  function drawLassoLive() {
    overlayDirty = true;
    clearOverlay();
    const P = lassoLive.pts, s = rendered.s;
    setWorld(octx, rendered);
    octx.beginPath();
    octx.moveTo(P[0], P[1]);
    for (let i = 2; i < P.length; i += 2) octx.lineTo(P[i], P[i + 1]);
    octx.lineWidth = 1.5 / s;
    octx.setLineDash([6 / s, 5 / s]);
    octx.strokeStyle = SEL_BLUE;
    octx.stroke();
    octx.setLineDash([]);
    overlayDirty = true;
  }
  function finishLasso() {
    const P = lassoLive.pts;
    lassoLive = null;
    overlayDirty = true; clearOverlay();
    const b = polyBox(P);
    if (P.length < 6 || ((b[2] - b[0]) * view.s < 6 && (b[3] - b[1]) * view.s < 6)) {
      const im = imageAt(P[0], P[1]); // הקשה בלאסו על תמונה: בוחרת אותה
      if (im) selectImage(im);
      return;
    }
    const S = computeSelection(P);
    if (!S.items.length) return;
    sel = S.items.length === 1 && S.items[0].img ? makeSel(S.items) : S;
    updateUI();
    drawSelOverlay();
  }

  function clearSelection() {
    if (!sel && !selDrag) return;
    const wasLifted = selDrag && selDrag.lifted;
    sel = null; selDrag = null;
    renderHide = renderExtra = null;
    overlayDirty = true; clearOverlay();
    if (wasLifted) render();
    updateUI();
  }

  // ידיות שינוי גודל בפינות (רק עיגולים קטנים, בלי מלבן סביב הבחירה)
  function selHandles(poly, s) {
    const b = polyBox(poly), pad = 12 / s;
    return [[b[0] - pad, b[1] - pad], [b[2] + pad, b[1] - pad], [b[2] + pad, b[3] + pad], [b[0] - pad, b[3] + pad]];
  }
  function drawSelOverlay() {
    overlayDirty = true;
    clearOverlay();
    if (!sel) return;
    const T = selDrag ? selDrag.T : { k: 1, tx: 0, ty: 0 }, s = rendered.s;
    const cropping = selDrag && selDrag.mode === 'crop' && selDrag.preview;
    setWorld(octx, rendered);
    if (selDrag && selDrag.lifted) {
      octx.save();
      octx.beginPath(); octx.rect(0, 0, PAGE_W, PAGE_H); octx.clip();
      octx.transform(T.k, 0, 0, T.k, T.tx, T.ty);
      const list = cropping ? [selDrag.preview] : sel.items;
      for (const it of list) if (it.img) drawImg(octx, it);
      for (const it of list) if (!it.img) drawInk(octx, it);
      octx.restore();
      octx.globalAlpha = 1;
    }
    const poly = cropping ? rectPoly(selDrag.preview.bbox) : tPoly(sel.poly, T);
    octx.beginPath();
    octx.moveTo(poly[0], poly[1]);
    for (let i = 2; i < poly.length; i += 2) octx.lineTo(poly[i], poly[i + 1]);
    octx.closePath();
    octx.fillStyle = 'rgba(30,79,216,0.05)';
    octx.fill();
    octx.lineWidth = 1.5 / s;
    octx.setLineDash([6 / s, 5 / s]);
    octx.strokeStyle = SEL_BLUE;
    octx.stroke();
    octx.setLineDash([]);
    for (const [hx, hy] of selHandles(poly, s)) {
      octx.beginPath();
      octx.arc(hx, hy, 8 / s, 0, Math.PI * 2);
      octx.fillStyle = '#fff';
      octx.fill();
      octx.lineWidth = 2 / s;
      octx.stroke();
    }
    if (sel.crop) { // מצב חיתוך: פסים באמצע כל צלע, גוררים אותם פנימה
      octx.lineCap = 'round';
      octx.lineWidth = 6 / s;
      octx.strokeStyle = SEL_BLUE;
      const b = polyBox(poly);
      for (const [mx, my, e] of cropMids(b)) {
        const L = Math.min(14 / s, (e % 2 ? b[2] - b[0] : b[3] - b[1]) / 4);
        octx.beginPath();
        if (e % 2) { octx.moveTo(mx - L, my); octx.lineTo(mx + L, my); } else { octx.moveTo(mx, my - L); octx.lineTo(mx, my + L); }
        octx.stroke();
      }
      octx.lineCap = 'butt';
    }
    overlayDirty = true;
  }
  // אמצע הצלעות לפי הסדר: שמאל, עליון, ימין, תחתון
  function cropMids(b) {
    const cx = (b[0] + b[2]) / 2, cy = (b[1] + b[3]) / 2;
    return [[b[0], cy, 0], [cx, b[1], 1], [b[2], cy, 2], [cx, b[3], 3]];
  }
  // חיתוך: הצלע i של המלבן המוצג זזה פנימה ב-d (בציר שלה); החיתוך בתמונה המקורית מחושב לפי הסיבוב
  function cropImg(im, i, d) {
    const a0 = i < 2 ? d : -d;
    const k = Math.round(im.rot / 90) % 4, j = (i - k + 4) % 4;
    const c = im.crop.slice();
    const span = j % 2 === 0 ? c[2] - c[0] : c[3] - c[1];
    const disp = i % 2 === 0 ? im.w : im.h;
    const minSpan = Math.min(span, Math.max(0.02, span * 20 / disp));
    const room = j === 0 ? c[0] : j === 1 ? c[1] : j === 2 ? 1 - c[2] : 1 - c[3]; // כמה אפשר להחזיר החוצה
    const sd = Math.max(-room, Math.min(a0 / disp * span, span - minSpan));
    if (j === 0) c[0] += sd; else if (j === 1) c[1] += sd; else if (j === 2) c[2] -= sd; else c[3] -= sd;
    const a = sd / span * disp;
    let x = im.x, y = im.y, w = im.w, h = im.h;
    if (i === 0) { x += a; w -= a; } else if (i === 1) { y += a; h -= a; } else if (i === 2) w -= a; else h -= a;
    return makeImg(Object.assign(imgRec(im), { x, y, w, h, crop: c }));
  }

  function selHit(x, y, touch) {
    const near = touch ? 32 : 24;
    if (sel.crop && sel.img) {
      for (const [mx, my, e] of cropMids(sel.img.bbox)) if (Math.hypot(x - mx, y - my) * view.s < near) return { mode: 'crop', edge: e };
    }
    const hs = selHandles(sel.poly, view.s);
    for (let i = 0; i < 4; i++) {
      if (Math.hypot(x - hs[i][0], y - hs[i][1]) * view.s < near) return { mode: 'scale', h: hs[i], anchor: hs[(i + 2) % 4] };
    }
    if (inPoly(sel.poly, x, y)) return { mode: 'move' };
    return null;
  }
  function startSelDrag(e, x, y, hit) {
    selDrag = {
      pointerId: e.pointerId, touch: e.pointerType === 'touch', mode: hit.mode, h: hit.h, anchor: hit.anchor,
      x0: x, y0: y, sx: e.clientX, sy: e.clientY, lifted: false, T: { k: 1, tx: 0, ty: 0 },
      edge: hit.edge, orig: sel.img, preview: null,
    };
  }
  // גרירה באצבע שהופסקה (אצבע שנייה לזום / העט נגע): מחזירים את הבחירה למקומה בלי שינוי
  function cancelSelDrag() {
    const D = selDrag;
    selDrag = null;
    if (D && D.lifted) { renderHide = renderExtra = null; render(); }
    else if (sel) drawSelOverlay();
  }
  function moveSelDrag(e) {
    const D = selDrag;
    if (!D.lifted) {
      if (Math.hypot(e.clientX - D.sx, e.clientY - D.sy) < (D.touch ? TOUCH_SLOP : 3)) return;
      // "מרימים" את הבחירה: מסתירים אותה מהדף ומציירים אותה בשכבה העליונה
      D.lifted = true;
      renderHide = new Set(sel.whole.concat(sel.remove).map((s) => s.id));
      renderExtra = sel.keep;
      render();
    }
    const x = wx(e.clientX), y = wy(e.clientY);
    if (D.mode === 'crop') D.preview = cropImg(D.orig, D.edge, D.edge % 2 === 0 ? x - D.x0 : y - D.y0);
    else if (D.mode === 'move') D.T = { k: 1, tx: x - D.x0, ty: y - D.y0 };
    else {
      const [ax, ay] = D.anchor, vx = D.h[0] - ax, vy = D.h[1] - ay;
      const b = polyBox(sel.poly), big = Math.max(b[2] - b[0], b[3] - b[1], 1);
      let k = ((x - ax) * vx + (y - ay) * vy) / (vx * vx + vy * vy || 1);
      k = Math.max(4 / big, Math.min(8, k));
      D.T = { k, tx: ax * (1 - k), ty: ay * (1 - k) };
    }
    drawSelOverlay();
  }
  function transformStroke(st, T) {
    if (st.img) return makeImg(Object.assign(imgRec(st), { id: newId(), page: curPage, x: st.x * T.k + T.tx, y: st.y * T.k + T.ty, w: st.w * T.k, h: st.h * T.k }));
    const src = st.pts, pts = new Float32Array(src.length);
    for (let i = 0; i < src.length; i += 3) {
      pts[i] = src[i] * T.k + T.tx; pts[i + 1] = src[i + 1] * T.k + T.ty; pts[i + 2] = src[i + 2];
    }
    return makeStroke({ id: newId(), page: curPage, type: st.type, color: st.color, size: st.size * T.k, pts });
  }
  function endSelDrag() {
    const D = selDrag;
    selDrag = null;
    if (D.mode === 'crop') {
      renderHide = renderExtra = null;
      const p = D.preview, o = D.orig;
      if (!D.lifted || !p || (p.x === o.x && p.y === o.y && p.w === o.w && p.h === o.h)) { if (D.lifted) render(); else drawSelOverlay(); return; }
      p.id = newId();
      sel = makeSel([p], null, true);
      commit({ add: [p], remove: [o] });
      render();
      return;
    }
    if (!D.lifted || (D.T.k === 1 && D.T.tx === 0 && D.T.ty === 0)) {
      renderHide = renderExtra = null;
      if (D.lifted) render(); else drawSelOverlay();
      return;
    }
    const moved = sel.items.map((st) => transformStroke(st, D.T));
    const action = { add: sel.keep.concat(moved), remove: sel.whole.concat(sel.remove) };
    renderHide = renderExtra = null;
    sel = makeSel(moved, tPoly(sel.poly, D.T), sel.crop);
    commit(action);
    render();
  }
  // העתקה: עותק של הבחירה מוזז משבצת אחת, והבחירה עוברת לעותק (אפשר לגרור אותו)
  function copySelection() {
    if (!sel || busy()) return;
    const T = { k: 1, tx: GRID, ty: GRID };
    const copies = sel.items.map((st) => transformStroke(st, T));
    sel = makeSel(copies, tPoly(sel.poly, T));
    commit({ add: copies, remove: [] });
    render();
    updateUI();
  }
  // מחיקת הבחירה (קו שנחתך בגבול הלאסו: נשאר החלק שמחוץ לבחירה)
  function deleteSelection() {
    if (!sel || busy()) return;
    const S = sel;
    clearSelection();
    commit({ add: S.keep, remove: S.whole.concat(S.remove) });
    render();
  }
  // סיבוב תמונה ברבע סיבוב (עם כיוון השעון), סביב המרכז
  function rotateSelImg() {
    if (!sel || !sel.img || busy()) return;
    const im = sel.img, cx = im.x + im.w / 2, cy = im.y + im.h / 2;
    const n = makeImg(Object.assign(imgRec(im), { id: newId(), rot: im.rot + 90, x: cx - im.h / 2, y: cy - im.w / 2, w: im.h, h: im.w }));
    sel = makeSel([n], null, sel.crop);
    commit({ add: [n], remove: [im] });
    render();
    updateUI();
  }
  function toggleCrop() {
    if (!sel || !sel.img || busy()) return;
    sel.crop = !sel.crop;
    drawSelOverlay();
    updateUI();
  }

  // העתקה והדבקה בלחיצה ארוכה באצבע: מעתיקים מהבחירה, ומדביקים במקום שבו לוחצים לחיצה ארוכה
  let clipboard = null;
  function copyToClipboard() {
    if (!sel) return;
    const b = polyBox(sel.poly);
    clipboard = {
      items: sel.items.map((st) => (st.img ? makeImg(imgRec(st)) : { page: curPage, type: st.type, color: st.color, size: st.size, pts: Float32Array.from(st.pts) })),
      poly: sel.poly.slice(), cx: (b[0] + b[2]) / 2, cy: (b[1] + b[3]) / 2,
    };
  }
  function pasteAt(x, y) {
    if (!clipboard || busy()) return;
    clearSelection();
    const T = { k: 1, tx: x - clipboard.cx, ty: y - clipboard.cy };
    const copies = clipboard.items.map((st) => transformStroke(st, T));
    sel = makeSel(copies, tPoly(clipboard.poly, T));
    commit({ add: copies, remove: [] });
    render();
    updateUI();
  }

  const ctxMenu = $('#ctxMenu');
  // items: [[תווית, פעולה], ...]
  function showCtx(cx, cy, items) {
    ctxMenu.textContent = '';
    for (const [label, fn] of items) {
      const b = document.createElement('button');
      b.textContent = label;
      b.addEventListener('click', () => { ctxMenu.hidden = true; fn(); });
      ctxMenu.appendChild(b);
    }
    ctxMenu.hidden = false;
    const w = ctxMenu.offsetWidth, h = ctxMenu.offsetHeight;
    let top = cy - h - 40;
    if (top < 64) top = cy + 40;
    ctxMenu.style.left = Math.max(8, Math.min(window.innerWidth - w - 8, cx - w / 2)) + 'px';
    ctxMenu.style.top = top + 'px';
  }

  const LONG_MS = 550;
  let lp = null;
  function armLongPress(e, kind) {
    clearLongPress();
    lp = { id: e.pointerId, kind, cx: e.clientX, cy: e.clientY, timer: setTimeout(fireLongPress, LONG_MS) };
  }
  function clearLongPress() { if (lp) { clearTimeout(lp.timer); lp = null; } }
  function fireLongPress() {
    const L = lp;
    lp = null;
    const t = touches.get(L.id);
    if (!t || t.ignored || activeIds().length !== 1) return;
    if (Math.hypot(t.x - t.sx, t.y - t.sy) > TAP_SLOP) return;
    if (L.kind === 'sel') {
      if (!selDrag || selDrag.pointerId !== L.id || selDrag.lifted) return;
      selDrag = null;
      t.ignored = true; // הרמת האצבע לא תעשה כלום
      showCtx(L.cx, L.cy, selMenuItems());
    } else {
      if (busy() || viewOnly || loading || (gesture && (gesture.moved || gesture.pinched))) return;
      const x = wx(L.cx), y = wy(L.cy), im = imageAt(x, y);
      if (!im && !clipboard) return;
      gesture = null; tap = null;
      t.ignored = true;
      if (im) { // לחיצה ארוכה על תמונה: בוחרת רק את התמונה (בלי הכתב שעליה), ותפריט
        selectImage(im);
        const items = selMenuItems();
        if (clipboard) items.push(['הדבקה', () => pasteAt(x, y)]);
        showCtx(L.cx, L.cy, items);
      } else showCtx(L.cx, L.cy, [['הדבקה', () => pasteAt(x, y)]]);
    }
  }
  function selMenuItems() {
    const items = [['העתקה', copyToClipboard], ['שכפול', copySelection]];
    if (sel && sel.img) items.push(['סיבוב', rotateSelImg], ['חיתוך', () => { if (sel && !sel.crop) toggleCrop(); }]);
    items.push(['מחיקה', deleteSelection]);
    return items;
  }

  // ===================== אצבעות: גלילה, זום, והקשות =====================
  const touches = new Map();
  let gesture = null, inertia = 0, tap = null;

  function activeIds() { const a = []; for (const [id, t] of touches) if (!t.ignored) a.push(id); return a; }
  function newGesture(now) { return { startView: { s: view.s, ox: view.ox, oy: view.oy }, startAt: now, pinched: false, moved: false, frozen: false, ids: [], samples: [] }; }
  function rebase() {
    const ids = activeIds().slice(0, 2);
    gesture.ids = ids;
    gesture.base = { s: view.s, ox: view.ox, oy: view.oy, pts: ids.map((id) => ({ x: touches.get(id).x, y: touches.get(id).y })) };
    if (ids.length > 1) gesture.pinched = true;
    gesture.samples = [];
  }
  function stopInertia() { if (inertia) { cancelAnimationFrame(inertia); inertia = 0; } }
  function restoreStartView(g) { view.s = g.startView.s; view.ox = g.startView.ox; view.oy = g.startView.oy; }

  function touchDown(e) {
    const now = performance.now();
    const penBusy = live || eraseState || lassoLive || (selDrag && !selDrag.touch);
    const palm = penIsDown || penBusy || now - lastPenAt < PALM_MS ||
      Math.max(e.width || 0, e.height || 0) > PALM_SIZE;
    touches.set(e.pointerId, { x: e.clientX, y: e.clientY, sx: e.clientX, sy: e.clientY, ignored: !!palm });
    if (palm) { if (tap) tap.invalid = true; return; }
    clearLongPress();
    ctxMenu.hidden = true;
    if (selDrag && selDrag.touch) cancelSelDrag(); // אצבע שנייה: עוברים לזום/גלילה
    const n = activeIds().length;
    if (n === 1 && sel) { // אצבע על הבחירה: מזיזה / משנה גודל, ולחיצה ארוכה = העתקה
      const x = wx(e.clientX), y = wy(e.clientY), hit = selHit(x, y, true);
      if (hit) {
        stopInertia();
        tap = { start: now, max: 1, moved: false, invalid: false };
        startSelDrag(e, x, y, hit);
        if (hit.mode === 'move') armLongPress(e, 'sel');
        return;
      }
    }
    if (n === 1) { tap = { start: now, max: 1, moved: false, invalid: false }; armLongPress(e, 'page'); }
    else if (tap) tap.max = Math.max(tap.max, n);
    if (n >= 4 && tap) tap.invalid = true; // יותר מדי נקודות מגע = כף יד
    stopInertia();
    if (!gesture) gesture = newGesture(now);
    if (n >= 3) { // שלוש אצבעות לא גוללות ולא מזיזות
      if (!gesture.frozen) { restoreStartView(gesture); gesture.frozen = true; render(); }
      return;
    }
    if (gesture.frozen) return;
    rebase();
  }
  function touchMove(e) {
    const t = touches.get(e.pointerId);
    if (!t) return;
    t.x = e.clientX; t.y = e.clientY;
    if (t.ignored) return;
    const far = Math.hypot(t.x - t.sx, t.y - t.sy) > TAP_SLOP;
    if (far && lp && lp.id === e.pointerId) clearLongPress();
    if (tap && !tap.moved && far) tap.moved = true;
    if (selDrag && selDrag.touch && e.pointerId === selDrag.pointerId) {
      if (Math.hypot(t.x - t.sx, t.y - t.sy) > TOUCH_SLOP) clearLongPress();
      moveSelDrag(e);
      return;
    }
    if (!gesture || gesture.frozen || !gesture.ids.includes(e.pointerId)) return;
    const b = gesture.base, t0 = touches.get(gesture.ids[0]);
    if (gesture.ids.length === 1) {
      if (!gesture.moved) {
        if (Math.hypot(t0.x - b.pts[0].x, t0.y - b.pts[0].y) < TOUCH_SLOP) return;
        gesture.moved = true;
        b.pts[0] = { x: t0.x, y: t0.y };
      }
      view.ox = b.ox + (t0.x - b.pts[0].x);
      view.oy = b.oy + (t0.y - b.pts[0].y);
      const now = performance.now();
      gesture.samples.push({ t: now, x: t0.x, y: t0.y });
      while (gesture.samples.length > 2 && now - gesture.samples[0].t > 100) gesture.samples.shift();
    } else {
      const t1 = touches.get(gesture.ids[1]);
      const d0 = Math.hypot(b.pts[1].x - b.pts[0].x, b.pts[1].y - b.pts[0].y) || 1;
      const d = Math.hypot(t1.x - t0.x, t1.y - t0.y);
      const m0x = (b.pts[0].x + b.pts[1].x) / 2 - stageLeft, m0y = (b.pts[0].y + b.pts[1].y) / 2 - stageTop;
      const mx = (t0.x + t1.x) / 2 - stageLeft, my = (t0.y + t1.y) / 2 - stageTop;
      const s = clampScale(b.s * d / d0);
      const wmx = (m0x - b.ox) / b.s, wmy = (m0y - b.oy) / b.s;
      view.s = s; view.ox = mx - s * wmx; view.oy = my - s * wmy;
    }
    const wantOy = view.oy;
    clampView();
    viewChanged();
    // משיכה מעבר לסוף הדף (באצבע אחת): עמוד הבא / חדש, ומעבר לראש הדף: עמוד קודם
    if (gesture.ids.length === 1 && gesture.moved && !gesture.pinched) {
      const pull = view.oy - wantOy;
      const was = Math.abs(gesture.pull || 0) >= PULL_PX;
      gesture.pull = pull;
      if (Math.abs(pull) >= PULL_PX && !was && navigator.vibrate) navigator.vibrate(12);
      drawPullHint(pull);
    }
  }

  const PULL_PX = 150;
  function pullTarget(dir) {
    if (!curNb || loading) return null;
    const i = curNb.pages.findIndex((p) => p.id === curPage), n = curNb.pages.length, pg = curPg();
    if (contOn()) { // גלילה רציפה: משיכה רק בסוף העמוד האחרון
      if (dir < 0 || i < n - 1 || viewOnly) return null;
      return pg && pg.grow ? 'grow' : 'new';
    }
    if (dir > 0) return pg && pg.grow && !viewOnly ? 'grow' : i < n - 1 ? 'next' : viewOnly ? null : 'new';
    return i > 0 ? 'prev' : null;
  }
  function drawPullHint(pull) {
    if (sel) return;
    overlayDirty = true; clearOverlay();
    const dir = Math.sign(pull), tgt = pullTarget(dir);
    if (Math.abs(pull) < 30 || !tgt) return;
    const ready = Math.abs(pull) >= PULL_PX;
    const text = ready
      ? (tgt === 'grow' ? 'שחרר: הארכת הדף' : tgt === 'new' ? 'שחרר: עמוד חדש' : tgt === 'next' ? 'שחרר: לעמוד הבא' : 'שחרר: לעמוד הקודם')
      : (tgt === 'grow' ? 'המשך למשוך להארכת הדף' : tgt === 'prev' ? 'המשך למשוך לעמוד הקודם' : tgt === 'new' ? 'המשך למשוך להוספת עמוד' : 'המשך למשוך לעמוד הבא');
    octx.setTransform(dpr, 0, 0, dpr, 0, 0);
    octx.globalAlpha = Math.min(1, (Math.abs(pull) - 30) / 60);
    octx.font = '600 16px system-ui, sans-serif';
    octx.direction = 'rtl';
    const w = octx.measureText(text).width + 36, h = 40, x = W / 2 - w / 2, y = dir > 0 ? H - h - 20 : 20;
    octx.fillStyle = ready ? '#1e4fd8' : 'rgba(60,60,60,0.85)';
    octx.beginPath();
    if (octx.roundRect) octx.roundRect(x, y, w, h, 20); else octx.rect(x, y, w, h);
    octx.fill();
    octx.fillStyle = '#fff';
    octx.textAlign = 'center'; octx.textBaseline = 'middle';
    octx.fillText(text, W / 2, y + h / 2 + 1);
    octx.globalAlpha = 1;
    overlayDirty = true;
  }
  function doPull(dir) {
    const tgt = pullTarget(dir);
    if (!tgt) return;
    const i = curNb.pages.findIndex((p) => p.id === curPage);
    if (tgt === 'new') { addPage(curNb.pages.length); return; }
    if (tgt === 'grow') { growPage(); return; }
    openPage(curNb.id, curNb.pages[tgt === 'next' ? i + 1 : i - 1].id);
    if (tgt === 'prev') { view.oy = -1e9; clampView(); render(); } // לעמוד הקודם: מגיעים לסוף שלו
  }
  function touchUp(e) {
    const t = touches.get(e.pointerId);
    touches.delete(e.pointerId);
    // מגע שהמערכת "לקחה" (למשל מחווה של שלוש אצבעות בטאבלט): לא מבטלים/משחזרים בטעות
    if (e.type === 'pointercancel' && tap) tap.invalid = true;
    if (lp && lp.id === e.pointerId) clearLongPress();
    if (selDrag && selDrag.touch && e.pointerId === selDrag.pointerId) {
      if (e.type === 'pointercancel') cancelSelDrag(); else endSelDrag();
      return;
    }
    if (!t || t.ignored || !gesture) return;
    if (activeIds().length) { if (!gesture.frozen) rebase(); return; }
    const g = gesture, T = tap;
    gesture = null; tap = null;
    // הקשה קצרה בלי תזוזה: שתי אצבעות = ביטול, שלוש = שחזור
    if (T && !T.invalid && !T.moved && (T.max === 2 || T.max === 3) && performance.now() - T.start < TAP_MS) {
      restoreStartView(g);
      render();
      if (T.max === 2) undo(); else redo();
      return;
    }
    if (g.frozen) { followScroll(); requestRender(); return; }
    if (g.pull) {
      if (!sel) { overlayDirty = true; clearOverlay(); }
      if (Math.abs(g.pull) >= PULL_PX) { doPull(Math.sign(g.pull)); return; }
    }
    const sm = g.samples || [];
    if (!g.pinched && sm.length >= 2) {
      const a = sm[0], z = sm[sm.length - 1], dt = z.t - a.t;
      if (dt > 0 && performance.now() - z.t < 80) {
        const vx = (z.x - a.x) / dt, vy = (z.y - a.y) / dt;
        if (Math.hypot(vx, vy) > 0.25) { startInertia(vx, vy); return; }
      }
    }
    followScroll();
    requestRender();
  }
  function startInertia(vx, vy) {
    let last = performance.now();
    const step = (now) => {
      const dt = Math.min(32, now - last); last = now;
      const bx = view.ox + vx * dt, by = view.oy + vy * dt;
      view.ox = bx; view.oy = by;
      clampView();
      if (view.ox !== bx) vx = 0;
      if (view.oy !== by) vy = 0;
      const f = Math.pow(0.995, dt); vx *= f; vy *= f;
      if (Math.hypot(vx, vy) < 0.03) { inertia = 0; followScroll(); requestRender(); return; }
      viewChanged();
      inertia = requestAnimationFrame(step);
    };
    inertia = requestAnimationFrame(step);
  }
  // העט נגע במסך: כף יד שהתחילה רגע לפני כן לא תזיז את הדף
  function cancelTouchGesture() {
    stopInertia();
    if (gesture) {
      // מגע שעדיין על המסך כשהעט נוגע = כף יד: מחזירים את הדף למקום שהיה לפניו
      restoreStartView(gesture);
      gesture = null;
    }
    tap = null;
    clearLongPress();
    if (selDrag && selDrag.touch) cancelSelDrag();
    for (const t of touches.values()) t.ignored = true;
  }

  // ===================== חיבור אירועים =====================
  const RAW = 'onpointerrawupdate' in window;

  // צפייה בלבד: העט (והעכבר) גוללים כמו אצבע ולא כותבים
  const asTouch = (e) => e.pointerType === 'touch' || viewOnly;

  function onDown(e) {
    if (e.target.closest && e.target.closest('#showBar')) return;
    if (e.pointerType === 'mouse' && e.button !== 0) return;
    if (asTouch(e)) { touchDown(e); return; }
    if (selDrag && selDrag.touch) cancelSelDrag(); // העט קודם לאצבע
    if (busy() || loading || !curPage) return;
    if (e.pointerType === 'pen') { penIsDown = true; lastPenAt = performance.now(); }
    closePops();
    cancelTouchGesture();
    // גלילה רציפה: העט נגע בעמוד אחר שעל המסך, והוא הופך לפעיל
    if (contOn()) {
      const ly = wy(e.clientY);
      if (ly < 0 || ly > PAGE_H) {
        const o = stackPages().find((q) => ly >= q.rel && ly <= q.rel + q.h);
        if (o) setActive(o.pg.id);
      }
    }
    ensureRendered();
    try { stage.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    const x = wx(e.clientX), y = wy(e.clientY);
    const erase = settings.tool === 'eraser' || (e.buttons & 32) || (e.pointerType === 'pen' && (e.buttons & 2));
    if (sel) {
      const hit = erase ? null : selHit(x, y);
      if (hit) { startSelDrag(e, x, y, hit); return; }
      clearSelection();
    }
    if (erase) {
      eraseState = {
        pointerId: e.pointerId, lx: x, ly: y, removedOrig: new Map(), added: new Map(),
        lsx: e.clientX, lsy: e.clientY, lt: e.timeStamp, v: 0, R: ERASER_SIZES[settings.eraserSize],
      };
      eraseSeg(x, y, x, y);
      drawEraserCursor(e.clientX, e.clientY);
      return;
    }
    if (settings.tool === 'lasso') { startLasso(e, x, y); return; }
    if (x < 0 || y < 0 || x > PAGE_W || y > PAGE_H) return; // מחוץ לדף
    startStroke(e, x, y);
  }

  function onPenMove(e) {
    if (e.pointerType === 'pen') lastPenAt = Math.max(lastPenAt, performance.now() - (PALM_MS - HOVER_MS));
    const evs = e.getCoalescedEvents ? e.getCoalescedEvents() : [];
    const list = evs.length ? evs : [e];
    if (live && e.pointerId === live.pointerId) {
      for (const ce of list) addLivePoint(wx(ce.clientX), wy(ce.clientY), pressureOf(ce));
      liveDraw(); // בלי חיזוי: הוא גרם לקפיצות בדיו
    } else if (eraseState && e.pointerId === eraseState.pointerId) {
      for (const ce of list) {
        updateEraserRadius(ce);
        const x = wx(ce.clientX), y = wy(ce.clientY);
        eraseSeg(eraseState.lx, eraseState.ly, x, y);
        eraseState.lx = x; eraseState.ly = y;
      }
      drawEraserCursor(e.clientX, e.clientY);
    } else if (lassoLive && e.pointerId === lassoLive.pointerId) {
      for (const ce of list) addLassoPoint(wx(ce.clientX), wy(ce.clientY));
      drawLassoLive();
    } else if (selDrag && e.pointerId === selDrag.pointerId) {
      moveSelDrag(e);
    }
  }

  function onPenUp(e) {
    if (e.pointerType === 'pen') { penIsDown = false; lastPenAt = performance.now(); }
    if (live && e.pointerId === live.pointerId) finishStroke();
    else if (eraseState && e.pointerId === eraseState.pointerId) {
      const E = eraseState;
      eraseState = null;
      clearOverlay();
      if (E.removedOrig.size || E.added.size) pushAction({ add: [...E.added.values()], remove: [...E.removedOrig.values()] });
    } else if (lassoLive && e.pointerId === lassoLive.pointerId) finishLasso();
    else if (selDrag && e.pointerId === selDrag.pointerId) endSelDrag();
  }

  stage.addEventListener('pointerdown', onDown);
  stage.addEventListener('pointermove', (e) => {
    if (asTouch(e)) { touchMove(e); return; }
    if (RAW && busy()) return;
    if (e.pointerType === 'mouse' && !busy()) return;
    onPenMove(e);
  });
  if (RAW) stage.addEventListener('pointerrawupdate', (e) => { if (!asTouch(e)) onPenMove(e); });
  for (const ev of ['pointerup', 'pointercancel']) {
    stage.addEventListener(ev, (e) => {
      if (touches.has(e.pointerId)) touchUp(e);
      else if (e.pointerType !== 'touch') onPenUp(e);
    });
  }
  stage.addEventListener('contextmenu', (e) => e.preventDefault());

  stage.addEventListener('wheel', (e) => {
    e.preventDefault();
    if (busy()) return;
    if (e.ctrlKey) {
      const mx = e.clientX - stageLeft, my = e.clientY - stageTop;
      const wmx = (mx - view.ox) / view.s, wmy = (my - view.oy) / view.s;
      view.s = clampScale(view.s * Math.exp(-e.deltaY * 0.01));
      view.ox = mx - view.s * wmx; view.oy = my - view.s * wmy;
    } else {
      view.ox -= e.deltaX; view.oy -= e.deltaY;
    }
    clampView();
    viewChanged();
    clearTimeout(stage._wt);
    stage._wt = setTimeout(() => { followScroll(); requestRender(); }, 150);
  }, { passive: false });

  // שמירה של קו פתוח אם האפליקציה נסגרת באמצע
  function flushLive() {
    if (live) finishStroke();
    if (eraseState) onPenUp({ pointerId: eraseState.pointerId, pointerType: 'mouse' });
    if (lassoLive) { lassoLive = null; overlayDirty = true; clearOverlay(); }
    if (selDrag) endSelDrag();
  }
  window.addEventListener('pagehide', flushLive);
  document.addEventListener('visibilitychange', () => { if (document.hidden) { flushLive(); saveCurThumb(); } });

  document.addEventListener('keydown', (e) => {
    if (!dlg.hidden || !library.hidden) {
      if (e.key === 'Escape') { if (!dlg.hidden) closeDialog(null); else closeLibrary(); }
      return;
    }
    if (e.key === 'Escape') { clearSelection(); pagesPanel.hidden = true; if (settings.barHidden) setBarHidden(false); return; }
    if (!(e.ctrlKey || e.metaKey)) return;
    const k = e.key.toLowerCase();
    if (k === 'z' && !e.shiftKey) { e.preventDefault(); undo(); }
    else if (k === 'y' || (k === 'z' && e.shiftKey)) { e.preventDefault(); redo(); }
  });

  // ===================== סרגל =====================
  const sizesEl = $('#sizes'), colorsEl = $('#colors'), palette = $('#palette'), menu = $('#menu');
  const pops = { pen: $('#penMenu'), hl: $('#hlMenu'), eraser: $('#eraserMenu'), lasso: $('#lassoMenu') };

  function setTool(t) {
    if (t !== 'lasso') clearSelection();
    const prev = inkTool();
    settings.tool = t;
    if (t === 'pen' || t === 'hl') settings.lastInk = t;
    saveSettings();
    if (inkTool() !== prev) { fillSizes(sizesEl, inkTool(), pickBarSize); buildColors(); }
    updateUI();
  }
  // לחיצה על גודל/צבע כשהכלי הוא מחק או לאסו: חוזרים לעט/מדגש האחרון
  function useInk() { if (viewOnly) setViewOnly(false); const k = inkTool(); if (settings.tool !== k) setTool(k); return k; }

  function fillSizes(el, kind, onPick) {
    el.textContent = '';
    (kind === 'hl' ? HL_DOTS : PEN_DOTS).forEach((px, i) => {
      const b = document.createElement('button');
      b.className = 'size';
      b.setAttribute('aria-label', 'גודל ' + (i + 1));
      const d = document.createElement('span');
      d.className = 'dot';
      d.style.width = d.style.height = px + 'px';
      if (kind === 'hl') d.style.borderRadius = '3px';
      b.appendChild(d);
      b.addEventListener('click', () => onPick(i));
      el.appendChild(b);
    });
  }
  function paintSizes(el, k, showActive) {
    const it = ink(k);
    [...el.children].forEach((b, i) => {
      b.classList.toggle('active', showActive && i === it.sizeIdx);
      b.firstChild.style.background = it.color;
      b.firstChild.style.opacity = k === 'hl' ? 0.65 : 1;
    });
  }

  function pickBarSize(i) { const k = useInk(); ink(k).sizeIdx = i; saveSettings(); updateUI(); tryRender(); }

  function setInkColor(c) {
    const k = useInk();
    ink(k).color = c;
    saveSettings(); updateUI(); tryRender();
  }
  function addCustom(c) {
    const list = colorList();
    if (!list.includes(c)) { list.push(c); if (list.length > 20) list.shift(); }
  }

  // לכל כלי (עט / מדגש) רשימת צבעים משלו. לחיצה ארוכה על צבע: הזזה ימינה/שמאלה או מחיקה
  const colorEdit = $('#colorEdit');
  let colorEditFor = null;
  function openColorEdit(c) {
    closePops();
    colorEditFor = c;
    colorEdit.hidden = false;
    const b = [...colorsEl.children].find((x) => x.dataset.color === c);
    if (b) placePop(colorEdit, b);
  }
  colorEdit.querySelectorAll('[data-cedit]').forEach((btn) => btn.addEventListener('click', () => {
    const list = colorList(), c = colorEditFor, i = list.indexOf(c);
    if (i < 0) { colorEdit.hidden = true; return; }
    if (list.length <= 1) return;
    list.splice(i, 1);
    const it = ink(inkTool());
    if (it.color === c) it.color = list[0];
    colorEdit.hidden = true;
    saveSettings(); buildColors(); updateUI(); tryRender();
  }));

  // גרירת צבע: לחיצה ארוכה "מרימה" אותו, ואז גוררים ימינה/שמאלה. שחרור בלי גרירה = תפריט מחיקה
  let colorDrag = null;
  function colorDragMove(e) {
    const D = colorDrag, list = colorList();
    const btns = [...colorsEl.querySelectorAll('.swatch:not(.add)')];
    let j = -1;
    btns.forEach((b, k) => { const r = b.getBoundingClientRect(); if (e.clientX >= r.left && e.clientX <= r.right) j = k; });
    let i = list.indexOf(D.c);
    if (j < 0 || i < 0 || j === i) return;
    D.moved = true;
    // מזיזים את השכנים (לא את הכפתור הנגרר, כדי שלא יאבד את המגע)
    while (i < j) { const n = btns[i + 1]; colorsEl.insertBefore(n, D.btn); list[i] = list[i + 1]; btns[i] = n; i++; }
    while (i > j) { const n = btns[i - 1]; colorsEl.insertBefore(n, D.btn.nextSibling); list[i] = list[i - 1]; btns[i] = n; i--; }
    list[i] = D.c; btns[i] = D.btn;
  }
  function colorDragEnd() {
    const D = colorDrag;
    colorDrag = null;
    D.btn.classList.remove('lifted');
    if (D.moved) { saveSettings(); buildColors(); updateUI(); }
    else openColorEdit(D.c);
  }

  function buildColors() {
    colorsEl.textContent = '';
    colorList().forEach((c) => {
      const b = document.createElement('button');
      b.className = 'swatch';
      b.dataset.color = c;
      b.setAttribute('aria-label', 'צבע');
      b.title = 'לחיצה ארוכה: גרירה, או שחרור למחיקה';
      const s = document.createElement('span');
      s.style.background = c;
      b.appendChild(s);
      let timer = 0, fired = false, sx = 0, sy = 0;
      const lift = (pid) => {
        if (fired) return;
        fired = true; clearTimeout(timer);
        closePops();
        try { b.setPointerCapture(pid); } catch (err) { /* ignore */ }
        b.classList.add('lifted');
        colorDrag = { c, btn: b, moved: false };
      };
      b.addEventListener('pointerdown', (e) => {
        fired = false; sx = e.clientX; sy = e.clientY;
        clearTimeout(timer);
        timer = setTimeout(() => lift(e.pointerId), 450);
      });
      b.addEventListener('pointermove', (e) => {
        if (colorDrag && colorDrag.btn === b) colorDragMove(e);
        else if (Math.hypot(e.clientX - sx, e.clientY - sy) > 10) clearTimeout(timer);
      });
      for (const ev of ['pointerup', 'pointercancel']) b.addEventListener(ev, () => {
        clearTimeout(timer);
        if (colorDrag && colorDrag.btn === b) colorDragEnd();
      });
      b.addEventListener('contextmenu', (e) => e.preventDefault());
      b.addEventListener('click', () => { if (fired) { fired = false; return; } setInkColor(c); });
      colorsEl.appendChild(b);
    });
    const add = document.createElement('button');
    add.className = 'swatch add';
    add.title = 'הוספת צבע';
    add.setAttribute('aria-label', 'הוספת צבע');
    const s = document.createElement('span');
    s.textContent = '+';
    add.appendChild(s);
    add.addEventListener('click', (e) => {
      e.stopPropagation();
      if (!palette.hidden) { closePalette(); return; }
      closePops();
      openPalette(add);
    });
    colorsEl.appendChild(add);
  }

  // לוח צבעים: הקשה על צבע מוסיפה אותו לסרגל ובוחרת בו
  PALETTE.forEach((c) => {
    const b = document.createElement('button');
    b.style.background = c;
    b.dataset.color = c;
    b.setAttribute('aria-label', 'צבע');
    b.addEventListener('click', () => {
      addCustom(c);
      buildColors(); setInkColor(c); closePalette();
    });
    palette.appendChild(b);
  });

  // צבע חופשי: גוון + בהירות, תצוגה מקדימה וכפתור הוספה
  const custom = document.createElement('div');
  custom.className = 'custom';
  custom.innerHTML =
    '<div class="custom-title">צבע אחר</div>' +
    '<input type="range" class="hue" min="0" max="359" value="210" aria-label="גוון">' +
    '<input type="range" class="light" min="5" max="90" value="45" aria-label="בהירות">' +
    '<div class="custom-row"><span class="preview"></span><button class="custom-add">הוספה</button></div>';
  palette.appendChild(custom);
  const hueIn = custom.querySelector('.hue'), lightIn = custom.querySelector('.light');
  const preview = custom.querySelector('.preview');
  function hslHex(h, s, l) {
    s /= 100; l /= 100;
    const f = (n) => {
      const k = (n + h / 30) % 12;
      const c = l - s * Math.min(l, 1 - l) * Math.max(-1, Math.min(k - 3, 9 - k, 1));
      return Math.round(c * 255).toString(16).padStart(2, '0');
    };
    return '#' + f(0) + f(8) + f(4);
  }
  function customColor() { return hslHex(+hueIn.value, 85, +lightIn.value); }
  function updateCustom() {
    const h = +hueIn.value;
    preview.style.background = customColor();
    lightIn.style.background = `linear-gradient(to left, ${hslHex(h, 85, 5)}, ${hslHex(h, 85, 47)}, ${hslHex(h, 85, 90)})`;
  }
  hueIn.addEventListener('input', updateCustom);
  lightIn.addEventListener('input', updateCustom);
  updateCustom();
  custom.querySelector('.custom-add').addEventListener('click', () => {
    const c = customColor();
    addCustom(c);
    buildColors(); setInkColor(c); closePalette();
  });

  function placePop(el, anchor) {
    const r = anchor.getBoundingClientRect(), w = el.offsetWidth;
    el.style.left = Math.max(8, Math.min(window.innerWidth - w - 8, r.left + r.width / 2 - w / 2)) + 'px';
  }
  function openPalette(anchor) {
    const have = new Set(colorList());
    [...palette.children].forEach((b) => b.classList.toggle('have', have.has(b.dataset.color)));
    palette.hidden = false;
    placePop(palette, anchor);
  }
  function closePalette() { palette.hidden = true; }
  function closeMenu() { menu.hidden = true; }
  function closePops() {
    closeMenu(); closePalette();
    for (const el of Object.values(pops)) el.hidden = true;
    colorEdit.hidden = true;
    ctxMenu.hidden = true;
    $('#pagesPanel').hidden = true;
  }

  function updateUI() {
    const k = inkTool(), inkActive = settings.tool === k, it = ink(k);
    document.querySelectorAll('.tool').forEach((b) => b.classList.toggle('active', b.dataset.tool === settings.tool));
    pops.lasso.querySelectorAll('[data-lmode]').forEach((b) => b.classList.toggle('active', b.dataset.lmode === settings.lassoMode));
    [...colorsEl.children].forEach((b) => b.classList.toggle('active', b.dataset.color === it.color));
    $('#selGroup').hidden = !sel;
    // בזמן בחירה: גדלים וצבעים מוסתרים, כדי שכפתורי הבחירה ייכנסו בסרגל גם במסך צר
    sizesEl.hidden = colorsEl.hidden = !!sel;
    $('#imgCrop').hidden = $('#imgRot').hidden = !(sel && sel.img);
    $('#imgCrop').classList.toggle('active', !!(sel && sel.crop));
    // תפריט העט
    pops.pen.querySelectorAll('[data-ptype]').forEach((b) => b.classList.toggle('active', b.dataset.ptype === settings.penType));
    paintSizes(sizesEl, k, inkActive);
    // תפריט המדגש
    pops.hl.querySelectorAll('[data-hmode]').forEach((b) => b.classList.toggle('active', b.dataset.hmode === settings.hl.mode));
  }

  // תפריט העט: סוג, 6 גדלים, וריבוע "נסה כאן"
  pops.pen.querySelectorAll('[data-ptype]').forEach((b) => b.addEventListener('click', () => {
    settings.penType = b.dataset.ptype; // כל סוג זוכר גודל וצבע משלו
    if (settings.tool !== 'pen') setTool('pen');
    saveSettings(); updateUI(); tryRender();
  }));

  const tryC = $('#tryC'), tryHint = $('#tryHint');
  let tryStrokes = [], tryLive = null;
  function tryRender() {
    if (pops.pen.hidden) return;
    const r = tryC.getBoundingClientRect();
    const w = Math.round(r.width * dpr), h = Math.round(r.height * dpr);
    if (tryC.width !== w || tryC.height !== h) { tryC.width = w; tryC.height = h; }
    const c = tryC.getContext('2d'), s = Math.max(0.6, Math.min(2.5, view.s));
    c.setTransform(1, 0, 0, 1, 0, 0);
    c.globalAlpha = 1;
    c.fillStyle = '#fff';
    c.fillRect(0, 0, w, h);
    c.setTransform(dpr * s, 0, 0, dpr * s, 0, 0);
    const pen = settings.pens[settings.penType];
    const list = tryLive ? tryStrokes.concat([tryLive.pts]) : tryStrokes;
    for (const pts of list) {
      const st = makeStroke({ type: settings.penType, color: pen.color, size: PEN_SIZES[pen.sizeIdx], pts });
      c.save(); drawInk(c, st); c.restore();
    }
    tryHint.hidden = list.length > 0;
  }
  function tryPoint(e) {
    const r = tryC.getBoundingClientRect(), s = Math.max(0.6, Math.min(2.5, view.s));
    const p = e.pointerType === 'mouse' ? 0.5 : (e.pressure > 0 ? Math.min(1, e.pressure) : 0.5);
    const P = tryLive.pts, x = (e.clientX - r.left) / s, y = (e.clientY - r.top) / s;
    if (P.length && Math.hypot(x - P[P.length - 3], y - P[P.length - 2]) < MIN_DIST) return;
    P.push(x, y, p);
  }
  tryC.addEventListener('pointerdown', (e) => {
    if (e.pointerType === 'touch') return; // אצבע לא כותבת
    if (e.pointerType === 'pen') lastPenAt = performance.now();
    try { tryC.setPointerCapture(e.pointerId); } catch (err) { /* ignore */ }
    tryLive = { id: e.pointerId, pts: [] };
    tryPoint(e); tryRender();
  });
  tryC.addEventListener('pointermove', (e) => {
    if (!tryLive || e.pointerId !== tryLive.id) return;
    if (e.pointerType === 'pen') lastPenAt = performance.now();
    const evs = e.getCoalescedEvents ? e.getCoalescedEvents() : [];
    for (const ce of (evs.length ? evs : [e])) tryPoint(ce);
    tryRender();
  });
  for (const ev of ['pointerup', 'pointercancel']) {
    tryC.addEventListener(ev, (e) => {
      if (!tryLive || e.pointerId !== tryLive.id) return;
      if (tryLive.pts.length) tryStrokes.push(tryLive.pts);
      if (tryStrokes.length > 30) tryStrokes.shift();
      tryLive = null;
      tryRender();
    });
  }
  $('#tryClear').addEventListener('click', () => { tryStrokes = []; tryRender(); });

  // תפריט המדגש: חופשי / חכם, 6 גדלים
  pops.hl.querySelectorAll('[data-hmode]').forEach((b) => b.addEventListener('click', () => {
    settings.hl.mode = b.dataset.hmode; saveSettings(); updateUI();
  }));

  // תפריט הלאסו: חיתוך בגבול / קו שלם
  pops.lasso.querySelectorAll('[data-lmode]').forEach((b) => b.addEventListener('click', () => {
    settings.lassoMode = b.dataset.lmode; saveSettings(); updateUI();
  }));

  // תפריט המחק
  const esizes = $('#esizes'), edyn = $('#edyn');
  ERASER_SIZES.forEach((_, i) => {
    const b = document.createElement('button');
    b.setAttribute('aria-label', 'גודל מחק ' + (i + 1));
    const d = document.createElement('span');
    d.className = 'dot';
    d.style.width = d.style.height = ERASER_DOTS[i] + 'px';
    b.appendChild(d);
    b.addEventListener('click', () => { settings.eraserSize = i; saveSettings(); updateEraserMenu(); });
    esizes.appendChild(b);
  });
  pops.eraser.querySelectorAll('[data-emode]').forEach((b) => b.addEventListener('click', () => {
    settings.eraserMode = b.dataset.emode; saveSettings(); updateEraserMenu();
  }));
  edyn.addEventListener('change', () => { settings.eraserDynamic = edyn.checked; saveSettings(); });
  function updateEraserMenu() {
    pops.eraser.querySelectorAll('[data-emode]').forEach((b) => b.classList.toggle('active', b.dataset.emode === settings.eraserMode));
    [...esizes.children].forEach((b, i) => b.classList.toggle('active', i === settings.eraserSize));
    edyn.checked = settings.eraserDynamic;
  }

  // כפתורי הכלים: הקשה על כלי שכבר נבחר פותחת את התפריט שלו
  document.querySelectorAll('.tool').forEach((b) => b.addEventListener('click', (e) => {
    const t = b.dataset.tool, el = pops[t];
    if (viewOnly) { setViewOnly(false); closePops(); setTool(t); return; } // יציאה מצפייה בלבד
    if (el && t === settings.tool) {
      e.stopPropagation();
      if (el.hidden) {
        closePops();
        if (t === 'eraser') updateEraserMenu();
        updateUI();
        el.hidden = false;
        placePop(el, b);
        if (t === 'pen') tryRender();
      } else el.hidden = true;
      return;
    }
    closePops();
    setTool(t);
  }));
  $('#undo').addEventListener('click', undo);
  $('#redo').addEventListener('click', redo);
  $('#selCopy').addEventListener('click', copySelection);
  $('#selDel').addEventListener('click', deleteSelection);
  $('#imgCrop').addEventListener('click', toggleCrop);
  $('#imgRot').addEventListener('click', rotateSelImg);

  // ===================== חלון שאלה (שם, אישור, רשימת פעולות) =====================
  const dlg = $('#dlg'), dlgTitle = dlg.querySelector('.dlg-title'), dlgInput = dlg.querySelector('.dlg-input');
  const dlgSeg = dlg.querySelector('.dlg-seg'), dlgList = dlg.querySelector('.dlg-list'), dlgBtns = dlg.querySelector('.dlg-btns');
  let dlgResolve = null, dlgOk = null;
  function closeDialog(v) {
    dlg.hidden = true;
    dlgInput.blur();
    const r = dlgResolve;
    dlgResolve = null; dlgOk = null;
    if (r) r(v);
  }
  // o: { title, input (טקסט התחלתי), placeholder, seg: [[ערך, תווית]], segVal, list: [{label, value, danger}], ok, danger, noCancel }
  // מחזיר: null בביטול; ערך מהרשימה; {text, seg} כשיש שדה; אחרת true
  function dialog(o) {
    if (dlgResolve) closeDialog(null);
    const mk = (label, cls) => { const b = document.createElement('button'); b.textContent = label; if (cls) b.className = cls; return b; };
    dlgTitle.textContent = o.title || '';
    dlgInput.hidden = o.input === undefined;
    dlgInput.value = o.input || '';
    dlgInput.placeholder = o.placeholder || '';
    dlgSeg.hidden = !o.seg; dlgSeg.textContent = '';
    let segVal = o.segVal;
    if (o.seg) o.seg.forEach(([v, label]) => {
      const b = mk(label, v === segVal ? 'active' : '');
      b.addEventListener('click', () => { segVal = v; [...dlgSeg.children].forEach((x) => x.classList.toggle('active', x === b)); });
      dlgSeg.appendChild(b);
    });
    let coverVal = o.coverVal, paperVal = o.paperVal;
    const covers = dlg.querySelector('.dlg-covers'), paper = dlg.querySelector('.dlg-paper');
    covers.hidden = !o.covers; covers.textContent = '';
    dlg.querySelector('[data-for=covers]').hidden = !o.covers;
    if (o.covers) o.covers.forEach((c) => {
      const b = mk('', c === coverVal ? 'active' : '');
      b.style.background = c;
      b.setAttribute('aria-label', 'צבע כריכה');
      b.addEventListener('click', () => { coverVal = c; [...covers.children].forEach((x) => x.classList.toggle('active', x === b)); });
      covers.appendChild(b);
    });
    paper.hidden = !o.paper; paper.textContent = '';
    dlg.querySelector('[data-for=paper]').hidden = !o.paper;
    if (o.paper) buildPaperTiles(paper, () => paperVal, (t) => { paperVal = t; });
    dlgList.hidden = !o.list; dlgList.textContent = '';
    if (o.list) o.list.forEach((it) => {
      const b = mk(it.label, it.danger ? 'danger' : '');
      b.addEventListener('click', () => closeDialog(it.value));
      dlgList.appendChild(b);
    });
    dlgBtns.textContent = '';
    if (!o.list) {
      const ok = mk(o.ok || 'אישור', 'ok' + (o.danger ? ' danger' : ''));
      dlgOk = () => closeDialog(o.input !== undefined || o.seg || o.covers || o.paper ? { text: dlgInput.value, seg: segVal, cover: coverVal, paper: paperVal } : true);
      ok.addEventListener('click', dlgOk);
      dlgBtns.appendChild(ok);
    }
    if (!o.noCancel) {
      const c = mk(o.list ? 'סגירה' : 'ביטול');
      c.addEventListener('click', () => closeDialog(null));
      dlgBtns.appendChild(c);
    }
    dlg.hidden = false;
    if (o.input !== undefined) setTimeout(() => { dlgInput.focus(); dlgInput.select(); }, 60);
    return new Promise((res) => { dlgResolve = res; });
  }
  dlg.addEventListener('pointerdown', (e) => { if (e.target === dlg) closeDialog(null); });
  dlgInput.addEventListener('keydown', (e) => { if (e.key === 'Enter' && dlgOk) { e.preventDefault(); dlgOk(); } });
  const info = (title) => dialog({ title, ok: 'סגירה', noCancel: true });

  // ----- תפריט קטן ליד הכפתור (כמו ב-GoodNotes) -----
  const ICONS = {
    rename: 'M4 20l1.2-4.2L16 5l3 3L8.2 18.8z M14 7l3 3',
    move: 'M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z M10 13h6 M13 10l3 3-3 3',
    del: 'M4 7h16 M9 7V5h6v2 M6 7l1 13h10l1-13 M10 11v6 M14 11v6',
    backup: 'M12 4v11 M7 10l5 5 5-5 M5 20h14',
    restore: 'M12 15V4 M7 9l5-5 5 5 M5 20h14',
    book: 'M5 4h11a2 2 0 0 1 2 2v14H7a2 2 0 0 1-2-2z M5 18a2 2 0 0 1 2-2h11 M9 8h5',
    folder: 'M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z M12 10v6 M9 13h6',
    cover: 'M12 3a9 9 0 1 0 0 18c1 0 1.5-.8 1.5-1.6 0-1.1-.9-1.4-.9-2.4 0-.9.7-1.5 1.6-1.5H17a4 4 0 0 0 4-4c0-4.7-4-8.5-9-8.5z M7.5 11.5h.01 M10 7.5h.01 M14.5 7.5h.01',
    add: 'M12 5v14 M5 12h14',
    up: 'M12 19V5 M6 11l6-6 6 6',
    star: 'M12 4l2.4 5 5.4.7-4 3.8 1 5.4-4.8-2.6-4.8 2.6 1-5.4-4-3.8 5.4-.7z',
    copy: 'M9 9h10v10H9z M15 9V5H5v10h4',
    sort: 'M7 5v14 M4 16l3 3 3-3 M17 19V5 M14 8l3-3 3 3',
    down: 'M12 5v14 M6 13l6 6 6-6',
    pdf: 'M6 3h8l4 4v14H6z M14 3v4h4 M9 13h6 M9 17h4',
  };
  const popMenuEl = $('#popMenu');
  let popResolve = null;
  function closePopMenu(v) {
    popMenuEl.hidden = true;
    const r = popResolve;
    popResolve = null;
    if (r) r(v);
  }
  // items: [{label, icon, value, danger} | '-'] ; מחזיר את הערך שנבחר או null
  function popMenu(anchor, items, title) {
    if (popResolve) closePopMenu(null);
    popMenuEl.textContent = '';
    if (title) { const t = document.createElement('div'); t.className = 'pm-title'; t.textContent = title; popMenuEl.appendChild(t); }
    for (const it of items) {
      if (it === '-') { const s = document.createElement('div'); s.className = 'pm-sep'; popMenuEl.appendChild(s); continue; }
      const b = document.createElement('button');
      if (it.danger) b.className = 'danger';
      b.innerHTML = '<svg viewBox="0 0 24 24"><path d="' + (ICONS[it.icon] || '') + '"/></svg>';
      const sp = document.createElement('span');
      sp.textContent = it.label;
      b.appendChild(sp);
      b.addEventListener('click', () => closePopMenu(it.value));
      popMenuEl.appendChild(b);
    }
    popMenuEl.hidden = false;
    const r = anchor.getBoundingClientRect(), w = popMenuEl.offsetWidth, h = popMenuEl.offsetHeight;
    let left = r.left + r.width / 2 - w / 2, top = r.bottom + 6;
    if (top + h > window.innerHeight - 8) top = Math.max(8, r.top - h - 6);
    left = Math.max(8, Math.min(window.innerWidth - w - 8, left));
    popMenuEl.style.left = left + 'px';
    popMenuEl.style.top = top + 'px';
    return new Promise((res) => { popResolve = res; });
  }
  document.addEventListener('pointerdown', (e) => {
    if (!popMenuEl.hidden && !popMenuEl.contains(e.target)) closePopMenu(null);
  }, true);

  // ----- בחירת סוג דף עם תצוגה מקדימה -----
  const PAPER_NAMES = { blank: 'ריק', lines: 'שורות', grid: 'משבצות', eng: 'הנדסאי', cornell: 'קורנל' };
  function paperPreview(type) {
    const savedH = PAGE_H;
    PAGE_H = PAGE_H0;
    try { return paperPreview0(type); } finally { PAGE_H = savedH; }
  }
  function paperPreview0(type) {
    const c = document.createElement('canvas'), w = 88, k = w / PAGE_W;
    c.width = w; c.height = Math.round(PAGE_H * k);
    const g = c.getContext('2d');
    g.setTransform(k, 0, 0, k, 0, 0);
    drawPaper(g, type, false, 1 / k, 0, 0, PAGE_W, PAGE_H);
    return c;
  }
  function buildPaperTiles(el, get, pick) {
    el.textContent = '';
    for (const t of PAPER_TYPES) {
      const b = document.createElement('button');
      b.dataset.paper = t;
      b.append(paperPreview(t), PAPER_NAMES[t]);
      b.classList.toggle('active', get() === t);
      b.addEventListener('click', () => {
        pick(t);
        [...el.children].forEach((x) => x.classList.toggle('active', x === b));
      });
      el.appendChild(b);
    }
  }

  // ===================== מחברות ועמודים =====================
  const pagesPanel = $('#pagesPanel'), ppList = $('#ppList'), library = $('#library');
  const KEBAB = '<svg viewBox="0 0 24 24"><circle cx="12" cy="5" r="1.8"/><circle cx="12" cy="12" r="1.8"/><circle cx="12" cy="19" r="1.8"/></svg>';
  const FOLDER_SVG = '<svg viewBox="0 0 120 96"><path d="M6 14a8 8 0 0 1 8-8h30l10 10h52a8 8 0 0 1 8 8v58a8 8 0 0 1-8 8H14a8 8 0 0 1-8-8z" fill="#e8b93a"/><path d="M6 30h108v52a8 8 0 0 1-8 8H14a8 8 0 0 1-8-8z" fill="#f6d365"/></svg>';
  const PAPER_OPTS = [['blank', 'ריק'], ['lines', 'שורות'], ['grid', 'משבצות']];
  let loadToken = 0;

  function uid() { return Date.now().toString(36) + Math.random().toString(36).slice(2, 8); }
  function saveRec(store, r) { persist(() => DB.putRec(store, r)); }
  function curPg() { return curNb ? curNb.pages.find((p) => p.id === curPage) : null; }
  const byName = (a, b) => a.name.localeCompare(b.name, 'he');
  const byUpdated = (a, b) => (b.updated || 0) - (a.updated || 0);

  async function openPage(nbId, pageId) {
    const nb = lib.notebooks.get(nbId);
    if (!nb) return;
    const pg = nb.pages.find((p) => p.id === pageId) || nb.pages.find((p) => p.id === nb.last) || nb.pages[0];
    flushLive();
    clearSelection();
    saveCurThumb();
    const tok = ++loadToken;
    loading = true;
    others.clear();
    curNb = nb; curPage = pg.id; curType = pg.type; PAGE_H = pageH(pg);
    settings.nb = nb.id; settings.page = pg.id; saveSettings();
    if (nb.last !== pg.id) { nb.last = pg.id; saveRec('notebooks', nb); }
    let h = histories.get(pg.id);
    if (!h) { h = { u: [], r: [] }; histories.set(pg.id, h); }
    undoStack = h.u; redoStack = h.r;
    updateUndoUI();
    strokes = []; images = []; pageDirty = false;
    view.oy = MARGIN; clampView();
    invalidateCache(); render();
    updatePageUI();
    if (!pagesPanel.hidden) renderPagesPanel();
    try {
      await saveChain;
      const [recs, ims] = await Promise.all([DB.load(pg.id), DB.loadImgs(pg.id)]);
      if (tok !== loadToken) return;
      images = ims.map(makeImg).sort((a, b) => a.id - b.id);
      if (images.length) lastId = Math.max(lastId, images[images.length - 1].id);
      strokes = recs.map(makeStroke).sort((a, b) => a.id - b.id);
      if (strokes.length) lastId = Math.max(lastId, strokes[strokes.length - 1].id);
    } catch (err) {
      console.error(err);
      if (tok === loadToken) setStatus('⚠ אין גישה לאחסון');
      return; // נשאר "בטעינה": אי אפשר לכתוב על עמוד שלא נטען
    }
    loading = false;
    invalidateCache(); render();
  }

  // קווים ותמונות של עמוד (מהזיכרון אם הוא הפתוח, אחרת מהאחסון)
  async function pageData(pid) {
    if (pid === curPage && !loading) return { strokes: strokes.slice(), images: images.slice() };
    await saveChain;
    const [s, i] = await Promise.all([DB.load(pid), DB.loadImgs(pid)]);
    return { strokes: s.map(makeStroke).sort((a, b) => a.id - b.id), images: i.map(makeImg).sort((a, b) => a.id - b.id) };
  }

  function updatePageUI() {
    if (!curNb) return;
    const i = curNb.pages.findIndex((p) => p.id === curPage);
    $('#pageNum').textContent = (i + 1) + '/' + curNb.pages.length;
    $('#pagesBtn').title = curNb.name;
  }

  function newNotebook(name, parent, type) {
    const now = Date.now();
    const nb = { id: uid(), name, parent, created: now, updated: now, pages: [{ id: uid(), type }] };
    lib.notebooks.set(nb.id, nb);
    saveRec('notebooks', nb);
    return nb;
  }
  async function openLatest() {
    if (!aliveNbs().length) newNotebook('מחברת חדשה', '', curType || 'grid');
    const nb = aliveNbs().sort(byUpdated)[0];
    await openPage(nb.id, nb.last);
  }

  // ----- תמונות מוקטנות -----
  const TH_W = 240, thumbUrls = new Map();
  // תמונה מוקטנת: החלק העליון של הדף (בגובה רגיל, או בגובה השקופית בעמוד PDF)
  function thumbCanvas(pg, list, imgs) { return withH(baseH(pg), () => thumbCanvas0(pg, list, imgs)); }
  function thumbCanvas0(pg, list, imgs) {
    const k = TH_W / PAGE_W, c = document.createElement('canvas');
    c.width = TH_W; c.height = Math.round(PAGE_H * k);
    const g = c.getContext('2d');
    g.setTransform(k, 0, 0, k, 0, 0);
    const wasDark = inkDark;
    inkDark = false; // תמונה מוקטנת תמיד בהירה
    try {
      drawPaper(g, pg.type, false, 0.8 / k, 0, 0, PAGE_W, PAGE_H);
      drawBg(g, pg);
      g.save();
      g.beginPath(); g.rect(0, 0, PAGE_W, PAGE_H); g.clip();
      for (const im of imgs) drawImg(g, im);
      for (const st of list) drawInk(g, st);
      g.restore();
    } finally { inkDark = wasDark; }
    return c;
  }
  function setThumbUrl(page, blob) {
    const old = thumbUrls.get(page);
    if (old) URL.revokeObjectURL(old);
    if (blob) thumbUrls.set(page, URL.createObjectURL(blob)); else thumbUrls.delete(page);
  }
  // מחכים שהרקע והתמונות מוכנים (עד 8 שניות), ואז מציירים
  async function assetsReady(pg, imgs, px) {
    const jobs = imgs.map(decodeImg);
    if (pg.bg) jobs.push(bgReady(pg, px));
    if (jobs.length) await Promise.race([Promise.all(jobs), new Promise((r) => setTimeout(r, 8000))]);
  }
  async function saveThumb(pg, list, imgs) {
    await assetsReady(pg, imgs, TH_W * 2);
    const c = thumbCanvas(pg, list, imgs);
    return new Promise((res) => c.toBlob((b) => {
      if (b) { setThumbUrl(pg.id, b); persist(() => DB.putThumb(pg.id, b)); }
      res(b);
    }, 'image/webp', 0.85));
  }
  // העמוד הנוכחי השתנה: מעדכנים את התמונה המוקטנת ואת תאריך העדכון של המחברת
  function saveCurThumb() {
    const pg = curPg();
    if (!pageDirty || !curNb || !pg || loading) return Promise.resolve();
    pageDirty = false;
    curNb.updated = Date.now();
    saveRec('notebooks', curNb);
    return saveThumb(Object.assign({}, pg), strokes.slice(), images.slice());
  }
  async function thumbUrl(pg) {
    if (pg.id === curPage) await saveCurThumb();
    const u = thumbUrls.get(pg.id);
    if (u) return u;
    const blob = await DB.getThumb(pg.id);
    if (blob) { setThumbUrl(pg.id, blob); return thumbUrls.get(pg.id); }
    const d = await pageData(pg.id);
    await saveThumb(pg, d.strokes, d.images);
    return thumbUrls.get(pg.id);
  }
  // טוען תמונות אחת-אחת (כדי לא להעמיס), ועוצר אם התצוגה התחלפה
  async function fillThumbs(jobs, alive) {
    for (const [pg, img] of jobs) {
      if (!alive()) return;
      try { const u = await thumbUrl(pg); if (u && alive()) img.src = u; } catch (err) { console.error(err); }
    }
  }

  // ----- רשימת העמודים (נפתחת מהסרגל) -----
  let ppToken = 0;
  function renderPagesPanel() {
    if (!curNb) return;
    const tok = ++ppToken, jobs = [];
    $('#ppTitle').textContent = curNb.name;
    ppList.textContent = '';
    let curEl = null;
    curNb.pages.forEach((pg, i) => {
      const it = document.createElement('div');
      it.className = 'pp-item' + (pg.id === curPage ? ' cur' : '');
      const img = document.createElement('img');
      img.alt = '';
      const u = thumbUrls.get(pg.id);
      if (u && !(pg.id === curPage && pageDirty)) img.src = u; else jobs.push([pg, img]);
      const num = document.createElement('div');
      num.className = 'pp-num';
      num.textContent = i + 1;
      const kb = document.createElement('button');
      kb.className = 'kebab';
      kb.setAttribute('aria-label', 'אפשרויות לעמוד');
      kb.innerHTML = KEBAB;
      kb.addEventListener('click', (e) => { e.stopPropagation(); pageActions(pg, kb); });
      const star = document.createElement('button');
      star.className = 'pp-star' + (pg.fav ? ' on' : '');
      star.textContent = pg.fav ? '★' : '☆';
      star.setAttribute('aria-label', 'עמוד מועדף');
      star.addEventListener('click', (e) => { e.stopPropagation(); pg.fav = !pg.fav; saveRec('notebooks', curNb); renderPagesPanel(); toast(pg.fav ? 'נוסף למועדפים ★' : 'הוסר מהמועדפים'); });
      it.append(img, num, kb, star);
      it.addEventListener('click', () => { if (pg.id !== curPage) openPage(curNb.id, pg.id); });
      ppList.appendChild(it);
      if (pg.id === curPage) curEl = it;
    });
    if (curEl) curEl.scrollIntoView({ block: 'nearest' });
    fillThumbs(jobs, () => tok === ppToken && !pagesPanel.hidden);
  }
  $('#pagesBtn').addEventListener('click', (e) => {
    e.stopPropagation();
    const wasHidden = pagesPanel.hidden;
    closePops();
    if (wasHidden && curNb) { pagesPanel.hidden = false; renderPagesPanel(); }
  });
  $('#ppClose').addEventListener('click', () => { pagesPanel.hidden = true; });
  $('#ppAdd').addEventListener('click', () => addPage(curNb.pages.length));

  function addPage(at) {
    if (!curNb) return;
    const pg = { id: uid(), type: curType };
    curNb.pages.splice(at, 0, pg);
    saveRec('notebooks', curNb);
    openPage(curNb.id, pg.id).then(() => { if (!pagesPanel.hidden) renderPagesPanel(); });
  }
  async function pageActions(pg, anchor) {
    const arr = curNb.pages, i = arr.indexOf(pg);
    if (i < 0) return;
    const list = [{ label: 'הוספת עמוד אחרי זה', icon: 'add', value: 'add' }];
    if (i > 0) list.push({ label: 'הזזה למעלה', icon: 'up', value: 'up' });
    if (i < arr.length - 1) list.push({ label: 'הזזה למטה', icon: 'down', value: 'down' });
    list.push({ label: pg.fav ? 'הסרה מהמועדפים' : 'הוספה למועדפים', icon: 'star', value: 'fav' });
    list.push('-', { label: 'מחיקת העמוד', icon: 'del', value: 'del', danger: true });
    const a = await popMenu(anchor, list, 'עמוד ' + (i + 1));
    if (a === 'add') addPage(i + 1);
    else if (a === 'fav') { pg.fav = !pg.fav; saveRec('notebooks', curNb); renderPagesPanel(); toast(pg.fav ? 'נוסף למועדפים' : 'הוסר מהמועדפים'); }
    else if (a === 'up' || a === 'down') {
      const j = a === 'up' ? i - 1 : i + 1;
      [arr[i], arr[j]] = [arr[j], arr[i]];
      saveRec('notebooks', curNb);
      updatePageUI(); renderPagesPanel();
    } else if (a === 'del') deletePage(pg);
  }
  async function deletePage(pg) {
    const nb = curNb;
    if (!await dialog({ title: 'למחוק את עמוד ' + (nb.pages.indexOf(pg) + 1) + '?\nאי אפשר לשחזר אחרי מחיקה.', ok: 'מחיקה', danger: true })) return;
    const i = nb.pages.indexOf(pg);
    if (i < 0 || nb !== curNb) return;
    const isCur = pg.id === curPage;
    if (isCur) { flushLive(); clearSelection(); pageDirty = false; }
    nb.pages.splice(i, 1);
    if (!nb.pages.length) nb.pages.push({ id: uid(), type: pg.type });
    saveRec('notebooks', nb);
    persist(() => DB.delPages([pg.id]));
    histories.delete(pg.id);
    others.delete(pg.id);
    setThumbUrl(pg.id, null);
    if (isCur) { curPage = null; await openPage(nb.id, nb.pages[Math.min(i, nb.pages.length - 1)].id); }
    updatePageUI();
    if (!pagesPanel.hidden) renderPagesPanel();
  }

  // ----- סוג דף, דף כהה, מסך מלא, צפייה בלבד, הסתרת הסרגל -----
  function setPaper(t) {
    const pg = curPg();
    if (!pg || !PAPER_TYPES.includes(t) || pg.type === t) return;
    pg.type = curType = t;
    saveRec('notebooks', curNb);
    if (!loading) pageDirty = true;
    invalidateCache(); render();
  }
  function applyDark() {
    inkDark = settings.dark;
    document.body.classList.toggle('dark', settings.dark);
    for (const o of others.values()) o.cache = null;
    invalidateCache(); render();
  }
  function setViewOnly(on) {
    if (on) { flushLive(); clearSelection(); closePops(); }
    viewOnly = on;
    touches.clear(); gesture = null; tap = null; clearLongPress();
    document.body.classList.toggle('viewonly', on);
  }
  const showBar = $('#showBar');
  function setBarHidden(h) {
    settings.barHidden = h; saveSettings();
    closePops();
    document.body.classList.toggle('nobar', h);
    showBar.hidden = !h;
    resize();
  }
  showBar.addEventListener('click', () => setBarHidden(false));
  function toggleFullscreen() {
    const d = document;
    if (d.fullscreenElement) d.exitFullscreen().catch(() => {});
    else d.documentElement.requestFullscreen().catch(() => {});
  }
  if (!document.documentElement.requestFullscreen) $('#fullBtn').hidden = true;

  // ----- ספרייה: תיקיות, מחברות, מועדפים, סל מחזור, הגדרות -----
  const COVERS = ['#3a56d4', '#1f8a70', '#d64545', '#e98b2a', '#8e4fd1', '#2c3e50', '#d4a017', '#e0558f', '#16a0a0', '#7f8c8d'];
  const FCOLORS = ['#4f74e8', '#25a98f', '#f0a13a', '#e75d68', '#9466dc', '#55637d', '#df73ae', '#38a9d4'];
  const hashOf = (s) => Math.abs([...s].reduce((h, ch) => (h * 31 + ch.charCodeAt(0)) | 0, 7));
  const coverOf = (nb) => nb.cover || COVERS[hashOf(nb.id) % COVERS.length];
  const fcolorOf = (f) => f.color || FCOLORS[hashOf(f.id) % FCOLORS.length];
  const SORTS = { updated: 'עריכה אחרונה', name: 'שם', created: 'תאריך יצירה' };
  const FOLDER_PATH = 'M3 7a2 2 0 0 1 2-2h4l2 2h8a2 2 0 0 1 2 2v8a2 2 0 0 1-2 2H5a2 2 0 0 1-2-2z';
  const libBody = $('#libBody'), libSearch = $('#libSearch');
  let libView = 'root', libFolder = '', libQuery = '', libToken = 0;

  // פריט "חי" = לא בסל, וגם אף תיקייה מעליו לא בסל
  function folderAlive(id) {
    let n = 0;
    while (id && n++ < 60) {
      const f = lib.folders.get(id);
      if (!f) return true;
      if (f.trashed) return false;
      id = f.parent;
    }
    return true;
  }
  const nbAlive = (nb) => !nb.trashed && folderAlive(nb.parent);
  const aliveNbs = () => [...lib.notebooks.values()].filter(nbAlive);
  const aliveFolders = () => [...lib.folders.values()].filter((f) => folderAlive(f.id));
  function folderPath(id) {
    const out = [];
    let f = lib.folders.get(id);
    while (f && out.length < 50) { out.unshift(f); f = lib.folders.get(f.parent); }
    return out;
  }
  function descFolders(id) { // כל התיקיות שבתוך (גם אלה שבסל)
    const out = [];
    const walk = (p) => { for (const f of lib.folders.values()) if (f.parent === p && !out.includes(f.id)) { out.push(f.id); walk(f.id); } };
    walk(id);
    return out;
  }
  function nbsUnder(id) { // מחברות חיות בתיקייה ובכל מה שבתוכה
    const set = new Set([id, ...descFolders(id)]);
    return aliveNbs().filter((n) => set.has(n.parent));
  }
  const nbCountText = (n) => (n === 0 ? 'אין מחברות' : n === 1 ? 'מחברת אחת' : n + ' מחברות');
  function sortItems(list, isFolder) {
    const k = settings.libSort;
    if (k === 'name' || (isFolder && k === 'updated')) return list.sort(byName);
    if (k === 'created') return list.sort((a, b) => (b.created || 0) - (a.created || 0));
    return list.sort(byUpdated);
  }
  function favPages() {
    const out = [];
    for (const nb of aliveNbs()) nb.pages.forEach((pg, i) => { if (pg.fav) out.push({ nb, pg, i }); });
    return out;
  }
  function trashItems() {
    const fs = [...lib.folders.values()].filter((f) => f.trashed && folderAlive(f.parent));
    const ns = [...lib.notebooks.values()].filter((n) => n.trashed && folderAlive(n.parent));
    return { fs, ns, n: fs.length + ns.length };
  }
  function dayText(t) {
    if (!t) return '';
    const d = new Date(t), now = new Date();
    const day = (x) => new Date(x.getFullYear(), x.getMonth(), x.getDate()).getTime();
    const diff = Math.round((day(now) - day(d)) / 864e5);
    if (diff === 0) return 'היום';
    if (diff === 1) return 'אתמול';
    return d.getDate() + '.' + (d.getMonth() + 1) + '.' + d.getFullYear();
  }

  // "היום 14:32" / "אתמול 09:05" / "3.12.2026 14:32"
  function stampText(t) {
    if (!t) return '';
    const d = new Date(t), p = (n) => String(n).padStart(2, '0');
    return dayText(t) + ' ' + p(d.getHours()) + ':' + p(d.getMinutes());
  }
  let toastTimer = 0;
  function toast(t) {
    const el = $('#toast');
    el.textContent = t; el.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(() => { el.hidden = true; }, 2800);
  }

  function openLibrary() {
    flushLive(); clearSelection(); closePops();
    saveCurThumb();
    if (curNb && curNb.parent && folderAlive(curNb.parent) && lib.folders.has(curNb.parent)) { libView = 'folder'; libFolder = curNb.parent; }
    else { libView = 'root'; libFolder = ''; }
    libQuery = ''; libSearch.value = '';
    library.hidden = false;
    renderLibrary();
  }
  function closeLibrary() { library.hidden = true; libToken++; closePopMenu(null); }
  function go(view, folder) {
    libView = view; libFolder = folder || '';
    libQuery = ''; libSearch.value = '';
    renderLibrary();
    libBody.scrollTop = 0;
  }

  // ----- סרגל הצד -----
  function backupState() {
    const last = settings.lastBackup || 0;
    const changed = aliveNbs().some((n) => (n.updated || 0) > last);
    const days = last ? Math.floor((Date.now() - last) / 864e5) : Infinity;
    return { last, days, warn: changed && days >= 5 };
  }
  function renderSide() {
    const on = libQuery ? '' : libView;
    library.querySelectorAll('.lib-side > .nav, .side-bottom .nav').forEach((b) => b.classList.toggle('on', b.dataset.view === on));
    const tr = trashItems();
    $('#cntAll').textContent = aliveNbs().length;
    $('#cntFav').textContent = favPages().length || '';
    $('#cntTrash').textContent = tr.n || '';
    $('#cntRoot').textContent = '';
    const tree = $('#sideTree');
    tree.textContent = '';
    const walk = (parent, depth) => {
      for (const f of sortItems(aliveFolders().filter((x) => x.parent === parent), true)) {
        const b = document.createElement('button');
        b.className = 'nav' + (libView === 'folder' && libFolder === f.id && !libQuery ? ' on' : '');
        b.style.paddingInlineStart = (14 + depth * 16) + 'px';
        const dot = document.createElement('span'), nm = document.createElement('span'), c = document.createElement('span');
        dot.className = 'dot'; dot.style.background = fcolorOf(f);
        nm.textContent = f.name; nm.style.overflow = 'hidden'; nm.style.textOverflow = 'ellipsis'; nm.style.whiteSpace = 'nowrap';
        c.className = 'cnt';
        c.textContent = aliveFolders().filter((x) => x.parent === f.id).length + aliveNbs().filter((x) => x.parent === f.id).length;
        b.append(dot, nm, c);
        attachPress(b, () => go('folder', f.id), (a) => folderMenu(f, a)); // לחיצה ארוכה: מחיקה, שינוי שם ועוד
        tree.appendChild(b);
        if (depth < 6) walk(f.id, depth + 1);
      }
    };
    walk('', 0);
    const note = $('#backupNote'), bs = backupState();
    note.className = 'backup-note' + (bs.warn ? ' warn' : '');
    if (bs.warn) note.textContent = bs.last ? 'עברו ' + bs.days + ' ימים מהגיבוי האחרון. הקשה כאן לגיבוי.' : 'עוד לא גיבית. הקשה כאן לגיבוי.';
    else note.textContent = bs.last ? 'גובה לאחרונה: ' + stampText(bs.last) : '';
    note.onclick = bs.warn ? () => exportBackup({}) : null;
  }
  library.querySelectorAll('.nav[data-view]').forEach((b) => b.addEventListener('click', () => go(b.dataset.view)));

  // ----- כותרת, חיפוש, מיון -----
  function renderHead() {
    const cr = $('#libCrumbs');
    cr.textContent = '';
    let title = 'ספרייה', sub = '', nbs = null;
    const crumb = (label, fn) => {
      if (cr.childNodes.length) { const s = document.createElement('span'); s.className = 'sep'; s.textContent = '›'; cr.appendChild(s); }
      const b = document.createElement('button'); b.textContent = label; b.addEventListener('click', fn); cr.appendChild(b);
    };
    if (libQuery) { title = 'חיפוש'; sub = '"' + libQuery + '"'; }
    else if (libView === 'folder') {
      const f = lib.folders.get(libFolder);
      crumb('ספרייה', () => go('root'));
      for (const x of folderPath(libFolder).slice(0, -1)) crumb(x.name, () => go('folder', x.id));
      title = f ? f.name : 'תיקייה';
      nbs = nbsUnder(libFolder);
    } else if (libView === 'all') { title = 'כל המחברות'; nbs = aliveNbs(); }
    else if (libView === 'fav') { title = 'עמודים מועדפים'; const n = favPages().length; sub = n === 1 ? 'עמוד אחד' : n + ' עמודים'; }
    else if (libView === 'trash') { title = 'סל מחזור'; sub = 'מה שנמחק נשאר כאן עד שמוחקים אותו סופית'; }
    else if (libView === 'settings') { title = 'הגדרות'; }
    else nbs = aliveNbs();
    if (nbs) {
      const last = nbs.reduce((m, n) => Math.max(m, n.updated || 0), 0);
      sub = nbCountText(nbs.length) + (last ? ' · עודכן ' + dayText(last) : '');
    }
    $('#libTitle').textContent = title;
    $('#libSub').textContent = sub;
    $('#libTools').hidden = ['fav', 'trash', 'settings'].includes(libView) && !libQuery;
    $('#sortLabel').textContent = SORTS[settings.libSort];
  }
  libSearch.addEventListener('input', () => { libQuery = libSearch.value.trim(); renderLibrary(); });
  $('#libSort').addEventListener('click', async (e) => {
    e.stopPropagation();
    const a = await popMenu(e.currentTarget, Object.keys(SORTS).map((k) => ({ label: (settings.libSort === k ? '✓ ' : '') + SORTS[k], icon: 'sort', value: k })), 'מיון לפי');
    if (a) { settings.libSort = a; saveSettings(); renderLibrary(); }
  });
  $('#libAdd').addEventListener('click', async (e) => {
    e.stopPropagation();
    const a = await popMenu(e.currentTarget, [
      { label: 'מחברת חדשה', icon: 'book', value: 'nb' }, { label: 'תיקייה חדשה', icon: 'folder', value: 'folder' },
      { label: 'ייבוא PDF (מחברת חדשה)', icon: 'pdf', value: 'pdf' }]);
    if (a === 'nb') newNotebookDialog();
    else if (a === 'folder') newFolderDialog();
    else if (a === 'pdf') pickPdf('new');
  });
  $('#libClose').addEventListener('click', closeLibrary);
  $('#libBtn').addEventListener('click', openLibrary);

  // ----- כרטיסים -----
  // הקשה = פתיחה; לחיצה ארוכה (או לחיצה ימנית) = תפריט
  function attachPress(el, onTap, onMenu) {
    let timer = 0, fired = false, sx = 0, sy = 0;
    const end = () => { clearTimeout(timer); el.classList.remove('pressed'); };
    el.addEventListener('pointerdown', (e) => {
      if (e.button > 0) return;
      fired = false; sx = e.clientX; sy = e.clientY;
      el.classList.add('pressed');
      clearTimeout(timer);
      timer = setTimeout(() => {
        fired = true; el.classList.remove('pressed');
        if (navigator.vibrate) navigator.vibrate(15);
        onMenu(el);
      }, 480);
    });
    el.addEventListener('pointermove', (e) => { if (Math.hypot(e.clientX - sx, e.clientY - sy) > 10) end(); });
    el.addEventListener('pointerup', end);
    el.addEventListener('pointercancel', end);
    el.addEventListener('pointerleave', end);
    el.addEventListener('click', () => { if (fired) { fired = false; return; } onTap(el); });
    el.addEventListener('contextmenu', (e) => { e.preventDefault(); if (!fired) { end(); fired = true; onMenu(el); } });
  }
  function grid(cls) {
    const g = document.createElement('div');
    g.className = 'grid ' + cls;
    libBody.appendChild(g);
    return g;
  }
  function secTitle(t) {
    const h = document.createElement('div');
    h.className = 'sec-title'; h.textContent = t;
    libBody.appendChild(h);
  }
  function emptyMsg(t) {
    const e = document.createElement('div');
    e.className = 'lib-empty'; e.textContent = t;
    libBody.appendChild(e);
  }
  function folderCard(g, f, onTap, onMenu) {
    const el = document.createElement('div');
    el.className = 'fcard';
    el.style.background = fcolorOf(f);
    el.innerHTML = '<svg class="fic" viewBox="0 0 24 24"><path d="' + FOLDER_PATH + '"/></svg>';
    const nm = document.createElement('div'), mt = document.createElement('div');
    nm.className = 'fname'; nm.textContent = f.name;
    mt.className = 'fmeta'; mt.textContent = nbCountText(f.trashed ? [...lib.notebooks.values()].filter((n) => new Set([f.id, ...descFolders(f.id)]).has(n.parent)).length : nbsUnder(f.id).length);
    el.append(nm, mt);
    attachPress(el, onTap, onMenu);
    g.appendChild(el);
  }
  function addFolderCard(g) {
    const el = document.createElement('button');
    el.className = 'fcard add';
    el.innerHTML = '<svg viewBox="0 0 24 24"><path d="M12 5v14 M5 12h14"/></svg><span>תיקייה חדשה</span>';
    el.addEventListener('click', newFolderDialog);
    g.appendChild(el);
  }
  function pageCard(g, nb, pg, name, meta, jobs, onTap, onMenu) {
    const el = document.createElement('div');
    el.className = 'ncard' + (nb === curNb && !nb.trashed ? ' cur' : '');
    const prev = document.createElement('div'), img = document.createElement('img'), bar = document.createElement('div');
    prev.className = 'prev'; bar.className = 'bar'; bar.style.background = coverOf(nb);
    img.alt = '';
    prev.append(img, bar);
    const nm = document.createElement('div'), mt = document.createElement('div');
    nm.className = 'nname'; nm.textContent = name;
    mt.className = 'nmeta'; mt.textContent = meta;
    el.append(prev, nm, mt);
    attachPress(el, onTap, onMenu);
    g.appendChild(el);
    jobs.push([pg, img]);
  }
  function nbCard(g, nb, jobs, onTap, onMenu) {
    const pg = nb.pages.find((p) => p.id === nb.last) || nb.pages[0];
    pageCard(g, nb, pg, nb.name, 'נערך ' + dayText(nb.updated), jobs, onTap, onMenu);
  }
  const openNb = (nb) => () => { closeLibrary(); if (nb !== curNb) openPage(nb.id, nb.last); };

  function renderLibrary() {
    const tok = ++libToken, jobs = [];
    if (libView === 'folder' && (!lib.folders.has(libFolder) || !folderAlive(libFolder))) { libView = 'root'; libFolder = ''; }
    renderSide();
    renderHead();
    libBody.textContent = '';
    if (libQuery) {
      const q = libQuery.toLowerCase();
      const fs = sortItems(aliveFolders().filter((f) => f.name.toLowerCase().includes(q)), true);
      const ns = sortItems(aliveNbs().filter((n) => n.name.toLowerCase().includes(q)), false);
      if (!fs.length && !ns.length) emptyMsg('לא נמצא שום דבר בשם הזה');
      if (fs.length) { secTitle('תיקיות'); const g = grid('folders'); for (const f of fs) folderCard(g, f, () => go('folder', f.id), (a) => folderMenu(f, a)); }
      if (ns.length) { secTitle('מחברות'); const g = grid('nbs'); for (const n of ns) nbCard(g, n, jobs, openNb(n), (a) => notebookMenu(n, a)); }
    } else if (libView === 'root' || libView === 'folder') {
      const parent = libView === 'folder' ? libFolder : '';
      const fs = sortItems(aliveFolders().filter((f) => f.parent === parent), true);
      const ns = sortItems(aliveNbs().filter((n) => n.parent === parent), false);
      secTitle('תיקיות');
      const g = grid('folders');
      for (const f of fs) folderCard(g, f, () => go('folder', f.id), (a) => folderMenu(f, a));
      addFolderCard(g);
      secTitle('מחברות');
      if (!ns.length) emptyMsg('אין כאן מחברות עדיין.\nאפשר ליצור בכפתור + למעלה.');
      else { const g2 = grid('nbs'); for (const n of ns) nbCard(g2, n, jobs, openNb(n), (a) => notebookMenu(n, a)); }
    } else if (libView === 'all') {
      const ns = sortItems(aliveNbs(), false);
      if (!ns.length) emptyMsg('אין מחברות עדיין.');
      const g = grid('nbs');
      for (const n of ns) nbCard(g, n, jobs, openNb(n), (a) => notebookMenu(n, a));
    } else if (libView === 'fav') {
      const fp = favPages();
      if (!fp.length) emptyMsg('אין עמודים מועדפים עדיין.\nמוסיפים מרשימת העמודים במחברת (כפתור ⋮ של עמוד).');
      const g = grid('nbs');
      for (const { nb, pg, i } of fp) {
        pageCard(g, nb, pg, nb.name, 'עמוד ' + (i + 1), jobs,
          () => { closeLibrary(); openPage(nb.id, pg.id); },
          async (a) => {
            const r = await popMenu(a, [{ label: 'הסרה מהמועדפים', icon: 'star', value: 'x' }], nb.name + ' · עמוד ' + (i + 1));
            if (r === 'x') { pg.fav = false; saveRec('notebooks', nb); renderLibrary(); }
          });
      }
    } else if (libView === 'trash') {
      const tr = trashItems();
      if (!tr.n) emptyMsg('סל המחזור ריק.');
      else {
        const head = document.createElement('div');
        head.className = 'trash-head';
        const t = document.createElement('span');
        t.textContent = 'הקשה על פריט: שחזור או מחיקה סופית';
        const b = document.createElement('button');
        b.className = 'tbtn'; b.textContent = 'ריקון הסל';
        b.style.color = '#c62828';
        b.addEventListener('click', emptyTrash);
        head.append(t, b);
        libBody.appendChild(head);
      }
      if (tr.fs.length) { secTitle('תיקיות'); const g = grid('folders'); for (const f of tr.fs) folderCard(g, f, (a) => trashMenu(f, 'folders', a), (a) => trashMenu(f, 'folders', a)); }
      if (tr.ns.length) {
        secTitle('מחברות');
        const g = grid('nbs');
        for (const n of tr.ns) {
          const pg = n.pages.find((p) => p.id === n.last) || n.pages[0];
          pageCard(g, n, pg, n.name, 'נמחק ' + dayText(n.trashed), jobs, (a) => trashMenu(n, 'notebooks', a), (a) => trashMenu(n, 'notebooks', a));
        }
      }
    } else if (libView === 'settings') renderSettings();
    fillThumbs(jobs, () => tok === libToken && !library.hidden);
  }

  function renderSettings() {
    const card = (rows) => {
      const c = document.createElement('div');
      c.className = 'set-card';
      for (const r of rows) c.appendChild(r);
      libBody.appendChild(c);
    };
    const row = (label, sub, right) => {
      const r = document.createElement('div');
      r.className = 'set-row';
      const l = document.createElement('div');
      l.textContent = label;
      if (sub) { const s = document.createElement('div'); s.className = 'sub'; s.textContent = sub; l.appendChild(s); }
      r.append(l, right);
      return r;
    };
    const pill = (t, fn) => { const b = document.createElement('button'); b.className = 'pill'; b.textContent = t; b.addEventListener('click', fn); return b; };
    const sw = document.createElement('button');
    sw.className = 'switch' + (settings.dark ? ' on' : '');
    sw.setAttribute('aria-label', 'מצב כהה');
    sw.addEventListener('click', () => { settings.dark = !settings.dark; saveSettings(); applyDark(); renderLibrary(); });
    secTitle('מראה');
    card([row('מצב כהה', 'גם הדף וגם הספרייה כהים', sw)]);
    secTitle('גיבוי');
    const bs = backupState();
    card([
      row('גיבוי כל המחברות לקובץ', bs.last ? 'גובה לאחרונה: ' + stampText(bs.last) : 'עוד לא גיבית', pill('גיבוי עכשיו', () => exportBackup({}))),
      row('שחזור מקובץ גיבוי', 'מוסיף מהקובץ, לא מוחק את מה שכבר כאן', pill('בחירת קובץ', () => restoreFile.click())),
    ]);
    const note = document.createElement('div');
    note.className = 'lib-empty';
    note.style.padding = '18px 4px'; note.style.textAlign = 'right'; note.style.fontSize = '14px';
    note.textContent = 'קובץ הגיבוי נשמר בתיקיית ההורדות של הטאבלט. כדאי להעתיק אותו גם למקום אחר (למשל Google Drive) עד שנחבר גיבוי אוטומטי.';
    libBody.appendChild(note);
  }

  // ----- פעולות -----
  async function askName(title, def, ok) {
    const r = await dialog({ title, input: def, ok });
    return r && r.text.trim() ? r.text.trim().slice(0, 80) : null;
  }
  async function moveItem(item, store) {
    const banned = store === 'folders' ? new Set([item.id, ...descFolders(item.id)]) : new Set();
    const list = [{ label: 'ספרייה (ראשי)', value: '' }];
    for (const f of aliveFolders().sort(byName)) {
      if (!banned.has(f.id)) list.push({ label: folderPath(f.id).map((x) => x.name).join(' › '), value: f.id });
    }
    const to = await dialog({ title: 'העברה אל', list });
    if (to === null || to === undefined || to === item.parent) return;
    item.parent = to;
    saveRec(store, item);
    renderLibrary();
    toast('הועבר');
  }
  async function folderMenu(f, anchor) {
    const a = await popMenu(anchor, [
      { label: 'שינוי שם', icon: 'rename', value: 'ren' }, { label: 'שינוי צבע', icon: 'cover', value: 'color' },
      { label: 'העברה לתיקייה אחרת', icon: 'move', value: 'move' }, { label: 'שכפול', icon: 'copy', value: 'dup' },
      { label: 'גיבוי התיקייה לקובץ', icon: 'backup', value: 'backup' }, '-',
      { label: 'מחיקה', icon: 'del', value: 'del', danger: true }], f.name);
    if (a === 'ren') {
      const n = await askName('שם התיקייה', f.name, 'שמירה');
      if (n) { f.name = n; saveRec('folders', f); renderLibrary(); }
    } else if (a === 'color') {
      const r = await dialog({ title: 'צבע התיקייה', covers: FCOLORS, coverVal: fcolorOf(f), ok: 'שמירה' });
      if (r && r.cover) { f.color = r.cover; saveRec('folders', f); renderLibrary(); }
    } else if (a === 'move') moveItem(f, 'folders');
    else if (a === 'dup') { await duplicateFolder(f); }
    else if (a === 'backup') exportBackup({ folder: f.id });
    else if (a === 'del') {
      const n = nbsUnder(f.id).length;
      const msg = 'להעביר את התיקייה "' + f.name + '" לסל המחזור?\n' + (n ? 'יש בה ' + nbCountText(n) + '. ' : 'התיקייה ריקה. ') + 'אפשר לשחזר מהסל.';
      if (!await dialog({ title: msg, ok: 'העברה לסל', danger: true })) return;
      f.trashed = Date.now();
      saveRec('folders', f);
      afterTrash();
      toast('התיקייה הועברה לסל המחזור');
    }
  }
  async function notebookMenu(nb, anchor) {
    const a = await popMenu(anchor, [
      { label: 'שינוי שם', icon: 'rename', value: 'ren' }, { label: 'שינוי צבע', icon: 'cover', value: 'color' },
      { label: 'העברה לתיקייה אחרת', icon: 'move', value: 'move' }, { label: 'שכפול', icon: 'copy', value: 'dup' },
      { label: 'גיבוי המחברת לקובץ', icon: 'backup', value: 'backup' }, { label: 'ייצוא ל-PDF', icon: 'pdf', value: 'pdf' }, '-',
      { label: 'מחיקה', icon: 'del', value: 'del', danger: true }], nb.name);
    if (a === 'pdf') { exportPdf(nb.pages.slice(), nb.name); return; }
    if (a === 'ren') {
      const n = await askName('שם המחברת', nb.name, 'שמירה');
      if (n) { nb.name = n; saveRec('notebooks', nb); renderLibrary(); updatePageUI(); }
    } else if (a === 'color') {
      const r = await dialog({ title: 'צבע המחברת', covers: COVERS, coverVal: coverOf(nb), ok: 'שמירה' });
      if (r && r.cover) { nb.cover = r.cover; saveRec('notebooks', nb); renderLibrary(); }
    } else if (a === 'move') moveItem(nb, 'notebooks');
    else if (a === 'dup') {
      try { await copyNotebook(nb, nb.parent, ' (עותק)'); toast('המחברת שוכפלה'); } catch (err) { console.error(err); info('השכפול לא הצליח. אפשר לנסות שוב.'); }
      renderLibrary();
    } else if (a === 'backup') exportBackup({ nb: nb.id });
    else if (a === 'del') {
      nb.trashed = Date.now();
      saveRec('notebooks', nb);
      afterTrash();
      toast('המחברת הועברה לסל המחזור');
    }
  }
  // אם המחברת הפתוחה עברה לסל: פותחים מחברת אחרת
  function afterTrash() {
    if (curNb && !nbAlive(curNb)) {
      flushLive(); clearSelection(); saveCurThumb();
      curNb = null; curPage = null;
      openLatest();
    }
    renderLibrary();
  }
  async function trashMenu(item, store, anchor) {
    const a = await popMenu(anchor || libBody, [
      { label: 'שחזור', icon: 'restore', value: 'r' }, '-',
      { label: 'מחיקה סופית', icon: 'del', value: 'd', danger: true }], item.name);
    if (a === 'r') {
      item.trashed = 0;
      if (item.parent && !(lib.folders.has(item.parent) && folderAlive(item.parent))) item.parent = '';
      saveRec(store, item);
      renderLibrary();
      toast('שוחזר');
    } else if (a === 'd') {
      if (store === 'folders') {
        const set = new Set([item.id, ...descFolders(item.id)]);
        const n = [...lib.notebooks.values()].filter((x) => set.has(x.parent)).length;
        if (!await dialog({ title: 'למחוק לצמיתות את התיקייה "' + item.name + '"' + (n ? ' ואת ' + nbCountText(n) + ' שבתוכה' : '') + '?\nאי אפשר לשחזר אחרי זה.', ok: 'מחיקה סופית', danger: true })) return;
        await purgeFolder(item);
      } else {
        if (!await dialog({ title: 'למחוק לצמיתות את המחברת "' + item.name + '"?\nאי אפשר לשחזר אחרי זה.', ok: 'מחיקה סופית', danger: true })) return;
        await purgeNotebooks([item]);
      }
      renderLibrary();
    }
  }
  async function emptyTrash() {
    const tr = trashItems();
    if (!tr.n) return;
    if (!await dialog({ title: 'לרוקן את סל המחזור?\n' + (tr.n === 1 ? 'פריט אחד יימחק' : tr.n + ' פריטים יימחקו') + ' לצמיתות.', ok: 'ריקון הסל', danger: true })) return;
    for (const f of tr.fs) await purgeFolder(f);
    await purgeNotebooks(tr.ns.filter((n) => lib.notebooks.has(n.id)));
    renderLibrary();
  }
  async function purgeFolder(f) {
    const fids = [f.id, ...descFolders(f.id)], set = new Set(fids);
    const nbs = [...lib.notebooks.values()].filter((n) => set.has(n.parent));
    for (const id of fids) { lib.folders.delete(id); persist(() => DB.delRec('folders', id)); }
    await purgeNotebooks(nbs);
  }
  async function purgeNotebooks(list) {
    if (!list.length) return;
    const hasCur = list.includes(curNb);
    if (hasCur) { flushLive(); clearSelection(); pageDirty = false; }
    const pages = [];
    for (const nb of list) {
      lib.notebooks.delete(nb.id);
      persist(() => DB.delRec('notebooks', nb.id));
      for (const p of nb.pages) pages.push(p.id);
    }
    persist(() => DB.delPages(pages));
    for (const p of pages) { histories.delete(p); setThumbUrl(p, null); }
    gcFiles();
    if (hasCur) { curNb = null; curPage = null; await openLatest(); }
  }
  // קובצי PDF שאף עמוד (גם בסל) כבר לא משתמש בהם נמחקים
  function gcFiles() {
    const used = new Set();
    for (const nb of lib.notebooks.values()) for (const p of nb.pages) if (p.bg) used.add(p.bg.file);
    persist(async () => {
      const ids = (await DB.fileIds()).filter((id) => !used.has(id));
      if (ids.length) await DB.delFiles(ids);
      for (const id of ids) pdfDocs.delete(id);
    });
  }

  // ----- שכפול -----
  async function copyNotebook(nb, parent, suffix) {
    flushLive();
    await saveChain;
    const now = Date.now(), pages = [];
    for (const pg of nb.pages) {
      const np = { id: uid(), type: pg.type };
      if (pg.grow) np.grow = true;
      if (pg.h) np.h = pg.h;
      if (pg.bg) np.bg = Object.assign({}, pg.bg); // אותו קובץ PDF, משותף
      pages.push(np);
      const src = await pageData(pg.id);
      const recs = src.strokes.map((s) => ({ id: newId(), page: np.id, type: s.type, color: s.color, size: s.size, pts: Float32Array.from(s.pts) }));
      if (recs.length) await persist(() => DB.putStrokeRecs(recs));
      const irecs = src.images.map((im) => Object.assign(imgRec(im), { id: newId(), page: np.id }));
      if (irecs.length) await persist(() => DB.putImgRecs(irecs));
    }
    const copy = { id: uid(), name: (nb.name + suffix).slice(0, 90), parent, cover: nb.cover, created: now, updated: now, pages, last: pages[0].id };
    await persist(() => DB.putRec('notebooks', copy));
    lib.notebooks.set(copy.id, copy);
    return copy;
  }
  async function copyFolderTree(f, parent, suffix) {
    const nf = { id: uid(), name: (f.name + suffix).slice(0, 90), parent, color: f.color, created: Date.now() };
    await persist(() => DB.putRec('folders', nf));
    lib.folders.set(nf.id, nf);
    for (const c of [...lib.folders.values()].filter((x) => x.parent === f.id && !x.trashed)) await copyFolderTree(c, nf.id, '');
    for (const n of [...lib.notebooks.values()].filter((x) => x.parent === f.id && !x.trashed)) await copyNotebook(n, nf.id, '');
    return nf;
  }
  async function duplicateFolder(f) {
    toast('משכפל…');
    try { await copyFolderTree(f, f.parent, ' (עותק)'); toast('התיקייה שוכפלה'); }
    catch (err) { console.error(err); info('השכפול לא הצליח. אפשר לנסות שוב.'); }
    renderLibrary();
  }

  async function newFolderDialog() {
    const r = await dialog({ title: 'תיקייה חדשה', input: '', placeholder: 'שם התיקייה', covers: FCOLORS, coverVal: FCOLORS[Math.floor(Math.random() * FCOLORS.length)], ok: 'יצירה' });
    if (!r) return;
    const f = { id: uid(), name: r.text.trim().slice(0, 80) || 'תיקייה חדשה', parent: libView === 'folder' ? libFolder : '', color: r.cover, created: Date.now() };
    lib.folders.set(f.id, f);
    saveRec('folders', f);
    if (libQuery) go(libView, libFolder); else renderLibrary();
  }
  async function newNotebookDialog() {
    const r = await dialog({
      title: 'מחברת חדשה', input: '', placeholder: 'שם המחברת', ok: 'יצירה',
      covers: COVERS, coverVal: COVERS[Math.floor(Math.random() * COVERS.length)],
      paper: true, paperVal: curType || 'grid',
    });
    if (!r) return;
    const nb = newNotebook(r.text.trim().slice(0, 80) || 'מחברת ללא שם', libView === 'folder' ? libFolder : '', r.paper || 'grid');
    nb.cover = r.cover;
    saveRec('notebooks', nb);
    closeLibrary();
    openPage(nb.id, nb.pages[0].id);
  }

  // ----- גיבוי לקובץ (עם בדיקה שהקובץ שלם) -----
  function fileStamp() {
    const d = new Date(), p = (n) => String(n).padStart(2, '0');
    return d.getFullYear() + '-' + p(d.getMonth() + 1) + '-' + p(d.getDate()) + '_' + p(d.getHours()) + p(d.getMinutes());
  }
  // שם קובץ בטוח: בלי מירכאות, גרש, לוכסנים וסימנים שמערכת הקבצים לא אוהבת
  const safeName = (s) => (String(s).replace(/["'׳״`\\/:*?<>|\s]+/g, '_').replace(/^_+|_+$/g, '').slice(0, 40) || 'מחברת');
  let backupBusy = false;
  // scope: {} = הכול, { nb } = מחברת אחת, { folder } = תיקייה עם כל מה שבתוכה
  async function exportBackup(scope) {
    if (backupBusy) return;
    backupBusy = true;
    let failed = false;
    try {
      toast('מכין גיבוי…');
      flushLive();
      await saveCurThumb();
      await saveChain;
      let folders = [...lib.folders.values()], nbs = [...lib.notebooks.values()], name = 'הכול';
      if (scope.nb) {
        nbs = nbs.filter((n) => n.id === scope.nb); folders = [];
        name = nbs.length ? nbs[0].name : 'מחברת';
      } else if (scope.folder) {
        const set = new Set([scope.folder, ...descFolders(scope.folder)]);
        folders = folders.filter((f) => set.has(f.id));
        nbs = nbs.filter((n) => set.has(n.parent));
        const f = lib.folders.get(scope.folder);
        name = f ? f.name : 'תיקייה';
      }
      const r2 = (v) => Math.round(v * 100) / 100;
      const parts = ['{"app":"machberet","version":2,"exported":' + JSON.stringify(new Date().toISOString()) +
        ',"folders":' + JSON.stringify(folders) + ',"notebooks":' + JSON.stringify(nbs) + ',"strokes":['];
      let count = 0, icount = 0, fcount = 0;
      const fileIds = new Set();
      for (const nb of nbs) {
        for (const pg of nb.pages) {
          if (pg.bg) fileIds.add(pg.bg.file);
          for (const s of await DB.load(pg.id)) {
            parts.push((count ? ',' : '') + JSON.stringify({ id: s.id, page: s.page, type: s.type, color: s.color, size: s.size, pts: Array.from(s.pts, r2) }));
            count++;
          }
        }
      }
      // תמונות וקובצי PDF: התוכן עצמו בתוך הקובץ (base64), כדי שהגיבוי יהיה שלם
      parts.push('],"images":[');
      for (const nb of nbs) {
        for (const pg of nb.pages) {
          for (const r of await DB.loadImgs(pg.id)) {
            const o = imgRec(r);
            delete o.blob;
            o.data = await blobB64(r.blob);
            parts.push((icount ? ',' : '') + JSON.stringify(o));
            icount++;
          }
        }
      }
      parts.push('],"files":[');
      for (const id of fileIds) {
        const r = await DB.getFile(id);
        if (!r || !r.blob) continue;
        parts.push((fcount ? ',' : '') + JSON.stringify({ id, name: r.name || '', mime: r.blob.type || 'application/pdf', data: await blobB64(r.blob) }));
        fcount++;
      }
      parts.push(']}');
      const blob = new Blob(parts, { type: 'application/json' });
      // בדיקה: קוראים את הקובץ בחזרה ומוודאים שהכול שם
      const back = validateBackup(JSON.parse(await blob.text()));
      if (!back || back.nbs.length !== nbs.length || back.folders.length !== folders.length || back.recs.length !== count ||
        back.imgs.length !== icount || back.files.length !== fcount ||
        back.nbs.some((n, i) => n.name !== nbs[i].name || n.pages.length !== nbs[i].pages.length)) throw new Error('verify');
      const a = document.createElement('a');
      a.href = URL.createObjectURL(blob);
      a.download = 'machberet-' + safeName(name) + '-' + fileStamp() + '.json';
      document.body.appendChild(a); a.click(); a.remove();
      setTimeout(() => URL.revokeObjectURL(a.href), 60000);
      if (!scope.nb && !scope.folder) { settings.lastBackup = Date.now(); saveSettings(); }
      toast('הגיבוי נבדק ונשמר בתיקיית ההורדות ✓');
      if (!library.hidden) renderLibrary();
    } catch (err) {
      console.error(err);
      failed = true;
    } finally { backupBusy = false; }
    if (failed && await dialog({ title: 'הגיבוי לא הצליח.\nשום דבר לא נמחק או השתנה.', ok: 'נסה שוב' })) exportBackup(scope);
  }

  // ----- שחזור: קודם בודקים את כל הקובץ, ורק אז כותבים (בפעולה אחת) -----
  const STROKE_TYPES = ['felt', 'fountain', 'brush', 'pencil', 'hl'];
  const str = (v, def) => (v === undefined || v === null ? def : String(v)).slice(0, 200);
  function blobB64(b) {
    return new Promise((res, rej) => {
      const r = new FileReader();
      r.onload = () => res(String(r.result).split(',')[1] || '');
      r.onerror = () => rej(r.error);
      r.readAsDataURL(b);
    });
  }
  function b64Blob(s, type) {
    const bin = atob(s), u = new Uint8Array(bin.length);
    for (let i = 0; i < bin.length; i++) u[i] = bin.charCodeAt(i);
    return new Blob([u], { type });
  }
  const fin = (v) => typeof v === 'number' && isFinite(v);
  function validateBackup(data) {
    if (!data || data.app !== 'machberet' || !Array.isArray(data.notebooks) || !Array.isArray(data.strokes)) return null;
    if (data.folders !== undefined && !Array.isArray(data.folders)) return null;
    if ((data.images !== undefined && !Array.isArray(data.images)) || (data.files !== undefined && !Array.isArray(data.files))) return null;
    const folders = [], nbs = [], recs = [], pages = [], imgs = [], files = [];
    try {
      for (const f of data.files || []) {
        if (!f || typeof f.id !== 'string' || !f.id || typeof f.data !== 'string') return null;
        files.push({ id: f.id, name: str(f.name, ''), blob: b64Blob(f.data, typeof f.mime === 'string' ? f.mime : 'application/pdf') });
      }
      for (const m of data.images || []) {
        if (!m || !fin(m.id) || typeof m.page !== 'string' || typeof m.data !== 'string' || ![m.x, m.y, m.w, m.h].every(fin) || !(m.w > 0 && m.h > 0)) return null;
        const crop = Array.isArray(m.crop) && m.crop.length === 4 && m.crop.every(fin) ? m.crop : [0, 0, 1, 1];
        const mime = typeof m.mime === 'string' ? m.mime : 'image/png';
        imgs.push({ id: m.id, page: m.page, blob: b64Blob(m.data, mime), mime, x: m.x, y: m.y, w: m.w, h: m.h, rot: [0, 90, 180, 270].includes(m.rot) ? m.rot : 0, crop });
      }
    } catch (e) { return null; } // base64 פגום
    for (const f of data.folders || []) {
      if (!f || typeof f.id !== 'string' || !f.id) return null;
      const r = { id: f.id, name: str(f.name, 'תיקייה'), parent: typeof f.parent === 'string' ? f.parent : '', created: +f.created || Date.now() };
      if (typeof f.color === 'string') r.color = f.color;
      r.trashed = +f.trashed || 0;
      folders.push(r);
    }
    for (const nb of data.notebooks) {
      if (!nb || typeof nb.id !== 'string' || !nb.id || !Array.isArray(nb.pages) || !nb.pages.length) return null;
      const ps = [];
      for (const p of nb.pages) {
        if (!p || typeof p.id !== 'string' || !p.id) return null;
        const np = { id: p.id, type: PAPER_TYPES.includes(p.type) ? p.type : 'grid' };
        if (p.fav) np.fav = true;
        if (p.grow) np.grow = true;
        // עמוד PDF: הפניה לקובץ (שנמצא בגיבוי, או כבר כאן)
        if (p.bg) {
          const b = p.bg;
          if (typeof b.file !== 'string' || !Number.isInteger(b.n) || b.n < 1 || !(b.h > 0) || !fin(b.h)) return null;
          np.bg = { file: b.file, n: b.n, h: b.h };
        }
        if (+p.h > baseH(np)) np.h = +p.h;
        ps.push(np);
        pages.push(p.id);
      }
      const r = {
        id: nb.id, name: str(nb.name, 'מחברת'), parent: typeof nb.parent === 'string' ? nb.parent : '',
        created: +nb.created || Date.now(), updated: +nb.updated || Date.now(), pages: ps,
        last: typeof nb.last === 'string' ? nb.last : ps[0].id,
      };
      if (typeof nb.cover === 'string') r.cover = nb.cover;
      r.trashed = +nb.trashed || 0; // תמיד נקבע: מחברת שנמצאת כאן בסל חוזרת מהסל לפי הגיבוי
      nbs.push(r);
    }
    for (const s of data.strokes) {
      if (!s || typeof s.id !== 'number' || !isFinite(s.id) || typeof s.page !== 'string' || !Array.isArray(s.pts) ||
        s.pts.length < 3 || s.pts.length % 3) return null;
      for (const v of s.pts) if (typeof v !== 'number' || !isFinite(v)) return null;
      recs.push({ id: s.id, page: s.page, type: STROKE_TYPES.includes(s.type) ? s.type : 'fountain', color: typeof s.color === 'string' ? s.color : '#000000', size: +s.size || 2.5, pts: Float32Array.from(s.pts) });
    }
    return { folders, nbs, recs, pages, imgs, files };
  }
  const restoreFile = $('#restoreFile');
  restoreFile.addEventListener('change', async () => {
    const f = restoreFile.files[0];
    restoreFile.value = '';
    if (!f) return;
    let v = null;
    try { v = validateBackup(JSON.parse(await f.text())); } catch (e) { v = null; }
    if (!v) {
      if (await dialog({ title: 'הקובץ הזה פגום, לא שלם, או שהוא לא גיבוי של המחברת.\nלא שיניתי כלום.', ok: 'בחירת קובץ אחר' })) restoreFile.click();
      return;
    }
    const n = v.nbs.length;
    if (!await dialog({ title: 'הקובץ תקין. לשחזר ממנו ' + nbCountText(n) + '?\nמה שכבר קיים כאן לא יימחק. מחברת שנמצאת גם כאן וגם בגיבוי תתעדכן לפי הגיבוי.', ok: 'שחזור' })) return;
    for (;;) {
      try { await applyRestore(v); break; } catch (err) {
        console.error(err);
        if (!await dialog({ title: 'השחזור לא הצליח.\nלא שיניתי כלום.', ok: 'נסה שוב' })) return;
      }
    }
    if (!library.hidden) renderLibrary();
    toast('השחזור הושלם ✓');
  });
  async function applyRestore(v) {
    flushLive(); clearSelection();
    await saveCurThumb();
    await saveChain;
    const known = new Set([...lib.folders.keys(), ...v.folders.map((f) => f.id)]);
    const fRecs = v.folders.map((f) => Object.assign({}, lib.folders.get(f.id) || {}, f, { parent: f.parent && known.has(f.parent) ? f.parent : '' }));
    const nRecs = v.nbs.map((nb) => {
      const old = lib.notebooks.get(nb.id);
      const pages = nb.pages.concat(old ? old.pages.filter((p) => !nb.pages.some((q) => q.id === p.id)) : []);
      return Object.assign({}, old || {}, nb, { pages, parent: nb.parent && known.has(nb.parent) ? nb.parent : '' });
    });
    await DB.restoreAll(fRecs, nRecs, v.recs, v.pages, v.imgs, v.files); // הכול או כלום
    for (const f of v.files) pdfDocs.delete(f.id);
    for (const f of fRecs) { const o = lib.folders.get(f.id); if (o) Object.assign(o, f); else lib.folders.set(f.id, f); }
    for (const n of nRecs) { const o = lib.notebooks.get(n.id); if (o) Object.assign(o, n); else lib.notebooks.set(n.id, n); }
    // מחברת/תיקייה ששוחזרה לתוך תיקייה שנמצאת בסל: עוברת לספרייה הראשית, כדי שתראה אותה
    for (const r of fRecs.concat(nRecs)) {
      const item = lib.folders.get(r.id) || lib.notebooks.get(r.id);
      if (item && !item.trashed && item.parent && !folderAlive(item.parent)) {
        item.parent = '';
        saveRec(lib.folders.has(item.id) ? 'folders' : 'notebooks', item);
      }
    }
    for (const p of v.pages) { setThumbUrl(p, null); histories.delete(p); }
    if (curNb && v.pages.includes(curPage)) await openPage(curNb.id, curPage);
    else updatePageUI();
  }

  // ----- דף שגדל -----
  function maybeGrow(list) {
    const pg = curPg();
    if (!pg || !pg.grow || !list.length) return;
    let bottom = 0;
    for (const st of list) bottom = Math.max(bottom, st.bbox[3]);
    if (bottom < PAGE_H - 250) return;
    while (bottom >= PAGE_H - 250) PAGE_H += GROW_STEP;
    pg.h = PAGE_H;
    saveRec('notebooks', curNb);
    invalidateCache(); clampView(); requestRender();
  }
  const GROW_STEP = 700; // 28 משבצות: הדף תמיד נגמר בסוף משבצת
  function growPage() {
    const pg = curPg();
    if (!pg) return;
    PAGE_H = Math.ceil(PAGE_H / GRID) * GRID + GROW_STEP;
    pg.h = PAGE_H;
    saveRec('notebooks', curNb);
    invalidateCache(); clampView(); render();
    toast('הדף הוארך');
  }
  // הקטנת הדף: מסיר את החלק הריק בסוף, בלי לחתוך כתב (משאיר 4 משבצות ריקות אחרי הכתב)
  function shrinkPage() {
    const pg = curPg();
    if (!pg) return;
    let bottom = 0;
    for (const st of strokes.concat(images)) if (st.bbox) bottom = Math.max(bottom, st.bbox[3]);
    const base = baseH(pg), h = Math.max(base, Math.ceil((bottom + 4 * GRID) / GRID) * GRID);
    if (h >= PAGE_H) { toast(PAGE_H <= base ? 'הדף כבר בגודל רגיל' : 'אין חלק ריק להסרה בסוף הדף'); return; }
    PAGE_H = h;
    if (h > base) pg.h = h; else delete pg.h;
    saveRec('notebooks', curNb);
    invalidateCache(); clampView(); render();
    toast('הדף הוקטן');
  }

  function downloadBlob(blob, name) {
    const a = document.createElement('a');
    a.href = URL.createObjectURL(blob);
    a.download = name;
    document.body.appendChild(a); a.click(); a.remove();
    setTimeout(() => URL.revokeObjectURL(a.href), 60000);
  }

  // ===================== ייבוא PDF =====================
  // הקובץ נשמר פעם אחת; כל עמוד במחברת מפנה לעמוד שלו בקובץ, וכותבים מעליו כמו על דף ריק
  const pdfFile = $('#pdfFile');
  let pdfTarget = 'new', importBusy = false;
  function pickPdf(target) { pdfTarget = target; pdfFile.click(); }
  pdfFile.addEventListener('change', () => {
    const f = pdfFile.files[0];
    pdfFile.value = '';
    if (f) importPdf(f, pdfTarget);
  });
  async function importPdf(file, target) {
    if (importBusy) return;
    importBusy = true;
    let msg = null, ok = false;
    try {
      toast('פותח את הקובץ…');
      const pdfjs = await loadPdfjs();
      const bytes = new Uint8Array(await file.arrayBuffer());
      let doc;
      try { doc = await pdfjs.getDocument({ data: bytes.slice(), isEvalSupported: false }).promise; } catch (err) {
        msg = err && err.name === 'PasswordException' ? 'הקובץ מוגן בסיסמה, ואי אפשר לפתוח אותו כאן.' : 'לא הצלחתי לפתוח את הקובץ.\nייתכן שהוא פגום, או שהוא לא PDF.';
        throw err;
      }
      const n = doc.numPages, fileId = uid(), pages = [];
      for (let i = 1; i <= n; i++) {
        const p = await doc.getPage(i);
        const v = p.getViewport({ scale: 1 });
        pages.push({ id: uid(), type: 'blank', bg: { file: fileId, n: i, h: Math.round(PAGE_W * v.height / v.width * 100) / 100 } });
        p.cleanup();
        if (n > 20 && i % 10 === 0) toast('מייבא… ' + i + '/' + n);
      }
      await persist(() => DB.putFile({ id: fileId, name: String(file.name || ''), blob: new Blob([bytes], { type: 'application/pdf' }) }));
      pdfDocs.set(fileId, Promise.resolve(doc));
      flushLive(); clearSelection();
      if (target === 'append' && curNb) {
        curNb.pages.push(...pages);
        await persist(() => DB.putRec('notebooks', curNb));
        await openPage(curNb.id, pages[0].id);
      } else {
        const now = Date.now(), name = String(file.name || '').replace(/\.pdf$/i, '').trim().slice(0, 80) || 'PDF';
        const nb = { id: uid(), name, parent: !library.hidden && libView === 'folder' ? libFolder : '', created: now, updated: now, pages, last: pages[0].id };
        lib.notebooks.set(nb.id, nb);
        await persist(() => DB.putRec('notebooks', nb));
        closeLibrary();
        await openPage(nb.id, pages[0].id);
      }
      fitWidth(); render();
      toast(n === 1 ? 'נוסף עמוד אחד מה-PDF' : 'נוספו ' + n + ' עמודים מה-PDF');
      ok = true;
    } catch (err) { console.error(err); } finally { importBusy = false; }
    if (!ok && await dialog({ title: msg || 'הייבוא לא הצליח.\nשום דבר לא השתנה.', ok: 'נסה שוב' })) pickPdf(target);
  }

  // ===================== הוספת תמונה (לוח, גלריה, מצלמה) =====================
  const IMG_MAX = 2048; // צד ארוך מקסימלי; תמונה גדולה יותר מוקטנת (חוסך מקום וזיכרון)
  async function prepImageBlob(blob) {
    const bmp = await createImageBitmap(blob);
    let w = bmp.width, h = bmp.height, out = blob;
    if (!w || !h) throw new Error('empty');
    const png = blob.type === 'image/png';
    if (Math.max(w, h) > IMG_MAX || !/^image\/(png|jpeg|webp)$/.test(blob.type) || blob.size > 4e6) {
      const k = Math.min(1, IMG_MAX / Math.max(w, h));
      const c = document.createElement('canvas');
      c.width = Math.max(1, Math.round(w * k)); c.height = Math.max(1, Math.round(h * k));
      const g = c.getContext('2d');
      if (!png) { g.fillStyle = '#fff'; g.fillRect(0, 0, c.width, c.height); }
      g.imageSmoothingQuality = 'high';
      g.drawImage(bmp, 0, 0, c.width, c.height);
      out = await new Promise((res) => c.toBlob(res, png ? 'image/png' : 'image/jpeg', 0.9));
      w = c.width; h = c.height;
    }
    if (bmp.close) bmp.close();
    if (!out) throw new Error('encode');
    return { blob: out, w, h };
  }
  async function insertImage(blob, retry) {
    if (!curPage || loading) return;
    if (viewOnly) setViewOnly(false);
    let r;
    try { r = await prepImageBlob(blob); } catch (err) {
      console.error(err);
      if (await dialog({ title: 'לא הצלחתי לפתוח את התמונה.', ok: retry ? 'נסה שוב' : 'סגירה', noCancel: !retry }) && retry) retry();
      return;
    }
    flushLive(); clearSelection();
    // במרכז מה שרואים על המסך, בגודל שנראה טבעי, ולא גדול מהמסך
    const vx0 = Math.max(0, -view.ox / view.s), vy0 = Math.max(0, -view.oy / view.s);
    const vx1 = Math.min(PAGE_W, (W - view.ox) / view.s), vy1 = Math.min(PAGE_H, (H - view.oy) / view.s);
    const vw = Math.max(100, vx1 - vx0), vh = Math.max(100, vy1 - vy0);
    let w = r.w / dpr / view.s, h = r.h / dpr / view.s;
    const k = Math.min(1, vw * 0.8 / w, vh * 0.8 / h, PAGE_W * 0.9 / w);
    w *= k; h *= k;
    const x = Math.max(0, Math.min(PAGE_W - w, (vx0 + vx1) / 2 - w / 2));
    const y = Math.max(0, Math.min(PAGE_H - h, (vy0 + vy1) / 2 - h / 2));
    const im = makeImg({ id: newId(), page: curPage, blob: r.blob, mime: r.blob.type, x, y, w, h, rot: 0 });
    commit({ add: [im], remove: [] });
    sel = makeSel([im]);
    updateUI();
    render();
    toast('גוררים להזזה, פינה לשינוי גודל. חיתוך וסיבוב בסרגל.');
  }
  const galFile = $('#galFile'), camFile = $('#camFile');
  for (const inp of [galFile, camFile]) {
    inp.addEventListener('change', () => {
      const f = inp.files[0];
      inp.value = '';
      if (f) insertImage(f, () => inp.click());
    });
  }
  async function pasteImage() {
    let msg = 'לא הצלחתי לקרוא את הלוח.\nאם הדפדפן שואל, צריך לאשר גישה ללוח.';
    try {
      if (navigator.clipboard && navigator.clipboard.read) {
        for (const it of await navigator.clipboard.read()) {
          const t = it.types.find((x) => x.startsWith('image/'));
          if (t) { insertImage(await it.getType(t), pasteImage); return; }
        }
        msg = 'אין תמונה בלוח.\nמעתיקים תמונה (למשל צילום מסך: שיתוף ← העתקה), ואז מנסים שוב.';
      }
    } catch (err) { console.error(err); }
    if (await dialog({ title: msg, ok: 'נסה שוב' })) pasteImage();
  }
  document.addEventListener('paste', (e) => {
    if (!library.hidden || !dlg.hidden || !e.clipboardData) return;
    const f = [...e.clipboardData.files].find((x) => x.type.startsWith('image/'));
    if (f) { e.preventDefault(); insertImage(f); }
  });

  // ===================== ייצוא PDF =====================
  // כתב וקווי הדף כווקטורים (חדים בכל זום), עמוד PDF מיובא נשאר המקורי, ותמונות כמו שהן במחברת
  let pdfLibP = null;
  function loadPdfLib() {
    if (window.PDFLib) return Promise.resolve(window.PDFLib);
    if (!pdfLibP) {
      pdfLibP = new Promise((res, rej) => {
        const s = document.createElement('script');
        s.src = 'lib/pdf-lib.min.js';
        s.onload = () => (window.PDFLib ? res(window.PDFLib) : rej(new Error('pdflib')));
        s.onerror = () => rej(new Error('pdflib'));
        document.head.appendChild(s);
      });
      pdfLibP.catch(() => { pdfLibP = null; });
    }
    return pdfLibP;
  }
  const f2 = (v) => Math.round(v * 100) / 100;
  function pdfRgb(P, c) { const [r, g, b] = hexRgb(c); return P.rgb(r / 255, g / 255, b / 255); }
  // "קנבס" שמתרגם את ציור קווי הדף (drawPaper) לפקודות PDF
  function pdfPaperCtx(P, page, k, Hpt) {
    let d = '', fill = '#ffffff', strokeC = '#000000', lw = 1;
    return {
      globalAlpha: 1,
      set fillStyle(v) { fill = v; },
      set strokeStyle(v) { strokeC = v; },
      set lineWidth(v) { lw = v; },
      fillRect(x, y, w, h) { page.drawRectangle({ x: x * k, y: Hpt - (y + h) * k, width: w * k, height: h * k, color: pdfRgb(P, fill) }); },
      beginPath() { d = ''; },
      moveTo(x, y) { d += 'M ' + f2(x) + ' ' + f2(y) + ' '; },
      lineTo(x, y) { d += 'L ' + f2(x) + ' ' + f2(y) + ' '; },
      stroke() { if (d) page.drawSvgPath(d, { x: 0, y: Hpt, scale: k, borderColor: pdfRgb(P, strokeC), borderWidth: lw }); },
    };
  }
  // נקודות לאורך הקו המוחלק [x, y, רדיוס, ...], באותה עקומה כמו על המסך
  function strokeSamples(st) {
    const pts = st.pts, n = st.n, out = [], ar = st.arc;
    sp(pts, n, 0, B);
    out.push(B[0], B[1], radiusAt(st, B[2], 0));
    for (let i = 0; i < n - 1; i++) {
      sp(pts, n, i - 1, A); sp(pts, n, i, B); sp(pts, n, i + 1, C); sp(pts, n, i + 2, D);
      const steps = Math.max(1, Math.ceil(Math.hypot(C[0] - B[0], C[1] - B[1]) / 3));
      const s0 = ar ? ar[Math.min(i, n - 1)] : 0, s1 = ar ? ar[Math.min(i + 1, n - 1)] : 0;
      for (let q = 1; q <= steps; q++) {
        const t = q / steps, t2 = t * t, t3 = t2 * t;
        const x = 0.5 * (2 * B[0] + (C[0] - A[0]) * t + (2 * A[0] - 5 * B[0] + 4 * C[0] - D[0]) * t2 + (3 * B[0] - A[0] - 3 * C[0] + D[0]) * t3);
        const y = 0.5 * (2 * B[1] + (C[1] - A[1]) * t + (2 * A[1] - 5 * B[1] + 4 * C[1] - D[1]) * t2 + (3 * B[1] - A[1] - 3 * C[1] + D[1]) * t3);
        out.push(x, y, radiusAt(st, B[2] + (C[2] - B[2]) * t, s0 + (s1 - s0) * t));
      }
    }
    return out;
  }
  function pdfStroke(P, page, st, k, Hpt) {
    const color = pdfRgb(P, st.color), S = strokeSamples(st), m = S.length / 3;
    const opacity = st.type === 'hl' ? HL_ALPHA : undefined;
    if (m === 1) { page.drawCircle({ x: S[0] * k, y: Hpt - S[1] * k, size: Math.max(0.2, S[2]) * k, color, opacity }); return; }
    const opt = (w) => ({ x: 0, y: Hpt, scale: k, borderColor: color, borderWidth: w, borderOpacity: opacity, borderLineCap: P.LineCapStyle.Round });
    page.pushOperators(P.pushGraphicsState(), P.setLineJoin(P.LineJoinStyle.Round));
    if (st.type === 'felt' || st.type === 'hl') { // עובי אחיד: מסלול אחד (גם כדי שמדגש שקוף לא יכהה בחפיפות)
      let d = 'M ' + f2(S[0]) + ' ' + f2(S[1]);
      for (let i = 1; i < m; i++) d += ' L ' + f2(S[i * 3]) + ' ' + f2(S[i * 3 + 1]);
      page.drawSvgPath(d, opt(Math.max(0.2, S[2] * 2)));
    } else { // עובי משתנה: רצפים של מקטעים באותו עובי (בקפיצות של 0.25), עם קצוות עגולים
      let d = '', q = -1;
      for (let i = 0; i < m - 1; i++) {
        const w = Math.max(0.25, Math.round((S[i * 3 + 2] + S[i * 3 + 5]) / 0.25) * 0.25);
        if (w !== q) { if (d) page.drawSvgPath(d, opt(q)); q = w; d = 'M ' + f2(S[i * 3]) + ' ' + f2(S[i * 3 + 1]); }
        d += ' L ' + f2(S[i * 3 + 3]) + ' ' + f2(S[i * 3 + 4]);
      }
      if (d) page.drawSvgPath(d, opt(q));
    }
    page.pushOperators(P.popGraphicsState());
  }
  async function pdfImage(P, doc, page, im, k, Hpt) {
    const c = im.crop, plain = !im.rot && c[0] === 0 && c[1] === 0 && c[2] === 1 && c[3] === 1;
    const png = im.mime === 'image/png';
    let bytes;
    if (plain && (png || im.mime === 'image/jpeg')) bytes = new Uint8Array(await im.blob.arrayBuffer());
    else { // חיתוך / סיבוב / סוג אחר: מכינים את התמונה כמו שהיא מוצגת
      const b = await decodeImg(im);
      if (!b) return;
      const sw = Math.max(1, Math.round((c[2] - c[0]) * b.width)), sh = Math.max(1, Math.round((c[3] - c[1]) * b.height));
      const odd = im.rot % 180 !== 0, cv = document.createElement('canvas');
      cv.width = odd ? sh : sw; cv.height = odd ? sw : sh;
      const g = cv.getContext('2d');
      if (!png) { g.fillStyle = '#fff'; g.fillRect(0, 0, cv.width, cv.height); }
      g.translate(cv.width / 2, cv.height / 2);
      g.rotate(im.rot * Math.PI / 180);
      g.drawImage(b, c[0] * b.width, c[1] * b.height, (c[2] - c[0]) * b.width, (c[3] - c[1]) * b.height, -sw / 2, -sh / 2, sw, sh);
      const blob = await new Promise((res) => cv.toBlob(res, png ? 'image/png' : 'image/jpeg', 0.92));
      if (!blob) throw new Error('encode');
      bytes = new Uint8Array(await blob.arrayBuffer());
    }
    const emb = png ? await doc.embedPng(bytes) : await doc.embedJpg(bytes);
    page.drawImage(emb, { x: im.x * k, y: Hpt - (im.y + im.h) * k, width: im.w * k, height: im.h * k });
  }
  // עמוד מהקובץ המקורי (וקטורי). אם אי אפשר (למשל קובץ מוצפן): כתמונה ברזולוציה גבוהה
  async function pdfSrcPage(P, srcDocs, bg) {
    let src = srcDocs.get(bg.file);
    if (src === undefined) {
      try { src = await P.PDFDocument.load(await fileBytes(bg.file)); } catch (e) { console.error(e); src = null; }
      srcDocs.set(bg.file, src);
    }
    if (!src || bg.n > src.getPageCount()) return null;
    return src.getPage(bg.n - 1);
  }
  async function pdfRasterBg(P, doc, page, pg, k, Hpt) {
    const pdoc = await getPdf(pg.bg.file), p = await pdoc.getPage(pg.bg.n);
    const v1 = p.getViewport({ scale: 1 }), vp = p.getViewport({ scale: 2000 / v1.width });
    const c = document.createElement('canvas');
    c.width = Math.round(vp.width); c.height = Math.round(vp.height);
    const g = c.getContext('2d');
    g.fillStyle = '#fff'; g.fillRect(0, 0, c.width, c.height);
    await p.render({ canvasContext: g, viewport: vp }).promise;
    const blob = await new Promise((res) => c.toBlob(res, 'image/jpeg', 0.9));
    c.width = 0;
    if (!blob) throw new Error('encode');
    const emb = await doc.embedJpg(new Uint8Array(await blob.arrayBuffer()));
    page.drawImage(emb, { x: 0, y: Hpt - pg.bg.h * k, width: PAGE_W * k, height: pg.bg.h * k });
  }
  let exportBusy = false;
  async function exportPdf(pages, name) {
    if (exportBusy || !pages.length) return;
    exportBusy = true;
    let failed = false;
    try {
      toast('מכין PDF…');
      flushLive();
      await saveChain;
      const P = await loadPdfLib();
      const doc = await P.PDFDocument.create();
      const srcDocs = new Map();
      let i = 0;
      for (const pg of pages) {
        if (pages.length > 3) toast('מכין PDF… ' + (++i) + '/' + pages.length);
        const data = await pageData(pg.id), H = pg.id === curPage ? PAGE_H : pageH(pg);
        let k = 595.28 / PAGE_W, emb = null, rot = 0; // רוחב A4
        if (pg.bg) {
          const sp = await pdfSrcPage(P, srcDocs, pg.bg);
          if (sp) {
            try {
              const cb = sp.getCropBox();
              emb = await doc.embedPage(sp, { left: cb.x, bottom: cb.y, right: cb.x + cb.width, top: cb.y + cb.height });
              rot = ((sp.getRotation().angle % 360) + 360) % 360;
              k = (rot % 180 ? emb.height : emb.width) / PAGE_W;
            } catch (e) { console.error(e); emb = null; }
          }
        }
        const Hpt = H * k, page = doc.addPage([PAGE_W * k, Hpt]);
        withH(H, () => drawPaper(pdfPaperCtx(P, page, k, Hpt), pg.type, false, 0.8, 0, 0, PAGE_W, H));
        if (emb) {
          const w0 = emb.width, h0 = emb.height, base = Hpt - (rot % 180 ? w0 : h0);
          const o = rot === 90 ? [0, base + w0, -90] : rot === 180 ? [w0, base + h0, 180] : rot === 270 ? [h0, base, 90] : [0, base, 0];
          page.drawPage(emb, { x: o[0], y: o[1], rotate: P.degrees(o[2]) });
        } else if (pg.bg) await pdfRasterBg(P, doc, page, pg, k, Hpt);
        for (const im of data.images) await pdfImage(P, doc, page, im, k, Hpt);
        for (const st of data.strokes) pdfStroke(P, page, st, k, Hpt);
      }
      const bytes = await doc.save();
      // בדיקה: פותחים את הקובץ שנוצר ומוודאים שכל העמודים שם
      if ((await P.PDFDocument.load(bytes)).getPageCount() !== pages.length) throw new Error('verify');
      downloadBlob(new Blob([bytes], { type: 'application/pdf' }), 'machberet-' + safeName(name) + '-' + fileStamp() + '.pdf');
      toast('ה-PDF נשמר בתיקיית ההורדות ✓');
    } catch (err) { console.error(err); failed = true; } finally { exportBusy = false; }
    if (failed && await dialog({ title: 'הייצוא ל-PDF לא הצליח.\nשום דבר לא השתנה.', ok: 'נסה שוב' })) exportPdf(pages, name);
  }
  async function exportPdfMenu() {
    if (!curNb) return;
    const nb = curNb, pg = curPg();
    let what = 'all';
    if (nb.pages.length > 1) {
      what = await dialog({ title: 'ייצוא ל-PDF', list: [
        { label: 'העמוד הזה', value: 'page' }, { label: 'כל המחברת (' + nb.pages.length + ' עמודים)', value: 'all' }] });
      if (!what) return;
    }
    exportPdf(what === 'page' && pg ? [pg] : nb.pages.slice(), nb.name + (what === 'page' ? '-עמוד' + (nb.pages.indexOf(pg) + 1) : ''));
  }

  // ===================== תפריט "..." =====================
  const paperGrid = $('#paperGrid');
  buildPaperTiles(paperGrid, () => curType, setPaper);
  function updateMenu() {
    paperGrid.querySelectorAll('[data-paper]').forEach((b) => b.classList.toggle('active', b.dataset.paper === curType));
    $('#darkBtn').classList.toggle('on', settings.dark);
    $('#growBtn').classList.toggle('on', !!(curPg() && curPg().grow));
    $('#contBtn').classList.toggle('on', settings.continuous);
    $('#favBtn').classList.toggle('on', !!(curPg() && curPg().fav));
    $('#fullBtn').classList.toggle('on', !!document.fullscreenElement);
    $('#viewBtn').classList.toggle('on', viewOnly);
    $('#fastBtn').classList.toggle('on', settings.fastInk);
  }
  $('#more').addEventListener('click', (e) => {
    e.stopPropagation();
    const wasHidden = menu.hidden;
    closePops();
    if (wasHidden) updateMenu();
    menu.hidden = !wasHidden;
  });
  document.addEventListener('pointerdown', (e) => {
    const t = e.target;
    if (!menu.hidden && !menu.contains(t) && !t.closest('#more')) closeMenu();
    if (!palette.hidden && !palette.contains(t) && !t.closest('.swatch.add')) closePalette();
    // החלפת גודל/צבע בסרגל לא סוגרת את תפריט העט, כדי לראות את השינוי ב"נסה כאן"
    const keepPen = t.closest('#sizes') || t.closest('.swatch:not(.add)');
    for (const [k, el] of Object.entries(pops)) {
      if (k === 'pen' && keepPen) continue;
      if (!el.hidden && !el.contains(t) && !t.closest('[data-tool=' + k + ']')) el.hidden = true;
    }
    if (!colorEdit.hidden && !colorEdit.contains(t)) colorEdit.hidden = true;
    if (!ctxMenu.hidden && !ctxMenu.contains(t)) ctxMenu.hidden = true;
    if (!pagesPanel.hidden && !pagesPanel.contains(t) && !t.closest('#pagesBtn') && !t.closest('#dlg')) pagesPanel.hidden = true;
  });
  menu.addEventListener('click', async (e) => {
    const btn = e.target.closest('button');
    if (!btn) return;
    if (btn.dataset.paper) return; // סוג דף: מטופל באריחים, והתפריט נשאר פתוח כדי לראות את השינוי
    const cmd = btn.dataset.cmd;
    closeMenu();
    if (cmd === 'fit') { fitWidth(); render(); }
    else if (cmd === 'cont') {
      settings.continuous = !settings.continuous; saveSettings();
      others.clear(); clampView(); render();
      toast(settings.continuous ? 'גלילה רציפה: העמודים אחד אחרי השני' : 'עמוד אחד בכל פעם');
    } else if (cmd === 'fav') { const pg = curPg(); if (pg) { pg.fav = !pg.fav; saveRec('notebooks', curNb); toast(pg.fav ? 'העמוד נוסף למועדפים ★' : 'העמוד הוסר מהמועדפים'); } }
    else if (cmd === 'grow') { const pg = curPg(); if (pg) { pg.grow = !pg.grow; saveRec('notebooks', curNb); toast(pg.grow ? 'הדף יתארך כשכותבים ליד הסוף' : 'הדף לא יתארך יותר'); } }
    else if (cmd === 'shrink') shrinkPage();
    else if (cmd === 'dark') { settings.dark = !settings.dark; saveSettings(); applyDark(); }
    else if (cmd === 'full') toggleFullscreen();
    else if (cmd === 'view') setViewOnly(!viewOnly);
    else if (cmd === 'hidebar') setBarHidden(true);
    else if (cmd === 'backup') exportBackup({ nb: curNb && curNb.id });
    else if (cmd === 'imgGal') galFile.click();
    else if (cmd === 'imgCam') camFile.click();
    else if (cmd === 'imgPaste') pasteImage();
    else if (cmd === 'pdfAdd') pickPdf('append');
    else if (cmd === 'pdfExport') exportPdfMenu();
    else if (cmd === 'fast') {
      settings.fastInk = !settings.fastInk;
      saveSettings();
      location.reload(); // הגדרת הקנבס נקבעת רק בטעינה
    } else if (cmd === 'clear') {
      clearSelection();
      if (!(strokes.length || images.length) || viewOnly || loading) return;
      if (await dialog({ title: 'לנקות את כל הדף?\nאפשר להחזיר עם "ביטול".', ok: 'ניקוי' })) commit({ add: [], remove: strokes.concat(images) });
    }
  });

  // ===================== הפעלה =====================
  inkDark = settings.dark;
  document.body.classList.toggle('dark', settings.dark);
  document.body.classList.toggle('nobar', settings.barHidden);
  showBar.hidden = !settings.barHidden;
  fillSizes(sizesEl, inkTool(), pickBarSize);
  buildColors();
  updateUI();
  updateUndoUI();
  resize();

  async function boot() {
    try {
      const [fs, nbs] = await Promise.all([DB.all('folders'), DB.all('notebooks')]);
      for (const f of fs) lib.folders.set(f.id, f);
      for (const n of nbs) if (n && Array.isArray(n.pages) && n.pages.length) lib.notebooks.set(n.id, n);
      if (!lib.notebooks.size) {
        // פעם ראשונה אחרי העדכון: הדף הקיים (p1) הופך לעמוד הראשון של מחברת
        const now = Date.now();
        const nb = { id: uid(), name: 'המחברת שלי', parent: '', created: now, updated: now, pages: [{ id: 'p1', type: 'grid' }] };
        lib.notebooks.set(nb.id, nb);
        await persist(() => DB.putRec('notebooks', nb));
      }
      const nb = lib.notebooks.get(settings.nb);
      if (nb && nbAlive(nb)) await openPage(nb.id, settings.page); else await openLatest();
    } catch (err) { console.error(err); setStatus('⚠ אין גישה לאחסון'); }
  }
  boot();
  if (navigator.storage && navigator.storage.persist) navigator.storage.persist().catch(() => {});
  if ('serviceWorker' in navigator && (location.protocol === 'https:' || location.hostname === 'localhost')) {
    navigator.serviceWorker.register('sw.js').catch(() => {});
  }
})();
