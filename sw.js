// רשת קודם (כדי לקבל עדכונים מיד), ומטמון כשאין אינטרנט או כשהרשת איטית מדי
const CACHE = 'machberet-v6';
const FILES = ['./', './index.html', './style.css', './app.js', './manifest.webmanifest',
  './icon.svg', './icon-192.png', './icon-512.png', './icon-maskable.png',
  './lib/pdf.min.js', './lib/pdf.worker.min.js', './lib/pdf-lib.min.js'];

self.addEventListener('install', (e) => {
  e.waitUntil(caches.open(CACHE).then((c) => c.addAll(FILES.map((f) => new Request(f, { cache: 'reload' })))));
  self.skipWaiting();
});

self.addEventListener('activate', (e) => {
  e.waitUntil(
    caches.keys()
      .then((ks) => Promise.all(ks.filter((k) => k !== CACHE).map((k) => caches.delete(k))))
      .then(() => self.clients.claim())
  );
});

async function fromCache(req) {
  const hit = await caches.match(req, { ignoreSearch: true });
  if (hit) return hit;
  if (req.mode === 'navigate') return caches.match('./index.html');
  return Response.error();
}

self.addEventListener('fetch', (e) => {
  const req = e.request;
  if (req.method !== 'GET' || new URL(req.url).origin !== location.origin) return;
  e.respondWith((async () => {
    const net = fetch(req, { cache: 'no-cache' }).then((r) => {
      if (r.ok) { const copy = r.clone(); caches.open(CACHE).then((c) => c.put(req, copy)); }
      return r;
    });
    // אינטרנט חלש: אחרי 4 שניות פותחים מהמטמון (הרשת ממשיכה לעדכן ברקע)
    const timer = new Promise((res) => setTimeout(() => res(null), 4000));
    try {
      const r = await Promise.race([net, timer]);
      if (r) return r;
      return (await caches.match(req, { ignoreSearch: true })) || await net;
    } catch {
      return fromCache(req);
    }
  })());
});
