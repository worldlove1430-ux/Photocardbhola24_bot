import io
import json
import os
import re
import threading
import zipfile
from datetime import datetime, timedelta, timezone
from html import unescape
from urllib.parse import unquote, urlparse

import freetype
import requests
import uharfbuzz as hb
from flask import Flask, request
from PIL import Image, ImageChops, ImageDraw, ImageOps

app = Flask(__name__)

TOKEN = os.environ.get("BOT_TOKEN", "")
API = f"https://api.telegram.org/bot{TOKEN}"
BASE_URL = os.environ.get("RENDER_EXTERNAL_URL", "")
URL_RE = re.compile(r"https?://\S+")
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Linux; Android 13; SM-A556E) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/124.0 Mobile Safari/537.36",
    "Accept-Language": "bn-BD,bn;q=0.9,en;q=0.8",
}

# ---------------------------------------------------------------- assets
HERE = os.path.dirname(os.path.abspath(__file__))
ASSET_DIR = os.path.join("/tmp", "card_assets")


def prepare_assets():
    os.makedirs(ASSET_DIR, exist_ok=True)
    zp = os.path.join(HERE, "assets.zip")
    if os.path.exists(zp):
        with zipfile.ZipFile(zp) as z:
            z.extractall(ASSET_DIR)


def asset(name):
    for d in (ASSET_DIR, HERE):
        p = os.path.join(d, name)
        if os.path.exists(p):
            return p
    raise FileNotFoundError(name)


prepare_assets()

# ---------------------------------------------------------------- card layout
W, H = 1229, 1536
PHOTO_H = 678
BANNER_Y, BANNER_H = 1384, 152
RED = (231, 65, 45)
BLACK = (20, 20, 20)
DEFAULT_BADGE = "বিস্তারিত কমেন্টে"
BN_DIGITS = str.maketrans("0123456789", "০১২৩৪৫৬৭৮৯")
BN_MONTHS = ["জানুয়ারি", "ফেব্রুয়ারি", "মার্চ", "এপ্রিল", "মে", "জুন", "জুলাই",
             "আগস্ট", "সেপ্টেম্বর", "অক্টোবর", "নভেম্বর", "ডিসেম্বর"]
FLAGS = freetype.FT_LOAD_RENDER | freetype.FT_LOAD_NO_HINTING


class Face:
    def __init__(self, path):
        self.hbface = hb.Face(hb.Blob.from_file_path(path))
        self.hbfont = hb.Font(self.hbface)
        self.upem = self.hbface.upem
        self.ft = freetype.Face(path)

    def shape(self, text, size):
        buf = hb.Buffer()
        buf.add_str(text)
        buf.guess_segment_properties()
        hb.shape(self.hbfont, buf, {"kern": True, "liga": True})
        k = size / self.upem
        glyphs, x = [], 0.0
        for info, pos in zip(buf.glyph_infos, buf.glyph_positions):
            glyphs.append((info.codepoint, x + pos.x_offset * k, pos.y_offset * k))
            x += pos.x_advance * k
        return glyphs, x

    def width(self, text, size):
        return self.shape(text, size)[1]

    def draw(self, img, text, size, x, baseline, color):
        glyphs, w = self.shape(text, size)
        self.ft.set_char_size(int(size * 64), 0, 72, 72)
        pad = int(size)
        base = int(size * 1.5)
        mask = Image.new("L", (int(w) + 2 * pad, int(size * 2.4)), 0)
        for gid, gx, gy in glyphs:
            self.ft.load_glyph(gid, FLAGS)
            g = self.ft.glyph
            bm = g.bitmap
            if bm.width == 0 or bm.rows == 0:
                continue
            gi = Image.frombuffer("L", (bm.width, bm.rows), bytes(bm.buffer), "raw", "L", bm.pitch, 1)
            px = pad + int(round(gx)) + g.bitmap_left
            py = base - g.bitmap_top - int(round(gy))
            box = (px, py, px + bm.width, py + bm.rows)
            mask.paste(ImageChops.lighter(mask.crop(box), gi), box)
        img.paste(color, (int(x) - pad, int(baseline) - base), mask)


_faces = {}


def face(name):
    if name not in _faces:
        _faces[name] = Face(asset(name))
    return _faces[name]


def bn_date(dt):
    return f"{str(dt.day).translate(BN_DIGITS)} {BN_MONTHS[dt.month - 1]} {str(dt.year).translate(BN_DIGITS)}"


def now_bd():
    return datetime.now(timezone(timedelta(hours=6)))


def cover(im, w, h, focus_y=0.35):
    im = ImageOps.exif_transpose(im).convert("RGB")
    s = max(w / im.width, h / im.height)
    nw, nh = int(im.width * s + 0.999), int(im.height * s + 0.999)
    im = im.resize((nw, nh), Image.LANCZOS)
    left = (nw - w) // 2
    top = int((nh - h) * focus_y)
    return im.crop((left, top, left + w, top + h))


def layout_words(words, f, size, maxw):
    sp = f.width(" ", size)
    lines, cur, curw = [], [], 0.0
    for i, wd in enumerate(words):
        ww = f.width(wd[0], size)
        if cur and curw + sp + ww > maxw:
            lines.append((cur, curw))
            cur, curw = [], 0.0
        curw += (sp if cur else 0) + ww
        cur.append((wd[0], wd[1], ww))
    if cur:
        lines.append((cur, curw))
    return lines, sp


def tokenize(title):
    """Red words, last word black. A | in the text decides the split instead."""
    title = " ".join(title.split())
    if "|" in title:
        left, right = title.split("|", 1)
        return [(w, RED) for w in left.split()] + [(w, BLACK) for w in right.split()]
    words = title.split()
    return [(w, RED if i < len(words) - 1 else BLACK) for i, w in enumerate(words)]


def make_card(photo, title, date_text, badge=DEFAULT_BADGE, banner=None):
    card = Image.new("RGB", (W, H), (255, 255, 255))
    card.paste(Image.open(asset("template.png")).convert("RGB"), (0, PHOTO_H))
    card.paste(cover(photo, W, PHOTO_H), (0, 0))
    if banner is not None:
        card.paste(cover(banner, W, BANNER_H, 0.5), (0, BANNER_Y))

    # badge
    bf = face("HindSiliguri-SemiBold.ttf")
    bsize = 40
    bw = int(bf.width(badge, bsize)) + 84
    bx = (W - bw) // 2
    d = ImageDraw.Draw(card)
    d.rounded_rectangle((bx, 700, bx + bw, 764), radius=24, fill=RED, outline=(255, 255, 255), width=4)
    bf.draw(card, badge, bsize, bx + (bw - bf.width(badge, bsize)) / 2, 700 + 46, (255, 255, 255))

    # headline
    hf = face("HindSiliguri-Bold.ttf")
    words = tokenize(title) or [(" ", BLACK)]
    maxw = 1140
    size = 120
    while True:
        lines, sp = layout_words(words, hf, size, maxw)
        if (len(lines) <= 3 and len(lines) * size * 1.3 <= 330) or size <= 52:
            break
        size -= 4
    lh = size * 1.3
    top = 985 - len(lines) * lh / 2
    for n, (ws, lw) in enumerate(lines):
        x = (W - lw) / 2
        baseline = top + n * lh + size * 1.0
        for wd, color, ww in ws:
            hf.draw(card, wd, size, x, baseline, color)
            x += ww + sp

    # logo
    logo = Image.open(asset("logo.png")).convert("RGBA")
    lw_ = 340
    logo = logo.resize((lw_, int(logo.height * lw_ / logo.width)), Image.LANCZOS)
    card.paste(logo, ((W - lw_) // 2, 1188), logo)

    # date line
    rf = face("HindSiliguri-Regular.ttf")
    line = f"{date_text}।  ভোলার বাণী"
    rf.draw(card, line, 27, (W - rf.width(line, 27)) / 2, 1320, (30, 30, 30))
    return card


# ---------------------------------------------------------------- news source
def wp_info(url):
    """Title, image URL, date from a WordPress link. Falls back to page meta tags."""
    p = urlparse(url)
    slug = unquote(p.path.rstrip("/").split("/")[-1])
    try:
        r = requests.get(f"{p.scheme}://{p.netloc}/wp-json/wp/v2/posts",
                         params={"slug": slug, "_embed": "1"}, headers=HEADERS, timeout=25)
        data = r.json() if r.ok else []
        if data:
            post = data[0]
            title = unescape(re.sub(r"<[^>]+>", "", post["title"]["rendered"])).strip()
            media = (post.get("_embedded", {}).get("wp:featuredmedia") or [{}])[0]
            image = media.get("source_url")
            dt = datetime.fromisoformat(post["date"]) if post.get("date") else now_bd()
            return title, image, dt
    except Exception:
        pass
    r = requests.get(url, headers=HEADERS, timeout=25)
    html = r.text

    def meta(prop):
        for pat in (r"""<meta[^>]+(?:property|name)=["']""" + re.escape(prop) + r"""["'][^>]+content=["']([^"']*)["']""",
                    r"""<meta[^>]+content=["']([^"']*)["'][^>]+(?:property|name)=["']""" + re.escape(prop) + r"""["']"""):
            m = re.search(pat, html, re.I)
            if m:
                return unescape(m.group(1)).strip()

    title = meta("og:title")
    published = meta("article:published_time")
    try:
        dt = datetime.fromisoformat(published) if published else now_bd()
    except ValueError:
        dt = now_bd()
    return title, meta("og:image"), dt


# ---------------------------------------------------------------- telegram helpers
def tg(method, **kw):
    return requests.post(f"{API}/{method}", timeout=40, **kw)


def say(chat_id, text):
    tg("sendMessage", json={"chat_id": chat_id, "text": text, "disable_web_page_preview": True})


def tg_download(file_id):
    info = requests.get(f"{API}/getFile", params={"file_id": file_id}, timeout=20).json()
    path = info["result"]["file_path"]
    return requests.get(f"https://api.telegram.org/file/bot{TOKEN}/{path}", timeout=60).content


def message_image_id(msg):
    if msg.get("photo"):
        return msg["photo"][-1]["file_id"]
    doc = msg.get("document") or {}
    if str(doc.get("mime_type", "")).startswith("image/"):
        return doc["file_id"]
    return None


# ---------------------------------------------------------------- settings kept in a pinned message
CACHE = {}
STATE = {}


def default_banner_bytes():
    t = Image.open(asset("template.png")).convert("RGB")
    b = t.crop((0, BANNER_Y - PHOTO_H, W, BANNER_Y - PHOTO_H + BANNER_H))
    out = io.BytesIO()
    b.save(out, "JPEG", quality=92)
    return out.getvalue()


def load_config(chat_id):
    if chat_id in CACHE:
        return CACHE[chat_id]
    cfg = {"badge": DEFAULT_BADGE, "banner": None}
    try:
        res = requests.get(f"{API}/getChat", params={"chat_id": chat_id}, timeout=20).json()
        pm = res.get("result", {}).get("pinned_message")
        if pm and pm.get("photo") and "CONFIG:" in (pm.get("caption") or ""):
            data = json.loads(pm["caption"].split("CONFIG:", 1)[1])
            cfg["badge"] = data.get("badge") or DEFAULT_BADGE
            cfg["banner"] = Image.open(io.BytesIO(tg_download(pm["photo"][-1]["file_id"]))).convert("RGB")
    except Exception:
        pass
    CACHE[chat_id] = cfg
    return cfg


def save_config(chat_id, badge, banner_bytes=None):
    if banner_bytes is None:
        banner_bytes = default_banner_bytes()
    caption = "সেটিংস, এই মেসেজ পিন করা থাকবে, মুছবেন না\nCONFIG:" + json.dumps({"badge": badge}, ensure_ascii=False)
    r = tg("sendPhoto", data={"chat_id": chat_id, "caption": caption},
           files={"photo": ("banner.jpg", banner_bytes)}).json()
    mid = r.get("result", {}).get("message_id")
    if mid:
        tg("pinChatMessage", json={"chat_id": chat_id, "message_id": mid, "disable_notification": True})
    CACHE[chat_id] = {"badge": badge, "banner": Image.open(io.BytesIO(banner_bytes)).convert("RGB")}


# ---------------------------------------------------------------- bot logic
HELP = ("ভোলার বাণীর ফটোকার্ড বট\n\n"
        "১. ওয়ার্ডপ্রেসের খবরের লিংক পাঠান, কার্ড তৈরি হয়ে আসবে\n"
        "২. অথবা ছবি পাঠান আর ক্যাপশনে শিরোনাম লিখে দিন\n\n"
        "বদলানোর কমান্ড:\n"
        "/banner  নিচের বিজ্ঞাপন ব্যানার বদলাতে\n"
        "/badge নতুন লেখা  লাল ব্যাজের লেখা বদলাতে\n"
        "/reset  আগের ডিজাইনে ফিরতে\n"
        "/settings  এখনকার সেটিং দেখতে\n\n"
        "শিরোনামে | চিহ্ন দিলে তার ডানের অংশ কালো হবে।")


def send_card(chat_id, photo_bytes, title, dt):
    cfg = load_config(chat_id)
    card = make_card(Image.open(io.BytesIO(photo_bytes)), title, bn_date(dt), cfg["badge"], cfg["banner"])
    jpg = io.BytesIO()
    card.save(jpg, "JPEG", quality=95)
    png = io.BytesIO()
    card.save(png, "PNG")
    tg("sendPhoto", data={"chat_id": chat_id, "caption": title[:1000]}, files={"photo": ("card.jpg", jpg.getvalue())})
    tg("sendDocument", data={"chat_id": chat_id, "caption": "পূর্ণ মানের ফাইল"}, files={"document": ("card.png", png.getvalue())})


def handle(msg):
    chat_id = msg["chat"]["id"]
    text = (msg.get("text") or "").strip()
    caption = (msg.get("caption") or "").strip()
    try:
        img_id = message_image_id(msg)

        if text.startswith("/start") or text.startswith("/help"):
            say(chat_id, HELP)
        elif text.startswith("/settings"):
            cfg = load_config(chat_id)
            say(chat_id, f"ব্যাজের লেখা: {cfg['badge']}\nব্যানার: {'নতুন দেওয়া' if cfg['banner'] else 'আগেরটাই'}")
        elif text.startswith("/reset"):
            save_config(chat_id, DEFAULT_BADGE)
            say(chat_id, "আগের ডিজাইনে ফিরেছে।")
        elif text.startswith("/badge"):
            new = text[len("/badge"):].strip()
            if not new:
                say(chat_id, "এভাবে লিখুন: /badge বিস্তারিত কমেন্টে")
            else:
                cfg = load_config(chat_id)
                banner_bytes = None
                if cfg["banner"] is not None:
                    b = io.BytesIO()
                    cfg["banner"].save(b, "JPEG", quality=92)
                    banner_bytes = b.getvalue()
                save_config(chat_id, new, banner_bytes)
                say(chat_id, f"ব্যাজের লেখা বদলে হয়েছে: {new}")
        elif text.startswith("/banner"):
            STATE[chat_id] = "banner"
            say(chat_id, "নতুন ব্যানারের ছবিটা পাঠান।")
        elif img_id and STATE.get(chat_id) == "banner":
            STATE.pop(chat_id, None)
            raw = tg_download(img_id)
            b = io.BytesIO()
            cover(Image.open(io.BytesIO(raw)), W, BANNER_H, 0.5).save(b, "JPEG", quality=92)
            cfg = load_config(chat_id)
            save_config(chat_id, cfg["badge"], b.getvalue())
            say(chat_id, "ব্যানার বদলে গেছে। এবার থেকে নতুন কার্ডে এটা বসবে।")
        elif img_id:
            if not caption:
                say(chat_id, "ছবির সাথে ক্যাপশনে শিরোনাম লিখে আবার পাঠান।")
            else:
                say(chat_id, "কার্ড বানানো হচ্ছে...")
                send_card(chat_id, tg_download(img_id), caption, now_bd())
        else:
            m = URL_RE.search(text)
            if not m:
                say(chat_id, "খবরের লিংক পাঠান, অথবা /help লিখুন।")
                return
            say(chat_id, "কার্ড বানানো হচ্ছে...")
            title, image, dt = wp_info(m.group(0))
            if not title or not image:
                say(chat_id, "লিংক থেকে শিরোনাম বা ছবি পাওয়া যায়নি। ছবি পাঠিয়ে ক্যাপশনে শিরোনাম দিন।")
                return
            photo = requests.get(image, headers=HEADERS, timeout=40).content
            send_card(chat_id, photo, title, dt)
    except Exception as e:
        say(chat_id, "কিছু একটা সমস্যা হয়েছে, আবার চেষ্টা করুন।")
        print("error:", repr(e))


@app.route("/")
def home():
    return "Bot is running"


@app.route(f"/webhook/{TOKEN}", methods=["POST"])
def webhook():
    msg = (request.get_json(silent=True) or {}).get("message")
    if msg:
        threading.Thread(target=handle, args=(msg,), daemon=True).start()
    return "ok"


def set_webhook():
    if TOKEN and BASE_URL:
        try:
            requests.get(f"{API}/setWebhook", params={"url": f"{BASE_URL}/webhook/{TOKEN}"}, timeout=20)
        except Exception:
            pass


set_webhook()

if __name__ == "__main__":
    app.run(host="0.0.0.0", port=int(os.environ.get("PORT", 5000)))
