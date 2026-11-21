import hashlib
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
MAX_DESIGNS = 5

# ---------------------------------------------------------------- assets
HERE = os.path.dirname(os.path.abspath(__file__))
ASSET_DIR = os.path.join("/tmp", "card_assets")
DESIGN_DIR = os.path.join("/tmp", "card_designs")


def prepare_assets():
    os.makedirs(ASSET_DIR, exist_ok=True)
    os.makedirs(DESIGN_DIR, exist_ok=True)
    zp = os.path.join(HERE, "assets.zip")
    if os.path.exists(zp):
        with zipfile.ZipFile(zp) as z:
            z.extractall(ASSET_DIR)


def asset(name):
    name = os.path.basename(name)
    for d in (ASSET_DIR, HERE):
        p = os.path.join(d, name)
        if os.path.exists(p):
            return p
    raise FileNotFoundError(name)


prepare_assets()

# ---------------------------------------------------------------- text engine
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


def face_at(path):
    if path not in _faces:
        _faces[path] = Face(path)
    return _faces[path]


def rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


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


def wrap_lines(text, f, size, maxw):
    sp = f.width(" ", size)
    lines, cur, curw = [], [], 0.0
    for wd in text.split():
        ww = f.width(wd, size)
        if cur and curw + sp + ww > maxw:
            lines.append(" ".join(cur))
            cur, curw = [], 0.0
        curw += (sp if cur else 0) + ww
        cur.append(wd)
    if cur:
        lines.append(" ".join(cur))
    return lines


def headline_lines(title, f, maxw, max_size=110):
    """Returns (lines, size). Enter or | in the title decides the split;
    otherwise the title is split into two balanced lines."""
    explicit = [p.strip() for p in re.split(r"[\n|]+", title) if p.strip()]
    if len(explicit) >= 2:
        lines = [" ".join(p.split()) for p in explicit]
    else:
        title = " ".join(title.split())
        words = title.split()
        if len(words) < 2:
            lines = [title or " "]
        else:
            best = None
            for k in range(1, len(words)):
                a_, b_ = " ".join(words[:k]), " ".join(words[k:])
                m = max(f.width(a_, 100), f.width(b_, 100))
                if best is None or m < best[0]:
                    best = (m, [a_, b_])
            lines = best[1]
    size = int(min(max_size, 100 * maxw / max(f.width(l, 100) for l in lines)))
    while size > 40 and max(f.width(l, size) for l in lines) > maxw:
        size -= 1
    if len(explicit) < 2 and size < 56:
        for size in range(56, 39, -2):
            lines = wrap_lines(" ".join(title.split()), f, size, maxw)
            if len(lines) <= 3:
                break
    return lines, size


# ---------------------------------------------------------------- designs
# A design is a folder with design.json and its images (and optional fonts).
def load_spec(path):
    with open(os.path.join(path, "design.json"), encoding="utf-8") as fh:
        spec = json.load(fh)
    spec["_dir"] = path
    w, h = spec["size"]
    if not (200 <= w <= 4000 and 200 <= h <= 4000):
        raise ValueError("size ঠিক নেই")
    if len(spec["headline"]["box"]) != 4:
        raise ValueError("headline box ঠিক নেই")
    for key in ("overlay",):
        if spec.get(key) and not os.path.exists(os.path.join(path, os.path.basename(spec[key]))):
            raise ValueError(f"{spec[key]} ফাইল নেই")
    return spec


_default = {}


def default_spec():
    if "spec" not in _default:
        _default["spec"] = load_spec(os.path.join(ASSET_DIR, "default"))
    return _default["spec"]


def design_path(spec, name):
    p = os.path.join(spec["_dir"], os.path.basename(name))
    return p if os.path.exists(p) else asset(name)


def make_card(photo, title, date_text, spec, badge=None, banner=None):
    W, H = spec["size"]
    card = Image.new("RGB", (W, H), (255, 255, 255))

    ph = spec.get("photo")
    if ph:
        x1, y1, x2, y2 = ph["box"]
        card.paste(cover(photo, x2 - x1, y2 - y1, ph.get("focus", 0.35)), (x1, y1))
    if spec.get("overlay"):
        ov = Image.open(design_path(spec, spec["overlay"])).convert("RGBA")
        card.paste(ov, (0, 0), ov)
    bn = spec.get("banner")
    if bn and banner is not None:
        x1, y1, x2, y2 = bn["box"]
        card.paste(cover(banner, x2 - x1, y2 - y1, 0.5), (x1, y1))

    bd = spec.get("badge")
    if bd:
        text = badge or bd.get("text", "")
        bf = face_at(design_path(spec, bd.get("font", "HindSiliguri-SemiBold.ttf")))
        size = bd.get("size", 40)
        tw = bf.width(text, size)
        bw = int(tw) + bd.get("pad", 84)
        bx = (W - bw) // 2
        y = bd["y"]
        d = ImageDraw.Draw(card)
        d.rounded_rectangle((bx, y, bx + bw, y + bd.get("h", 64)), radius=bd.get("radius", 24),
                            fill=rgb(bd.get("fill", "#e7412d")),
                            outline=rgb(bd.get("outline", "#ffffff")), width=bd.get("outline_w", 4))
        bf.draw(card, text, size, bx + (bw - tw) / 2, y + bd.get("baseline", 46), rgb(bd.get("color", "#ffffff")))

    hs = spec["headline"]
    hf = face_at(design_path(spec, hs.get("font", "HindSiliguri-SemiBold.ttf")))
    x1, y1, x2, y2 = hs["box"]
    lines, size = headline_lines(title, hf, x2 - x1, hs.get("max_size", 110))
    lh = size * hs.get("line_height", 1.32)
    top = hs.get("center_y", (y1 + y2) / 2) - len(lines) * lh / 2
    cols = hs.get("colors", ["#141414"])
    c_main, c_last = rgb(cols[0]), rgb(cols[-1])
    align = hs.get("align", "center")
    for n, line in enumerate(lines):
        w = hf.width(line, size)
        x = x1 if align == "left" else (x2 - w if align == "right" else x1 + (x2 - x1 - w) / 2)
        hf.draw(card, line, size, x, top + n * lh + size * 1.0, c_last if n == len(lines) - 1 else c_main)

    lg = spec.get("logo")
    if lg:
        logo = Image.open(design_path(spec, lg["file"])).convert("RGBA")
        lw = lg.get("w", logo.width)
        logo = logo.resize((lw, int(logo.height * lw / logo.width)), Image.LANCZOS)
        lx = (W - lw) // 2 if lg.get("x", "center") == "center" else lg["x"]
        card.paste(logo, (lx, lg["y"]), logo)

    dt = spec.get("date")
    if dt:
        rf = face_at(design_path(spec, dt.get("font", "HindSiliguri-Regular.ttf")))
        line = dt.get("text", "{date}").replace("{date}", date_text)
        size = dt.get("size", 27)
        w = rf.width(line, size)
        dx = (W - w) / 2 if dt.get("x", "center") == "center" else dt["x"]
        rf.draw(card, line, size, dx, dt["baseline"], rgb(dt.get("color", "#1e1e1e")))
    return card


def extract_zip_flat(data, dest):
    os.makedirs(dest, exist_ok=True)
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for info in z.infolist():
            name = os.path.basename(info.filename)
            if info.is_dir() or not name or info.file_size > 15_000_000:
                continue
            with z.open(info) as src, open(os.path.join(dest, name), "wb") as out:
                out.write(src.read())


DESIGN_CACHE = {}


def design_from_file_id(file_id):
    if file_id in DESIGN_CACHE:
        return DESIGN_CACHE[file_id]
    dest = os.path.join(DESIGN_DIR, hashlib.sha1(file_id.encode()).hexdigest()[:14])
    if not os.path.exists(os.path.join(dest, "design.json")):
        extract_zip_flat(tg_download(file_id), dest)
    spec = load_spec(dest)
    DESIGN_CACHE[file_id] = spec
    return spec


def active_spec(cfg):
    key = cfg.get("active", "default")
    if key != "default" and key in cfg["designs"]:
        return design_from_file_id(cfg["designs"][key]["f"])
    return default_spec()


def placeholder_photo():
    im = Image.new("RGB", (1600, 900), (96, 112, 138))
    d = ImageDraw.Draw(im)
    d.ellipse((560, 120, 1040, 600), fill=(150, 165, 190))
    d.rectangle((300, 600, 1300, 900), fill=(70, 84, 108))
    return im


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
    spec = default_spec()
    x1, y1, x2, y2 = spec["banner"]["box"]
    ov = Image.open(design_path(spec, spec["overlay"])).convert("RGB")
    out = io.BytesIO()
    ov.crop((x1, y1, x2, y2)).save(out, "JPEG", quality=92)
    return out.getvalue()


def new_cfg():
    return {"badge": None, "active": "default", "designs": {}, "banner": None}


def load_config(chat_id):
    if chat_id in CACHE:
        return CACHE[chat_id]
    cfg = new_cfg()
    try:
        res = requests.get(f"{API}/getChat", params={"chat_id": chat_id}, timeout=20).json()
        pm = res.get("result", {}).get("pinned_message")
        if pm and pm.get("photo") and "CONFIG:" in (pm.get("caption") or ""):
            data = json.loads(pm["caption"].split("CONFIG:", 1)[1])
            cfg["badge"] = data.get("badge") or None
            cfg["active"] = data.get("active") or "default"
            cfg["designs"] = data.get("designs") or {}
            if data.get("has_banner"):
                cfg["banner"] = Image.open(io.BytesIO(tg_download(pm["photo"][-1]["file_id"]))).convert("RGB")
    except Exception:
        pass
    CACHE[chat_id] = cfg
    return cfg


def save_config(chat_id, cfg):
    if cfg["banner"] is not None:
        b = io.BytesIO()
        cfg["banner"].save(b, "JPEG", quality=92)
        data = b.getvalue()
    else:
        data = default_banner_bytes()
    payload = {"badge": cfg["badge"], "active": cfg["active"], "designs": cfg["designs"],
               "has_banner": cfg["banner"] is not None}
    caption = ("সেটিংস, এই মেসেজ পিন করা থাকবে, মুছবেন না\nCONFIG:"
               + json.dumps(payload, ensure_ascii=False, separators=(",", ":")))
    if len(caption) > 1000:
        raise ValueError("সেটিং বেশি লম্বা হয়ে গেছে")
    r = tg("sendPhoto", data={"chat_id": chat_id, "caption": caption}, files={"photo": ("banner.jpg", data)}).json()
    mid = r.get("result", {}).get("message_id")
    if mid:
        tg("pinChatMessage", json={"chat_id": chat_id, "message_id": mid, "disable_notification": True})
    CACHE[chat_id] = cfg


def design_names(cfg):
    items = [("default", default_spec().get("name", "ডিজাইন ১"))]
    items += [(k, v["n"]) for k, v in cfg["designs"].items()]
    return items


# ---------------------------------------------------------------- bot logic
HELP = ("ভোলার বাণীর ফটোকার্ড বট\n\n"
        "১. ওয়ার্ডপ্রেসের খবরের লিংক পাঠান, কার্ড তৈরি হয়ে আসবে\n"
        "২. অথবা ছবি পাঠান আর ক্যাপশনে শিরোনাম লিখে দিন\n\n"
        "ডিজাইন:\n"
        "/designs  সব ডিজাইনের তালিকা\n"
        "/design 2  ২ নম্বর ডিজাইন চালু করতে\n"
        "/adddesign  নতুন ডিজাইন যোগ করতে\n"
        "/removedesign 2  যোগ করা ডিজাইন মুছতে\n\n"
        "বদলানোর কমান্ড:\n"
        "/banner  নিচের বিজ্ঞাপন ব্যানার বদলাতে\n"
        "/badge নতুন লেখা  লাল ব্যাজের লেখা বদলাতে\n"
        "/reset  ব্যাজ, ব্যানার আর ডিজাইন আগের অবস্থায় ফেরাতে\n"
        "/settings  এখনকার সেটিং দেখতে\n\n"
        "নিজে লাইন ভাগ করতে চাইলে শিরোনামে Enter দিয়ে নতুন লাইনে লিখুন। "
        "উপরের লাইন প্রথম রঙে, শেষ লাইন দ্বিতীয় রঙে হবে।")


def send_card(chat_id, photo_bytes, title, dt):
    cfg = load_config(chat_id)
    try:
        spec = active_spec(cfg)
    except Exception as e:
        print("design load error:", repr(e))
        say(chat_id, "ডিজাইনটা লোড হয়নি, প্রথম ডিজাইনে বানানো হচ্ছে।")
        spec = default_spec()
    card = make_card(Image.open(io.BytesIO(photo_bytes)), title, bn_date(dt), spec, cfg["badge"], cfg["banner"])
    jpg = io.BytesIO()
    card.save(jpg, "JPEG", quality=95)
    png = io.BytesIO()
    card.save(png, "PNG")
    tg("sendPhoto", data={"chat_id": chat_id, "caption": title[:1000]}, files={"photo": ("card.jpg", jpg.getvalue())})
    tg("sendDocument", data={"chat_id": chat_id, "caption": "পূর্ণ মানের ফাইল"}, files={"document": ("card.png", png.getvalue())})


def add_design(chat_id, doc, cfg):
    if len(cfg["designs"]) >= MAX_DESIGNS:
        say(chat_id, f"সর্বোচ্চ {MAX_DESIGNS}টা ডিজাইন যোগ করা যায়। আগে /removedesign দিয়ে একটা মুছুন।")
        return
    spec = design_from_file_id(doc["file_id"])
    preview = make_card(placeholder_photo(), "ডিজাইনের নমুনা শিরোনাম এখানে বসবে", bn_date(now_bd()), spec)
    out = io.BytesIO()
    preview.save(out, "JPEG", quality=90)
    n = 2
    while f"d{n}" in cfg["designs"]:
        n += 1
    key = f"d{n}"
    cfg["designs"][key] = {"n": str(spec.get("name", f"ডিজাইন {n}"))[:30], "f": doc["file_id"]}
    cfg["active"] = key
    save_config(chat_id, cfg)
    tg("sendPhoto", data={"chat_id": chat_id, "caption": "নতুন ডিজাইন যোগ হয়েছে আর এখন চালু আছে। আগেরটায় ফিরতে /design 1 লিখুন।"},
       files={"photo": ("preview.jpg", out.getvalue())})


def handle(msg):
    chat_id = msg["chat"]["id"]
    text = (msg.get("text") or "").strip()
    caption = (msg.get("caption") or "").strip()
    try:
        img_id = message_image_id(msg)
        doc = msg.get("document") or {}
        is_zip = str(doc.get("file_name", "")).lower().endswith(".zip") or "zip" in str(doc.get("mime_type", ""))
        cfg = load_config(chat_id)
        cmd = text.split()[0].split("@")[0] if text.startswith("/") else ""
        arg = text[len(text.split()[0]):].strip() if cmd else ""

        if cmd in ("/start", "/help"):
            say(chat_id, HELP)
        elif cmd == "/settings":
            names = dict(design_names(cfg))
            say(chat_id, f"চালু ডিজাইন: {names.get(cfg['active'], 'ডিজাইন ১')}\n"
                         f"ব্যাজের লেখা: {cfg['badge'] or 'ডিজাইনের নিজের'}\n"
                         f"ব্যানার: {'নতুন দেওয়া' if cfg['banner'] else 'আগেরটাই'}")
        elif cmd == "/designs":
            lines = []
            for i, (k, name) in enumerate(design_names(cfg), 1):
                lines.append(f"{i}. {name}" + ("  (চালু)" if k == cfg["active"] else ""))
            say(chat_id, "ডিজাইনের তালিকা:\n" + "\n".join(lines) + "\n\nবদলাতে লিখুন: /design 2")
        elif cmd == "/design":
            items = design_names(cfg)
            if not arg.isdigit() or not 1 <= int(arg) <= len(items):
                say(chat_id, "এভাবে লিখুন: /design 2 (তালিকা দেখতে /designs)")
            else:
                key, name = items[int(arg) - 1]
                cfg["active"] = key
                save_config(chat_id, cfg)
                say(chat_id, f"চালু হয়েছে: {name}")
        elif cmd == "/removedesign":
            items = design_names(cfg)
            if not arg.isdigit() or not 2 <= int(arg) <= len(items):
                say(cha
