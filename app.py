# -*- coding: utf-8 -*-
"""
Kta3Box — video link → vertical shorts (YouTube / TikTok / Instagram links)
Free mode: yt-dlp (video + captions with timestamps) + smart highlight scoring
+ free translation + free TTS dubbing + ffmpeg montage. No API keys needed.
"""
import json
import os
import re
import threading
import time
import uuid
import webbrowser
import zipfile
import shutil
import hashlib
import random
import subprocess
import sys
from pathlib import Path

import requests
import yt_dlp
from flask import Flask, request as flask_request, jsonify, send_from_directory, send_file

try:
    from gtts import gTTS
except Exception:
    gTTS = None

BASE = Path(__file__).resolve().parent
BIN_DIR = BASE / "bin"
TEMP_DIR = BASE / "temp"
DL_DIR = BASE / "downloads"
STATIC_DIR = BASE / "static"

for d in (TEMP_DIR, DL_DIR, STATIC_DIR):
    d.mkdir(exist_ok=True)

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

JOBS = {}
JOBS_LOCK = threading.Lock()
NO_WINDOW = subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0


def find_ffmpeg(name):
    hits = list(BIN_DIR.rglob(name)) or list(BIN_DIR.rglob(name + ".exe"))
    return str(hits[0]) if hits else name


FFMPEG = find_ffmpeg("ffmpeg")
FFPROBE = find_ffmpeg("ffprobe")
# make sure yt-dlp finds deno (JS runtime) and ffprobe/ffmpeg even if not on PATH
os.environ["PATH"] = str(BIN_DIR) + os.pathsep + os.environ.get("PATH", "")

LANGS = {
    "original": "Original (video language)",
    "ar": "Arabic",
    "en": "English",
    "fr": "Français",
    "es": "Español",
    "de": "Deutsch",
    "pt": "Português",
    "it": "Italiano",
    "tr": "Türkçe",
    "ru": "Русский",
    "hi": "हिन्दी",
    "id": "Indonesia",
    "ja": "日本語",
    "ko": "한국어",
    "zh-Hans": "中文",
}

# output size / aspect per target platform
PLATFORMS = {
    "youtube_short": (1080, 1920),   # 9:16 vertical
    "tiktok": (1080, 1920),          # 9:16 vertical
    "instagram_reel": (1080, 1920),  # 9:16 vertical
    "instagram_feed": (1080, 1350),  # 4:5 vertical feed
}

# generic high-traffic hashtag packs per platform
PLATFORM_HASHTAGS = {
    "youtube_short": ["shorts", "viral", "trending", "youtubeshorts", "shortsfeed", "ytshorts"],
    "tiktok": ["fyp", "foryou", "foryoupage", "viral", "tiktok", "learnontiktok", "xyzbca"],
    "instagram_reel": ["reels", "reelsvideo", "reelsinstagram", "explorepage", "viral", "instagood"],
    "instagram_feed": ["instagram", "instagood", "explore", "trending", "reels"],
}

HOOK_WORDS = {
    "en": ["how", "why", "secret", "never", "always", "best", "worst", "stop", "trick", "fail", "proof",
           "million", "billion", "free", "top", "mistake", "actually", "crazy", "money", "first",
           "big", "warning", "danger", "truth", "know", "everyone", "nobody", "shocking"],
    "fr": ["comment", "pourquoi", "secret", "jamais", "toujours", "meilleur", "pire", "astuce", "million",
           "gratuit", "erreur", "attention", "danger", "vérité", "tout", "personne", "argent"],
    "ar": ["كيف", "لماذا", "سر", "أفضل", "أسوأ", "خطأ", "خطر", "حقيقة", "المال", "مليون",
           "مجانا", "انتباه", "أسرار", "خطير", "قصة", "معنى", "دائما", "لن"],
    "es": ["como", "por qué", "secreto", "nunca", "siempre", "mejor", "peor", "truco", "error", "dinero",
           "millón", "gratis", "peligro", "verdad", "todos", "nadie"],
    "de": ["wie", "warum", "geheimnis", "nie", "immer", "beste", "fehler", "geld", "million", "kostenlos"],
    "pt": ["como", "por que", "segredo", "nunca", "sempre", "melhor", "pior", "truque", "erro", "dinheiro",
           "milhão", "grátis"],
}

BRACKET_NOISE = re.compile(r"\[[^\]]{0,40}\]", re.I)
SPEAKER_NOISE = re.compile(r"^\W*[-–—]\s*$")


def log(job, msg):
    job["msgs"].append(msg)
    try:
        print(f"[{job['id'][:6]}] {msg}", flush=True)
    except Exception:
        pass


def slug(text):
    t = re.sub(r"[^\w\s-]", "", text or "", flags=re.UNICODE).strip()
    t = re.sub(r"\s+", "-", t)[:48] or "clip"
    return t


# ================= ffmpeg helpers =================

def probe_streams(path):
    """returns (duration: float|None, has_audio: bool)"""
    dur, audio = None, False
    try:
        out = subprocess.check_output(
            [FFPROBE, "-v", "error", "-show_entries", "format=duration:stream=codec_type",
             "-of", "json", str(path)], timeout=30, creationflags=NO_WINDOW)
        data = json.loads(out)
        if data.get("format", {}).get("duration"):
            dur = float(data["format"]["duration"])
        for st in data.get("streams", []):
            if st.get("codec_type") == "audio":
                audio = True
    except Exception:
        pass
    return dur, audio


# ================= yt-dlp helpers =================

def _base_opts():
    o = {"quiet": True, "no_warnings": True, "noplaylist": True, "socket_timeout": 30, "retries": 5}
    c = BASE / "cookies.txt"
    if c.exists():
        o["cookiefile"] = str(c)
    return o


def fetch_info(url):
    with yt_dlp.YoutubeDL(_base_opts()) as y:
        return y.extract_info(url, download=False)


def pick_sub_language(info):
    """Return a yt-dlp language key for the *original* track, or None."""
    autos = info.get("automatic_captions") or {}
    manual = info.get("captions") or {}
    orig_keys = sorted(k for k in autos if k.endswith("-orig"))
    if orig_keys:
        return orig_keys[0]
    if manual:
        return sorted(manual.keys())[0]
    plain = sorted(k for k in autos if "+" not in k)
    return plain[0] if plain else None


def download_subs(job, lang_key):
    """Download subs (auto converted to srt by yt-dlp) into temp dir. Returns path or None."""
    jdir = TEMP_DIR / job["id"]
    jdir.mkdir(parents=True, exist_ok=True)
    opts = {
        "skip_download": True, "noplaylist": True,
        "writesubtitles": True, "writeautomaticsub": True,
        "subtitleslangs": sorted({lang_key, lang_key.replace("-orig", "")}),
        "subtitlesformat": "json3/vtt/srv1",
        "convertsubtitles": "srt",
        "outtmpl": {"subtitle": str(jdir / "sub.%(ext)s")},
        **_base_opts(),
    }
    try:
        with yt_dlp.YoutubeDL(opts) as y:
            y.extract_info(job["url"], download=True)
    except Exception as e:
        log(job, f"Subtitles download warning: {e}")
    srt = sorted(jdir.glob("sub*.srt"))
    if srt:
        return srt[0]
    vtt = sorted(jdir.glob("sub*.vtt"))
    if vtt:
        return vtt[0]
    j3 = sorted(jdir.glob("sub*.json3"))
    return j3[0] if j3 else None


# ================= subtitle parsing =================

def parse_srt(path):
    data = path.read_text(encoding="utf-8", errors="replace")
    cue = re.compile(
        r"\n?\s*\d+\s*\n(\d{2}:\d{2}:\d{2}[,.]\d{3})\s*-->\s*(\d{2}:\d{2}:\d{2}[,.]\d{3})([\s\S]*?)(?=\n\s*\n|\Z)")
    cues = []

    def ts(x):
        h, m, s, ms = re.split(r"[:,.]", x.strip())
        return int(h) * 3600 + int(m) * 60 + int(s) + int(ms) / 1000

    for m in cue.finditer(data):
        start, end = ts(m.group(1)), ts(m.group(2))
        body = re.sub(r"<[^>]+>", " ", m.group(3))
        body = (body.replace("&nbsp;", " ").replace("&amp;", "&")
                .replace("&gt;", ">").replace("&lt;", "<").replace("&#39;", "'"))
        body = " ".join(body.split())
        body = BRACKET_NOISE.sub(" ", body).strip()
        if body and SPEAKER_NOISE.match(body) is None and start < end:
            cues.append({"start": start, "end": end, "text": body})
    return cues


def parse_vtt(path):
    data = path.read_text(encoding="utf-8", errors="replace")

    def ts(x):
        m = re.match(r"(\d+):(\d+):(\d+)\.(\d+)", x.strip())
        if not m:
            return None
        h, mi, s, ms = m.groups()
        return int(h) * 3600 + int(mi) * 60 + int(s) + int(ms) / 1000

    cues = []
    for block in re.split(r"\n\s*\n", data):
        m = re.search(r"([\d:.]+)\s+-->\s+([\d:.]+)", block)
        if not m:
            continue
        start, end = ts(m.group(1)), ts(m.group(2))
        lines = [re.sub(r"<[^>]+>", "", ln).strip() for ln in block.splitlines() if "-->" not in ln]
        txt = " ".join(lines)
        txt = re.sub(r"\b(WEBVTT|NOTE)\b.*", " ", txt).strip()
        txt = BRACKET_NOISE.sub(" ", txt).strip()
        if txt and start is not None and end is not None and start < end:
            cues.append({"start": start, "end": end, "text": txt})
    return cues


def parse_json3(path):
    try:
        data = json.loads(path.read_text(encoding="utf-8", errors="replace"))
    except Exception:
        return []
    words = []
    for ev in data.get("events", []):
        if "segs" not in ev:
            continue
        base = ev.get("tStartMs", 0) / 1000.0
        end = base + (ev.get("dDurationMs", 0) / 1000.0)
        for seg in ev["segs"]:
            txt_ = (seg.get("utf8") or "").strip()
            if not txt_ or txt_ == "\n":
                continue
            off = (seg.get("tOffsetMs") or 0) / 1000.0
            for w in txt_.split():
                if "|" in w and w.count("|") == len(w):
                    continue
                words.append({"t": base + off, "w": w.strip("\n|")})
        # extend end via last token
    words.sort(key=lambda x: x["t"])
    # merge into ~4-word cues
    cues = []
    buf, bt = [], None
    for i, item in enumerate(words):
        if not item["w"]:
            continue
        if bt is None:
            bt = item["t"]
        buf.append(item["w"])
        wlen = sum(len(x) for x in buf)
        last = item["w"][-1]
        nxt = words[i + 1]["t"] if i + 1 < len(words) else end
        if (len(buf) >= 4 or wlen > 24 or last in ".?!؟…،" or nxt - item["t"] > 2.5) and buf:
            cues.append({"start": bt, "end": max(nxt, bt + 0.3), "text": " ".join(buf)})
            buf, bt = [], None
    if buf and bt is not None:
        cues.append({"start": bt, "end": bt + 1.2, "text": " ".join(buf)})
    return cues


def parse_any(path):
    suf = path.suffix.lower()
    if suf == ".vtt":
        return parse_vtt(path)
    if suf == ".json3":
        return parse_json3(path)
    cues = parse_srt(path)
    if not cues:
        try:
            cues = parse_vtt(path)
        except Exception:
            pass
    return cues


def clean_cues(cues):
    """merge repeated auto-sub marks / deduplicate / clamp"""
    out = []
    for c in cues:
        t = BRACKET_NOISE.sub(" ", c["text"]).strip()
        t = re.sub(r"\s+", " ", t)
        if not t or SPEAKER_NOISE.match(t):
            continue
        c2 = dict(c, text=t)
        if out and out[-1]["text"] == t and abs(c2["start"] - out[-1]["end"]) < 1.0:
            out[-1]["end"] = c2["end"]
            continue
        out.append(c2)
    return out


# ================= caption groups =================

def split_groups(cues, max_words=4, max_chars=26):
    """flatten cues into small caption chips (word-group timings)."""
    groups = []
    for c in cues:
        words = c["text"].split()
        if not words:
            continue
        dur = max(0.4, c["end"] - c["start"])
        chunks, cur, clen = [], [], 0.0
        for w in words:
            cur.append(w)
            clen += len(w) + 1
            brk = len(w) >= 1 and w[-1] in ".?!؟…،:;"
            if (clen >= max_chars and len(cur) >= 2) or len(cur) >= max_words or brk:
                chunks.append(" ".join(cur))
                cur, clen = [], 0.0
        if cur:
            chunks.append(" ".join(cur))
        if not chunks:
            continue
        total_chars = sum(len(ch) for ch in chunks) + 0.01
        t = c["start"]
        for ch in chunks:
            share = (len(ch) + 0.01) / total_chars
            g_end = min(c["end"], t + share * dur)
            groups.append({"start": t, "end": max(g_end, t + 0.15), "text": ch})
            t = g_end
    return groups


# ================= highlight selection =================

def _lang_guess(text):
    if re.search(r"[\u0600-\u06FF]", text):
        w = "ar"
    elif re.search(r"[àâçéèêëîïôùûœ]", text, re.I):
        w = "fr"
    elif re.search(r"[¿¡ñ]", text):
        w = "es"
    elif re.search(r"[äöüß]", text, re.I):
        w = "de"
    elif re.search(r"[ãõç]", text, re.I):
        w = "pt"
    else:
        w = "en"
    return HOOK_WORDS.get(w, HOOK_WORDS["en"])


def window_score(inner, total_dur, target):
    if len(inner) < 4:
        return 0.0
    start, end = inner[0]["start"], inner[-1]["end"]
    dur = end - start
    if dur < 6:
        return 0.0
    text = " ".join(g["text"] for g in inner).lower()
    words = text.split()
    if len(words) < 25:
        return 0.0
    hooks = _lang_guess(text)
    hits = sum(1 for w in words if (w.strip(".,!?؟…\"'،")).lower() in hooks)
    digits = len(re.findall(r"\b\d[\d.,]*\b", text))
    exclam = min(6, text.count("!") + text.count("؟") + text.count("?"))
    density = len(words) / dur
    center = (start + end) / 2 / max(total_dur, 1)
    center_bias = 1.0 - abs(center - 0.45)
    score = (
        0.10 * min(density, 4.5)
        + 1.35 * min(hits, 8)
        + 0.5 * min(digits, 6)
        + 0.6 * exclam
        + 1.2 * max(center_bias, 0)
        + 0.4
        + random.uniform(0, 0.45)
        - 0.6 * abs(dur - target) / max(target, 1)
    )
    return score


def best_end_for(groups, s, L, total_dur):
    """last group end in [s+0.55L, s+1.35L]"""
    best = None
    for g in groups:
        if g["end"] > s + L * 1.35:
            break
        if g["start"] >= s - 0.3:
            best = g["end"]
    if best is None or best - s < L * 0.55:
        return None
    return min(best, total_dur - 0.15)


def choose_segments(cues, n, target, total_dur):
    groups = split_groups(cues) if cues else []
    if len(groups) < 8:
        return fallback_segments(n, target, total_dur)
    starts = sorted({round(g["start"], 1) for g in groups})
    stride = max(1, len(starts) // 500)
    idx_of = {}
    for i, g in enumerate(groups):
        idx_of.setdefault(round(g["start"], 1), i)
    candidates = []
    for mult in (0.85, 1.0, 1.18):
        L = target * mult
        for s in starts[::stride]:
            e = best_end_for(groups, s, L, total_dur)
            if e is None:
                continue
            i0 = idx_of.get(round(s, 1))
            if i0 is None:
                continue
            inner = []
            for g in groups[i0:]:
                if g["start"] >= s - 0.3 and g["end"] <= e + 0.4:
                    inner.append(g)
                if g["start"] > e:
                    break
            sc = window_score(inner, total_dur, target)
            if sc > 0:
                candidates.append({"start": s, "end": e, "score": sc})
    if not candidates:
        return fallback_segments(n, target, total_dur)
    candidates.sort(key=lambda c: -c["score"])
    picks, min_gap = [], max(4.0, target * 0.3)
    for c in candidates:
        if len(picks) >= n:
            break
        if all(c["end"] + min_gap < p["start"] or c["start"] > p["end"] + min_gap for p in picks):
            picks.append(c)
    if len(picks) < n:
        for c in candidates:
            if len(picks) >= n:
                break
            if all(c["end"] <= p["start"] or c["start"] >= p["end"] for p in picks) and c not in picks:
                picks.append(c)
    picks.sort(key=lambda p: p["start"])
    for p in picks:
        p["end"] = min(p["end"], total_dur - 0.1)
        p["start"] = max(p["start"], 0.0)
    return picks


def fallback_segments(n, target, total_dur):
    head, tail = int(total_dur * 0.04), int(total_dur * 0.06)
    usable = max(total_dur - head - tail, target * n * 0.6)
    gap = usable / max(n, 1)
    segs = []
    for i in range(n):
        s = head + i * gap + min((gap - target) / 2, 30)
        s = max(0.0, s)
        e = min(total_dur - 0.15, s + target)
        if e - s < 8:
            continue
        segs.append({"start": s, "end": e, "score": 0.0})
    return segs


# ================= viral hashtags =================

TAG_STOP = {
    "the", "a", "an", "and", "or", "of", "in", "on", "to", "for", "with", "you", "your",
    "is", "are", "was", "it", "this", "that", "be", "have", "has", "will", "my", "we",
    "at", "from", "by", "not", "but", "so", "as", "can", "do", "did", "if", "then",
    "just", "about", "out", "up", "down", "what", "when", "who", "all", "no", "yes",
    "like", "get", "got", "new", "his", "her", "they", "them", "was", "they're",
}


def _tag_clean(word):
    t = re.sub(r"[^\w\-]", "", re.sub(r"\s+", "-", word.strip().lower()), flags=re.UNICODE)
    t = t.strip("-")
    return t if len(t) > 2 and not t.isdigit() else None


def make_hashtags(title, video_tags, clip_text, platform, limit=16):
    out = []

    def add(word):
        t = _tag_clean(word)
        if t and t not in out:
            out.append(t)

    for tag in PLATFORM_HASHTAGS.get(platform, PLATFORM_HASHTAGS["youtube_short"]):
        add(tag)
    for w in re.findall(r"\w{3,}", title or "", re.UNICODE)[:10]:
        add(w) if w.lower() not in TAG_STOP else None
    for t in (video_tags or [])[:10]:
        if 2 < len(t) <= 22 and " " not in t:
            add(t)
    words = [w for w in re.findall(r"\w{4,}", clip_text or "", re.UNICODE) if w not in TAG_STOP]
    seen = {}
    for w in words:
        seen[w] = seen.get(w, 0) + 1
    for w, _c in sorted(seen.items(), key=lambda kv: -kv[1])[:5]:
        add(w)
    return ["#" + t for t in out[:limit]]


# ================= free translation =================

TR_CACHE = {}
TR_LOCK = threading.Lock()


def translate_line(text, target, retry=2):
    if not text or not target or target == "original":
        return text
    target = {"zh-Hans": "zh-CN"}.get(target, target)
    key = (target, text)
    with TR_LOCK:
        if key in TR_CACHE:
            return TR_CACHE[key]
    for attempt in range(retry + 1):
        try:
            r = requests.get(
                "https://translate.googleapis.com/translate_a/single",
                params={"client": "gtx", "sl": "auto", "tl": target, "dt": "t", "q": text},
                timeout=10, headers={"User-Agent": "Mozilla/5.0"})
            data = r.json()
            out = "".join(p[0] for p in data[0] if isinstance(p, list) and p and isinstance(p[0], str))
            out = out.strip()
            if out:
                with TR_LOCK:
                    TR_CACHE[key] = out
                return out
        except Exception:
            time.sleep(0.3 * (attempt + 1))
    return text


# ================= free TTS dubbing =================

GTTS_OK = {
    "en", "ar", "fr", "es", "de", "pt", "it", "tr", "ru", "hi", "id", "ja", "ko",
    "zh-CN", "zh-TW", "nl", "pl", "tl", "vi", "th", "bn", "ta", "te", "ur", "uk",
    "cs", "da", "el", "fi", "he", "hu", "mk", "ml", "mr", "my", "ne", "no", "ro",
    "sk", "sq", "sr", "sv", "sw", "lt", "lv", "bs", "hr", "km", "kn", "gu",
}


def gtts_lang(code):
    """Map a caption language key to a gTTS language code, or None."""
    if not code:
        return None
    base = code.split("+")[0]
    if base.endswith("-orig"):
        base = base[:-len("-orig")]
    base = base.split("-")[0]
    if base == "zh":
        return "zh-CN"
    return base if base in GTTS_OK else None


def make_sfx(jdir):
    """Synthesize a short attention-grabbing whoosh+boom sound with ffmpeg (free, local)."""
    out = jdir / "sfx_start.wav"
    if out.exists() and out.stat().st_size > 1000:
        return out
    filt = ("[0:a]highpass=f=250,lowpass=f=3800,"
            "afade=t=in:st=0:d=0.04,afade=t=out:st=0.13:d=0.34,volume=1.5[n];"
            "[1:a]lowpass=f=120,afade=t=in:st=0:d=0.02,afade=t=out:st=0.06:d=0.42,volume=2.0[b];"
            "[n][b]amix=inputs=2:duration=first:dropout_transition=0:normalize=0[out]")
    cmd = [FFMPEG, "-hide_banner", "-loglevel", "error", "-y",
           "-f", "lavfi", "-i", "anoisesrc=color=brown:amplitude=0.5:duration=0.55:sample_rate=44100",
           "-f", "lavfi", "-i", "sine=frequency=66:duration=0.55:sample_rate=44100",
           "-filter_complex", filt, "-map", "[out]", "-ar", "44100", "-ac", "2", str(out)]
    try:
        subprocess.run(cmd, timeout=30, creationflags=NO_WINDOW, check=True)
    except Exception:
        return None
    return out if out.exists() else None


def synth_dub_track(job, lines, s, e, jdir, idx):
    """Generate a voice-over WAV for one clip with gTTS (translated caption text),
    aligned to caption timings. Returns wav path or None."""
    if gTTS is None:
        log(job, "Voice dub skipped: gTTS is not installed (pip install gTTS).")
        return None
    if job["sub_lang"] != "original":
        lang = gtts_lang(job["sub_lang"])
    else:
        lang = gtts_lang(job.get("video_sub_base", ""))
    if not lang:
        log(job, "Voice dub skipped: language not supported by the free TTS engine.")
        return None
    clip_dur = max(0.5, e - s)
    plan = []
    for i, g in enumerate(lines):
        text = re.sub(r"\s+", " ", g["text"]).strip()
        if not text:
            continue
        slot_start = min(max(g["start"] - s, 0.0), clip_dur - 0.3)
        slot_end = min(max((lines[i + 1]["start"] - s) if i + 1 < len(lines) else clip_dur,
                           slot_start + 0.6), clip_dur)
        slot = slot_end - slot_start
        if slot < 0.35:
            continue
        mp3 = jdir / f"dub{idx}_{i}.mp3"
        wav = mp3.with_suffix(".wav")
        try:
            gTTS(text=text, lang=lang, slow=False).save(str(mp3))
        except Exception:
            continue
        try:
            subprocess.run([FFMPEG, "-hide_banner", "-loglevel", "error", "-y", "-i", str(mp3),
                            "-ar", "44100", "-ac", "2", str(wav)],
                           timeout=40, creationflags=NO_WINDOW, check=True, cwd=str(jdir),
                           capture_output=True)
        except subprocess.CalledProcessError as e:
            log(job, "Voice line convert failed: " + (e.stderr or b"").decode(errors="replace")[-300:])
            continue
        except Exception:
            continue
        dur, _ = probe_streams(wav)
        if not dur or dur < 0.05:
            continue
        tempo = ""
        ratio = slot / max(dur, 0.01)
        if ratio < 1.0:
            f_c = max(0.5, min(1.9, ratio))
            tempo = f",atempo={f_c:.4f}" if 0.5 <= f_c < 1.9 else ""
        plan.append({"wav": str(wav), "ms": int(slot_start * 1000), "tempo": tempo})
    if not plan:
        return None
    chains, labels = [], []
    for i2, item in enumerate(plan):
        chains.append(f"[{i2}:a]aformat=sample_rates=44100:channel_layouts=stereo"
                      f"{item['tempo']},adelay={item['ms']}|{item['ms']}[a{i2}]")
        labels.append(f"[a{i2}]")
    fc = (";".join(chains) + ";" + "".join(labels) +
          f"amix=inputs={len(plan)}:duration=longest:dropout_transition=0:normalize=0,"
          f"atrim=0:{clip_dur:.3f},apad=whole_dur={clip_dur:.3f}[out]")
    out = jdir / f"dub{idx}.wav"
    cmd = [FFMPEG, "-hide_banner", "-loglevel", "error", "-y"]
    for item in plan:
        cmd += ["-i", item["wav"]]
    cmd += ["-filter_complex", fc, "-map", "[out]", "-ar", "44100", "-ac", "2", str(out)]
    try:
        subprocess.run(cmd, timeout=120, creationflags=NO_WINDOW, check=True, cwd=str(jdir),
                       capture_output=True)
    except subprocess.CalledProcessError as e:
        log(job, "Voice-over assemble failed: " + (e.stderr or b"").decode(errors="replace")[-400:])
        return None
    except Exception:
        return None
    if out.exists() and out.stat().st_size > 2000:
        for item in plan:
            try:
                os.remove(item["wav"])
            except Exception:
                pass
        log(job, f"Voice-over ready for clip {idx} ({lang}).")
        return str(out)
    return None


# ================= ASS =================

def ts_ass(x, clip_dur):
    x = max(0.0, min(clip_dur, x))
    h = int(x // 3600)
    m = int(x % 3600 // 60)
    s = x % 60
    return f"{h}:{m:02d}:{s:05.2f}"


def wrap_title(t, width=30):
    t = t.strip()
    if len(t) <= width:
        return t
    cut = t[:width].rsplit(" ", 1)[0] or t[:width]
    rest = t[len(cut):].strip()
    if len(rest) > width:
        rest = rest[:width - 1].rsplit(" ", 1)[0] + "…"
    return cut + r"\N" + rest


def make_ass(groups, s0, e0, title_text, lang, rtl, w=1080, h=1920):
    clip_dur = max(0.5, e0 - s0)
    k = h / 1920.0
    cap_size = int(round((62 if not rtl else 58) * k))
    cap_margin_v = int(round(345 * k))
    title_size = int(round(42 * k))
    title_margin_v = int(round(140 * k))
    head = f"""[Script Info]
ScriptType: v4.00+
PlayResX: {w}
PlayResY: {h}
WrapStyle: 2
ScaledBorderAndShadow: yes
YCbCr Matrix: TV.709

[V4+ Styles]
Format: Name, Fontname, Fontsize, PrimaryColour, SecondaryColour, OutlineColour, BackColour, Bold, Italic, Underline, StrikeOut, ScaleX, ScaleY, Spacing, Angle, BorderStyle, Outline, Shadow, Alignment, MarginL, MarginR, MarginV, Encoding
Style: Cap,Arial Black,{cap_size},&H00FFFFFF,&H00000000,&H00000000,&H96000000,0,0,0,0,100,100,0,0,1,{int(round(6*k))},2,2,30,30,{cap_margin_v},1
Style: Title,Arial Black,{title_size},&H00FFFFFF,&H00000000,&H00000000,&HAA000000,1,0,0,0,100,100,0,0,1,{int(round(5*k))},1,8,30,30,{title_margin_v},1

[Events]
Format: Layer, Start, End, Style, Name, MarginL, MarginR, MarginV, Effect, Text
"""
    events = []
    for g in groups:
        if g["end"] <= s0 or g["start"] >= e0:
            continue
        txt = g["text"]
        txt = txt.replace("\\", "/").replace("{", "(").replace("}", ")")
        txt = re.sub(r"\s+", " ", txt).strip()
        if not txt:
            continue
        if lang in ("en",):
            txt = txt.upper()
        st = ts_ass(max(g["start"], s0) - s0, clip_dur)
        en = ts_ass(min(g["end"], e0) - s0 + 0.04, clip_dur)
        if en > st:
            events.append(f"Dialogue: 0,{st},{en},Cap,,0,0,0,,{txt}")
    if title_text:
        t = title_text.replace("\\", "/").replace("{", "(").replace("}", ")").strip()
        if t:
            t = wrap_title(t)
            events.append(f"Dialogue: 2,{ts_ass(0,clip_dur)},{ts_ass(clip_dur,clip_dur)},Title,,0,0,0,,{t}")
    return head + "\n".join(events) + "\n"


# ================= render =================

def render_clip(job, seg, idx, video_path, has_audio):
    jdir = TEMP_DIR / job["id"]
    out_dir = DL_DIR / job["id"]
    out_dir.mkdir(exist_ok=True)
    out_name = f"{idx:02d}-kta3-{slug(job.get('video_title'))}.mp4"
    out_path = out_dir / out_name
    s, e = float(seg["start"]), float(seg["end"])
    clip_dur = e - s
    if clip_dur < 3:
        return None

    w, h = job.get("out_w", 1080), job.get("out_h", 1920)

    # ------- captions (translate + burn-in)
    clipped = []
    if job["captions"]:
        clipped = [dict(g) for g in job["caption_groups"]
                   if g["start"] >= s - 0.2 and g["end"] <= e + 0.2]
    if clipped and job["sub_lang"] != "original":
        n_tr = len(clipped)
        for k, g in enumerate(clipped):
            g["text"] = translate_line(g["text"], job["sub_lang"])
            if k % 5 == 0:
                with JOBS_LOCK:
                    job["translate_frac"] = k / max(n_tr, 1)
    ass_file = None
    if clipped:
        title_single = (job.get("video_title") or "")[:74] if job["add_title"] else ""
        ass_file = jdir / f"cap{idx}.ass"
        ass_file.write_text(make_ass(clipped, s, e, title_single,
                                     job["sub_lang"] if job["sub_lang"] != "original" else "",
                                     job.get("rtl", False), w, h), encoding="utf-8")

    base = (f"[0:v]split=2[bg][fg];"
            f"[bg]scale={w}:{h}:force_original_aspect_ratio=increase,crop={w}:{h},"
            "boxblur=luma_radius=24:luma_power=2:chroma_radius=12:chroma_power=2,"
            "eq=brightness=-0.07:saturation=1.1[bgb];"
            f"[fg]scale={w}:{h}:force_original_aspect_ratio=decrease[fgs];"
            "[bgb][fgs]overlay=(W-w)/2:(H-h)/2")
    if ass_file:
        vf = base + f"[base];[base]subtitles=cap{idx}.ass[v]"
    else:
        vf = base + "[v]"

    # ------- audio plan (original / attention sfx / free dub)
    voice = job.get("voice", "original")
    sfx_file = job.get("sfx_file")
    use_sfx = bool(job.get("sfx")) and bool(sfx_file) and os.path.exists(sfx_file)
    dub_wav = None
    if voice.startswith("dub"):
        if clipped:
            dub_wav = synth_dub_track(job, clipped, s, e, jdir, idx)
        elif voice == "dub_replace":
            log(job, "Voice dub skipped: no captions in this video, keeping original audio.")
    if voice == "dub_replace" and dub_wav is None:
        keep_orig = has_audio
    else:
        keep_orig = has_audio

    input_args = ["-ss", f"{s:.3f}", "-i", str(video_path)]
    sfx_idx = dub_idx = None
    if use_sfx:
        sfx_idx = input_args.count("-i")
        input_args += ["-i", str(sfx_file)]
    if dub_wav:
        dub_idx = input_args.count("-i")
        input_args += ["-i", str(dub_wav)]

    afilter = ""
    on_lines, labels = [], []
    if keep_orig and has_audio:
        vol = 0.35 if dub_wav else 1.0
        on_lines.append(f"[0:a]aformat=sample_rates=44100:channel_layouts=stereo,"
                        f"atrim=0:{clip_dur:.3f},volume={vol}[a_orig]")
        labels.append("[a_orig]")
    if dub_wav:
        on_lines.append(f"[{dub_idx}:a]aformat=sample_rates=44100:channel_layouts=stereo,volume=1.0[a_dub]")
        labels.append("[a_dub]")
    if use_sfx:
        on_lines.append(f"[{sfx_idx}:a]aformat=sample_rates=44100:channel_layouts=stereo,volume=1.15[a_sfx]")
        labels.append("[a_sfx]")
    if labels:
        if len(labels) == 1:
            afilter = (";".join(on_lines) + labels[0] +
                       f"loudnorm=I=-14:TP=-1.5:LRA=11,apad=whole_dur={clip_dur:.3f}[a]")
        else:
            afilter = (";".join(on_lines) + ";" + "".join(labels) +
                       f"amix=inputs={len(labels)}:duration=first:dropout_transition=0:normalize=0,"
                       "loudnorm=I=-14:TP=-1.5:LRA=11[a]")

    cmd = ([FFMPEG, "-hide_banner", "-nostats", "-loglevel", "error", "-y"] + input_args +
           ["-filter_complex", vf + ";" + afilter if afilter else vf, "-map", "[v]"])
    if afilter:
        cmd += ["-map", "[a]", "-c:a", "aac", "-b:a", "160k", "-ar", "44100", "-ac", "2"]
    else:
        cmd += ["-an"]
    cmd += ["-t", f"{clip_dur:.3f}", "-c:v", "libx264", "-preset", "veryfast", "-crf", "20",
            "-profile:v", "high", "-level", "4.1", "-pix_fmt", "yuv420p", "-movflags", "+faststart",
            "-progress", "pipe:1", str(out_path)]

    log(job, f"Building clip {idx} ({int(s)}s -> {int(e)}s)...")
    proc = subprocess.Popen(cmd, cwd=str(jdir), stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True, encoding="utf-8",
                            errors="replace", creationflags=NO_WINDOW)
    tail = []
    for line in proc.stdout:
        tail.append(line.rstrip())
        if len(tail) > 15:
            tail.pop(0)
        m = re.search(r"out_time_us=(\d+)", line)
        if m:
            with JOBS_LOCK:
                job["clip_frac"] = min(1.0, int(m.group(1)) / max(clip_dur * 1e6, 1))
    ret = proc.wait()
    with JOBS_LOCK:
        job["clip_frac"] = 0.0
    if ret != 0 or not out_path.exists() or out_path.stat().st_size < 20_000:
        log(job, f"ffmpeg failed for clip {idx} (code {ret})")
        for tl in tail:
            if tl.strip():
                log(job, "  " + tl)
        return None
    log(job, f"Clip {idx} ready ({out_path.stat().st_size/1e6:.1f} MB)")
    return out_path


# ================= pipeline =================

def pipeline(job):
    video_path = None
    try:
        job["stage"] = "info"
        with JOBS_LOCK:
            job["progress"] = 3
        log(job, "Reading video info...")
        info = fetch_info(job["url"])
        job["video_title"] = info.get("title") or "Video"
        job["video_duration"] = float(info.get("duration") or 0) or None
        job["thumbnail"] = info.get("thumbnail") or ""
        job["uploader"] = info.get("uploader") or ""
        job["video_tags"] = [t for t in (info.get("tags") or [])][:12]
        job["video_sub_base"] = pick_sub_language(info) or ""
        log(job, f"Loaded: {job['video_title']} — {int(job.get('video_duration') or 0)}s")

        if (job.get("video_duration") or 0) < 25:
            raise Exception("Video is too short (<25s). Give me a bigger video.")

        n, target = job["count"], job["target"]
        vdur = job["video_duration"]
        if vdur and vdur < n * target * 0.75:
            new_n = max(1, int(vdur // (target * 0.85)) or 1)
            if new_n != n:
                log(job, f"Video is not long enough: cutting {new_n} clips instead of {n}.")
                job["count"] = n = new_n

        # ------- subtitles
        job["stage"] = "subs"
        log(job, "Reading subtitles (timestamps)...")
        lang_key = pick_sub_language(info)
        cues = []
        if lang_key:
            job["video_subs_lang"] = lang_key
            sub_path = download_subs(job, lang_key)
            if sub_path:
                cues = clean_cues(parse_any(sub_path))
                log(job, f"Loaded {len(cues)} caption lines (track: {lang_key})")
        if not cues:
            job["captions"] = False
            job["caption_groups"] = []
            job["sub_lang"] = "original"
            log(job, "No captions found — segments will be spread evenly, without burned captions.")
        else:
            job["captions"] = True
            job["caption_groups"] = split_groups(cues)
            rtl_src = " ".join(c["text"] for c in cues[:60])
            job["rtl"] = bool(re.search(r"[\u0590-\u08FF\uFB50-\uFDFF]", rtl_src))

        # ------- download video
        job["stage"] = "video"
        max_h = 1080 if (vdur or 0) < 3300 else 720
        fmt = (f"bestvideo[height<={max_h}][ext=mp4]+bestaudio[ext=m4a]/"
               f"bestvideo[height<={max_h}]+bestaudio/"
               f"best[ext=mp4][height<={max_h}]/best[height<={max_h}]/best")
        jdir = TEMP_DIR / job["id"]
        jdir.mkdir(parents=True, exist_ok=True)

        def hook(d):
            if d.get("status") == "downloading":
                tot = d.get("total_bytes") or d.get("total_bytes_estimate") or 0
                if tot:
                    with JOBS_LOCK:
                        job["down_pct"] = min(1.0, (d.get("downloaded_bytes") or 0) / tot)
            elif d.get("status") == "finished":
                with JOBS_LOCK:
                    job["down_pct"] = 1.0

        cache = TEMP_DIR / "cache" / hashlib.sha1(job["url"].encode("utf-8")).hexdigest()[:16]
        cached = []
        if cache.exists():
            cached = [p for p in cache.iterdir()
                      if p.suffix.lower() in (".mp4", ".mkv", ".webm", ".mov")]
        if cached:
            hc = max(cached, key=lambda p: p.stat().st_size)
            shutil.copy2(hc, jdir / ("video" + hc.suffix.lower()))
            log(job, "Reusing the cached download for this link (fast).")
        else:
            log(job, f"Downloading video (up to {max_h}p)...")
            vopts = {"format": fmt, "outtmpl": {"default": str(jdir / "video.%(ext)s")},
                     "progress_hooks": [hook], "merge_output_format": "mp4", **_base_opts()}
            with yt_dlp.YoutubeDL(vopts) as y:
                y.extract_info(job["url"], download=True)
        hits = [p for p in jdir.glob("video.*") if p.suffix.lower() in (".mp4", ".mkv", ".webm", ".mov")]
        if not hits:
            raise Exception("Download failed. If this is Instagram/TikTok, add a cookies.txt file "
                            "in the kta3box folder (export from a logged-in browser) and try again.")
        video_path = max(hits, key=lambda p: p.stat().st_size)
        if not cached:
            try:
                cache.mkdir(parents=True, exist_ok=True)
                shutil.copy2(video_path, cache / ("video" + video_path.suffix.lower()))
                log(job, "Download kept in the local cache (reused on any retry).")
            except Exception:
                pass
        log(job, f"Video ready ({video_path.stat().st_size/1e6:.0f} MB)")

        dur_v, has_audio = probe_streams(video_path)

        # ------- pick best moments
        job["stage"] = "select"
        job["progress"] = 31
        log(job, "Scoring windows and picking the best moments...")
        segments = choose_segments(cues, job["count"], job["target"], dur_v or vdur or 0)
        if len(segments) < job["count"]:
            extra = fallback_segments(job["count"] - len(segments), job["target"], dur_v or vdur or 0)
            segments += extra
        log(job, "Picks: " + " | ".join(f"{int(x['start'])}s->{int(x['end'])}s" for x in segments))

        # viral hashtags per clip
        platform = job.get("platform", "youtube_short")
        union = []
        for seg in segments:
            clip_text = ""
            if job["captions"]:
                clip_text = " ".join(g["text"] for g in job["caption_groups"]
                                     if g["start"] >= seg["start"] - 0.2 and g["end"] <= seg["end"] + 0.2)
            tags = make_hashtags(job.get("video_title") or "", job.get("video_tags"),
                                 clip_text, platform)
            seg["hashtags"] = tags
            for t in tags:
                if t not in union:
                    union.append(t)
        job["hashtags"] = union[:20]
        if union:
            log(job, f"Viral hashtags generated ({len(job['hashtags'])}).")

        # ------- attention sound effect (free, synthesized locally)
        job["stage"] = "render"
        if job.get("sfx"):
            sfx = make_sfx(jdir)
            job["sfx_file"] = str(sfx) if sfx else None
            log(job, "Attention sound effect ready." if sfx else
                      "Sound effect could not be generated, continuing without it.")

        job["clips_total"] = len(segments)
        ok = []
        for i, seg in enumerate(segments, 1):
            with JOBS_LOCK:
                job["clip_idx"] = i
            out = render_clip(job, seg, i, video_path, has_audio)
            if out:
                ok.append({"file": out.name, "name": out.name,
                           "start": int(seg["start"]), "end": int(seg["end"]),
                           "hashtags": seg.get("hashtags", []),
                           "url": f"/api/file/{job['id']}/{out.name}",
                           "download": f"/api/download/{job['id']}/{out.name}"})
            with JOBS_LOCK:
                job["done_clips"] = len(ok)
        if not ok:
            raise Exception("Every render attempt failed — try again with another link.")
        job["clips"] = ok
        job["stage"] = "done"
        job["progress"] = 100
        log(job, f"DONE! {len(ok)} clips ready — download buttons are below.")
        try:
            video_path.unlink()
            for f in jdir.glob("*.ass"):
                f.unlink()
            for f in sorted(jdir.glob("sub.*")):
                f.unlink()
        except Exception:
            pass
    except Exception as e:
        job["stage"] = "error"
        job["error"] = str(e)
        log(job, f"ERROR: {e}")
        if video_path:
            try:
                video_path.unlink()
            except Exception:
                pass
    with JOBS_LOCK:
        job["running"] = False


# ================= flask =================

app = Flask(__name__, static_folder=None)


@app.get("/")
def index():
    return send_from_directory(STATIC_DIR, "index.html")


@app.post("/api/create")
def create():
    data = flask_request.get_json(force=True, silent=True) or {}
    url = (data.get("url") or "").strip()
    if url.startswith("www."):
        url = "https://" + url
    if not re.search(r"(youtube\.com/|youtu\.be/|tiktok\.com/|instagram\.com/)", url):
        return jsonify({"error": "That is not a YouTube / TikTok / Instagram link — "
                                 "copy the full link."}), 400
    try:
        count = max(1, min(8, int(data.get("count") or 4)))
        target = max(15, min(170, int(data.get("target") or 45)))
    except Exception:
        count, target = 4, 45
    platform = data.get("platform") if data.get("platform") in PLATFORMS else "youtube_short"
    if platform == "youtube_short":
        target = min(target, 60)
    sub_lang = data.get("sub_lang") if data.get("sub_lang") in LANGS else "original"
    voice = data.get("voice") if data.get("voice") in ("original", "dub_mix", "dub_replace") else "original"
    w, h = PLATFORMS[platform]
    jid = uuid.uuid4().hex[:10]
    job = {"id": jid, "url": url, "count": count, "target": target, "sub_lang": sub_lang,
           "add_title": bool(data.get("add_title", True)), "platform": platform,
           "out_w": w, "out_h": h, "voice": voice, "sfx": bool(data.get("sfx")),
           "hashtags": [], "stage": "queued", "msgs": [], "clips": [],
           "done_clips": 0, "clips_total": 0, "clip_idx": 0, "clip_frac": 0.0,
           "down_pct": 0.0, "running": True, "created": time.time()}
    with JOBS_LOCK:
        JOBS[jid] = job
    threading.Thread(target=pipeline, args=(job,), daemon=True).start()
    return jsonify({"id": jid, "platform": platform})


def overall_progress(job):
    st = job.get("stage")
    if st in ("queued", "info"):
        return 4
    if st == "subs":
        return 6
    if st == "video":
        with JOBS_LOCK:
            return 6 + int(26 * job.get("down_pct", 0.0))
    if st == "select":
        return 32
    if st == "render":
        with JOBS_LOCK:
            total = max(job.get("clips_total", 1), 1)
            frac = (job.get("done_clips", 0) + job.get("clip_frac", 0.0)) / total
        return 33 + int(65 * min(frac, 1.0))
    if st == "done":
        return 100
    return 0 if st == "error" else 4


STAGE_LABELS = {
    "queued": "Queued...", "info": "Reading video info...", "subs": "Reading subtitles...",
    "video": "Downloading video...", "select": "Picking best moments...",
    "render": "Building montage...", "done": "Done! Clips are ready", "error": "Error"
}


@app.get("/api/status/<jid>")
def status(jid):
    with JOBS_LOCK:
        job = JOBS.get(jid)
        if not job:
            return jsonify({"error": "job not found"}), 404
        job = dict(job)
    job.pop("caption_groups", None)
    return jsonify({"stage": job["stage"], "stage_label": STAGE_LABELS.get(job["stage"], ""),
                    "progress": overall_progress(job), "msgs": job["msgs"][-7:],
                    "clips": job.get("clips", []), "error": job.get("error"),
                    "video_title": job.get("video_title"), "thumbnail": job.get("thumbnail"),
                    "uploader": job.get("uploader"), "video_duration": job.get("video_duration"),
                    "count": job.get("count"), "captions": job.get("captions"),
                    "platform": job.get("platform", "youtube_short"),
                    "out_w": job.get("out_w"), "out_h": job.get("out_h"),
                    "hashtags": job.get("hashtags", []),
                    "running": job.get("running")})


@app.get("/api/file/<jid>/<path:name>")
def preview(jid, name):
    return send_from_directory(DL_DIR / jid, name, conditional=True)


@app.get("/api/download/<jid>/<path:name>")
def download(jid, name):
    return send_from_directory(DL_DIR / jid, name, as_attachment=True)


@app.get("/api/zip/<jid>")
def zip_all(jid):
    with JOBS_LOCK:
        job = JOBS.get(jid)
        clips = list(job.get("clips", [])) if job else []
    if not clips:
        return jsonify({"error": "no clips yet"}), 404
    zpath = DL_DIR / jid / "kolhom.zip"
    if not zpath.exists():
        with zipfile.ZipFile(zpath, "w", zipfile.ZIP_DEFLATED) as z:
            for c in clips:
                z.write(DL_DIR / jid / c["file"], arcname=c["file"])
    return send_file(zpath, as_attachment=True, download_name="kta3box-shorts.zip")


if __name__ == "__main__":
    import socket

    def lan_ip():
        try:
            s_ = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s_.connect(("8.8.8.8", 80))
            ip = s_.getsockname()[0]
            s_.close()
            return ip
        except Exception:
            return "127.0.0.1"

    port = 8080
    print()
    print("  Kta3Box — video link into shorts (YouTube / TikTok / Instagram)")
    print(f"  ffmpeg  : {FFMPEG}")
    print(f"  web     : http://127.0.0.1:{port}")
    print(f"  network : http://{lan_ip()}:{port}  (phones on the same Wi-Fi)")
    print()
    threading.Timer(1.2, lambda: webbrowser.open(f"http://127.0.0.1:{port}")).start()
    app.run(host="0.0.0.0", port=port, debug=False, threaded=True)
