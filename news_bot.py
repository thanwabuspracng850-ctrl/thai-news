#!/usr/bin/env python3
"""
THAI NEWS - Free 3-hour news collector/classifier.

Changes in this version:
- Reads Google News RSS feeds.
- Opens the original article page to find og:image / twitter:image when RSS has no image.
- Downloads the cover image into assets/news/ so GitHub Pages can display it reliably.
- Extracts a substantially longer article body from JSON-LD/article paragraphs when available.
- Keeps the existing JSON structure used by the THAI NEWS website.
- Keeps manual records untouched.
"""

from __future__ import annotations

import hashlib
import html
import json
import re
import time
import urllib.parse
import urllib.request
import urllib.error
import xml.etree.ElementTree as ET
from datetime import datetime, timezone, timedelta
from pathlib import Path
from email.utils import parsedate_to_datetime

ROOT = Path(__file__).resolve().parent
DATA_FILE = ROOT / "data" / "news.json"
IMAGE_DIR = ROOT / "assets" / "news"

MAX_TOTAL = 120
MAX_AGE_HOURS = 72
MAX_NEW_PER_CATEGORY = 2
REQUEST_TIMEOUT = 20
ARTICLE_TIMEOUT = 15
MAX_IMAGE_BYTES = 8 * 1024 * 1024

CATEGORY_NAMES = {
    "latest": "ข่าวล่าสุด",
    "politics": "การเมือง",
    "entertainment": "บันเทิง",
    "accident": "อุบัติเหตุ",
    "economy": "เศรษฐกิจ",
    "society": "สังคม",
    "sports": "กีฬา",
    "international": "ต่างประเทศ",
    "general": "ข่าวทั่วไป",
}

FEEDS = {
    "politics": ["การเมือง ไทย นโยบาย รัฐบาล รัฐสภา กฎหมาย"],
    "entertainment": ["บันเทิง ดารา นักแสดง ภาพยนตร์ ซีรีส์ ละคร"],
    "accident": ["อุบัติเหตุ รถชน น้ำท่วม ภัยพิบัติ ไฟไหม้ กู้ภัย"],
    "economy": ["เศรษฐกิจ หุ้น ราคาสินค้า การลงทุน ธุรกิจ เงินเฟ้อ"],
    "society": ["สังคม ชุมชน แรงงาน โรงงาน คุณภาพชีวิต สิทธิ"],
    "sports": ["กีฬา ฟุตบอล ทีมชาติไทย นักกีฬา แข่งขัน"],
    "international": ["ต่างประเทศ ผู้นำโลก สงคราม พายุ ความร่วมมือระหว่างประเทศ"],
    "general": ["ข่าวทั่วไป ประเทศไทย ชุมชน กิจกรรม ประชาสัมพันธ์"],
}

CATEGORY_KEYWORDS = {
    "politics": [
        "รัฐบาล", "นายกรัฐมนตรี", "รัฐสภา", "สภา", "พรรคการเมือง", "เลือกตั้ง",
        "กฎหมาย", "พ.ร.บ.", "นโยบาย", "ครม.", "ฝ่ายค้าน", "รัฐมนตรี",
    ],
    "entertainment": [
        "บันเทิง", "ดารา", "นักแสดง", "ภาพยนตร์", "ซีรีส์", "ละคร", "เพลง",
        "ศิลปิน", "ไอดอล", "พรมแดง", "แฟนคลับ", "ดราม่าโซเชียล",
    ],
    "accident": [
        "อุบัติเหตุ", "รถชน", "ชน", "เสียชีวิต", "บาดเจ็บ", "ไฟไหม้", "ระเบิด",
        "น้ำท่วม", "น้ำป่า", "ดินถล่ม", "พายุ", "ภัยพิบัติ", "กู้ภัย", "ตกจาก",
    ],
    "economy": [
        "เศรษฐกิจ", "หุ้น", "ตลาดหุ้น", "เงินบาท", "ดอกเบี้ย", "ลงทุน", "การลงทุน",
        "ราคาน้ำมัน", "ราคาทอง", "สินค้า", "ธุรกิจ", "ส่งออก", "นำเข้า", "เงินเฟ้อ",
    ],
    "society": [
        "สังคม", "ชุมชน", "แรงงาน", "โรงงาน", "ความปลอดภัย", "สิทธิ", "คุณภาพชีวิต",
        "ประชาชน", "โรงเรียน", "โรงพยาบาล", "สาธารณสุข", "ตรวจสอบ",
    ],
    "sports": [
        "กีฬา", "ฟุตบอล", "ทีมชาติไทย", "นักกีฬา", "แข่งขัน", "ชิงแชมป์", "พรีเมียร์ลีก",
        "เอเชียนเกมส์", "ซีเกมส์", "โอลิมปิก", "แบดมินตัน", "มวย", "วอลเลย์บอล",
    ],
    "international": [
        "ต่างประเทศ", "สหรัฐ", "จีน", "ญี่ปุ่น", "เกาหลี", "รัสเซีย", "ยูเครน",
        "ผู้นำโลก", "ประธานาธิบดี", "นายกรัฐมนตรี", "ทอร์นาโด", "พายุ", "ต่างชาติ",
        "ความร่วมมือระหว่างประเทศ", "สหประชาชาติ",
    ],
}

IMPORTANT_WORDS = [
    "ด่วน", "ล่าสุด", "จับตา", "เปิดเผย", "ประกาศ", "เตือน", "เสียชีวิต",
    "วิกฤต", "ชนะ", "แชมป์", "ไฟไหม้", "น้ำท่วม", "แผ่นดินไหว", "พายุ",
    "รัฐบาล", "รัฐสภา", "ราคาทอง", "หุ้น", "ทีมชาติไทย",
]

USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/131 Safari/537.36 THAI-NEWS-BOT/2.0"


def now_utc() -> datetime:
    return datetime.now(timezone.utc)


def clean_text(value: str) -> str:
    value = html.unescape(value or "")
    value = re.sub(r"<[^>]+>", " ", value)
    value = re.sub(r"\s+", " ", value)
    return value.strip()


def normalize_key(value: str) -> str:
    value = clean_text(value).lower()
    value = re.sub(r"https?://", "", value)
    value = re.sub(r"[^\wก-๙]+", " ", value, flags=re.UNICODE)
    return re.sub(r"\s+", " ", value).strip()


def parse_date(value: str) -> datetime:
    if not value:
        return now_utc()
    try:
        dt = parsedate_to_datetime(value)
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc)
    except Exception:
        try:
            return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(timezone.utc)
        except Exception:
            return now_utc()


def google_news_url(query: str) -> str:
    return (
        "https://news.google.com/rss/search?"
        + urllib.parse.urlencode({"q": query, "hl": "th", "gl": "TH", "ceid": "TH:th"})
    )


def fetch_bytes(url: str, timeout: int = REQUEST_TIMEOUT) -> bytes:
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": USER_AGENT,
            "Accept": "text/html,application/xhtml+xml,application/xml,application/rss+xml,text/xml,*/*",
        },
    )
    with urllib.request.urlopen(request, timeout=timeout) as response:
        return response.read()


def fetch_xml(url: str) -> bytes:
    return fetch_bytes(url, REQUEST_TIMEOUT)


def first_text(node: ET.Element, names: tuple[str, ...]) -> str:
    for child in list(node):
        tag = child.tag.split("}")[-1]
        if tag in names and child.text:
            return child.text
    return ""


def parse_feed(xml_bytes: bytes, fallback_category: str) -> list[dict]:
    root = ET.fromstring(xml_bytes)
    items = []
    for item in root.iter():
        if item.tag.split("}")[-1] != "item":
            continue

        title = clean_text(first_text(item, ("title",)))
        link = clean_text(first_text(item, ("link",)))
        raw_description = first_text(item, ("description",))
        description = clean_text(raw_description)
        pub_date = clean_text(first_text(item, ("pubDate", "published", "updated")))

        if not title or not link:
            continue

        # Google News RSS sometimes puts the real thumbnail inside the
        # description as <img src="...">. Keep it before clean_text() strips HTML.
        image = ""
        img_match = re.search(r'<img[^>]+src=["\']([^"\']+)["\']', raw_description or "", flags=re.I)
        if img_match:
            image = html.unescape(img_match.group(1)).strip()

        source_name = ""
        for child in list(item):
            tag = child.tag.split("}")[-1]
            if tag in ("content", "thumbnail", "enclosure"):
                image = child.attrib.get("url", "") or child.attrib.get("href", "") or image
                if image:
                    break
            if tag == "source" and child.text:
                source_name = clean_text(child.text)

        published = parse_date(pub_date)
        items.append({
            "title": title,
            "description": description[:1000],
            "url": link,
            "publishedAt": published.isoformat(),
            "image": image,
            "sourceName": source_name,
            "seedCategory": fallback_category,
        })
    return items


def absolute_url(url: str, base: str) -> str:
    if not url:
        return ""
    return urllib.parse.urljoin(base, url.strip())


def extract_meta(html_text: str, names: tuple[str, ...]) -> str:
    # Handles both <meta property="og:image" content="..."> and reversed attribute order.
    for name in names:
        patterns = [
            rf'<meta[^>]+(?:property|name)=["\']{re.escape(name)}["\'][^>]+content=["\']([^"\']+)["\']',
            rf'<meta[^>]+content=["\']([^"\']+)["\'][^>]+(?:property|name)=["\']{re.escape(name)}["\']',
        ]
        for pattern in patterns:
            match = re.search(pattern, html_text, flags=re.I)
            if match:
                return html.unescape(match.group(1)).strip()
    return ""


def extract_jsonld_article_body(html_text: str) -> str:
    """Extract articleBody/description from JSON-LD without depending on a site-specific parser."""
    bodies = []
    for match in re.finditer(
        r'<script[^>]+type=["\']application/ld\+json["\'][^>]*>(.*?)</script>',
        html_text,
        flags=re.I | re.S,
    ):
        raw = html.unescape(match.group(1)).strip()
        if not raw:
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue

        stack = data if isinstance(data, list) else [data]
        while stack:
            obj = stack.pop()
            if isinstance(obj, list):
                stack.extend(obj)
                continue
            if not isinstance(obj, dict):
                continue
            if isinstance(obj.get("@graph"), list):
                stack.extend(obj["@graph"])
            body = obj.get("articleBody")
            if isinstance(body, str) and len(clean_text(body)) >= 200:
                bodies.append(clean_text(body))
            desc = obj.get("description")
            if isinstance(desc, str) and len(clean_text(desc)) >= 120:
                bodies.append(clean_text(desc))
    # Longest body is usually the actual articleBody.
    if not bodies:
        return ""
    return max(bodies, key=len)


def extract_article_paragraphs(html_text: str) -> list[str]:
    """Extract readable paragraphs from common article containers."""
    body = re.sub(r'<script[\s\S]*?</script>', ' ', html_text, flags=re.I)
    body = re.sub(r'<style[\s\S]*?</style>', ' ', body, flags=re.I)
    body = re.sub(r'<noscript[\s\S]*?</noscript>', ' ', body, flags=re.I)

    candidates = []
    # Prefer article/main containers if present.
    containers = re.findall(
        r'<(?:article|main)[^>]*>(.*?)</(?:article|main)>',
        body,
        flags=re.I | re.S,
    )
    search_area = "\n".join(containers) if containers else body

    for raw in re.findall(r'<p[^>]*>(.*?)</p>', search_area, flags=re.I | re.S):
        value = clean_text(raw)
        value = re.sub(r'\s+', ' ', value).strip()
        if 70 <= len(value) <= 2500:
            candidates.append(value)

    # Remove obvious UI/navigation noise.
    bad_terms = (
        "สมัครสมาชิก", "เข้าสู่ระบบ", "ติดตามเรา", "โฆษณา",
        "อ่านเพิ่มเติม", "ข่าวที่เกี่ยวข้อง", "เมนู", "ค้นหา",
        "copyright", "privacy policy",
    )
    filtered = []
    seen = set()
    for item in candidates:
        key = normalize_key(item)
        if not key or key in seen:
            continue
        if any(term in item.lower() for term in bad_terms):
            continue
        seen.add(key)
        filtered.append(item)
    return filtered


def split_long_text(text: str, max_chars: int = 900) -> list[str]:
    """Split articleBody into readable paragraphs while preserving source wording."""
    text = clean_text(text)
    if not text:
        return []
    # Prefer sentence boundaries in Thai/English.
    sentences = re.split(r'(?<=[.!?。！？])\s+|(?<=\u0e2f)\s+', text)
    sentences = [s.strip() for s in sentences if s.strip()]
    chunks, current = [], ""
    for sentence in sentences:
        if not current:
            current = sentence
        elif len(current) + 1 + len(sentence) <= max_chars:
            current += " " + sentence
        else:
            chunks.append(current.strip())
            current = sentence
    if current:
        chunks.append(current.strip())
    return [c for c in chunks if len(c) >= 60]


def extract_article_page(url: str) -> dict:
    """Find cover + substantial source paragraphs for a long article page."""
    try:
        raw = fetch_bytes(url, ARTICLE_TIMEOUT)
        text = raw.decode("utf-8", errors="ignore")
        text_head = text[:4_000_000]

        image = extract_meta(text_head, ("og:image", "twitter:image", "twitter:image:src"))
        description = extract_meta(text_head, ("og:description", "twitter:description", "description"))
        site_name = extract_meta(text_head, ("og:site_name",))
        article_body = extract_jsonld_article_body(text_head)

        paragraphs = []
        if article_body:
            paragraphs.extend(split_long_text(article_body, 900))
        if len(paragraphs) < 5:
            paragraphs.extend(extract_article_paragraphs(text_head))

        # De-duplicate while keeping order.
        unique = []
        seen = set()
        for para in paragraphs:
            key = normalize_key(para)
            if key and key not in seen:
                seen.add(key)
                unique.append(para)

        # A useful description should be the first few source paragraphs.
        if not description and unique:
            description = " ".join(unique[:2])[:900]

        return {
            "image": absolute_url(image, url),
            "description": clean_text(description)[:900],
            "paragraphs": unique[:24],
            "sourceName": clean_text(site_name),
        }
    except Exception as exc:
        print(f"[WARN] article page failed: {url} -> {exc}")
        return {"image": "", "description": "", "paragraphs": [], "sourceName": ""}


def safe_extension(content_type: str, url: str) -> str:
    ct = (content_type or "").lower().split(";", 1)[0].strip()
    mapping = {
        "image/jpeg": ".jpg",
        "image/jpg": ".jpg",
        "image/png": ".png",
        "image/webp": ".webp",
        "image/gif": ".gif",
    }
    if ct in mapping:
        return mapping[ct]
    path = urllib.parse.urlparse(url).path.lower()
    for ext in (".jpg", ".jpeg", ".png", ".webp", ".gif"):
        if path.endswith(ext):
            return ".jpg" if ext == ".jpeg" else ext
    return ".jpg"


def download_cover(url: str, item_id: str) -> str:
    """Download article cover to assets/news and return a GitHub Pages relative path."""
    if not url:
        return ""

    IMAGE_DIR.mkdir(parents=True, exist_ok=True)
    existing = list(IMAGE_DIR.glob(item_id + ".*"))
    if existing:
        return existing[0].relative_to(ROOT).as_posix()

    try:
        request = urllib.request.Request(
            url,
            headers={
                "User-Agent": USER_AGENT,
                "Accept": "image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8",
                "Referer": urllib.parse.urlsplit(url).scheme + "://" + urllib.parse.urlsplit(url).netloc + "/",
            },
        )
        with urllib.request.urlopen(request, timeout=ARTICLE_TIMEOUT) as response:
            content_type = response.headers.get("Content-Type", "")
            data = response.read(MAX_IMAGE_BYTES + 1)

        if len(data) > MAX_IMAGE_BYTES:
            print(f"[WARN] image too large: {url}")
            return ""

        if not content_type.lower().startswith("image/"):
            # Some servers omit Content-Type. Check common magic bytes.
            if not (data.startswith(b"\xff\xd8\xff") or data.startswith(b"\x89PNG") or data.startswith(b"RIFF")):
                print(f"[WARN] not an image: {url}")
                return ""

        ext = safe_extension(content_type, url)
        path = IMAGE_DIR / f"{item_id}{ext}"
        path.write_bytes(data)
        print(f"[IMAGE] saved {path}")
        return path.relative_to(ROOT).as_posix()
    except Exception as exc:
        print(f"[WARN] image download failed: {url} -> {exc}")
        return ""


def classify(item: dict) -> str:
    text = f"{item.get('title','')} {item.get('description','')}".lower()
    scores = {key: 0 for key in CATEGORY_KEYWORDS}

    for category, words in CATEGORY_KEYWORDS.items():
        for word in words:
            if word.lower() in text:
                scores[category] += 1

    seed = item.get("seedCategory")
    if seed in scores:
        scores[seed] += 2

    best = max(scores, key=scores.get)
    return best if scores[best] > 0 else "general"


def score(item: dict) -> float:
    published = parse_date(item.get("publishedAt", ""))
    age_hours = max(0.0, (now_utc() - published).total_seconds() / 3600)
    recency = max(0.0, 48.0 - age_hours)
    text = f"{item.get('title','')} {item.get('description','')}".lower()
    importance = sum(1 for word in IMPORTANT_WORDS if word.lower() in text) * 4
    return recency + importance


def make_id(url: str, title: str) -> str:
    digest = hashlib.sha256((url + "|" + normalize_key(title)).encode("utf-8")).hexdigest()[:18]
    return "auto_" + digest


def load_db() -> list[dict]:
    if not DATA_FILE.exists():
        return []
    try:
        data = json.loads(DATA_FILE.read_text(encoding="utf-8"))
        return data if isinstance(data, list) else []
    except Exception:
        return []


def save_db(items: list[dict]) -> None:
    DATA_FILE.parent.mkdir(parents=True, exist_ok=True)
    DATA_FILE.write_text(json.dumps(items, ensure_ascii=False, indent=2), encoding="utf-8")


def dedupe(items: list[dict]) -> list[dict]:
    result = []
    seen_urls = set()
    seen_titles = set()

    for item in sorted(items, key=lambda x: x.get("publishedAt", ""), reverse=True):
        url_key = normalize_key(item.get("sourceUrl", item.get("url", "")))
        title_key = normalize_key(item.get("title", ""))

        if url_key and url_key in seen_urls:
            continue
        if title_key and title_key in seen_titles:
            continue

        if url_key:
            seen_urls.add(url_key)
        if title_key:
            seen_titles.add(title_key)
        result.append(item)

    return result


def enrich_candidate(item: dict) -> dict:
    """Get cover + substantial article paragraphs from the original page."""
    page = extract_article_page(item.get("url", ""))
    if page.get("image"):
        item["image"] = page["image"]
    if page.get("description") and len(page["description"]) > len(item.get("description", "")):
        item["description"] = page["description"]
    if page.get("paragraphs"):
        item["paragraphs"] = page["paragraphs"]
    if page.get("sourceName"):
        item["sourceName"] = page["sourceName"]
    return item


def collect() -> list[dict]:
    candidates = []
    for seed_category, queries in FEEDS.items():
        for query in queries:
            url = google_news_url(query)
            try:
                xml = fetch_xml(url)
                candidates.extend(parse_feed(xml, seed_category))
            except Exception as exc:
                print(f"[WARN] feed failed: {seed_category}: {exc}")
            time.sleep(0.4)

    # Work on the newest candidates first, so we don't request hundreds of pages.
    candidates.sort(key=lambda x: x.get("publishedAt", ""), reverse=True)
    unique = dedupe(candidates)

    # Enrich enough candidates to fill the per-category quota.
    enriched = []
    for item in unique[:72]:
        enriched.append(enrich_candidate(item))
        time.sleep(0.15)

    return enriched


def build_records(candidates: list[dict], old: list[dict]) -> list[dict]:
    cutoff = now_utc() - timedelta(hours=MAX_AGE_HOURS)
    fresh = []

    for item in candidates:
        published = parse_date(item.get("publishedAt", ""))
        if published < cutoff:
            continue

        category = classify(item)
        record_id = make_id(item["url"], item["title"])
        description = clean_text(item.get("description", ""))

        if not description:
            description = f"ติดตามรายละเอียดข่าวล่าสุดจาก {item.get('sourceName') or 'THAI NEWS'}"

        # Prefer the downloaded local image. This prevents GitHub Pages from
        # depending on hotlinking permissions of another news website.
        cover_url = item.get("image", "")
        local_cover = download_cover(cover_url, record_id)
        cover = local_cover or cover_url or "assets/banner.jpg"

        source_paragraphs = [
            clean_text(p) for p in (item.get("paragraphs") or [])
            if clean_text(p)
        ]

        # Prefer the real article text extracted from the source page.
        # If a source exposes only a short description, keep that instead of
        # inventing facts that were not present in the source.
        if source_paragraphs:
            content_blocks = [{"text": p} for p in source_paragraphs[:24]]
        else:
            content_blocks = [{"text": description[:900]}]

        content_blocks.append({
            "text": "หมายเหตุ: THAI NEWS สรุป/รวบรวมจากข้อมูลที่เผยแพร่โดยแหล่งข่าวต้นทาง ควรตรวจสอบรายละเอียดกับต้นทางก่อนนำข้อมูลไปใช้อ้างอิง"
        })

        record = {
            "id": record_id,
            "category": category,
            "title": clean_text(item["title"]),
            "description": description[:900],
            "cover": cover,
            "content": content_blocks,
            "publishedAt": published.isoformat(),
            "views": 0,
            "sourceUrl": item["url"],
            "sourceName": item.get("sourceName") or "RSS / Google News",
            "automated": True,
        }
        record["_score"] = score(record)
        fresh.append(record)

    existing_auto = [x for x in old if x.get("automated") is True]
    combined = dedupe(existing_auto + fresh)

    selected = []
    for category in CATEGORY_NAMES:
        if category == "latest":
            continue
        bucket = [x for x in combined if x.get("category") == category]
        bucket.sort(key=lambda x: (float(x.get("_score", 0)), x.get("publishedAt", "")), reverse=True)
        selected.extend(bucket[:MAX_NEW_PER_CATEGORY])

    manual = [x for x in old if x.get("automated") is not True]
    final = dedupe(manual + selected)
    final.sort(key=lambda x: x.get("publishedAt", x.get("created_at", "")), reverse=True)

    for item in final:
        item.pop("_score", None)

    return final[:MAX_TOTAL]


def main() -> None:
    print("[THAI NEWS] collecting...")
    old = load_db()
    candidates = collect()
    print(f"[THAI NEWS] candidates enriched: {len(candidates)}")

    final = build_records(candidates, old)
    save_db(final)

    counts = {k: 0 for k in CATEGORY_NAMES}
    for item in final:
        category = item.get("category", "general")
        counts[category] = counts.get(category, 0) + 1

    print("[THAI NEWS] saved:", DATA_FILE)
    print("[THAI NEWS] category counts:", json.dumps(counts, ensure_ascii=False))


if __name__ == "__main__":
    main()
