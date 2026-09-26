#!/usr/bin/env python3
"""
THAI NEWS - Free 3-hour news collector/classifier.

No paid API is required.
- Reads public RSS/Google News RSS feeds.
- Classifies articles into exactly 9 English keys.
- Deduplicates by normalized URL/title.
- Keeps a rolling central data/news.json.
- Adds only a small number of top-scoring stories per run.
"""

from __future__ import annotations

import hashlib
import html
import json
import re
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone, timedelta
from pathlib import Path
from email.utils import parsedate_to_datetime

ROOT = Path(__file__).resolve().parent
DATA_FILE = ROOT / "data" / "news.json"

MAX_TOTAL = 120
MAX_AGE_HOURS = 72
MAX_NEW_PER_CATEGORY = 2
REQUEST_TIMEOUT = 20

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

# Google News RSS search feeds. "latest" is calculated from all categories,
# so the collector only needs eight source buckets.
FEEDS = {
    "politics": [
        "การเมือง ไทย นโยบาย รัฐบาล รัฐสภา กฎหมาย",
    ],
    "entertainment": [
        "บันเทิง ดารา นักแสดง ภาพยนตร์ ซีรีส์ ละคร",
    ],
    "accident": [
        "อุบัติเหตุ รถชน น้ำท่วม ภัยพิบัติ ไฟไหม้ กู้ภัย",
    ],
    "economy": [
        "เศรษฐกิจ หุ้น ราคาสินค้า การลงทุน ธุรกิจ เงินเฟ้อ",
    ],
    "society": [
        "สังคม ชุมชน แรงงาน โรงงาน คุณภาพชีวิต สิทธิ",
    ],
    "sports": [
        "กีฬา ฟุตบอล ทีมชาติไทย นักกีฬา แข่งขัน",
    ],
    "international": [
        "ต่างประเทศ ผู้นำโลก สงคราม พายุ ความร่วมมือระหว่างประเทศ",
    ],
    "general": [
        "ข่าวทั่วไป ประเทศไทย ชุมชน กิจกรรม ประชาสัมพันธ์",
    ],
}

CATEGORY_KEYWORDS = {
    "politics": [
        "รัฐบาล","นายกรัฐมนตรี","รัฐสภา","สภา","พรรคการเมือง","เลือกตั้ง",
        "กฎหมาย","พ.ร.บ.","นโยบาย","ครม.","ฝ่ายค้าน","รัฐบาล","รัฐมนตรี",
    ],
    "entertainment": [
        "บันเทิง","ดารา","นักแสดง","ภาพยนตร์","ซีรีส์","ละคร","เพลง",
        "ศิลปิน","ไอดอล","พรมแดง","แฟนคลับ","ดราม่าโซเชียล",
    ],
    "accident": [
        "อุบัติเหตุ","รถชน","ชน","เสียชีวิต","บาดเจ็บ","ไฟไหม้","ระเบิด",
        "น้ำท่วม","น้ำป่า","ดินถล่ม","พายุ","ภัยพิบัติ","กู้ภัย","ตกจาก",
    ],
    "economy": [
        "เศรษฐกิจ","หุ้น","ตลาดหุ้น","เงินบาท","ดอกเบี้ย","ลงทุน","การลงทุน",
        "ราคาน้ำมัน","ราคาทอง","สินค้า","ธุรกิจ","ส่งออก","นำเข้า","เงินเฟ้อ",
    ],
    "society": [
        "สังคม","ชุมชน","แรงงาน","โรงงาน","ความปลอดภัย","สิทธิ","คุณภาพชีวิต",
        "ประชาชน","โรงเรียน","โรงพยาบาล","สาธารณสุข","ตรวจสอบ",
    ],
    "sports": [
        "กีฬา","ฟุตบอล","ทีมชาติไทย","นักกีฬา","แข่งขัน","ชิงแชมป์","พรีเมียร์ลีก",
        "เอเชียนเกมส์","ซีเกมส์","โอลิมปิก","แบดมินตัน","มวย","วอลเลย์บอล",
    ],
    "international": [
        "ต่างประเทศ","สหรัฐ","จีน","ญี่ปุ่น","เกาหลี","รัสเซีย","ยูเครน",
        "ผู้นำโลก","ประธานาธิบดี","นายกรัฐมนตรี","ทอร์นาโด","พายุ","ต่างชาติ",
        "ความร่วมมือระหว่างประเทศ","สหประชาชาติ",
    ],
}

IMPORTANT_WORDS = [
    "ด่วน","ล่าสุด","จับตา","เปิดเผย","ประกาศ","เตือน","เสียชีวิต",
    "วิกฤต","ชนะ","แชมป์","ไฟไหม้","น้ำท่วม","แผ่นดินไหว","พายุ",
    "รัฐบาล","รัฐสภา","ราคาทอง","หุ้น","ทีมชาติไทย",
]

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

def fetch_xml(url: str) -> bytes:
    request = urllib.request.Request(
        url,
        headers={
            "User-Agent": "THAI-NEWS-BOT/1.0 (+GitHub Actions RSS collector)",
            "Accept": "application/rss+xml, application/xml, text/xml, */*",
        },
    )
    with urllib.request.urlopen(request, timeout=REQUEST_TIMEOUT) as response:
        return response.read()

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
        description = clean_text(first_text(item, ("description",)))
        pub_date = clean_text(first_text(item, ("pubDate", "published", "updated")))

        if not title or not link:
            continue

        # RSS images are not guaranteed. Prefer media/enclosure URLs when present.
        image = ""
        for child in list(item):
            tag = child.tag.split("}")[-1]
            if tag in ("content", "thumbnail", "enclosure"):
                image = child.attrib.get("url", "") or child.attrib.get("href", "")
                if image:
                    break

        published = parse_date(pub_date)
        items.append({
            "title": title,
            "description": description[:500],
            "url": link,
            "publishedAt": published.isoformat(),
            "image": image,
            "sourceName": "",
            "seedCategory": fallback_category,
        })
    return items

def classify(item: dict) -> str:
    text = f"{item['title']} {item['description']}".lower()
    scores = {key: 0 for key in CATEGORY_KEYWORDS}

    for category, words in CATEGORY_KEYWORDS.items():
        for word in words:
            if word.lower() in text:
                scores[category] += 1

    # The RSS search bucket gets a small tie-break bonus.
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
    DATA_FILE.write_text(
        json.dumps(items, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

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

    return candidates

def build_records(candidates: list[dict], old: list[dict]) -> list[dict]:
    cutoff = now_utc() - timedelta(hours=MAX_AGE_HOURS)

    fresh = []
    for item in candidates:
        published = parse_date(item.get("publishedAt", ""))
        if published < cutoff:
            continue

        category = classify(item)
        record = {
            "id": make_id(item["url"], item["title"]),
            "category": category,
            "title": item["title"],
            "description": item["description"],
            "cover": item["image"] or "assets/banner.jpg",
            "content": [{"text": item["description"]}] if item["description"] else [],
            "publishedAt": published.isoformat(),
            "views": 0,
            "sourceUrl": item["url"],
            "sourceName": item.get("sourceName") or "RSS / Google News",
            "automated": True,
        }
        record["_score"] = score(record)
        fresh.append(record)

    # Existing auto records are retained for a short rolling window.
    existing_auto = [x for x in old if x.get("automated") is True]
    combined = existing_auto + fresh

    # De-duplicate before selecting the run's quota.
    combined = dedupe(combined)

    # Only add up to N top stories per category per run.
    selected = []
    for category in CATEGORY_NAMES:
        if category == "latest":
            continue
        bucket = [x for x in combined if x.get("category") == category]
        bucket.sort(key=lambda x: (float(x.get("_score", 0)), x.get("publishedAt", "")), reverse=True)
        selected.extend(bucket[:MAX_NEW_PER_CATEGORY])

    # Keep manual records exactly as they are; auto records are selected separately.
    manual = [x for x in old if x.get("automated") is not True]
    final = dedupe(manual + selected)
    final.sort(key=lambda x: x.get("publishedAt", x.get("created_at", "")), reverse=True)

    # Strip internal scoring field.
    for item in final:
        item.pop("_score", None)

    return final[:MAX_TOTAL]

def main() -> None:
    print("[THAI NEWS] collecting...")
    old = load_db()
    candidates = collect()
    print(f"[THAI NEWS] candidates: {len(candidates)}")

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
