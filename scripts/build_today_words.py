from __future__ import annotations

import csv
import html
import io
import json
import re
import unicodedata
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import feedparser
import requests
from sudachipy import dictionary, tokenizer


OUTPUT_FILE = Path("public/today_words.json")
TARGET_PER_LEVEL = 15
LEVELS_HARD_TO_EASY = ("N1", "N2", "N3", "N4", "N5")
LEVELS_EASY_TO_HARD = tuple(reversed(LEVELS_HARD_TO_EASY))

GOOGLE_NEWS_RSS = "https://news.google.com/rss?hl=ja&gl=JP&ceid=JP:ja"
QIITA_API = "https://qiita.com/api/v2/items?page=1&per_page=100"

# Danh sách hỗ trợ gắn mức JLPT. Mỗi từ được xếp ở mức dễ nhất xuất hiện
# trong bộ danh sách để các từ cơ bản không bị xếp nhầm sang N1/N2.
JLPT_CSV_URLS = {
    "N1": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n1.csv",
    "N2": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n2.csv",
    "N3": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n3.csv",
    "N4": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n4.csv",
    "N5": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n5.csv",
}

HEADERS = {"User-Agent": "GoodLuckDailyJapaneseWords/2.0"}

STOP_WORDS = {
    "する",
    "いる",
    "ある",
    "なる",
    "できる",
    "行う",
    "こと",
    "もの",
    "ため",
    "ところ",
    "これ",
    "それ",
    "今回",
    "同社",
    "同日",
    "日本",
    "東京",
    "今日",
    "記事",
    "ニュース",
    "場合",
    "内容",
    "結果",
}

JAPANESE_WORD = re.compile(r"^[ぁ-んァ-ヶ一-龯々ー]+$")
HTML_TAG = re.compile(r"<[^>]+>")
PARENTHETICAL_SUFFIX = re.compile(r"\s*[（(].*?[）)]\s*$")


@dataclass(frozen=True)
class Article:
    text: str
    link: str
    channel: str


def clean_text(value: str) -> str:
    value = HTML_TAG.sub(" ", value or "")
    value = html.unescape(value)
    return re.sub(r"\s+", " ", value).strip()


def normalize_jlpt_term(value: str) -> str | None:
    """Chỉ giữ một từ có thể so trực tiếp với dictionary form Sudachi."""
    value = unicodedata.normalize("NFKC", value or "").strip()
    value = PARENTHETICAL_SUFFIX.sub("", value)
    value = value.replace("～", "").replace("~", "").strip()

    # Bộ danh sách có vài mục là cụm/mẫu. Các mục đó không thể đối chiếu chính
    # xác với token đơn mà script đang lấy từ tiêu đề RSS.
    if not value or " " in value or "　" in value:
        return None
    if not JAPANESE_WORD.fullmatch(value):
        return None
    return value


def fetch_jlpt_levels() -> dict[str, str]:
    """Trả về term -> mức. Ưu tiên mức dễ hơn nếu term bị lặp giữa các list."""
    per_level: dict[str, set[str]] = {}

    for level in LEVELS_HARD_TO_EASY:
        response = requests.get(JLPT_CSV_URLS[level], headers=HEADERS, timeout=60)
        response.raise_for_status()
        text = response.content.decode("utf-8-sig")
        reader = csv.DictReader(io.StringIO(text))

        words: set[str] = set()
        for row in reader:
            for column in ("expression", "reading"):
                normalized = normalize_jlpt_term(row.get(column, ""))
                if normalized:
                    words.add(normalized)
        per_level[level] = words

    levels: dict[str, str] = {}
    for level in LEVELS_EASY_TO_HARD:
        for word in per_level.get(level, set()):
            levels.setdefault(word, level)
    return levels


def fetch_google_news() -> list[Article]:
    try:
        response = requests.get(GOOGLE_NEWS_RSS, headers=HEADERS, timeout=30)
        response.raise_for_status()
        feed = feedparser.parse(response.content)

        results: list[Article] = []
        for entry in feed.entries:
            title = clean_text(entry.get("title", ""))
            summary = clean_text(entry.get("summary", ""))
            link = entry.get("link", "")
            if title:
                results.append(Article(text=f"{title} {summary}", link=link, channel="news"))
        return results
    except Exception as error:
        print(f"[WARN] Google News lỗi: {error}")
        return []


def fetch_qiita() -> list[Article]:
    try:
        response = requests.get(QIITA_API, headers=HEADERS, timeout=30)
        response.raise_for_status()

        results: list[Article] = []
        for item in response.json():
            title = clean_text(item.get("title", ""))
            tags = " ".join(tag.get("name", "") for tag in item.get("tags", []))
            link = item.get("url", "")
            if title:
                results.append(Article(text=f"{title} {tags}", link=link, channel="community"))
        return results
    except Exception as error:
        print(f"[WARN] Qiita lỗi: {error}")
        return []


_TOKENIZER = dictionary.Dictionary().create()
_TOKENIZER_MODE = tokenizer.Tokenizer.SplitMode.C


def extract_terms(text: str) -> list[str]:
    terms: list[str] = []

    for token in _TOKENIZER.tokenize(text, _TOKENIZER_MODE):
        pos = token.part_of_speech()
        pos_main = pos[0]
        pos_sub = pos[1]

        if pos_main not in {"名詞", "動詞", "形容詞", "形状詞"}:
            continue
        if pos_main == "名詞" and pos_sub in {"固有名詞", "数詞", "代名詞", "非自立可能"}:
            continue

        word = token.dictionary_form()
        if (
            word == "*"
            or len(word) < 2
            or word in STOP_WORDS
            or not JAPANESE_WORD.fullmatch(word)
        ):
            continue
        terms.append(word)

    return terms


def build_items(articles: list[Article], jlpt_levels: dict[str, str]) -> tuple[list[dict], dict[str, int]]:
    stats = defaultdict(
        lambda: {
            "article_ids": set(),
            "channels": set(),
            "links": set(),
            "jlpt_level": "",
        }
    )

    for index, article in enumerate(articles):
        seen_in_article: set[str] = set()
        for term in extract_terms(article.text):
            level = jlpt_levels.get(term)
            if level is None or term in seen_in_article:
                continue

            seen_in_article.add(term)
            stat = stats[term]
            stat["article_ids"].add(index)
            stat["channels"].add(article.channel)
            stat["jlpt_level"] = level
            if article.link:
                stat["links"].add(article.link)

    by_level: dict[str, list[dict]] = {level: [] for level in LEVELS_HARD_TO_EASY}
    for term, info in stats.items():
        article_count = len(info["article_ids"])
        channel_count = len(info["channels"])
        score = article_count * 3 + channel_count * 5
        level = info["jlpt_level"]
        if level not in by_level:
            continue

        by_level[level].append(
            {
                "term": term,
                "jlptLevel": level,
                "articleCount": article_count,
                "channels": sorted(info["channels"]),
                "score": score,
                "sourceUrls": sorted(info["links"])[:3],
            }
        )

    result: list[dict] = []
    level_counts: dict[str, int] = {}
    for level in LEVELS_HARD_TO_EASY:
        candidates = by_level[level]
        # Ưu tiên từ có nhiều bài nguồn; nếu chưa đủ 15 thì từ 1 bài cũng được
        # giữ để cố gắng luôn cung cấp đủ danh sách trong từng mức.
        candidates.sort(
            key=lambda item: (
                item["articleCount"],
                len(item["channels"]),
                item["score"],
                item["term"],
            ),
            reverse=True,
        )
        selected = candidates[:TARGET_PER_LEVEL]
        result.extend(selected)
        level_counts[level] = len(selected)

    return result, level_counts


def main() -> None:
    jlpt_levels = fetch_jlpt_levels()
    articles = fetch_google_news() + fetch_qiita()
    if not articles:
        raise RuntimeError("Không tải được dữ liệu từ bất kỳ nguồn nào.")

    items, level_counts = build_items(articles, jlpt_levels)
    now_japan = datetime.now(ZoneInfo("Asia/Tokyo"))

    payload = {
        "schemaVersion": 2,
        "generatedAt": now_japan.isoformat(),
        "generatedAtDisplay": now_japan.strftime("%d/%m · %H:%M"),
        "timezone": "Asia/Tokyo",
        "articleCount": len(articles),
        "targetPerJlptLevel": TARGET_PER_LEVEL,
        "levelCounts": level_counts,
        "items": items,
    }

    OUTPUT_FILE.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_FILE.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    summary = ", ".join(f"{level}={level_counts[level]}" for level in LEVELS_HARD_TO_EASY)
    print(f"Đã tạo {OUTPUT_FILE} ({summary}).")


if __name__ == "__main__":
    main()
