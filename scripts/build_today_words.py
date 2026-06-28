from __future__ import annotations

import html
import json
import re
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import feedparser
import requests
from sudachipy import dictionary, tokenizer


OUTPUT_FILE = Path("public/today_words.json")

# Nguồn báo tổng hợp Nhật và cộng đồng công nghệ Nhật.
GOOGLE_NEWS_RSS = (
    "https://news.google.com/rss?hl=ja&gl=JP&ceid=JP:ja"
)
QIITA_API = "https://qiita.com/api/v2/items?page=1&per_page=100"

HEADERS = {
    "User-Agent": "GoodLuckDailyJapaneseWords/1.0"
}

STOP_WORDS = {
    "する", "いる", "ある", "なる", "できる", "行う",
    "こと", "もの", "ため", "ところ", "これ", "それ",
    "今回", "同社", "同日", "日本", "東京", "今日",
    "記事", "ニュース", "場合", "内容", "結果",
}

JAPANESE_WORD = re.compile(r"^[ぁ-んァ-ヶ一-龯々ー]+$")
HTML_TAG = re.compile(r"<[^>]+>")


@dataclass
class Article:
    text: str
    link: str
    channel: str


def clean_text(value: str) -> str:
    value = HTML_TAG.sub(" ", value or "")
    value = html.unescape(value)
    return re.sub(r"\s+", " ", value).strip()


def fetch_google_news() -> list[Article]:
    try:
        response = requests.get(
            GOOGLE_NEWS_RSS,
            headers=HEADERS,
            timeout=30,
        )
        response.raise_for_status()

        feed = feedparser.parse(response.content)
        results: list[Article] = []

        for entry in feed.entries:
            title = clean_text(entry.get("title", ""))
            summary = clean_text(entry.get("summary", ""))
            link = entry.get("link", "")

            if title:
                results.append(
                    Article(
                        text=f"{title} {summary}",
                        link=link,
                        channel="news",
                    )
                )

        return results
    except Exception as error:
        print(f"[WARN] Google News lỗi: {error}")
        return []


def fetch_qiita() -> list[Article]:
    try:
        response = requests.get(
            QIITA_API,
            headers=HEADERS,
            timeout=30,
        )
        response.raise_for_status()

        results: list[Article] = []

        for item in response.json():
            title = clean_text(item.get("title", ""))
            tags = " ".join(
                tag.get("name", "")
                for tag in item.get("tags", [])
            )
            link = item.get("url", "")

            if title:
                results.append(
                    Article(
                        text=f"{title} {tags}",
                        link=link,
                        channel="community",
                    )
                )

        return results
    except Exception as error:
        print(f"[WARN] Qiita lỗi: {error}")
        return []


def extract_terms(text: str) -> list[str]:
    tokenizer_obj = dictionary.Dictionary().create()
    mode = tokenizer.Tokenizer.SplitMode.C

    terms: list[str] = []

    for token in tokenizer_obj.tokenize(text, mode):
        pos = token.part_of_speech()
        pos_main = pos[0]
        pos_sub = pos[1]

        if pos_main not in {"名詞", "動詞", "形容詞", "形状詞"}:
            continue

        if pos_main == "名詞" and pos_sub in {
            "固有名詞",
            "数詞",
            "代名詞",
            "非自立可能",
        }:
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


def build_items(articles: list[Article]) -> list[dict]:
    stats = defaultdict(
        lambda: {
            "article_ids": set(),
            "channels": set(),
            "links": set(),
        }
    )

    for index, article in enumerate(articles):
        seen_in_article = set()

        for term in extract_terms(article.text):
            if term in seen_in_article:
                continue

            seen_in_article.add(term)
            stats[term]["article_ids"].add(index)
            stats[term]["channels"].add(article.channel)

            if article.link:
                stats[term]["links"].add(article.link)

    items: list[dict] = []

    for term, info in stats.items():
        article_count = len(info["article_ids"])
        channel_count = len(info["channels"])

        # Bản đầu: tối thiểu xuất hiện ở 2 bài.
        if article_count < 2:
            continue

        score = article_count * 3 + channel_count * 5

        items.append(
            {
                "term": term,
                "articleCount": article_count,
                "channels": sorted(info["channels"]),
                "score": score,
                "sourceUrls": sorted(info["links"])[:3],
            }
        )

    items.sort(
        key=lambda item: (
            item["score"],
            item["articleCount"],
            item["term"],
        ),
        reverse=True,
    )

    return items[:20]


def main() -> None:
    articles = fetch_google_news() + fetch_qiita()

    if not articles:
        raise RuntimeError("Không tải được dữ liệu từ bất kỳ nguồn nào.")

    items = build_items(articles)

    now_japan = datetime.now(ZoneInfo("Asia/Tokyo"))

    payload = {
        "schemaVersion": 1,
        "generatedAt": now_japan.isoformat(),
        "timezone": "Asia/Tokyo",
        "articleCount": len(articles),
        "items": items,
    }

    OUTPUT_FILE.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_FILE.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    print(f"Đã tạo {OUTPUT_FILE} với {len(items)} từ.")


if __name__ == "__main__":
    main()
