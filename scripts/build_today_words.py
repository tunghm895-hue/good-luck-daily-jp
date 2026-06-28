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
# Riêng N*: tách quota theo nguồn để sheet Cộng đồng luôn có
# tối đa 20 mục Báo chí và 10 mục Forum.
NSTAR_NEWS_TARGET = 20
NSTAR_FORUM_TARGET = 10

# N* = từ được Sudachi tách ra nhưng không nằm trong bất kỳ danh sách N1–N5
# tham chiếu nào. Trong app, N* được coi là bậc cao nhất.
JLPT_LEVELS_HARD_TO_EASY = ("N1", "N2", "N3", "N4", "N5")
JLPT_LEVELS_EASY_TO_HARD = tuple(reversed(JLPT_LEVELS_HARD_TO_EASY))
OUTPUT_LEVELS_HARD_TO_EASY = ("N*",) + JLPT_LEVELS_HARD_TO_EASY

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
# Chính xác một chữ Kanji. Dùng để giữ các từ một ký tự như 米, 月, 局.
SINGLE_KANJI = re.compile(r"^[一-龯]$")
HTML_TAG = re.compile(r"<[^>]+>")
PARENTHETICAL_SUFFIX = re.compile(r"\s*[（(].*?[）)]\s*$")

# Trợ từ, trợ động từ, liên từ và phó từ chỉ được đưa vào danh sách
# khi cách đọc có từ 3 mora (âm tiết Nhật) trở lên. Ví dụ: しかし (3),
# かなり (3), ながら (3), らしい (3). Các token ngắn như が, を, に,
# は, だ, ない (2 mora), また (2 mora) sẽ bị bỏ qua để danh sách không
# bị ngập từ chức năng quá ngắn.
FUNCTION_POS = {"助詞", "助動詞", "接続詞", "副詞"}
FUNCTION_POS_MIN_MORA = 3

# Ký tự nhỏ ghép với mora ngay trước đó, nên không được tính thành một
# mora riêng. Dấu trường âm ー, っ và ん vẫn là mora riêng và được tính.
SMALL_KANA = frozenset(
    "ァィゥェォャュョヮヵヶ"
    "ぁぃぅぇぉゃゅょゎゕゖ"
    "ㇰㇱㇲㇳㇴㇵㇶㇷㇸㇹㇺㇻㇼㇽㇾㇿ"
)

# Nhóm nội dung đang được xử lý bình thường. Từ một ký tự chỉ được giữ
# khi đó là Kanji, để tránh danh sách tràn các token kana đơn lẻ.
CONTENT_POS = {"名詞", "動詞", "形容詞", "形状詞"}

# Với token một Kanji thuộc POS khác, vẫn giữ nếu không phải các nhóm
# từ chức năng/cảm thán bên dưới. Ví dụ: 各 (接頭辞), 氏 (接尾辞).
SINGLE_KANJI_EXCLUDED_POS = FUNCTION_POS | {"感動詞"}


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

    for level in JLPT_LEVELS_HARD_TO_EASY:
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
    for level in JLPT_LEVELS_EASY_TO_HARD:
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


def mora_count(reading: str) -> int:
    """Đếm mora từ cách đọc kana của Sudachi.

    Ví dụ: かなり → 3, でしょう → 3, いっそう → 4.
    Ký tự nhỏ như ャ/ュ/ョ không tăng mora; ー/ッ/ン vẫn được tính.
    """
    reading = unicodedata.normalize("NFKC", reading or "").strip()
    if not reading or reading == "*":
        return 0
    return sum(1 for char in reading if char not in SMALL_KANA)


def should_keep_term(
    word: str,
    reading: str,
    pos_main: str,
    pos_sub: str,
) -> bool:
    """Quy tắc giữ token cho danh sách từ nổi bật.

    - Giữ trợ từ, trợ động từ, liên từ và phó từ khi cách đọc có từ 3
      mora trở lên, không dựa trên số ký tự viết.
    - Giữ danh từ/động từ/tính từ/tính từ-na như trước; token một ký tự
      chỉ được giữ khi là đúng một Kanji.
    - Giữ thêm token đúng một Kanji thuộc POS khác, miễn không phải trợ từ,
      trợ động từ, liên từ, phó từ hoặc cảm thán.
    - Vẫn loại tên riêng, số từ, đại từ và danh từ phụ thuộc để không làm
      danh sách bị chi phối bởi tên người, số liệu hay token ngữ pháp vụn.
    """
    if pos_main == "名詞" and pos_sub in {"固有名詞", "数詞", "代名詞", "非自立可能"}:
        return False

    if pos_main in FUNCTION_POS:
        return mora_count(reading) >= FUNCTION_POS_MIN_MORA

    if pos_main in CONTENT_POS:
        return len(word) >= 2 or bool(SINGLE_KANJI.fullmatch(word))

    return bool(SINGLE_KANJI.fullmatch(word)) and pos_main not in SINGLE_KANJI_EXCLUDED_POS


def extract_terms(text: str) -> list[str]:
    terms: list[str] = []

    for token in _TOKENIZER.tokenize(text, _TOKENIZER_MODE):
        pos = token.part_of_speech()
        pos_main = pos[0]
        pos_sub = pos[1]
        word = token.dictionary_form()
        reading = token.reading_form()

        if (
            word == "*"
            or word in STOP_WORDS
            or not JAPANESE_WORD.fullmatch(word)
            or not should_keep_term(word, reading, pos_main, pos_sub)
        ):
            continue

        terms.append(word)

    return terms


def _sort_candidates(candidates: list[dict]) -> list[dict]:
    """Sắp xếp ưu tiên theo số bài, số nguồn và điểm nổi bật."""
    candidates.sort(
        key=lambda item: (
            item["articleCount"],
            len(item["channels"]),
            item["score"],
            item["term"],
        ),
        reverse=True,
    )
    return candidates


def build_items(
    articles: list[Article],
    jlpt_levels: dict[str, str],
) -> tuple[list[dict], dict[str, int], dict[str, int]]:
    """Tạo danh sách từ theo mức JLPT.

    N1-N5: tối đa 15 từ mỗi mức như trước.
    N*: tách riêng tối đa 20 từ thuộc báo chí và 10 từ thuộc Forum.
    Một từ N* đã được chọn cho báo chí sẽ không lặp lại ở Forum để tránh
    thẻ trùng trong mục Tất cả. Item N* chỉ mang channel mà nó được chọn,
    nhờ đó bộ lọc Báo chí/Forum hiện đúng quota của từng nguồn.
    """
    stats = defaultdict(
        lambda: {
            "article_ids": set(),
            "channels": set(),
            "links": set(),
            "article_ids_by_channel": defaultdict(set),
            "links_by_channel": defaultdict(set),
            "jlpt_level": "",
        }
    )

    for index, article in enumerate(articles):
        seen_in_article: set[str] = set()
        for term in extract_terms(article.text):
            if term in seen_in_article:
                continue

            # Không tìm thấy trong toàn bộ N1-N5 thì gắn N* thay vì loại bỏ.
            level = jlpt_levels.get(term, "N*")

            # Từ đúng một Kanji ở N4/N5 thường là từ quá cơ bản đối với
            # danh sách gợi ý của sheet Cộng đồng. Các từ một Kanji ở N*,
            # N1, N2 hoặc N3 vẫn được giữ.
            if SINGLE_KANJI.fullmatch(term) and level in {"N4", "N5"}:
                continue

            seen_in_article.add(term)
            stat = stats[term]
            stat["article_ids"].add(index)
            stat["channels"].add(article.channel)
            stat["article_ids_by_channel"][article.channel].add(index)
            stat["jlpt_level"] = level

            if article.link:
                stat["links"].add(article.link)
                stat["links_by_channel"][article.channel].add(article.link)

    by_level: dict[str, list[dict]] = {
        level: [] for level in OUTPUT_LEVELS_HARD_TO_EASY
    }
    nstar_by_channel: dict[str, list[dict]] = {
        "news": [],
        "community": [],
    }

    for term, info in stats.items():
        level = info["jlpt_level"]
        if level not in by_level:
            continue

        article_count = len(info["article_ids"])
        channel_count = len(info["channels"])
        score = article_count * 3 + channel_count * 5

        # Với N*, tạo ứng viên riêng theo từng nguồn. Việc này để quota
        # 20 Báo chí + 10 Forum không bị một từ xuất hiện ở hai nguồn chiếm
        # cả hai vị trí hoặc hiện trùng trong mục Tất cả.
        if level == "N*":
            for channel in ("news", "community"):
                source_article_ids = info["article_ids_by_channel"].get(channel, set())
                if not source_article_ids:
                    continue

                source_article_count = len(source_article_ids)
                source_score = source_article_count * 3 + 5
                nstar_by_channel[channel].append(
                    {
                        "term": term,
                        "jlptLevel": level,
                        "articleCount": source_article_count,
                        "channels": [channel],
                        "score": source_score,
                        "sourceUrls": sorted(
                            info["links_by_channel"].get(channel, set())
                        )[:3],
                    }
                )
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

    # N*: 20 Báo chí trước, sau đó 10 Forum và không cho trùng term để
    # danh sách Tất cả không có hai thẻ cho cùng một từ.
    nstar_news = _sort_candidates(nstar_by_channel["news"])[:NSTAR_NEWS_TARGET]
    selected_nstar_terms = {item["term"] for item in nstar_news}

    nstar_forum_candidates = [
        item for item in nstar_by_channel["community"]
        if item["term"] not in selected_nstar_terms
    ]
    nstar_forum = _sort_candidates(nstar_forum_candidates)[:NSTAR_FORUM_TARGET]

    result: list[dict] = [*nstar_news, *nstar_forum]
    level_counts: dict[str, int] = {"N*": len(nstar_news) + len(nstar_forum)}
    nstar_source_counts = {
        "news": len(nstar_news),
        "community": len(nstar_forum),
    }

    # N1-N5 vẫn chọn tối đa 15 từ/mức, không thay đổi thuật toán cũ.
    for level in JLPT_LEVELS_HARD_TO_EASY:
        selected = _sort_candidates(by_level[level])[:TARGET_PER_LEVEL]
        result.extend(selected)
        level_counts[level] = len(selected)

    return result, level_counts, nstar_source_counts

def main() -> None:
    jlpt_levels = fetch_jlpt_levels()
    articles = fetch_google_news() + fetch_qiita()
    if not articles:
        raise RuntimeError("Không tải được dữ liệu từ bất kỳ nguồn nào.")

    items, level_counts, nstar_source_counts = build_items(articles, jlpt_levels)
    now_japan = datetime.now(ZoneInfo("Asia/Tokyo"))

    payload = {
        "schemaVersion": 4,
        "generatedAt": now_japan.isoformat(),
        "generatedAtDisplay": now_japan.strftime("%d/%m · %H:%M"),
        "timezone": "Asia/Tokyo",
        "articleCount": len(articles),
        "targetPerJlptLevel": TARGET_PER_LEVEL,
        "nStarTargets": {
            "news": NSTAR_NEWS_TARGET,
            "community": NSTAR_FORUM_TARGET,
        },
        "nStarSourceCounts": nstar_source_counts,
        "levelCounts": level_counts,
        "items": items,
    }

    OUTPUT_FILE.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_FILE.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )

    summary = ", ".join(f"{level}={level_counts[level]}" for level in OUTPUT_LEVELS_HARD_TO_EASY)
    print(
        f"Đã tạo {OUTPUT_FILE} ({summary}; "
        f"N* báo={nstar_source_counts['news']}, "
        f"Forum={nstar_source_counts['community']})."
    )


if __name__ == "__main__":
    main()
