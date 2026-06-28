from __future__ import annotations

import csv
import html
import io
import json
import re
import unicodedata
from urllib.parse import urlencode
from collections import defaultdict
from dataclasses import dataclass
from datetime import datetime, timedelta
from pathlib import Path
from zoneinfo import ZoneInfo

import feedparser
import requests
from sudachipy import dictionary, tokenizer


REPO_ROOT = Path(__file__).resolve().parents[1]
OUTPUT_FILE = REPO_ROOT / "public" / "today_words.json"
SINGLE_KANJI_BLOCKLIST_FILE = REPO_ROOT / "data" / "single_kanji_blocklist.txt"
RECENT_TERMS_FILE = REPO_ROOT / "data" / "recent_suggested_terms.json"

TARGET_PER_LEVEL = 15
# Riêng N*: tách quota theo nguồn để sheet Cộng đồng luôn có
# tối đa 20 mục Báo chí và 10 mục Forum.
NSTAR_NEWS_TARGET = 20
NSTAR_FORUM_TARGET = 10

# Không lặp lại các term đã từng được đưa vào JSON trong 48 giờ gần nhất.
RECENT_DEDUPE_HOURS = 48

# N* = từ được Sudachi tách ra nhưng không nằm trong bất kỳ danh sách N1–N5
# tham chiếu nào. Trong app, N* được coi là bậc cao nhất.
JLPT_LEVELS_HARD_TO_EASY = ("N1", "N2", "N3", "N4", "N5")
JLPT_LEVELS_EASY_TO_HARD = tuple(reversed(JLPT_LEVELS_HARD_TO_EASY))
OUTPUT_LEVELS_HARD_TO_EASY = ("N*",) + JLPT_LEVELS_HARD_TO_EASY

GOOGLE_NEWS_RSS = "https://news.google.com/rss?hl=ja&gl=JP&ceid=JP:ja"
# Đọc thêm nhiều luồng Google News để sau khi loại từ trùng 48 giờ,
# script vẫn có đủ ứng viên thay thế cho từng quota.
GOOGLE_NEWS_SEARCH_QUERIES = (
    "経済",
    "社会",
    "国際",
    "科学 技術",
    "暮らし",
    "文化",
)
QIITA_API = "https://qiita.com/api/v2/items"
QIITA_PAGES = (1, 2, 3)
QIITA_ITEMS_PER_PAGE = 100

# Danh sách hỗ trợ gắn mức JLPT. Mỗi từ được xếp ở mức dễ nhất xuất hiện
# trong bộ danh sách để các từ cơ bản không bị xếp nhầm sang N1/N2.
JLPT_CSV_URLS = {
    "N1": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n1.csv",
    "N2": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n2.csv",
    "N3": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n3.csv",
    "N4": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n4.csv",
    "N5": "https://raw.githubusercontent.com/jamsinclair/open-anki-jlpt-decks/main/src/n5.csv",
}

HEADERS = {"User-Agent": "GoodLuckDailyJapaneseWords/3.0"}

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

# Nhóm từ có nội dung. Một Kanji chỉ được giữ nếu Sudachi nhận nó là
# một trong bốn nhóm này, không phải 接頭辞/接尾辞/非自立可能...
CONTENT_POS = {"名詞", "動詞", "形容詞", "形状詞"}
DISALLOWED_NOUN_SUBTYPES = {"固有名詞", "数詞", "代名詞", "非自立可能"}


@dataclass(frozen=True)
class Article:
    text: str
    link: str
    channel: str


def clean_text(value: str) -> str:
    value = HTML_TAG.sub(" ", value or "")
    value = html.unescape(value)
    return re.sub(r"\s+", " ", value).strip()


def load_single_kanji_blocklist() -> frozenset[str]:
    """Đọc danh sách Kanji một ký tự cần loại trừ.

    Chỉ nhận dòng đúng một Kanji; dòng trống và dòng bắt đầu bằng # là chú thích.
    Thiếu file không làm workflow dừng, nhưng sẽ in cảnh báo để dễ phát hiện.
    """
    try:
        lines = SINGLE_KANJI_BLOCKLIST_FILE.read_text(encoding="utf-8").splitlines()
    except FileNotFoundError:
        print(f"[WARN] Không tìm thấy {SINGLE_KANJI_BLOCKLIST_FILE}; bỏ qua blocklist.")
        return frozenset()

    blocked: set[str] = set()
    for raw_line in lines:
        value = raw_line.strip()
        if not value or value.startswith("#"):
            continue
        if SINGLE_KANJI.fullmatch(value):
            blocked.add(value)
        else:
            print(f"[WARN] Bỏ qua dòng blocklist không phải một Kanji: {value!r}")

    return frozenset(blocked)


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


def _google_news_search_rss_url(query: str) -> str:
    params = {
        "q": query,
        "hl": "ja",
        "gl": "JP",
        "ceid": "JP:ja",
    }
    return f"https://news.google.com/rss/search?{urlencode(params)}"


def fetch_google_news() -> list[Article]:
    """Lấy nhiều luồng tin để tạo đủ ứng viên thay thế không trùng 48 giờ."""
    feed_urls = [GOOGLE_NEWS_RSS]
    feed_urls.extend(_google_news_search_rss_url(query) for query in GOOGLE_NEWS_SEARCH_QUERIES)

    results: list[Article] = []
    seen_articles: set[str] = set()

    for feed_url in feed_urls:
        try:
            response = requests.get(feed_url, headers=HEADERS, timeout=30)
            response.raise_for_status()
            feed = feedparser.parse(response.content)

            for entry in feed.entries:
                title = clean_text(entry.get("title", ""))
                summary = clean_text(entry.get("summary", ""))
                link = entry.get("link", "")
                article_key = link or title

                if not title or not article_key or article_key in seen_articles:
                    continue

                seen_articles.add(article_key)
                results.append(
                    Article(
                        text=f"{title} {summary}",
                        link=link,
                        channel="news",
                    )
                )
        except Exception as error:
            print(f"[WARN] Google News lỗi ({feed_url}): {error}")

    return results


def fetch_qiita() -> list[Article]:
    """Lấy ba trang Qiita để có đủ ứng viên Forum thay thế khi cần."""
    results: list[Article] = []
    seen_urls: set[str] = set()

    for page in QIITA_PAGES:
        try:
            response = requests.get(
                QIITA_API,
                params={"page": page, "per_page": QIITA_ITEMS_PER_PAGE},
                headers=HEADERS,
                timeout=30,
            )
            response.raise_for_status()

            for item in response.json():
                title = clean_text(item.get("title", ""))
                tags = " ".join(tag.get("name", "") for tag in item.get("tags", []))
                link = item.get("url", "")

                if not title or not link or link in seen_urls:
                    continue

                seen_urls.add(link)
                results.append(
                    Article(
                        text=f"{title} {tags}",
                        link=link,
                        channel="community",
                    )
                )
        except Exception as error:
            print(f"[WARN] Qiita lỗi (trang {page}): {error}")

    return results


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
    single_kanji_blocklist: frozenset[str],
) -> bool:
    """Quy tắc giữ token cho danh sách từ nổi bật.

    - Giữ trợ từ, trợ động từ, liên từ và phó từ khi cách đọc có từ 3
      mora trở lên, không dựa trên số ký tự viết.
    - Từ chỉ đúng một Kanji phải là danh từ/động từ/tính từ/tính từ-na có
      nghĩa độc lập. 接頭辞, 接尾辞, 非自立可能, trợ từ... luôn bị loại.
    - Blocklist xử lý các Kanji một ký tự vẫn dễ bị Sudachi nhận nhầm là
      token độc lập hữu ích, như 化/性/的/者.
    - Vẫn loại tên riêng, số từ, đại từ và danh từ phụ thuộc để không làm
      danh sách bị chi phối bởi tên người, số liệu hay token ngữ pháp vụn.
    """
    is_single_kanji = bool(SINGLE_KANJI.fullmatch(word))

    if pos_main == "名詞" and pos_sub in DISALLOWED_NOUN_SUBTYPES:
        return False

    if is_single_kanji:
        if word in single_kanji_blocklist:
            return False
        # Đây là điểm quan trọng: không còn giữ 接頭辞/接尾辞 chỉ vì chúng
        # là một Kanji. Chỉ nhận các POS nội dung có khả năng đứng độc lập.
        return pos_main in CONTENT_POS

    if pos_main in FUNCTION_POS:
        return mora_count(reading) >= FUNCTION_POS_MIN_MORA

    if pos_main in CONTENT_POS:
        return len(word) >= 2

    return False


def extract_terms(text: str, single_kanji_blocklist: frozenset[str]) -> list[str]:
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
            or not should_keep_term(
                word,
                reading,
                pos_main,
                pos_sub,
                single_kanji_blocklist,
            )
        ):
            continue

        terms.append(word)

    return terms


def _read_json_file(path: Path) -> dict:
    try:
        raw = path.read_text(encoding="utf-8")
        data = json.loads(raw)
    except FileNotFoundError:
        return {}
    except (OSError, json.JSONDecodeError) as error:
        print(f"[WARN] Không đọc được {path}: {error}")
        return {}
    return data if isinstance(data, dict) else {}


def _parse_iso_datetime(value: object) -> datetime | None:
    if not isinstance(value, str) or not value.strip():
        return None
    try:
        parsed = datetime.fromisoformat(value.strip().replace("Z", "+00:00"))
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=ZoneInfo("Asia/Tokyo"))
    return parsed.astimezone(ZoneInfo("Asia/Tokyo"))


def _merge_recent_term(
    target: dict[str, datetime],
    term: object,
    suggested_at: datetime | None,
    cutoff: datetime,
) -> None:
    if not isinstance(term, str) or not term.strip() or suggested_at is None:
        return
    normalized = term.strip()
    if suggested_at <= cutoff:
        return
    previous = target.get(normalized)
    if previous is None or suggested_at > previous:
        target[normalized] = suggested_at


def load_recent_suggested_terms(now_japan: datetime) -> dict[str, datetime]:
    """Đọc các term đã thực sự xuất hiện trong JSON 48 giờ gần nhất.

    `recent_suggested_terms.json` là nguồn chính. Ở lần nâng cấp đầu tiên,
    script cũng đọc `today_words.json` hiện có để tránh lặp ngay danh sách
    vừa được đề xuất trước khi file lịch sử mới được tạo.
    """
    cutoff = now_japan - timedelta(hours=RECENT_DEDUPE_HOURS)
    recent: dict[str, datetime] = {}

    history_payload = _read_json_file(RECENT_TERMS_FILE)
    entries = history_payload.get("entries", [])
    if isinstance(entries, list):
        for entry in entries:
            if not isinstance(entry, dict):
                continue
            _merge_recent_term(
                recent,
                entry.get("term"),
                _parse_iso_datetime(entry.get("suggestedAt")),
                cutoff,
            )

    # Bootstrap: lịch sử có thể trống ngay sau khi cập nhật script. Lấy danh
    # sách hiện hành làm một lần đề xuất nếu JSON đó còn trong cửa sổ 48 giờ.
    current_payload = _read_json_file(OUTPUT_FILE)
    current_generated_at = _parse_iso_datetime(current_payload.get("generatedAt"))
    if current_generated_at is not None:
        current_items = current_payload.get("items", [])
        if isinstance(current_items, list):
            for item in current_items:
                if isinstance(item, dict):
                    _merge_recent_term(
                        recent,
                        item.get("term"),
                        current_generated_at,
                        cutoff,
                    )

    return recent


def write_recent_suggested_terms(
    previous_recent: dict[str, datetime],
    selected_items: list[dict],
    now_japan: datetime,
) -> None:
    """Lưu lại chỉ các term được chọn thật sự trong JSON lần này."""
    cutoff = now_japan - timedelta(hours=RECENT_DEDUPE_HOURS)
    recent = {
        term: suggested_at
        for term, suggested_at in previous_recent.items()
        if suggested_at > cutoff
    }

    for item in selected_items:
        term = item.get("term")
        if isinstance(term, str) and term.strip():
            recent[term.strip()] = now_japan

    entries = [
        {
            "term": term,
            "suggestedAt": suggested_at.isoformat(),
        }
        for term, suggested_at in sorted(
            recent.items(),
            key=lambda pair: (pair[1], pair[0]),
            reverse=True,
        )
    ]

    RECENT_TERMS_FILE.parent.mkdir(parents=True, exist_ok=True)
    RECENT_TERMS_FILE.write_text(
        json.dumps(
            {
                "schemaVersion": 1,
                "updatedAt": now_japan.isoformat(),
                "windowHours": RECENT_DEDUPE_HOURS,
                "entries": entries,
            },
            ensure_ascii=False,
            indent=2,
        ),
        encoding="utf-8",
    )


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


def _select_unique_candidates(
    candidates: list[dict],
    target: int,
    recent_terms: set[str],
    selected_terms: set[str],
) -> list[dict]:
    """Chọn đủ quota bằng cách bỏ term trùng và tiếp tục lấy ứng viên kế tiếp.

    Đây là phần thay thế chính: một term đã xuất hiện trong 48 giờ bị bỏ qua,
    sau đó script tiếp tục duyệt toàn bộ danh sách xếp hạng để lấy term khác,
    thay vì chỉ xóa term trùng rồi để quota bị thiếu.
    """
    selected: list[dict] = []

    for candidate in _sort_candidates(candidates.copy()):
        term = candidate["term"]
        if term in recent_terms or term in selected_terms:
            continue

        selected.append(candidate)
        selected_terms.add(term)

        if len(selected) == target:
            break

    return selected


def _require_full_quotas(
    level_counts: dict[str, int],
    nstar_source_counts: dict[str, int],
) -> None:
    """Không công bố JSON mới nếu không thể giữ đúng số lượng đã cam kết.

    Nhờ vậy file công khai luôn đầy đủ quota. Trường hợp cực hiếm nguồn dữ liệu
    không đủ ứng viên mới sau khi đã lấy rộng hơn, workflow báo lỗi và giữ nguyên
    file JSON hoàn chỉnh của lần trước, thay vì ghi một danh sách thiếu số lượng.
    """
    shortages: list[str] = []

    if nstar_source_counts.get("news", 0) < NSTAR_NEWS_TARGET:
        shortages.append(
            f"N* Báo chí {nstar_source_counts.get('news', 0)}/{NSTAR_NEWS_TARGET}"
        )
    if nstar_source_counts.get("community", 0) < NSTAR_FORUM_TARGET:
        shortages.append(
            f"N* Forum {nstar_source_counts.get('community', 0)}/{NSTAR_FORUM_TARGET}"
        )

    for level in JLPT_LEVELS_HARD_TO_EASY:
        actual = level_counts.get(level, 0)
        if actual < TARGET_PER_LEVEL:
            shortages.append(f"{level} {actual}/{TARGET_PER_LEVEL}")

    if shortages:
        raise RuntimeError(
            "Không đủ ứng viên chưa xuất hiện trong 48 giờ để thay thế toàn bộ "
            "từ trùng: "
            + ", ".join(shortages)
            + ". Không ghi JSON mới; file đầy đủ của lần trước được giữ nguyên."
        )


def build_items(
    articles: list[Article],
    jlpt_levels: dict[str, str],
    recent_terms: set[str],
    single_kanji_blocklist: frozenset[str],
) -> tuple[list[dict], dict[str, int], dict[str, int], int]:
    """Tạo đúng quota theo cấp độ và tự thay term trùng bằng term kế tiếp.

    - N*: đúng 20 Báo chí + 10 Forum.
    - N1 đến N5: đúng 15 từ mỗi mức.
    - Mọi term đã đề xuất trong 48 giờ bị bỏ qua khi chọn; selector tiếp tục
      duyệt ứng viên thấp hơn cho đến khi đủ quota.
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
        for term in extract_terms(article.text, single_kanji_blocklist):
            if term in seen_in_article:
                continue
            seen_in_article.add(term)

            level = jlpt_levels.get(term, "N*")

            # Từ đúng một Kanji ở N4/N5 thường quá cơ bản cho danh sách.
            if SINGLE_KANJI.fullmatch(term) and level in {"N4", "N5"}:
                continue

            stat = stats[term]
            stat["article_ids"].add(index)
            stat["channels"].add(article.channel)
            stat["article_ids_by_channel"][article.channel].add(index)
            stat["jlpt_level"] = level

            if article.link:
                stat["links"].add(article.link)
                stat["links_by_channel"][article.channel].add(article.link)

    # Đếm đúng số term bị lịch sử 48h loại ở giai đoạn chọn, không đếm lặp
    # nhiều lần theo số bài/tần suất.
    excluded_by_recent_count = len(set(stats).intersection(recent_terms))

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

    # Duy trì uniqueness toàn bộ danh sách lần này. N* Báo chí ưu tiên trước,
    # Forum chỉ lấy term chưa dùng ở Báo chí và chưa tồn tại lịch sử 48 giờ.
    selected_terms: set[str] = set()
    nstar_news = _select_unique_candidates(
        nstar_by_channel["news"],
        NSTAR_NEWS_TARGET,
        recent_terms,
        selected_terms,
    )
    nstar_forum = _select_unique_candidates(
        nstar_by_channel["community"],
        NSTAR_FORUM_TARGET,
        recent_terms,
        selected_terms,
    )

    result: list[dict] = [*nstar_news, *nstar_forum]
    level_counts: dict[str, int] = {"N*": len(nstar_news) + len(nstar_forum)}
    nstar_source_counts = {
        "news": len(nstar_news),
        "community": len(nstar_forum),
    }

    # Từng level cũng tiếp tục duyệt xuống ứng viên khác cho đến đủ 15.
    for level in JLPT_LEVELS_HARD_TO_EASY:
        selected = _select_unique_candidates(
            by_level[level],
            TARGET_PER_LEVEL,
            recent_terms,
            selected_terms,
        )
        result.extend(selected)
        level_counts[level] = len(selected)

    _require_full_quotas(level_counts, nstar_source_counts)
    return result, level_counts, nstar_source_counts, excluded_by_recent_count


def main() -> None:
    now_japan = datetime.now(ZoneInfo("Asia/Tokyo"))
    single_kanji_blocklist = load_single_kanji_blocklist()
    recent_suggested_terms = load_recent_suggested_terms(now_japan)

    jlpt_levels = fetch_jlpt_levels()
    articles = fetch_google_news() + fetch_qiita()
    if not articles:
        raise RuntimeError("Không tải được dữ liệu từ bất kỳ nguồn nào.")

    items, level_counts, nstar_source_counts, excluded_by_recent_count = build_items(
        articles,
        jlpt_levels,
        set(recent_suggested_terms),
        single_kanji_blocklist,
    )

    payload = {
        "schemaVersion": 6,
        "generatedAt": now_japan.isoformat(),
        "generatedAtDisplay": now_japan.strftime("%d/%m · %H:%M"),
        "timezone": "Asia/Tokyo",
        "articleCount": len(articles),
        "quotaComplete": True,
        "selectionRule": "replace-48h-duplicates-with-next-ranked-candidate",
        "targetPerJlptLevel": TARGET_PER_LEVEL,
        "nStarTargets": {
            "news": NSTAR_NEWS_TARGET,
            "community": NSTAR_FORUM_TARGET,
        },
        "nStarSourceCounts": nstar_source_counts,
        "levelCounts": level_counts,
        "dedupeWindowHours": RECENT_DEDUPE_HOURS,
        "recentExcludedTermsCount": excluded_by_recent_count,
        "items": items,
    }

    OUTPUT_FILE.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT_FILE.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )
    write_recent_suggested_terms(recent_suggested_terms, items, now_japan)

    summary = ", ".join(
        f"{level}={level_counts[level]}" for level in OUTPUT_LEVELS_HARD_TO_EASY
    )
    print(
        f"Đã tạo {OUTPUT_FILE} ({summary}; "
        f"N* báo={nstar_source_counts['news']}, "
        f"Forum={nstar_source_counts['community']}; "
        f"loại do trùng 48h={excluded_by_recent_count}; "
        f"blocklist Kanji={len(single_kanji_blocklist)})."
    )


if __name__ == "__main__":
    main()
