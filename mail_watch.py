# -*- coding: utf-8 -*-
"""雇主来信监控：已投递的公司一来邮件，马上推送到手机。

设计成**单文件、只用标准库**，因为它要复制到一个独立的公开仓库里跑
（公开仓库的 Actions 不限分钟数；私有仓库每月只有 2,000 分钟）。
所以这里**不能有任何个人信息**：邮箱、仓库名、推送 key、看板地址
全部来自环境变量（GitHub Secrets），日志只打印数量，不打印主题/发件人。

流程（每小时一次）：
  1. 从私有仓库读 tracker/tracker.json，取出进度是 已投/面试/Offer/拒绝 的岗位
  2. 只读方式登录 Gmail（IMAP），看投递日前 2 天以来的邮件头；
     发件人/主题里出现这些雇主名（或来自招聘系统域名）的，再取正文确认
  3. 新来信 → 立即推送（任何时间）；写进 tracker.mail，看板上高亮
  4. 没在看板上看过的来信 → 只在 Edmonton 时间 18:00–22:59 用「持续响铃」
     再提醒，每封最多 3 次，每次间隔至少 50 分钟
"""
import base64
import email
import imaplib
import json
import os
import re
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from email.header import decode_header, make_header
from email.utils import parseaddr, parsedate_to_datetime

try:
    from zoneinfo import ZoneInfo
    LOCAL_TZ = ZoneInfo("America/Edmonton")
except Exception:                                    # noqa: BLE001
    LOCAL_TZ = timezone(timedelta(hours=-6))

APPLIED_STATUSES = ("applied", "interview", "offer", "rejected")
RING_START, RING_END = 18, 23          # 18:00 起（含），23:00 前
MAX_RINGS = 3
RING_GAP_MIN = 50
LOOKBACK_PAD_DAYS = 2                  # 投递确认信可能比「标为已投」早到
MAX_LOOKBACK_DAYS = 60

# 招聘系统（ATS）的发信域名：雇主名常常只出现在正文里
ATS_DOMAINS = ("successfactors", "myworkday", "workday.com", "greenhouse", "lever.co",
               "icims", "taleo", "smartrecruiters", "jobvite", "ashbyhq", "bamboohr",
               "ultipro", "ukg", "dayforce", "ceridian", "oraclecloud", "avature",
               "phenom", "eightfold", "hirevue", "brassring", "pageuppeople", "njoyn")
# 求职网站的订阅提醒 —— 里面满是雇主名，但不是雇主来信
ALERT_DOMAINS = ("linkedin.com", "indeed.com", "indeedemail.com", "jobbank.gc.ca",
                 "guichetemplois.gc.ca", "glassdoor", "ziprecruiter", "talent.com",
                 "workopolis", "eluta", "simplyhired")
_SUFFIX = re.compile(r"\b(inc|ltd|limited|llp|llc|corp|corporation|co|company|group|"
                     r"the|of|canada|canadian|and|&)\b\.?", re.I)
# 和投递有关的词：避免雇主名只是在新闻、广告里顺带出现
_JOBWORDS = re.compile(r"applica|applicant|candida|interview|position|requisition|"
                       r"role\b|recruit|hiring|talent|offer|assessment|opportunit|"
                       r"resume|résumé|career", re.I)

KINDS = [  # (kind, 中文, 关键词) —— 按顺序判断，先中先得
    ("offer", "Offer 🎉", re.compile(r"pleased to offer|offer of employment|offer letter|job offer", re.I)),
    ("reject", "未通过", re.compile(r"unfortunately|regret to|not (?:be )?mov(?:e|ing) forward|"
                                     r"other candidates|not been selected|were not selected|"
                                     r"decided not to|no longer under consideration|"
                                     r"position has been filled|will not be proceeding", re.I)),
    # 只认「请你来面试」这类说法：确认信里常有 interviewers、interview process 之类的套话
    ("interview", "面试 / 下一步 ✨", re.compile(
        r"invit(?:e|ing) you (?:to|for) (?:an? |the )?(?:\w+ )?(?:interview|call|conversation|meeting|assessment)|"
        r"(?:schedule|book|arrange) (?:an? |your )?(?:\w+ )?(?:interview|call|time|meeting)|"
        r"your availability|phone screen|video interview|interview (?:invitation|request)|"
        r"(?:complete|take) (?:an? |the |our )?(?:online )?assessment|"
        r"move(?:d)? (?:you )?forward to the next (?:step|stage|round)|"
        # Hatch 等公司的后续环节：在线测评邀请、按需视频面试（常限 48 小时）、推荐人核查（Xref 等）
        r"(?:invit\w*|invitation) (?:you )?to (?:complete|take)|on-demand video|one-way video|hirevue|"
        r"(?:submit|provide) (?:your |the names of )?(?:professional )?references|reference check|xref", re.I)),
    ("receipt", "已收到申请", re.compile(r"received your application|thank you for (?:applying|your "
                                          r"application|your interest)|application (?:has been|was) "
                                          r"(?:received|submitted)|successfully submitted", re.I)),
]
KIND_ZH = {k: zh for k, zh, _ in KINDS}
KIND_ZH["other"] = "新消息"

_TIMELINE = re.compile(
    r"[^.!?\n]*\b(?:within|in the next|over the (?:next|coming)|in (?:about|approximately))\s+"
    r"(?:\d+|one|two|three|four|five|six|a few|several|a couple of)"
    r"(?:\s*(?:-|to|–)\s*(?:\d+|two|three|four|five|six))?\s*(?:business\s+)?(?:days|weeks|months)"
    r"[^.!?\n]*[.!?]?", re.I)


# ── 纯逻辑（有单元测试）──────────────────────────────────
def norm(text):
    return re.sub(r"[^a-z0-9]+", " ", (text or "").lower()).strip()


def employer_keys(name):
    """「Hatch Ltd.」→ ['hatch']；「University of Alberta」→ ['university alberta']。"""
    full = norm(_SUFFIX.sub(" ", name or ""))
    full = re.sub(r"\s+", " ", full).strip()
    return [full] if len(full) >= 3 else []


def targets(tracker, now=None):
    """已投递的岗位 → [{uid, employer, title, keys, since}]"""
    now = now or datetime.now(timezone.utc)
    out = []
    for uid, it in (tracker.get("items") or {}).items():
        if it.get("status") not in APPLIED_STATUSES or not it.get("employer"):
            continue
        keys = employer_keys(it["employer"])
        if not keys:
            continue
        since = _parse_iso(it.get("applied_at") or it.get("_t")) or (now - timedelta(days=30))
        since = max(since - timedelta(days=LOOKBACK_PAD_DAYS), now - timedelta(days=MAX_LOOKBACK_DAYS))
        out.append({"uid": uid, "employer": it["employer"], "title": it.get("title", ""),
                    "keys": keys, "since": since})
    return out


def _has(key, text):
    # 文本也去掉 of/inc/ltd 之类，和 employer_keys 的处理一致
    text = re.sub(r"\s+", " ", norm(_SUFFIX.sub(" ", text or "")))
    return bool(key) and (" %s " % key) in (" %s " % text)


def is_alert_sender(addr):
    dom = (addr or "").lower().rsplit("@", 1)[-1]
    return any(d in dom for d in ALERT_DOMAINS)


def is_ats_sender(addr):
    dom = (addr or "").lower().rsplit("@", 1)[-1]
    return any(d in dom for d in ATS_DOMAINS)


def header_candidates(msg, tlist):
    """只看邮件头就能初筛：发件人/主题提到雇主，或来自招聘系统。返回可能相关的 target。"""
    name, addr = parseaddr(msg.get("from", ""))
    if is_alert_sender(addr) or msg.get("list_id"):
        return []
    head = "%s %s %s" % (name, addr.replace("@", " ").replace(".", " "), msg.get("subject", ""))
    hits = [t for t in tlist if any(_has(k, head) for k in t["keys"])]
    if hits:
        return hits
    return list(tlist) if is_ats_sender(addr) else []


def match(msg, tlist):
    """完整判断：返回匹配到的 target，或 None。msg: from/subject/body/date(aware)/list_id"""
    cands = header_candidates(msg, tlist)
    if not cands:
        return None
    name, addr = parseaddr(msg.get("from", ""))
    head = "%s %s %s" % (name, addr.replace("@", " ").replace(".", " "), msg.get("subject", ""))
    text = head + " " + msg.get("body", "")
    if not _JOBWORDS.search(msg.get("subject", "") + " " + msg.get("body", "")):
        return None
    date = msg.get("date")
    for t in cands:
        if date and date < t["since"]:
            continue
        if any(_has(k, head) for k in t["keys"]) or \
                (is_ats_sender(addr) and any(_has(k, text) for k in t["keys"])):
            return t
    return None


def classify(subject, body):
    text = "%s\n%s" % (subject or "", body or "")
    for kind, _zh, rx in KINDS:
        if rx.search(text):
            return kind
    return "other"


def timeline_hint(body):
    m = _TIMELINE.search(body or "")
    return re.sub(r"\s+", " ", m.group(0)).strip()[:200] if m else ""


def watches(tracker, now=None):
    """tracker["watches"]：非雇主、但要第一时间知道的发件人（如账号审核结果）。

    每条 {id, label, since, rules: [{from: 地址片段, name: 发件人名正则(可选)}]}
    """
    now = now or datetime.now(timezone.utc)
    out = []
    for w in tracker.get("watches") or []:
        if not w.get("id") or not w.get("rules") or w.get("off"):
            continue
        since = _parse_iso(w.get("since")) or (now - timedelta(days=7))
        out.append(dict(w, since=since))
    return out


def watch_match(msg, wlist):
    name, addr = parseaddr(msg.get("from", ""))
    addr = addr.lower()
    date = msg.get("date")
    for w in wlist:
        if date and date < w["since"]:
            continue
        for r in w["rules"]:
            if r.get("from") and r["from"].lower() in addr and \
                    (not r.get("name") or re.search(r["name"], name or "", re.I)):
                return w
    return None


def should_ring(entry, now_utc):
    """没看过的来信，在晚上 18:00–22:59 用持续响铃再提醒。"""
    if str(entry.get("uid", "")).startswith("watch:"):
        return False          # 关注的发件人只推一次，不长响
    if entry.get("seen_at") or entry.get("ignored"):
        return False
    rings = entry.get("rings") or []
    if len(rings) >= MAX_RINGS:
        return False
    local = now_utc.astimezone(LOCAL_TZ)
    if not (RING_START <= local.hour < RING_END):
        return False
    last = _parse_iso(rings[-1]) if rings else _parse_iso(entry.get("pushed_at"))
    return not last or (now_utc - last) >= timedelta(minutes=RING_GAP_MIN)


def _parse_iso(s):
    if not s:
        return None
    try:
        d = datetime.fromisoformat(str(s).replace("Z", "+00:00"))
        return d if d.tzinfo else d.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def iso(d):
    return d.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ── IMAP ────────────────────────────────────────────────
def _dec(v):
    try:
        return str(make_header(decode_header(v or "")))
    except Exception:                                # noqa: BLE001
        return str(v or "")


def _body_text(m):
    html_part = plain = ""
    for part in (m.walk() if m.is_multipart() else [m]):
        ct = part.get_content_type()
        if ct not in ("text/plain", "text/html"):
            continue
        try:
            txt = (part.get_payload(decode=True) or b"").decode(part.get_content_charset() or "utf-8",
                                                               errors="replace")
        except (LookupError, ValueError):
            continue
        if ct == "text/plain" and not plain:
            plain = txt
        elif ct == "text/html" and not html_part:
            html_part = txt
    if plain.strip():
        return plain
    txt = re.sub(r"(?is)<(script|style).*?</\1>", " ", html_part)
    txt = re.sub(r"<[^>]+>", " ", txt)
    import html as _h
    return re.sub(r"[ \t\r\f\v]+", " ", _h.unescape(txt))


def fetch(user, password, since, own_addrs):
    """只读登录，返回 (conn, [{id, from, subject, date, list_id, body=None}])。"""
    conn = imaplib.IMAP4_SSL("imap.gmail.com", 993)
    out = []
    try:
        conn.login(user, password)
        for folder in ("INBOX", "[Gmail]/Spam"):
            typ, _ = conn.select('"%s"' % folder, readonly=True)
            if typ != "OK":
                continue
            typ, data = conn.search(None, "SINCE", since.strftime("%d-%b-%Y"))
            ids = (data[0] or b"").split() if typ == "OK" else []
            for num in ids[-800:]:
                typ, hd = conn.fetch(num, "(BODY.PEEK[HEADER.FIELDS (FROM SUBJECT DATE MESSAGE-ID LIST-ID)])")
                if typ != "OK" or not hd or not isinstance(hd[0], tuple):
                    continue
                h = email.message_from_bytes(hd[0][1])
                frm = _dec(h.get("From"))
                if parseaddr(frm)[1].lower() in own_addrs:
                    continue
                try:
                    date = parsedate_to_datetime(h.get("Date"))
                    date = date if date.tzinfo else date.replace(tzinfo=timezone.utc)
                except Exception:                    # noqa: BLE001
                    date = None
                out.append({"num": num, "folder": folder, "id": (h.get("Message-ID") or "").strip()
                            or "%s-%s" % (folder, num.decode()), "from": frm,
                            "subject": _dec(h.get("Subject")), "date": date,
                            "list_id": bool(h.get("List-Id")), "body": None})
        return conn, out        # 正文由 fetch_body 按需取（只取初筛命中的）
    except Exception:
        try:
            conn.logout()
        except Exception:                            # noqa: BLE001
            pass
        raise


def fetch_body(conn, msg):
    conn.select('"%s"' % msg["folder"], readonly=True)
    typ, data = conn.fetch(msg["num"], "(BODY.PEEK[])")
    if typ != "OK" or not data or not isinstance(data[0], tuple):
        return ""
    return _body_text(email.message_from_bytes(data[0][1]))[:20000]


# ── GitHub tracker ──────────────────────────────────────
def _gh(method, url, token, body=None):
    req = urllib.request.Request(url, method=method, data=json.dumps(body).encode() if body else None,
                                 headers={"Authorization": "Bearer " + token,
                                          "Accept": "application/vnd.github+json",
                                          "User-Agent": "mail-watch"})
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.loads(r.read().decode())


def get_tracker(repo, token):
    url = "https://api.github.com/repos/%s/contents/tracker/tracker.json" % repo
    try:
        body = _gh("GET", url, token)
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return {"items": {}}, None
        raise
    return json.loads(base64.b64decode(body["content"]).decode("utf-8")), body["sha"]


def put_tracker(repo, token, data, sha, message):
    url = "https://api.github.com/repos/%s/contents/tracker/tracker.json" % repo
    payload = {"message": message, "content": base64.b64encode(
        json.dumps(data, ensure_ascii=False, indent=1).encode("utf-8")).decode("ascii")}
    if sha:
        payload["sha"] = sha
    return _gh("PUT", url, token, payload)


def apply_updates(tracker, new_entries, ring_ids, pushed, now):
    """把本轮结果合并进（可能刚被看板改过的）tracker。只动 mail，不碰 items。"""
    mail = tracker.setdefault("mail", {})
    for key, entry in new_entries.items():
        if key not in mail:
            mail[key] = entry
    for key in ring_ids:
        if key in mail and not mail[key].get("seen_at"):
            mail[key].setdefault("rings", []).append(iso(now))
    for key in pushed:
        if key in mail:
            mail[key]["pushed_at"] = mail[key].get("pushed_at") or iso(now)
    return tracker


# ── 推送 ────────────────────────────────────────────────
def bark(key, title, body, url, call=False):
    payload = {"title": title, "body": body, "group": "雇主来信", "level": "timeSensitive",
               "isArchive": "1", "sound": "multiwayinvitation" if call else "bell"}
    if call:
        payload["call"] = "1"
    if url:
        payload["url"] = url
    req = urllib.request.Request("https://api.day.app/" + key, data=json.dumps(payload).encode(),
                                 headers={"Content-Type": "application/json"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=20) as r:
            return r.status == 200
    except Exception:                                # noqa: BLE001
        return False        # 不打印异常：异常信息里带着含 key 的 URL


_GREETING = re.compile(r"^\s*(?:dear|hi|hello|hey|good (?:morning|afternoon|day))\s+[^,:\n]{1,40}[,:]\s*", re.I)


def scrub(text, names):
    """存进 tracker 之前去掉称呼和本人姓名：记录里只需要雇主说了什么，不需要叫你什么。"""
    text = _GREETING.sub("", text or "")
    for n in names:
        if len(n) >= 2:
            text = re.sub(r"\b%s\b" % re.escape(n), "你", text, flags=re.I)
    return text


def entry_key(msg_id):
    return "m" + base64.urlsafe_b64encode(msg_id.encode()).decode().rstrip("=")[-40:]


def main():
    env = os.environ.get
    user, password = env("RADAR_EMAIL_USER", ""), "".join((env("RADAR_EMAIL_PASSWORD") or "").split())
    token, repo, bark_key = env("RADAR_TRACKER_TOKEN", ""), env("RADAR_TRACKER_REPO", ""), env("BARK_DEVICE_KEY", "")
    board = env("RADAR_BOARD_URL", "")
    own = {a.strip().lower() for a in (env("RADAR_OWN_ADDRS", "") + "," + user).split(",") if a.strip()}
    names = [n.strip() for n in env("RADAR_REDACT_NAMES", "").split(",") if n.strip()]
    missing = [n for n, v in (("RADAR_EMAIL_USER", user), ("RADAR_EMAIL_PASSWORD", password),
                              ("RADAR_TRACKER_TOKEN", token), ("RADAR_TRACKER_REPO", repo),
                              ("BARK_DEVICE_KEY", bark_key)) if not v]
    if missing:
        print("缺少配置：%s" % ", ".join(missing))
        return 1
    now = datetime.now(timezone.utc)
    tracker, _sha = get_tracker(repo, token)
    tlist = targets(tracker, now)
    wlist = watches(tracker, now)
    known = tracker.get("mail") or {}
    new_entries, pushed = {}, []
    if tlist or wlist:
        since = min([t["since"] for t in tlist] + [w["since"] for w in wlist])
        conn, msgs = fetch(user, password, since, own)
        try:
            for msg in msgs:
                key = entry_key(msg["id"])
                if key in known:
                    continue
                w = watch_match(msg, wlist)
                if w:
                    new_entries[key] = {"uid": "watch:" + w["id"], "employer": w.get("label") or w["id"],
                                        "title": "", "msgid": msg["id"][:300], "from": msg["from"][:120],
                                        "subject": scrub(msg["subject"], names)[:200],
                                        "date": iso(msg["date"]) if msg["date"] else iso(now),
                                        "kind": "other", "snippet": "", "timeline": "",
                                        "folder": "垃圾邮件" if "Spam" in msg["folder"] else "",
                                        "found_at": iso(now)}
                    continue
                if not tlist or not header_candidates(msg, tlist):
                    continue
                msg["body"] = fetch_body(conn, msg)
                t = match(msg, tlist)
                if not t:
                    continue
                kind = classify(msg["subject"], msg["body"])
                snippet = scrub(re.sub(r"\s+", " ", msg["body"]).strip(), names)[:400]
                new_entries[key] = {"uid": t["uid"], "employer": t["employer"], "title": t["title"],
                                    "msgid": msg["id"][:300],      # 看板用它跳到邮箱里的原信
                                    "from": msg["from"][:120], "subject": scrub(msg["subject"], names)[:200],
                                    "date": iso(msg["date"]) if msg["date"] else iso(now),
                                    "kind": kind, "snippet": snippet,
                                    "timeline": scrub(timeline_hint(msg["body"]), names),
                                    "folder": "垃圾邮件" if "Spam" in msg["folder"] else "",
                                    "found_at": iso(now)}
        finally:
            try:
                conn.logout()
            except Exception:                        # noqa: BLE001
                pass
    link = board + ("#applied" if board else "")
    for key, e in new_entries.items():
        where = "（在垃圾邮件里！）" if e["folder"] else ""
        if e["uid"].startswith("watch:"):
            if bark(bark_key, "📮 %s 有新邮件" % e["employer"], "%s%s\n去邮箱查看" % (e["subject"], where), ""):
                pushed.append(key)
            continue
        if bark(bark_key, "📬 %s 来信 · %s" % (e["employer"], KIND_ZH[e["kind"]]),
                "%s%s\n点开看板「已投递」查看" % (e["subject"], where), link):
            pushed.append(key)
    ring_ids = []
    for key, e in known.items():
        if should_ring(e, now):
            if bark(bark_key, "🔔 还没看：%s 的来信" % e.get("employer", ""),
                    "%s\n点开这条就不会再响" % e.get("subject", ""), link, call=True):
                ring_ids.append(key)
    if new_entries or ring_ids:
        for attempt in range(4):
            data, sha = get_tracker(repo, token)
            apply_updates(data, new_entries, ring_ids, pushed, now)
            try:
                put_tracker(repo, token, data, sha, "来信监控：%d 封新来信，%d 次响铃" % (len(new_entries), len(ring_ids)))
                break
            except urllib.error.HTTPError as e:
                if e.code not in (409, 422) or attempt == 3:
                    raise
                time.sleep(2)
    print("已投递 %d 家；新来信 %d 封；响铃 %d 次" % (len(tlist), len(new_entries), len(ring_ids)))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:                         # noqa: BLE001
        # 公开仓库的日志谁都能看：只报异常类型，不带任何内容
        print("运行失败：%s" % type(exc).__name__)
        sys.exit(1)
