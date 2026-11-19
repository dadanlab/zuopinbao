#!/usr/bin/env python3
"""把 portfolio.json 填进作品堡页面模板，一次生成两个版本。

用法：
  python3 build.py --data portfolio.json --out 输出目录
  python3 build.py --data portfolio.json --check     # 只检查，不生成

生成：
  <网站名>-自己看.html   系统版：亮卡、没亮的卡、小任务都在，能切到 HR 版预览
  <网站名>-发给HR.html   只放亮着的卡，没有系统任务、没有出处，也切不回系统版；发布、发给 HR 用这一份

只用 Python 标准库就能跑。截图写本地路径（相对 portfolio.json 所在文件夹）会被转成内嵌图片，
放在页面最后（页面先能用，图后到）；同一张图只存一份；长边超过 2000 像素的，电脑上有 PIL 或者是 Mac
就自动缩小，都没有就先读图片尺寸，真超过了才提醒。
「几家要」只认每张卡的 need（阿拉伯数字，不超过实际读到的 jdCount 家），排序用的 weight 不拿来顶。生成的页面是单个文件，断网也能打开；设备显示不了 3D 时，页面自己换成一页版。
风格（style）四套里选一套：晨雾紫 / 奶油杏 / 薄荷绿 / 海盐蓝，写中文名或英文名都行，没写就是晨雾紫。
"""
import argparse
import base64
import copy
import hashlib
import html
import io
import json
import mimetypes
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile

STATES = {"lit", "unclear", "weak", "todo"}
ICONS = {"copy", "data", "book", "content", "talk", "cap", "event", "ai"}
BACKGROUND = "个人背景"
RESOURCE = "个人资源"
MAX_REGIONS = 6
SOFT_MAX_CARDS = 4
HARD_MAX_CARDS = 6
MAX_HIGHLIGHTS = 4
TOP_N = 3
SHORT_MAX = 14
MAX_SIDE = 2000
IMG_WARN_BYTES = int(0.6 * 1024 * 1024)
TOTAL_WARN_BYTES = 4 * 1024 * 1024
DATA_TAG = re.compile(r'(<script id="portfolio-data" type="application/json">)(.*?)(</script>)', re.S)
IMG_TAG = re.compile(r'(<script id="portfolio-images" type="application/json">)(.*?)(</script>)', re.S)
# 还没填的占位：【待补】【待她给】【……】
PLACEHOLDER = re.compile(r"【(待[^】]*|…+|\.{3,})】")
# 四套风格：只能选，不能自己调色（区域颜色也跟着风格走）
STYLES = {"mist": "晨雾紫", "apricot": "奶油杏", "mint": "薄荷绿", "sea": "海盐蓝"}
# 手机号、微信号的样子（wx / vx 前后不能紧挨着字母，免得把 wxlin@ 这种邮箱当成微信号）
PHONE_LIKE = re.compile(r"(?<!\d)1\d{10}(?!\d)|微信|(?<![a-z])(?:wechat|vx|wx)(?![a-z])", re.I)
# 示例数据里那句脚注，用户自己的数据里不该出现
EXAMPLE_NOTE = re.compile(r"示例数据|都是编的")


def fail(msg):
    print("✗ " + msg)
    sys.exit(1)


def num(v):
    try:
        return float(v)
    except (TypeError, ValueError):
        return 0.0


def img_side(raw):
    """不靠 PIL 也读出 PNG / JPEG / GIF / WebP 的长边（读不出来返回 None）。"""
    try:
        if raw[:8] == b"\x89PNG\r\n\x1a\n":
            return max(struct.unpack(">II", raw[16:24]))
        if raw[:6] in (b"GIF87a", b"GIF89a"):
            return max(struct.unpack("<HH", raw[6:10]))
        if raw[:4] == b"RIFF" and raw[8:12] == b"WEBP":
            k = raw[12:16]
            if k == b"VP8X":
                return 1 + max(int.from_bytes(raw[24:27], "little"), int.from_bytes(raw[27:30], "little"))
            if k == b"VP8 ":
                return max(v & 0x3FFF for v in struct.unpack("<HH", raw[26:30]))
            if k == b"VP8L":
                b = int.from_bytes(raw[21:25], "little")
                return 1 + max(b & 0x3FFF, (b >> 14) & 0x3FFF)
        if raw[:2] == b"\xff\xd8":
            i = 2
            while i + 9 < len(raw):
                if raw[i] != 0xFF:
                    i += 1
                    continue
                m = raw[i + 1]
                if m in (0xC0, 0xC1, 0xC2, 0xC3, 0xC5, 0xC6, 0xC7, 0xC9, 0xCA, 0xCB, 0xCD, 0xCE, 0xCF):
                    return max(struct.unpack(">HH", raw[i + 5:i + 9]))
                i += 2 if (m in (0xD8, 0x01, 0xFF) or 0xD0 <= m <= 0xD7) else 2 + struct.unpack(">H", raw[i + 2:i + 4])[0]
    except Exception:
        return None
    return None


def shrink(full, warns, note):
    """读图片；长边超过 2000 像素的缩小：有 PIL 用 PIL，Mac 上用自带的 sips，都没有就提醒一次。"""
    with open(full, "rb") as f:
        raw = f.read()
    try:
        from PIL import Image  # 可选，装了就用
        im = Image.open(io.BytesIO(raw))
        if max(im.size) <= MAX_SIDE:
            return raw
        fmt = im.format or "PNG"
        im.thumbnail((MAX_SIDE, MAX_SIDE))
        buf = io.BytesIO()
        im.save(buf, format=fmt, **({"quality": 85, "optimize": True} if fmt == "JPEG" else {"optimize": True}))
        return buf.getvalue()
    except ImportError:
        pass
    except Exception:
        return raw
    if shutil.which("sips"):
        try:
            info = subprocess.run(["sips", "-g", "pixelWidth", "-g", "pixelHeight", full], capture_output=True, text=True).stdout
            side = max(int(x) for x in re.findall(r"pixel(?:Width|Height):\s*(\d+)", info))
            if side <= MAX_SIDE:
                return raw
            with tempfile.TemporaryDirectory() as d:
                out = os.path.join(d, os.path.basename(full))
                subprocess.run(["sips", "-Z", str(MAX_SIDE), full, "--out", out], capture_output=True, check=True)
                with open(out, "rb") as f:
                    return f.read()
        except Exception:
            return raw
    side = img_side(raw)
    if side is not None and side <= MAX_SIDE:
        return raw
    if not note[0]:
        note[0] = True
        warns.append("有截图长边超过 %d 像素没法自动缩（这台电脑没有 PIL，也不是 Mac），页面会偏大" % MAX_SIDE)
    return raw


class Images:
    """截图都收进一个表，同一张图只存一份；卡里只写「#i0」这种编号。"""

    def __init__(self, base_dir, warns):
        self.base_dir, self.warns, self.map, self.ids, self.total, self.note = base_dir, warns, {}, {}, 0, [False]

    def add(self, path, keep=True):
        if not isinstance(path, str) or not path.strip():
            return None
        p = path.strip()
        if re.match(r"^https?://", p, re.I):
            return p
        if p.startswith("data:image/"):
            uri = p
        else:
            full = p if os.path.isabs(p) else os.path.join(self.base_dir, p)
            if not os.path.isfile(full):
                self.warns.append("找不到截图：" + p + "（已跳过）")
                return None
            mime = mimetypes.guess_type(full)[0] or "image/png"
            if not mime.startswith("image/"):
                self.warns.append("不是图片：" + p + "（已跳过）")
                return None
            raw = shrink(full, self.warns, self.note)
            if len(raw) > IMG_WARN_BYTES:
                self.warns.append("截图偏大（%.1f MB）：%s，建议压到 0.6 MB 以内" % (len(raw) / 1048576, p))
            uri = "data:%s;base64,%s" % (mime, base64.b64encode(raw).decode("ascii"))
        if not keep:
            return uri
        key = hashlib.sha1(uri.encode("ascii", "ignore")).hexdigest()
        if key not in self.ids:
            self.ids[key] = "i%d" % len(self.map)
            self.map[self.ids[key]] = uri
            self.total += len(uri) * 3 // 4
        return "#" + self.ids[key]


def clean_links(items, warns):
    """链接只收 http(s) 开头的。"""
    links = []
    for l in items or []:
        if not isinstance(l, dict):
            warns.append("链接要写成 {\"label\": …, \"url\": …}，已跳过：" + str(l))
            continue
        url = str(l.get("url", "")).strip()
        if re.match(r"^https?://", url, re.I):
            links.append({"label": str(l.get("label", "")).strip() or "打开链接", "url": url})
        elif url:
            warns.append("链接不是 http(s) 开头，已跳过：" + url)
    return links


def pick_top(data, warns):
    """最高光三条：用户挑的卡名优先；没挑或不够三条，按「几家要」补齐（个人资源、个人背景是用户自己带来的，排后面）。"""
    lit = []
    for ri, r in enumerate(data["regions"]):
        for ci, c in enumerate(r.get("cards") or []):
            if c.get("state") == "lit" and not c.get("fact"):
                lit.append((r["name"] in (RESOURCE, BACKGROUND), -num(c.get("need", c.get("weight"))), ri, ci, c["name"]))
    names = [x[4] for x in lit]
    given = data.get("top")
    if given is not None and not isinstance(given, list):
        warns.append("top 要写成卡名的列表，比如 [\"卡A\", \"卡B\", \"卡C\"]，已忽略")
        given = []
    top = []
    for n in given or []:
        n = str(n).strip()
        if n in top:
            continue
        if n not in names:
            warns.append("最高光里的「%s」不是亮卡，或者名字对不上，已跳过" % n)
            continue
        if len(top) < TOP_N:
            top.append(n)
    auto = []
    for x in sorted(lit):
        if len(top) >= TOP_N:
            break
        if x[4] not in top:
            top.append(x[4])
            auto.append(x[4])
    data["top"] = top
    for r in data["regions"]:
        for c in r.get("cards") or []:
            h = (c.get("highlights") or [{}])[0]
            if c["name"] in top and not h.get("short") and len(str(h.get("result", ""))) > SHORT_MAX:
                warns.append("「%s」是最高光，但没写短版（short），首屏和逛一圈会显示完整结果" % c["name"])
    return auto


def placeholders(data):
    """还没填的【待…】【……】：生成前要换成用户自己的话。"""
    hits = []

    def look(where, s):
        for m in PLACEHOLDER.finditer(str(s or "")):
            hits.append("%s：%s" % (where, m.group(0)))
    look("一句话介绍", data.get("tagline"))
    look("自我介绍", data.get("about"))
    look("联系方式", data.get("contact"))
    for l in data.get("links") or []:
        look("个人链接", l.get("label"))
    for r in data["regions"]:
        for c in r.get("cards") or []:
            for h in c.get("highlights") or []:
                for k in ("project", "step", "did", "result", "short"):
                    look("%s · %s" % (r["name"], c.get("name")), h.get(k))
    return hits


def normalize(data, base_dir):
    warns = []
    imgs = Images(base_dir, warns)
    if not isinstance(data, dict):
        fail("portfolio.json 最外层要是一个对象 {}")
    if not str(data.get("role", "")).strip():
        fail("缺少 role（目标岗位）")
    if not str(data.get("site", "")).strip():
        # 采访第 4 题「先生成一版看看」时还没起名字：先用通用的名字生成，第 9 题起好名字再生成一次
        data["site"] = "个人作品堡"
        warns.append("还没起网站名（site），先用「个人作品堡」生成；第 9 题起好名字再生成一次")
    for key in ("tagline", "about", "contact"):
        if key in data:
            data[key] = str(data.get(key) or "").strip()
    if not data.get("tagline"):
        warns.append("没写一句话介绍（tagline），首屏只会显示目标岗位；采访第 9 题拟好给用户确认")
    if data.get("contact") and PHONE_LIKE.search(data["contact"]):
        warns.append("联系方式像是手机号或微信号：链接谁都能打开，建议只放邮箱")
    if "jdCount" in data:
        n = int(num(data["jdCount"]))
        if 1 <= n <= 50:
            data["jdCount"] = n
        else:
            warns.append("jdCount（扒到几家）要写 1 到 50 的数，已忽略：%s" % data["jdCount"])
            data.pop("jdCount")
    data["links"] = clean_links(data.get("links"), warns)
    if EXAMPLE_NOTE.search(str(data.get("footnote") or "")):
        warns.append("左下角那行小字（footnote）是「%s」：示例数据才这么写；给用户做的，换成用户自己的话，或者不写（不写就显示「个人作品堡 · 用 AI 做的」）" % data["footnote"])
    st = str(data.get("style") or "").strip()
    key = next((k for k, v in STYLES.items() if st.lower() in (k, v)), None)
    if st and not key:
        warns.append("风格不认识：%s，改用晨雾紫（只能选：%s）" % (st, "、".join(STYLES.values())))
    data["style"] = key or "mist"
    regions = data.get("regions")
    if not isinstance(regions, list) or not regions:
        fail("regions 不能为空")
    if len(regions) > MAX_REGIONS:
        fail("区域最多 %d 个，现在有 %d 个" % (MAX_REGIONS, len(regions)))
    if len(regions) < MAX_REGIONS:
        warns.append("区域只有 %d 个，页面会空出 %d 个位置（HR 版里看不到空位）" % (len(regions), MAX_REGIONS - len(regions)))
    # 个人背景放最后：劣势放后面，跟简历一样
    bg = [r for r in regions if r.get("name") == BACKGROUND]
    regions = [r for r in regions if r.get("name") != BACKGROUND] + bg
    for ri, r in enumerate(regions):
        name = str(r.get("name", "")).strip() or "区域%d" % (ri + 1)
        r["name"] = name
        if r.get("icon") and r["icon"] not in ICONS:
            warns.append("「%s」的 icon 不认识：%s，改用默认" % (name, r["icon"]))
            r.pop("icon")
        if "color" in r:
            warns.append("「%s」写了颜色，已忽略：颜色跟着风格走，不能单独改" % name)
            r.pop("color")
        cards = r.get("cards") or []
        if len(cards) > HARD_MAX_CARDS:
            fail("「%s」有 %d 张卡，最多 %d 张" % (name, len(cards), HARD_MAX_CARDS))
        if len(cards) > SOFT_MAX_CARDS:
            warns.append("「%s」有 %d 张卡，建议每个区域不超过 %d 张，问起来不累" % (name, len(cards), SOFT_MAX_CARDS))
        for c in cards:
            cname = str(c.get("name", "")).strip()
            if not cname:
                fail("「%s」里有一张卡没写名字" % name)
            c["name"] = cname
            st = c.get("state", "todo")
            if st not in STATES:
                fail("「%s · %s」的 state 只能是 lit / unclear / weak / todo" % (name, cname))
            # 「几家要」单独记在 need，跟排序用的 weight 分开；只认阿拉伯数字，不能比实际读到的家数还多
            if "need" in c:
                v = str(c.pop("need")).strip()
                n = int(float(v)) if re.fullmatch(r"\d+(\.0+)?", v, re.ASCII) else None
                if name in (RESOURCE, BACKGROUND):
                    warns.append("「%s · %s」是用户自己带来的卡，不标几家要，need 已忽略" % (name, cname))
                elif n is None:
                    warns.append("「%s · %s」的 need（几家要）要写阿拉伯数字，已忽略：%s" % (name, cname, v))
                elif data.get("jdCount") and n > data["jdCount"]:
                    warns.append("「%s · %s」的 need 是 %d，比实际读到的 %d 家还多，已忽略" % (name, cname, n, data["jdCount"]))
                else:
                    c["need"] = n
            if name == BACKGROUND:
                c["fact"] = True  # 个人背景区的卡只写事实（学历、证书），不当高光
            # 一张卡最多 4 件事：highlight 写一件，highlights 写好几件（最亮的放第一）
            hs = c.get("highlights") if isinstance(c.get("highlights"), list) else ([c["highlight"]] if c.get("highlight") else [])
            hs = [h for h in hs if isinstance(h, dict)]
            if str(c.get("short", "")).strip():
                if hs and not str(hs[0].get("short", "")).strip():
                    hs[0]["short"] = c["short"]
                    warns.append("「%s · %s」的短版写在卡上了，已挪到最亮的那件事里（short 写在 highlight 里）" % (name, cname))
                c.pop("short")
            if len(hs) > MAX_HIGHLIGHTS:
                warns.append("「%s · %s」有 %d 件事，只放前 %d 件（最亮的放前面）" % (name, cname, len(hs), MAX_HIGHLIGHTS))
                hs = hs[:MAX_HIGHLIGHTS]
            if st == "lit":
                if not hs or not (str(hs[0].get("did", "")).strip() or str(hs[0].get("result", "")).strip()):
                    fail("「%s · %s」是亮卡，但没有写做了什么、结果是什么" % (name, cname))
                for k, h in enumerate(hs):
                    if not str(h.get("source", "")).strip():
                        warns.append("「%s · %s」%s没写出处（用户原话 / 截图 / 链接），HR 问起来要答得上" % (name, cname, "第 %d 件" % (k + 1) if len(hs) > 1 else ""))
            if st == "todo" and not str(c.get("task", "")).strip():
                warns.append("「%s · %s」没亮，也没写小任务" % (name, cname))
            for h in hs:
                short = str(h.get("short", "")).strip()
                if short:
                    h["short"] = short
                    if len(re.sub(r"\s", "", short)) > SHORT_MAX:
                        warns.append("「%s · %s」的短版超过 %d 个字：%s" % (name, cname, SHORT_MAX, short))
                else:
                    h.pop("short", None)
                h["shots"] = [s for s in (imgs.add(x) for x in (h.get("shots") or [])) if s]
                h["links"] = clean_links(h.get("links"), warns)
            c.pop("highlight", None)
            if hs:
                c["highlights"] = hs
            else:
                c.pop("highlights", None)
    data["regions"] = regions
    if data.get("jdCount"):
        miss = [c["name"] for r in regions if r["name"] not in (RESOURCE, BACKGROUND) for c in r.get("cards") or [] if "need" not in c]
        if miss:
            warns.append("这几张卡没写 need（几家要），页面上就不标几家要：" + "、".join(miss))
    if data.get("avatar"):
        data["avatar"] = imgs.add(data["avatar"], keep=False) or ""
    if imgs.total > TOTAL_WARN_BYTES:
        warns.append("截图加起来 %.1f MB，页面会比较大，手机打开会慢；挑最能说明问题的放" % (imgs.total / 1048576))
    auto = pick_top(data, warns)
    return data, warns, auto, imgs


def hr_version(data):
    """发给 HR 的版本：只留亮卡，拿掉任务、备注、高光值和出处（出处是给本人核对「AI 没编」用的）。"""
    d = copy.deepcopy(data)
    d["audience"] = "hr"
    d["points"] = 0
    d.pop("aboutSource", None)
    for r in d["regions"]:
        r["cards"] = [c for c in r.get("cards") or [] if c.get("state") == "lit"]
        for c in r["cards"]:
            c.pop("task", None)
            c.pop("taskPoints", None)
            c.pop("note", None)
            for h in c.get("highlights") or []:
                h.pop("source", None)
    d["regions"] = [r for r in d["regions"] if r["cards"]]
    return d


def used_images(d, imgs):
    ids = set()
    for r in d["regions"]:
        for c in r.get("cards") or []:
            for h in c.get("highlights") or []:
                ids.update(s[1:] for s in h.get("shots") or [] if s.startswith("#i"))
    return {k: v for k, v in imgs.map.items() if k in ids}


def fill(template, data, images):
    if not DATA_TAG.search(template) or not IMG_TAG.search(template):
        fail("模板里找不到 portfolio-data / portfolio-images 那段，模板文件可能被改坏了")
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    out = DATA_TAG.sub(lambda m: m.group(1) + payload + m.group(3), template, count=1)
    out = IMG_TAG.sub(lambda m: m.group(1) + json.dumps(images).replace("</", "<\\/") + m.group(3), out, count=1)
    # 链接发到微信、Boss 直聘时显示的标题和简介，生成时就写好（预览卡片不会跑页面里的代码）
    title = html.escape("%s｜%s" % (data["site"], data["role"]))
    desc = html.escape(PLACEHOLDER.sub("", data.get("tagline") or "") or "目标岗位：" + data["role"])
    out = out.replace("<title>个人作品堡</title>", "<title>%s</title>" % title, 1)
    out = out.replace('<meta property="og:title" content="个人作品堡">', '<meta property="og:title" content="%s">' % title, 1)
    out = out.replace('content="个人作品堡：照目标岗位整理的个人作品集"', 'content="%s"' % desc)
    return out


def safe_name(s):
    return re.sub(r'[\\/:*?"<>|\s]+', "", s) or "作品堡"


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser(description="生成个人作品堡页面")
    ap.add_argument("--data", required=True, help="portfolio.json 路径")
    ap.add_argument("--out", help="输出文件夹")
    ap.add_argument("--template", default=os.path.join(here, "..", "assets", "template.html"))
    ap.add_argument("--check", action="store_true", help="只检查数据，不生成")
    a = ap.parse_args()

    with open(a.data, encoding="utf-8") as f:
        try:
            data = json.load(f)
        except json.JSONDecodeError as e:
            fail("portfolio.json 格式不对：第 %d 行第 %d 列，%s" % (e.lineno, e.colno, e.msg))
    data, warns, auto, imgs = normalize(data, os.path.dirname(os.path.abspath(a.data)))

    lit = sum(1 for r in data["regions"] for c in r.get("cards") or [] if c.get("state") == "lit")
    allc = sum(len(r.get("cards") or []) for r in data["regions"])
    print("网站名：%s ｜ 目标岗位：%s ｜ 风格：%s" % (data["site"], data["role"], STYLES[data["style"]]))
    for r in data["regions"]:
        cs = r.get("cards") or []
        print("  %s：亮 %d / %d" % (r["name"], sum(1 for c in cs if c.get("state") == "lit"), len(cs)))
    print("共 %d 张卡，亮 %d 张；截图 %d 张（去掉重复以后），一共 %.1f MB" % (allc, lit, len(imgs.map), imgs.total / 1048576))
    if data["top"]:
        print("最高光三条：" + "、".join(data["top"]) +
              ("（%s 是按「几家要」自动挑的，跟用户确认一下）" % "、".join(auto) if auto else ""))
    for w in warns:
        print("⚠ " + w)
    for p in placeholders(data):
        print("⚠ 还没填（换成用户自己的话再发布）：" + p)
    if lit == 0:
        fail("一张亮卡都没有，HR 版会是空的。先把素材对上至少一张卡")
    if a.check:
        print("✓ 检查完，没有生成文件")
        return
    if not a.out:
        fail("要生成文件，请加 --out 输出文件夹")

    with open(a.template, encoding="utf-8") as f:
        tpl = f.read()
    os.makedirs(a.out, exist_ok=True)
    base = safe_name(data["site"])
    self_data = copy.deepcopy(data)
    self_data["audience"] = "self"
    hr = hr_version(data)
    outs = [(os.path.join(a.out, base + "-自己看.html"), self_data, imgs.map),
            (os.path.join(a.out, base + "-发给HR.html"), hr, used_images(hr, imgs))]
    for path, d, im in outs:
        with open(path, "w", encoding="utf-8") as f:
            f.write(fill(tpl, d, im))
        print("✓ 已生成 " + path + "（%.0f KB）" % (os.path.getsize(path) / 1024))
    print("发布、发给 HR、放进简历的，用「发给HR」那一份。")


if __name__ == "__main__":
    main()
