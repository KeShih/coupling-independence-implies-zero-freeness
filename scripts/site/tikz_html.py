"""Render the TikZ pictures and tikz-cd diagrams of the papers as HTML.

A tikzpicture becomes an inline SVG for the strokes and fills, with its node
texts laid over it as HTML, so that math in labels is typeset by KaTeX like
the rest of the page. The interpreter covers what the papers use: styles
(.style, .append style, style n args), pics with arguments, \\coordinate,
\\node, \\draw paths with -- segments, circles and nodes along the path,
\\foreach over slash lists, \\ifnum, scopes and \\tikzset, xcolor mixes,
line widths, dash patterns, line caps and joins, and Latex arrow tips.
A tikzcd matrix whose arrows each join neighbouring cells becomes a CSS
grid with drawn arrows and KaTeX labels.

Anything outside that raises Unsupported; the caller then falls back to an
image cut from the PDF.
"""
import html
import math
import re

PT_PER_CM = 72.27 / 2.54
PT_PER_MM = PT_PER_CM / 10
FONT_PT = {"tiny": 6, "scriptsize": 8, "footnotesize": 9, "small": 10, "normalsize": 10.95,
           "large": 12, "Large": 14.4}
BASE_COLORS = {
    "black": (0, 0, 0), "white": (1, 1, 1), "red": (1, 0, 0), "green": (0, 1, 0), "blue": (0, 0, 1),
    "cyan": (0, 1, 1), "magenta": (1, 0, 1), "yellow": (1, 1, 0), "gray": (.5, .5, .5),
    "darkgray": (.25, .25, .25), "lightgray": (.75, .75, .75), "brown": (.75, .5, .25),
    "lime": (.75, 1, 0), "olive": (.5, .5, 0), "orange": (1, .5, 0), "pink": (1, .75, .75),
    "purple": (.75, 0, .25), "teal": (0, .5, .5), "violet": (.5, 0, .5),
}


class Unsupported(Exception):
    pass


# ---------------------------------------------------------------------------
# Small parsers

def group(text, i):
    """Contents of the balanced group opening at text[i] ({, [ or ()."""
    close = {"{": "}", "[": "]", "(": ")"}[text[i]]
    opening, depth, j = text[i], 0, i
    while j < len(text):
        c = text[j]
        if c == "\\":
            j += 2
            continue
        if c in "{[(" and (c == opening or c == "{"):
            depth += 1
        elif c in "}])" and (c == close or c == "}"):
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1
        j += 1
    raise Unsupported("unbalanced %s" % opening)


def skip(text, i):
    while i < len(text) and text[i] in " \t\n":
        i += 1
    return i


def split_top(text, sep=","):
    parts, depth, start = [], 0, 0
    for k, c in enumerate(text):
        if c in "{[(":
            depth += 1
        elif c in "}])":
            depth -= 1
        elif c == sep and depth == 0:
            parts.append(text[start:k])
            start = k + 1
    parts.append(text[start:])
    return [p.strip() for p in parts if p.strip()]


def partition_top(item):
    """key, '=', value split at the first '=' outside braces and brackets."""
    depth = 0
    for k, c in enumerate(item):
        if c in "{[(":
            depth += 1
        elif c in "}])":
            depth -= 1
        elif c == "=" and depth == 0:
            return item[:k], "=", item[k + 1:]
    return item, "", ""


def dimension(text, default_unit="pt"):
    """A TeX dimension in points."""
    m = re.fullmatch(r"\s*(-?[\d.]+)\s*(pt|mm|cm|em|ex|in|bp)?\s*", text)
    if not m:
        raise Unsupported("dimension %r" % text)
    value, unit = float(m.group(1)), m.group(2) or default_unit
    return value * {"pt": 1, "mm": PT_PER_MM, "cm": PT_PER_CM, "em": 10, "ex": 4.3, "in": 72.27,
                    "bp": 72.27 / 72}[unit]


def color(expr):
    """An xcolor expression such as teal!75!black as an rgb() string."""
    parts = expr.strip().split("!")
    if parts[0] not in BASE_COLORS:
        raise Unsupported("colour %r" % expr)
    rgb = BASE_COLORS[parts[0]]
    k = 1
    while k < len(parts):
        pct = float(parts[k]) / 100
        other = BASE_COLORS.get(parts[k + 1], None) if k + 1 < len(parts) else BASE_COLORS["white"]
        if other is None:
            raise Unsupported("colour %r" % expr)
        rgb = tuple(pct * a + (1 - pct) * b for a, b in zip(rgb, other))
        k += 2
    return "rgb(%d,%d,%d)" % tuple(round(255 * c) for c in rgb)


def is_color(expr):
    try:
        color(expr)
        return True
    except (Unsupported, ValueError):
        return False


# ---------------------------------------------------------------------------
# Styles and options

class Styles:
    def __init__(self, parent=None):
        self.parent, self.defs = parent, {}

    def get(self, name):
        s = self
        while s is not None:
            if name in s.defs:
                return s.defs[name]
            s = s.parent
        return None

    def define(self, text):
        """Read style definitions (key/.style={...}, key/.append style={...},
        pics/name/.style n args={n}{code={...}}); returns other options."""
        rest = []
        for item in split_top(text):
            m = re.match(r"([\w ]+)/\.(style|append style)\s*=\s*", item)
            p = re.match(r"pics/([\w ]+)/\.style n args\s*=\s*", item)
            if p:
                j = p.end()
                n, j = group(item, skip(item, j))
                body, _ = group(item, skip(item, j))
                code = re.match(r"\s*code\s*=\s*", body)
                if not code:
                    raise Unsupported("pic without code")
                inner, _ = group(body, skip(body, code.end()))
                self.defs["pic:" + p.group(1).strip()] = (int(n), inner)
            elif m:
                value = item[m.end():].strip()
                if value.startswith("{"):
                    value, _ = group(value, 0)
                name = m.group(1).strip()
                if m.group(2) == "append style":
                    self.defs[name] = (self.get(name) or "") + "," + value
                else:
                    self.defs[name] = value
            else:
                rest.append(item)
        return ",".join(rest)


def resolve(opts, styles, into=None, depth=0):
    """Options as a dict, expanding style names."""
    out = into if into is not None else {}
    if depth > 20:
        raise Unsupported("style recursion")
    for item in split_top(opts or ""):
        key, eq, value = partition_top(item)
        key, value = key.strip(), value.strip()
        if value.startswith("{") and value.endswith("}"):
            value = value[1:-1]
        if not eq and styles.get(key) is not None:
            resolve(styles.get(key), styles, out, depth + 1)
        elif not eq and key.startswith("-") or key in ("->", "<-", "<->"):
            out["arrow"] = key
        elif not eq and key in ("dashed", "densely dashed", "loosely dashed", "dotted"):
            out["dash"] = {"dashed": "3 3", "densely dashed": "3 2", "loosely dashed": "3 6", "dotted": "0.4 2"}[key]
        elif not eq and key in ("circle", "rectangle"):
            out["shape"] = key
        elif not eq and key in ("midway", "near end", "near start", "at end", "at start"):
            out["pos"] = {"midway": .5, "near end": .75, "near start": .25, "at end": 1, "at start": 0}[key]
        elif key in ("above", "below", "left", "right", "above left", "above right", "below left", "below right"):
            out["place"] = key
            out["shift"] = dimension(value) if value else 0
        elif not eq and is_color(key):
            out["color"] = color(key)
        elif key in ("draw", "fill", "text"):
            if value and value not in ("none",):
                out[key] = color(value)
            elif key == "draw":
                out[key] = out.get("color", "rgb(0,0,0)") if value != "none" else None
            elif value == "none":
                out[key] = None
        elif key == "line width":
            out["width"] = dimension(value)
        elif key == "dash pattern":
            nums = re.findall(r"(on|off)\s*([\d.]+\s*\w*)", value)
            out["dash"] = " ".join("%.2f" % dimension(v) for _, v in nums)
        elif key in ("line cap", "line join"):
            out[key.replace(" ", "_")] = value
        elif key == "minimum size":
            out["min"] = dimension(value)
        elif key == "inner sep":
            out["inner"] = dimension(value)
        elif key == "font":
            size = [s for s in re.findall(r"\\(\w+)", value) if s in FONT_PT]
            if size:
                out["font"] = FONT_PT[size[-1]]
            if "bfseries" in value:
                out["bold"] = True
        elif key == "anchor":
            out["anchor"] = value
        elif key == "pos":
            out["pos"] = float(value)
        elif key in ("x", "y"):
            out[key] = dimension(value, "cm")
        elif key in ("radius",):
            out["radius"] = dimension(value, "cm")
        elif key in ("outer sep", "text width", "align", "labels", "column sep", "row sep", "every node/.style"):
            pass
        else:
            raise Unsupported("option %r" % item)
    return out


# ---------------------------------------------------------------------------
# The interpreter

class Picture:
    def __init__(self, render_text):
        self.render_text = render_text
        self.coords = {}
        self.shapes = []   # SVG strings, in drawing order
        self.labels = []   # dicts: x, y (pt), anchor, html, font, bold, color
        self.box = [math.inf, math.inf, -math.inf, -math.inf]
        self.unit = (PT_PER_CM, PT_PER_CM)

    def grow(self, x0, y0, x1, y1):
        b = self.box
        b[0], b[1], b[2], b[3] = min(b[0], x0), min(b[1], y0), max(b[2], x1), max(b[3], y1)

    def point(self, text, shift):
        text = text.strip()
        if text in self.coords:
            return self.coords[text]
        m = re.fullmatch(r"\s*([-\d.]+)\s*,\s*([-\d.]+)\s*", text)
        if not m:
            raise Unsupported("coordinate %r" % text)
        return (float(m.group(1)) * self.unit[0] + shift[0], -float(m.group(2)) * self.unit[1] + shift[1])

    def run(self, body, styles, shift=(0.0, 0.0)):
        i = 0
        while True:
            i = skip(body, i)
            if i >= len(body):
                return
            if body.startswith("\\begin{scope}", i):
                j = skip(body, i + len("\\begin{scope}"))
                opts = ""
                if j < len(body) and body[j] == "[":
                    opts, j = group(body, j)
                end = self.matching(body, j, "\\begin{scope}", "\\end{scope}")
                inner = Styles(styles)
                inner.define(opts)
                self.run(body[j:end], inner, shift)
                i = end + len("\\end{scope}")
            elif body.startswith("\\ifnum", i):
                m = re.match(r"\\ifnum\s*(-?\d+)\s*([=<>])\s*(-?\d+)", body[i:])
                if not m:
                    raise Unsupported("ifnum")
                j = i + m.end()
                end = self.matching(body, j, "\\ifnum", "\\fi")
                block = body[j:end]
                yes, no = self.split_else(block)
                a, op, b = int(m.group(1)), m.group(2), int(m.group(3))
                ok = a == b if op == "=" else a < b if op == "<" else a > b
                self.run(yes if ok else no, styles, shift)
                i = end + len("\\fi")
            elif body.startswith("\\foreach", i):
                m = re.match(r"\\foreach\s*((?:\\\w+\s*/?\s*)+)\s*in\s*", body[i:])
                if not m:
                    raise Unsupported("foreach")
                names = re.findall(r"\\(\w+)", m.group(1))
                j = skip(body, i + m.end())
                items, j = group(body, j)
                j = skip(body, j)
                if body[j] == "{":
                    inner, j = group(body, j)
                else:
                    end = self.statement_end(body, j)
                    inner, j = body[j:end + 1], end + 1
                for item in split_top(items):
                    values = item.split("/")
                    text = inner
                    for name, value in zip(names, values):
                        text = re.sub(r"\\%s(?![A-Za-z])" % name, value.strip(), text)
                    self.run(text, styles, shift)
                i = j
            elif body.startswith("\\tikzset", i):
                opts, i = group(body, skip(body, i + len("\\tikzset")))
                styles.define(opts)
            elif body[i] == "%":
                i = body.find("\n", i) + 1 or len(body)
            else:
                end = self.statement_end(body, i)
                self.statement(body[i:end].strip(), styles, shift)
                i = end + 1

    @staticmethod
    def matching(body, j, opening, closing):
        depth = 1
        pattern = re.compile("%s|%s|\\\\else" % (re.escape(opening), re.escape(closing)))
        for m in pattern.finditer(body, j):
            if m.group() == opening:
                depth += 1
            elif m.group() == closing:
                depth -= 1
                if depth == 0:
                    return m.start()
        raise Unsupported("unclosed " + opening)

    @staticmethod
    def split_else(block):
        depth = 0
        for m in re.finditer(r"\\ifnum|\\fi|\\else", block):
            if m.group() == "\\ifnum":
                depth += 1
            elif m.group() == "\\fi":
                depth -= 1
            elif depth == 0:
                return block[:m.start()], block[m.end():]
        return block, ""

    @staticmethod
    def statement_end(body, i):
        depth = 0
        for k in range(i, len(body)):
            c = body[k]
            if c in "{[(":
                depth += 1
            elif c in "}])":
                depth -= 1
            elif c == ";" and depth == 0:
                return k
        raise Unsupported("statement without ;")

    def statement(self, text, styles, shift):
        m = re.match(r"\\(coordinate|node|draw|path|fill|filldraw|pic)\b", text)
        if not m:
            raise Unsupported("command %r" % text[:30])
        cmd, rest = m.group(1), text[m.end():]
        if cmd == "coordinate":
            c = re.match(r"\s*\((\w+)\)\s*at\s*\(([^)]*)\)\s*$", rest)
            if not c:
                raise Unsupported("coordinate form")
            self.coords[c.group(1)] = self.point(c.group(2), shift)
        elif cmd == "node":
            j = skip(rest, 0)
            opts = ""
            if j < len(rest) and rest[j] == "[":
                opts, j = group(rest, j)
            c = re.match(r"\s*(?:\((\w+)\)\s*)?at\s*", rest[j:])
            if not c:
                raise Unsupported("node form")
            j += c.end()
            where, j = group(rest, skip(rest, j))
            content, j = group(rest, skip(rest, j))
            p = self.point(where, shift)
            if c.group(1):
                self.coords[c.group(1)] = p
            self.node(p, resolve(opts, styles), content)
        elif cmd == "pic":
            c = re.match(r"\s*at\s*", rest)
            if not c:
                raise Unsupported("pic form")
            where, j = group(rest, skip(rest, c.end()))
            spec, j = group(rest, skip(rest, j))
            pm = re.match(r"\s*([\w ]+?)\s*=\s*", spec)
            name = pm.group(1) if pm else spec.strip()
            args, k = [], pm.end() if pm else len(spec)
            while k < len(spec):
                k = skip(spec, k)
                if k < len(spec) and spec[k] == "{":
                    a, k = group(spec, k)
                    args.append(a)
                else:
                    break
            pic = styles.get("pic:" + name)
            if pic is None:
                raise Unsupported("pic %s" % name)
            n, code = pic
            for a in range(n):
                code = code.replace("#%d" % (a + 1), args[a] if a < len(args) else "")
            origin = self.point(where, shift)
            self.run(code, Styles(styles), origin)
        else:
            self.draw(cmd, rest, styles, shift)

    def node(self, p, o, content):
        font = o.get("font", 10.95)
        inner = o.get("inner", 0.3333 * font)
        if o.get("shape") == "circle" and (o.get("draw", None) or o.get("fill")):
            r = max(o.get("min", 0) / 2, 0.8 * font / 2 + inner)
            stroke = o.get("draw") if "draw" in o else None
            width = o.get("width", 0.4)
            self.shapes.append('<circle cx="%.2f" cy="%.2f" r="%.2f" fill="%s" stroke="%s" stroke-width="%.2f"/>'
                               % (p[0], p[1], r, o.get("fill") or "none", stroke or "none", width))
            self.grow(p[0] - r - width, p[1] - r - width, p[0] + r + width, p[1] + r + width)
        place, shift = o.get("place"), o.get("shift", 0)
        anchor = o.get("anchor", "center")
        dx = dy = 0.0
        if place:
            words = place.split()
            anchor = " ".join({"above": "south", "below": "north", "left": "east", "right": "west"}[w] for w in words)
            anchor = {"south east": "south east", "south west": "south west", "north east": "north east",
                      "north west": "north west", "east south": "south east"}.get(anchor, anchor)
            dx = shift * (("right" in words) - ("left" in words))
            dy = shift * (("below" in words) - ("above" in words))
        x, y = p[0] + dx, p[1] + dy
        text = self.render_text(content)
        if not text.strip():
            return
        est_w = 0.55 * font * max(1, len(re.sub(r"\\[A-Za-z]+|[{}$\\()]", "", content)))
        est_h = 1.2 * font
        ax, ay = self.anchor_offsets(anchor)
        pad = 0 if o.get("shape") == "circle" else inner
        x += {-1: pad, 0: 0, 1: -pad}[ax]
        y += {-1: pad, 0: 0, 1: -pad, 2: 0}[ay]
        self.grow(x - (1 + ax) / 2 * est_w - 2, y - {-1: 0, 0: .5, 1: 1, 2: .8}[ay] * est_h - 2,
                  x + (1 - ax) / 2 * est_w + 2, y + {-1: 1, 0: .5, 1: 0, 2: .2}[ay] * est_h + 2)
        self.labels.append(dict(x=x, y=y, ax=ax, ay=ay, html=text, font=font, bold=o.get("bold", False),
                                color=o.get("text") or o.get("color")))

    @staticmethod
    def anchor_offsets(anchor):
        """(ax, ay): ax -1 = west edge at x, 0 centre, 1 east edge; ay -1 = north
        edge at y, 0 centre, 1 south edge, 2 baseline."""
        ax = -1 if "west" in anchor else 1 if "east" in anchor else 0
        ay = -1 if "north" in anchor else 1 if "south" in anchor else 2 if anchor == "base" else 0
        return ax, ay

    def draw(self, cmd, rest, styles, shift):
        j = skip(rest, 0)
        opts = ""
        if j < len(rest) and rest[j] == "[":
            opts, j = group(rest, j)
        o = resolve(opts, styles)
        stroke = o.get("draw", o.get("color", "rgb(0,0,0)")) if cmd in ("draw", "filldraw") else o.get("draw")
        fill = o.get("fill") if cmd in ("fill", "filldraw") or "fill" in o else None
        if cmd == "fill" and fill is None:
            fill = o.get("color", "rgb(0,0,0)")
        width = o.get("width", 0.4)
        subpaths, current, last, nodes, joined = [], [], None, [], False
        k = j
        while True:
            k = skip(rest, k)
            if k >= len(rest):
                break
            if rest[k] == "(":
                inner, k = group(rest, k)
                last = self.point(inner, shift)
                if current and not joined:  # a move-to starts a new subpath
                    subpaths.append(current)
                    current = []
                current.append(last)
                joined = False
            elif rest.startswith("--", k):
                k += 2
                joined = True
            elif rest.startswith("circle", k):
                k = skip(rest, k + len("circle"))
                if rest[k] == "[":
                    copts, k = group(rest, k)
                    r = resolve(copts, styles).get("radius")
                else:
                    rtext, k = group(rest, k)
                    r = dimension(rtext, "cm")
                if last is None or r is None:
                    raise Unsupported("circle")
                self.shapes.append(self.stroke_attrs('<circle cx="%.2f" cy="%.2f" r="%.2f"' % (last[0], last[1], r),
                                                     stroke, fill, width, o) + "/>")
                self.grow(last[0] - r - width, last[1] - r - width, last[0] + r + width, last[1] + r + width)
            elif rest.startswith("node", k):
                k = skip(rest, k + 4)
                nopts = ""
                if rest[k] == "[":
                    nopts, k = group(rest, k)
                content, k = group(rest, skip(rest, k))
                nodes.append((list(current), resolve(nopts, styles), content))
            else:
                raise Unsupported("path element %r" % rest[k:k + 20])
        if current:
            subpaths.append(current)
        for pts in subpaths:
            if len(pts) < 2:
                continue
            closed = pts[0] == pts[-1] and len(pts) > 2
            d = "M" + " L".join("%.2f %.2f" % q for q in pts) + (" Z" if closed else "")
            self.shapes.append(self.stroke_attrs('<path d="%s"' % d, stroke, fill if closed else None, width, o) + "/>")
            for q in pts:
                self.grow(q[0] - width / 2, q[1] - width / 2, q[0] + width / 2, q[1] + width / 2)
            if o.get("arrow") and stroke:
                self.arrow_tip(pts[-2], pts[-1], o["arrow"], stroke, width)
        for pts, nopts, content in nodes:
            pos = nopts.get("pos", 1)
            if len(pts) >= 2:
                a, b = pts[-2], pts[-1]
                p = (a[0] + pos * (b[0] - a[0]), a[1] + pos * (b[1] - a[1]))
            elif pts:
                p = pts[-1]
            else:
                raise Unsupported("node on empty path")
            self.node(p, nopts, content)

    @staticmethod
    def stroke_attrs(start, stroke, fill, width, o):
        attrs = [start, 'fill="%s"' % (fill or "none")]
        if stroke:
            attrs.append('stroke="%s" stroke-width="%.2f"' % (stroke, width))
            if o.get("dash"):
                attrs.append('stroke-dasharray="%s"' % o["dash"])
            attrs.append('stroke-linecap="%s"' % {"round": "round", "rect": "square"}.get(o.get("line_cap"), "butt"))
            attrs.append('stroke-linejoin="%s"' % {"round": "round", "bevel": "bevel"}.get(o.get("line_join"), "miter"))
        return " ".join(attrs)

    def arrow_tip(self, a, b, spec, stroke, width):
        m = re.search(r"length\s*=\s*([\d.]+\s*\w+)", spec)
        w = re.search(r"width\s*=\s*([\d.]+\s*\w+)", spec)
        length = dimension(m.group(1)) if m else 3 + 2 * width
        half = (dimension(w.group(1)) if w else 0.75 * length) / 2
        dx, dy = b[0] - a[0], b[1] - a[1]
        n = math.hypot(dx, dy) or 1
        ux, uy = dx / n, dy / n
        base = (b[0] - ux * length, b[1] - uy * length)
        pts = [b, (base[0] - uy * half, base[1] + ux * half), (base[0] + uy * half, base[1] - ux * half)]
        self.shapes.append('<path d="M%.2f %.2f L%.2f %.2f L%.2f %.2f Z" fill="%s"/>'
                           % (pts[0] + pts[1] + pts[2] + (stroke,)))

    def html(self):
        x0, y0, x1, y1 = self.box
        if not math.isfinite(x0):
            raise Unsupported("empty picture")
        pad = 2.0
        x0, y0, x1, y1 = x0 - pad, y0 - pad, x1 + pad, y1 + pad
        w, h = x1 - x0, y1 - y0
        labels = []
        for lab in self.labels:
            tx = {-1: "0", 0: "-50%", 1: "-100%"}[lab["ax"]]
            ty = {-1: "0", 0: "-50%", 1: "-100%", 2: "-78%"}[lab["ay"]]
            style = "left:%.3f%%;top:%.3f%%;transform:translate(%s,%s);font-size:calc(100cqi*%.4f)" % (
                100 * (lab["x"] - x0) / w, 100 * (lab["y"] - y0) / h, tx, ty, lab["font"] / w)
            if lab["bold"]:
                style += ";font-weight:700"
            if lab["color"]:
                style += ";color:%s" % lab["color"]
            labels.append('<span class="tz-label" style="%s">%s</span>' % (style, lab["html"]))
        svg = ('<svg class="tz-svg" viewBox="%.2f %.2f %.2f %.2f" aria-hidden="true">%s</svg>'
               % (x0, y0, w, h, "".join(self.shapes)))
        return ('<div class="tz" style="--tz-w:%.2f;aspect-ratio:%.2f/%.2f">%s%s</div>'
                % (w, w, h, svg, "".join(labels)))


def picture(body, render_text):
    """HTML for the body of a tikzpicture environment (options included)."""
    styles = Styles()
    pic = Picture(render_text)
    j = skip(body, 0)
    if j < len(body) and body[j] == "[":
        opts, j = group(body, j)
        rest = styles.define(opts)
        o = resolve(rest, styles)
        pic.unit = (o.get("x", PT_PER_CM), o.get("y", PT_PER_CM))
    pic.run(body[j:], styles)
    return pic.html()


# ---------------------------------------------------------------------------
# tikz-cd

def cd_matrix(body, render_math):
    """HTML for a tikzcd matrix whose arrows join horizontally or vertically
    adjacent cells."""
    j = skip(body, 0)
    col_sep, row_sep, label_scale = 1.8, 1.8, 1.0
    if j < len(body) and body[j] == "[":
        opts, j = group(body, j)
        for item in split_top(opts):
            key, _, value = item.partition("=")
            key, value = key.strip(), value.strip()
            if key == "column sep":
                col_sep = dimension(value) / 10
            elif key == "row sep":
                row_sep = dimension(value) / 10
            elif key == "labels":
                if "footnotesize" in value:
                    label_scale = 0.8
                elif "small" in value:
                    label_scale = 0.9
            else:
                raise Unsupported("tikzcd option %r" % item)
    rows = [r for r in re.split(r"\\\\", body[j:]) if r.strip()]
    grid = [split_cells(r) for r in rows]
    ncols = max(len(r) for r in grid)
    cells, arrows = [], []
    for r, row in enumerate(grid):
        for c, cell in enumerate(row):
            content, cell_arrows = split_arrows(cell)
            cells.append((r, c, content.strip()))
            for spec in cell_arrows:
                arrows.append((r, c) + parse_arrow(spec))
    out = []
    for r, c, content in cells:
        if content:
            out.append('<div class="cd-node" style="grid-row:%d;grid-column:%d"><span class="m">%s</span></div>'
                       % (2 * r + 1, 2 * c + 1, html.escape(render_math(content), quote=False)))
    for r, c, (dr, dc), label, swap, dashed in arrows:
        if abs(dr) + abs(dc) != 1:
            raise Unsupported("tikzcd arrow that is not between neighbours")
        horizontal = dr == 0
        row, col = 2 * r + 1 + dr, 2 * c + 1 + dc
        # tikz-cd puts a label on the left of the direction of travel; ' swaps it
        left = {(0, 1): "above", (0, -1): "below", (1, 0): "right", (-1, 0): "left"}[(dr, dc)]
        other = {"above": "below", "below": "above", "left": "right", "right": "left"}
        side = other[left] if swap else left
        direction = {(0, 1): "r", (0, -1): "l", (1, 0): "d", (-1, 0): "u"}[(dr, dc)]
        box, path = {"l": ("0 0 6 8", "M6 0 L0 4 L6 8"), "r": ("0 0 6 8", "M0 0 L6 4 L0 8"),
                     "u": ("0 0 8 6", "M0 6 L4 0 L8 6"), "d": ("0 0 8 6", "M0 0 L4 6 L8 0")}[direction]
        out.append('<div class="cd-arrow %s%s" data-dir="%s" style="grid-row:%d;grid-column:%d">'
                   '<span class="cd-shaft"><svg class="cd-head" viewBox="%s" aria-hidden="true">'
                   '<path d="%s"/></svg></span>%s</div>'
                   % ("cd-h" if horizontal else "cd-v", " dashed" if dashed else "", direction, row, col, box, path,
                      '<span class="cd-label %s" style="font-size:%.2fem"><span class="m">%s</span></span>'
                      % (side, label_scale, html.escape(render_math(label), quote=False)) if label else ""))
    cols = " ".join("auto" if k % 2 == 0 else "%.2fem" % col_sep for k in range(2 * ncols - 1))
    rows_css = " ".join("auto" if k % 2 == 0 else "%.2fem" % row_sep for k in range(2 * len(grid) - 1))
    return ('<div class="cd" role="img" aria-label="Commutative diagram" style="grid-template-columns:%s;'
            'grid-template-rows:%s">%s</div>' % (cols, rows_css, "".join(out)))


def split_cells(row):
    cells, depth, start = [], 0, 0
    for k, c in enumerate(row):
        if c in "{[":
            depth += 1
        elif c in "}]":
            depth -= 1
        elif c == "&" and depth == 0:
            cells.append(row[start:k])
            start = k + 1
    cells.append(row[start:])
    return cells


def split_arrows(cell):
    arrows, out, k = [], [], 0
    while True:
        m = re.search(r"\\(arrow|ar)(?![A-Za-z])", cell[k:])
        if not m:
            out.append(cell[k:])
            break
        out.append(cell[k:k + m.start()])
        j = skip(cell, k + m.end())
        if j >= len(cell) or cell[j] != "[":
            raise Unsupported("arrow without options")
        spec, k = group(cell, j)
        arrows.append(spec)
    return "".join(out), arrows


def parse_arrow(spec):
    label, swap, dashed, move = None, False, False, None
    for item in split_top(spec):
        if item.startswith('"'):
            m = re.fullmatch(r'"(.*)"(\'?)', item, re.S)
            if not m:
                raise Unsupported("arrow label %r" % item)
            text = m.group(1).strip()
            if text.startswith("{") and text.endswith("}"):
                text = text[1:-1]
            label, swap = text, bool(m.group(2))
        elif re.fullmatch(r"[rlud]+", item):
            move = (item.count("d") - item.count("u"), item.count("r") - item.count("l"))
        elif item == "dashed":
            dashed = True
        else:
            raise Unsupported("arrow option %r" % item)
    if move is None:
        raise Unsupported("arrow without direction")
    return move, label, swap, dashed
