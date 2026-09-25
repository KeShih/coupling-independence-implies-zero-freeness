"""Render a paper's LaTeX source as HTML for the reader built by build_reader.py.

The converter knows the constructs the two papers use: sectioning (with
\\appendix and \\numberwithin), amsthm environments, proofs, amsmath
displays, enumitem lists, booktabs tables, figures, \\cref-style references,
citations from the .bbl and the title block. Math is left as TeX for KaTeX.

Numbers are computed the way LaTeX computes them: theorem-like environments
share one counter within sections, equations are numbered through the
document until \\numberwithin{equation}{section}, and appendix sections are
lettered. convert() checks the numbered statements against coverage.json;
check_pdf() checks theorem, equation and section numbers against the named
destinations hyperref wrote into the compiled PDF. Figures and tikz-cd
diagrams are drawn from their TikZ source by tikz_html.py; one it cannot read
is cut from the PDF as an image instead, with a warning.
"""
import html
import re
import sys
import unicodedata
from pathlib import Path

import build as checker
import tikz_html

ROMAN = [(1000, "m"), (900, "cm"), (500, "d"), (400, "cd"), (100, "c"), (90, "xc"),
         (50, "l"), (40, "xl"), (10, "x"), (9, "ix"), (5, "v"), (4, "iv"), (1, "i")]
DISPLAYS = ("equation", "equation*", "align", "align*", "gather", "gather*", "multline", "multline*")
NUMBERED = {"equation", "align", "gather", "multline"}
ACCENTS = {"'": "\u0301", "`": "\u0300", "^": "\u0302", '"': "\u0308", "~": "\u0303", "=": "\u0304",
           ".": "\u0307", "u": "\u0306", "v": "\u030c", "H": "\u030b", "c": "\u0327", "k": "\u0328",
           "r": "\u030a"}
LETTERS = {"ss": "ß", "o": "ø", "O": "Ø", "aa": "å", "AA": "Å", "ae": "æ", "AE": "Æ", "oe": "œ",
           "OE": "Œ", "l": "ł", "L": "Ł", "i": "ı", "j": "ȷ"}
SYMBOLS = {"S": "§", "P": "¶", "ldots": "…", "dots": "…", "textendash": "–", "textemdash": "—",
           "textquoteright": "’", "textquoteleft": "‘", "copyright": "©", "&": "&", "%": "%",
           "$": "$", "#": "#", "_": "_", "{": "{", "}": "}", "textbackslash": "\\", "LaTeX": "LaTeX",
           "TeX": "TeX", "dag": "†", "ddag": "‡"}
# commands whose arguments produce no text: name -> number of mandatory arguments
DROP = {"label": 1, "vspace": 1, "hspace": 1, "setlength": 2, "renewcommand": 2, "setcounter": 2,
        "addtocounter": 2, "numberwithin": 2, "crefalias": 2, "bibliographystyle": 1,
        "theoremstyle": 1, "pagestyle": 1, "thispagestyle": 1, "enlargethispage": 1, "phantom": 1,
        "hypersetup": 1, "embedfile": 1, "addcontentsline": 3}
IGNORE = {"smallskip", "medskip", "bigskip", "noindent", "indent", "centering", "raggedright",
          "raggedleft", "leavevmode", "hfill", "vfill", "small", "footnotesize", "scriptsize",
          "normalsize", "large", "Large", "tiny", "clearpage", "newpage", "FloatBarrier", "maketitle",
          "tableofcontents", "appendix", "protect", "relax", "sloppy", "par", "newline", "nobreak",
          "allowbreak", "linebreak", "pagebreak", "bfseries", "itshape", "rmfamily", "normalfont",
          "upshape", "mdseries", "ttfamily", "sffamily", "scshape", "toprule", "midrule",
          "bottomrule", "hline", "unskip", "ignorespaces", "strut", "null", "break", "displaystyle"}
STYLES = {"em": "em", "it": "em", "itshape": "em", "bf": "strong", "bfseries": "strong",
          "tt": "code", "ttfamily": "code", "sc": "span class=\"sc\"", "scshape": "span class=\"sc\""}


def warn(message):
    print("warning: " + message, file=sys.stderr)


def fail(problems, what):
    if problems:
        sys.exit(what + ":\n  " + "\n  ".join(problems))


def accented(base, accent):
    base = base.strip()
    base = {"\\i": "i", "\\j": "j"}.get(base, LETTERS.get(base.lstrip("\\"), base) if base.startswith("\\") else base)
    return unicodedata.normalize("NFC", base + ACCENTS[accent])


def roman(n):
    out = ""
    for value, digits in ROMAN:
        while n >= value:
            out, n = out + digits, n - value
    return out


def alph(n):
    return "abcdefghijklmnopqrstuvwxyz"[n - 1]


def read_group(text, i):
    """The brace group at text[i] (after optional spaces) and the index after it."""
    while i < len(text) and text[i] in " \t\n":
        i += 1
    if i >= len(text) or text[i] != "{":
        return None, i
    return group_at(text, i)


def group_at(text, i):
    """The brace group at text[i], or None when it is not closed."""
    try:
        return checker.read_group(text, i)
    except IndexError:
        return None, i + 1


def read_optional(text, i):
    j = i
    while j < len(text) and text[j] in " \t\n":
        j += 1
    if j >= len(text) or text[j] != "[":
        return None, i
    depth, k = 0, j + 1
    while not (text[k] == "]" and depth == 0):
        depth += {"{": 1, "}": -1}.get(text[k], 0)
        k += 1
    return text[j + 1:k], k + 1


def matching_end(text, env, start):
    """Index of the \\end{env} closing the environment whose body starts at start."""
    depth, pattern = 1, re.compile(r"\\(begin|end)\{%s\}" % re.escape(env))
    for match in pattern.finditer(text, start):
        depth += 1 if match.group(1) == "begin" else -1
        if depth == 0:
            return match.start(), match.end()
    raise ValueError("unclosed environment " + env)


def split_top(text, separator):
    """Split at separator ("\\\\" or "&") outside braces and nested environments."""
    parts, depth, env, start, i = [], 0, 0, 0, 0
    while i < len(text):
        if text.startswith("\\begin{", i):
            env += 1
        elif text.startswith("\\end{", i):
            env -= 1
        if text[i] == "\\" and text.startswith(separator, i) and depth == 0 and env == 0:
            parts.append(text[start:i])
            i += len(separator)
            start = i
            continue
        if text[i] == "\\":
            i += 2
            continue
        if text[i] == "&" and separator == "&" and depth == 0 and env == 0:
            parts.append(text[start:i])
            start = i + 1
        depth += {"{": 1, "}": -1}.get(text[i], 0)
        i += 1
    parts.append(text[start:])
    return parts


# ---------------------------------------------------------------------------
# Source

def load(main):
    """The source with \\input files inlined, verbatim blocks set aside and
    comments removed as TeX removes them."""
    root = main.parent

    def inline(tex):
        return re.sub(r"\\input\{([^}]*)\}",
                      lambda m: inline((root / (m.group(1) if m.group(1).endswith(".tex")
                                                 else m.group(1) + ".tex")).read_text()), tex)

    tex = inline(main.read_text())
    verbatim = []

    def keep(match):
        verbatim.append(match.group(1))
        return "\\verbatimblock{%d}" % (len(verbatim) - 1)

    tex = re.sub(r"\\begin\{verbatim\}\n?(.*?)\\end\{verbatim\}", keep, tex, flags=re.S)
    tex = re.sub(r"(?<!\\)%[^\n]*\n(?![ \t]*\n)[ \t]*", "", tex)
    tex = re.sub(r"(?<!\\)%[^\n]*", "", tex)
    return tex, verbatim


def theorem_styles(preamble):
    """env -> (word, amsthm style), first declaration of each env winning."""
    styles, style = {}, "plain"
    for match in re.finditer(r"\\theoremstyle\{(\w+)\}|\\newtheorem\{(\w+)\}(?:\[\w+\])?\{([^}]*)\}",
                             preamble):
        if match.group(1):
            style = match.group(1)
        elif match.group(2) not in styles:
            styles[match.group(2)] = (match.group(3), style)
    return styles


def bibliography(bbl):
    """[(key, label, body)] from a .bbl file of the alpha style."""
    items = []
    parts = re.split(r"\\bibitem", bbl)
    for part in parts[1:]:
        label, i = read_optional(part, 0)
        key, i = read_group(part, i)
        body = part[i:].split("\\end{thebibliography}")[0]
        label = re.sub(r"\\etalchar\{([^}]*)\}", r"\1", label or key).replace("{", "").replace("}", "")
        items.append((key, label, body.strip()))
    return items


# ---------------------------------------------------------------------------
# Numbering: one pass that computes what LaTeX would number, and annotates
# the source with markers \x03...\x03 that the HTML pass reads.

TOKEN = re.compile(
    r"\\(?P<sec>section|subsection|subsubsection)(?P<star>\*?)(?![A-Za-z])"
    r"|\\(?P<appendix>appendix)(?![A-Za-z])"
    r"|\\numberwithin\{(?P<nw>\w+)\}\{(?P<nwin>\w+)\}"
    r"|\\begin\{(?P<begin>[A-Za-z*]+)\}"
    r"|\\end\{(?P<end>[A-Za-z*]+)\}"
    r"|\\label\{(?P<label>[^}]*)\}"
    r"|(?P<row>\\\\)"
    r"|\\(?P<nonum>nonumber|notag)(?![A-Za-z])"
    r"|\\(?P<item>item)(?![A-Za-z])"
    r"|\\(?P<caption>caption)(?![A-Za-z])"
    r"|(?P<brace>(?<!\\)[{}])")


class Numbering:
    def __init__(self, tex, theorems):
        self.labels, self.kinds = {}, {}
        self.statements, self.sections, self.equations = [], [], []
        self.markers = []
        sec, sub, subsub, thm, eq, tables, figures = 0, 0, 0, 0, 0, 0, 0
        appendix, eq_within, table_within = False, False, False
        current, envs, lists, align = ("", ""), [], [], None
        depth = 0

        def secnum():
            return chr(64 + sec) if appendix else str(sec)

        def set_current(number, kind):
            nonlocal current
            current = (number, kind)

        for match in TOKEN.finditer(tex):
            g = next(name for name, value in match.groupdict().items() if value is not None)
            if g == "brace":
                depth += 1 if match.group() == "{" else -1
            elif g == "sec":
                if match.group("star"):
                    continue
                level = match.group("sec")
                if level == "section":
                    sec, sub, subsub, thm = sec + 1, 0, 0, 0
                    if eq_within:
                        eq = 0
                    if table_within:
                        tables = 0
                    number, kind = secnum(), "appendix" if appendix else "section"
                elif level == "subsection":
                    sub, subsub = sub + 1, 0
                    number, kind = "%s.%d" % (secnum(), sub), "subappendix" if appendix else "subsection"
                else:
                    subsub += 1
                    number, kind = "%s.%d.%d" % (secnum(), sub, subsub), "subsubsection"
                self.sections.append((level, number))
                self.markers.append((match.end(), "num=" + number))
                set_current(number, kind)
            elif g == "appendix":
                appendix, sec = True, 0
            elif g == "nw":
                if match.group("nw") == "equation":
                    eq_within = True
                elif match.group("nw") == "table":
                    table_within = True
            elif g == "begin":
                env = match.group("begin")
                envs.append(env)
                if env in theorems:
                    thm += 1
                    number = "%s.%d" % (secnum(), thm)
                    self.statements.append(dict(kind=env, number=number, label=None, at=match.start()))
                    self.markers.append((match.end(), "num=" + number))
                    set_current(number, env)
                elif env == "equation":
                    eq += 1
                    number = ("%s.%d" % (secnum(), eq)) if eq_within else str(eq)
                    self.equations.append(number)
                    self.markers.append((match.end(), "num=" + number))
                    set_current(number, "equation")
                elif env in ("align", "gather", "multline"):
                    align = dict(depth=depth, env=len(envs), numbered=True, labels=[], nums=[],
                                 start=match.end())
                elif env in ("enumerate", "itemize"):
                    options, _ = read_optional(tex, match.end())
                    fmt = None
                    if options:
                        fm = re.search(r"label=(\{[^}]*\}|\\textup\{[^}]*\}|[^,]*)", options)
                        fmt = fm.group(1) if fm else None
                    lists.append(dict(env=env, count=0, fmt=fmt))
            elif g == "end":
                env = match.group("end")
                if envs:
                    envs.pop()
                if env in ("align", "gather", "multline") and align is not None:
                    self._row(align, eq, eq_within, secnum)
                    eq = align["eq"]
                    self.markers.append((align["start"], "nums=" + ",".join(align["nums"])))
                    align = None
                elif env in ("enumerate", "itemize") and lists:
                    lists.pop()
            elif g == "row":
                if align is not None and depth == align["depth"] and len(envs) == align["env"]:
                    self._row(align, eq, eq_within, secnum)
                    eq = align["eq"]
            elif g == "nonum":
                if align is not None:
                    align["numbered"] = False
            elif g == "label":
                label = match.group("label")
                if align is not None:
                    align["labels"].append(label)
                    continue
                if self.statements and current[1] in theorems and self.statements[-1]["label"] is None \
                        and self.statements[-1]["number"] == current[0]:
                    self.statements[-1]["label"] = label
                self.labels[label], self.kinds[label] = current
            elif g == "item":
                if lists:
                    top = lists[-1]
                    top["count"] += 1
                    custom, _ = read_optional(tex, match.end())
                    if custom is not None:
                        text = custom
                    elif top["env"] == "itemize":
                        text = "•"
                    else:
                        text = self.item_label(top["fmt"], top["count"])
                    self.markers.append((match.end(), "item=" + text))
                    if top["env"] == "enumerate":
                        set_current(text, "enumi")
            elif g == "caption":
                env = next((e for e in reversed(envs) if e in ("table", "figure")), None)
                if env == "table":
                    tables += 1
                    number = ("%s.%d" % (secnum(), tables)) if table_within else str(tables)
                elif env == "figure":
                    figures += 1
                    number = str(figures)
                else:
                    continue
                self.markers.append((match.end(), "num=" + number))
                set_current(number, env)

    def _row(self, align, eq, eq_within, secnum):
        if align["numbered"]:
            eq += 1
            number = ("%s.%d" % (secnum(), eq)) if eq_within else str(eq)
            align["nums"].append(number)
            self.equations.append(number)
            for label in align["labels"]:
                self.labels[label], self.kinds[label] = number, "equation"
        else:
            align["nums"].append("")
        align["eq"], align["numbered"], align["labels"] = eq, True, []

    @staticmethod
    def item_label(fmt, n):
        if not fmt:
            return str(n)
        if fmt.startswith("{") and fmt.endswith("}"):
            fmt = fmt[1:-1]
        fmt = re.sub(r"\\textup\{(.*)\}", r"\1", fmt)
        fmt = fmt.replace("\\roman*", roman(n)).replace("\\Roman*", roman(n).upper())
        fmt = fmt.replace("\\alph*", alph(n)).replace("\\Alph*", alph(n).upper())
        return fmt.replace("\\arabic*", str(n))

    def annotate(self, tex):
        for at, marker in sorted(self.markers, key=lambda m: m[0], reverse=True):
            tex = tex[:at] + "\x03" + marker + "\x03" + tex[at:]
        return tex


def take_marker(text, i):
    """The marker at text[i] (if any) as (key, value) and the index after it."""
    if i < len(text) and text[i] == "\x03":
        end = text.index("\x03", i + 1)
        key, _, value = text[i + 1:end].partition("=")
        return (key, value), end + 1
    return None, i


# ---------------------------------------------------------------------------
# HTML

class Converter:
    def __init__(self, paper, numbering, theorems, bib, verbatim, figure_images):
        self.paper, self.num, self.theorems = paper, numbering, theorems
        self.cites = {key: label for key, label, _ in bib}
        self.verbatim, self.figure_images = verbatim, figure_images
        self.in_figure = False
        self.titles = {}
        self.math = []
        self.sections = []
        self.statement_ids = {}

    # -- math ---------------------------------------------------------------

    def protect_math(self, tex):
        """Replace inline math by placeholders; displays are handled as blocks."""
        def keep(body):
            self.math.append(self.math_tex(body))
            return "\x00%d\x00" % (len(self.math) - 1)

        tex = re.sub(r"\\\((.*?)\\\)", lambda m: keep(m.group(1)), tex, flags=re.S)
        tex = re.sub(r"(?<![\\$])\$(?!\$)(.+?)(?<!\\)\$", lambda m: keep(m.group(1)), tex, flags=re.S)
        return tex

    def math_tex(self, body):
        body = re.sub(r"\x00(\d+)\x00", lambda m: "$%s$" % self.math[int(m.group(1))], body)
        body = re.sub(r"\x03[^\x03]*\x03", "", body)
        body = re.sub(r"\\label\{[^}]*\}", "", body)
        body = re.sub(r"\\eqref\{([^}]*)\}",
                      lambda m: "\\href{#%s}{\\text{(%s)}}" % (m.group(1), self.num.labels.get(m.group(1), "??")),
                      body)
        body = re.sub(r"\\[Cc]ref\{([^}]*)\}",
                      lambda m: "\\text{%s}" % self.ref_text(m.group(1).split(",")), body)
        body = re.sub(r"\\ref\{([^}]*)\}",
                      lambda m: "\\href{#%s}{%s}" % (m.group(1), self.num.labels.get(m.group(1), "??")), body)
        return body

    def display(self, env, body, marker):
        """A display as a block; numbered rows carry \\tag, labels become anchors."""
        labels = re.findall(r"\\label\{([^}]*)\}", body)
        name = env.rstrip("*")
        anchors = "".join('<span class="anchor" id="%s"></span>' % html.escape(l) for l in labels[1:])
        if name == "equation" and env in NUMBERED:
            tex = "%s \\tag{%s}" % (self.math_tex(body).strip(), marker)
        elif name in ("align", "gather", "multline"):
            rows = split_top(body, "\\\\")
            nums = marker.split(",") if marker and env in NUMBERED else [""] * len(rows)
            out = []
            for row, n in zip(rows, nums + [""] * (len(rows) - len(nums))):
                row = self.math_tex(row).strip()
                if not row and not n:
                    continue
                out.append(row + (" \\tag{%s}" % n if n else " \\notag" if env in NUMBERED else ""))
            inner = "aligned" if name == "align" else "gathered"
            if env in NUMBERED:
                inner = name
            tex = "\\begin{%s}%s\\end{%s}" % (inner, "\\\\\n".join(out), inner)
        else:
            tex = self.math_tex(body).strip()
        ident = ' id="%s"' % html.escape(labels[0]) if labels else ""
        return '<div class="eq"%s>%s<span class="md">%s</span></div>' % (ident, anchors, html.escape(tex, quote=False))

    # -- references -----------------------------------------------------------

    def ref_groups(self, labels):
        groups = []
        for label in labels:
            label = label.strip()
            num, kind = self.num.labels.get(label, "??"), self.num.kinds.get(label, "")
            words = checker.KIND_WORDS.get(kind, ("", ""))
            if kind == "enumi":
                words = ("item", "items")
            elif kind == "equation":
                words = ("", "")
            if groups and groups[-1][0] == words:
                groups[-1][1].append((label, num, kind))
            else:
                groups.append((words, [(label, num, kind)]))
        return groups

    def ref_text(self, labels):
        parts = []
        for (single, plural), refs in self.ref_groups(labels):
            nums = ["(%s)" % n if k == "equation" else n for _, n, k in refs]
            word = single if len(nums) == 1 else plural
            parts.append((word + " " if word else "") + checker.and_join(nums))
        return checker.and_join(parts)

    def ref_html(self, labels, style="cref"):
        parts = []
        for (single, plural), refs in self.ref_groups(labels):
            links = []
            for label, num, kind in refs:
                shown = "(%s)" % num if kind == "equation" or style == "eqref" else num
                links.append((label, shown))
            if style != "cref":
                parts.append(checker.and_join('<a class="ref" href="#%s">%s</a>' % (html.escape(l), s)
                                              for l, s in links))
                continue
            word = single if len(links) == 1 else plural
            if len(links) == 1:
                parts.append('<a class="ref" href="#%s">%s%s</a>'
                             % (html.escape(links[0][0]), word + "\u00a0" if word else "", links[0][1]))
            else:
                joined = checker.and_join('<a class="ref" href="#%s">%s</a>' % (html.escape(l), s)
                                          for l, s in links)
                parts.append((word + "\u00a0" if word else "") + joined)
        return checker.and_join(parts)

    def cite_html(self, keys, note):
        links = ['<a class="cite" href="#bib-%s">%s</a>' % (html.escape(k.strip()),
                                                          html.escape(self.cites.get(k.strip(), k.strip())))
                 for k in keys.split(",")]
        return "[" + ", ".join(links) + (", " + note if note else "") + "]"

    # -- inline text ------------------------------------------------------------

    def inline(self, tex):
        if not tex:
            return ""
        out, plain = [], []
        i = 0

        def flush():
            if plain:
                run = "".join(plain)
                run = run.replace("---", "\u2014").replace("--", "\u2013")
                run = run.replace("``", "\u201c").replace("''", "\u201d").replace("`", "\u2018")
                run = run.replace("'", "\u2019").replace("~", "\u00a0")
                out.append(html.escape(re.sub(r"\s+", " ", run), quote=False))
                plain.clear()

        def emit(markup):
            flush()
            out.append(markup)

        while i < len(tex):
            c = tex[i]
            if c == "\x00":
                end = tex.index("\x00", i + 1)
                math = '<span class="m">%s</span>' % html.escape(self.math[int(tex[i + 1:end])], quote=False)
                punct = re.match(r"[,.;:!?)\]]+", tex[end + 1:])
                if punct:  # keep trailing punctuation on the formula's line
                    math = '<span class="mw">%s%s</span>' % (math, html.escape(punct.group()))
                    end += punct.end()
                emit(math)
                i = end + 1
            elif c == "\x03":
                i = tex.index("\x03", i + 1) + 1
            elif c == "{":
                inner, j = group_at(tex, i)
                if inner is None:
                    i = j
                    continue
                style = re.match(r"\\(em|it|bf|tt|sc|itshape|bfseries|ttfamily|scshape)(?![A-Za-z])\s*", inner)
                if style:
                    tag = STYLES[style.group(1)]
                    emit("<%s>%s</%s>" % (tag, self.inline(inner[style.end():]), tag.split()[0]))
                else:
                    emit(self.inline(inner))
                i = j
            elif c == "}":
                i += 1
            elif c == "\\":
                match = re.match(r"\\([A-Za-z]+)\*?|\\(.)", tex[i:])
                i += match.end()
                symbol, name = match.group(2), match.group(1)
                if symbol is not None:
                    if symbol == "\\":
                        _, i = read_optional(tex, i)
                        emit("<br>")
                    elif symbol in ACCENTS:
                        arg, j = read_group(tex, i)
                        if arg is None:
                            arg, j = tex[i], i + 1
                        plain.append(accented(arg, symbol))
                        i = j
                    elif symbol in SYMBOLS:
                        plain.append(SYMBOLS[symbol])
                    else:
                        plain.append({",": "\u2009", ";": " ", " ": " ", "!": "", "/": "", "-": "\u00ad",
                                      "@": ""}.get(symbol, symbol))
                    continue
                i = self.command(name, tex, i, emit, plain)
            else:
                plain.append(c)
                i += 1
        flush()
        return "".join(out)

    def command(self, name, tex, i, emit, plain):
        """Handle \\name at tex[i:] (just after the name); returns the new index."""
        if name in ACCENTS:
            arg, j = read_group(tex, i)
            if arg is None:
                j = i + (1 if tex[i:i + 1] == " " else 0)
                arg, j = tex[j], j + 1
            plain.append(accented(arg, name))
            return j
        if name in ("Cref", "cref", "ref", "eqref", "autoref"):
            labels, i = read_group(tex, i)
            emit(self.ref_html(labels.split(","), {"ref": "ref", "eqref": "eqref"}.get(name, "cref")))
        elif name == "hyperref":
            label, i = read_optional(tex, i)
            body, i = read_group(tex, i)
            emit('<a class="ref" href="#%s">%s</a>' % (html.escape(label or ""), self.inline(body)))
        elif name in ("cite", "citep", "citet"):
            note, i = read_optional(tex, i)
            keys, i = read_group(tex, i)
            emit(self.cite_html(keys, self.inline(note) if note else None))
        elif name in ("emph", "textit", "textsl"):
            body, i = read_group(tex, i)
            emit("<em>%s</em>" % self.inline(body))
        elif name == "textbf":
            body, i = read_group(tex, i)
            emit("<strong>%s</strong>" % self.inline(body))
        elif name == "textsc":
            body, i = read_group(tex, i)
            emit('<span class="sc">%s</span>' % self.inline(body))
        elif name in ("texttt", "nolinkurl", "path", "detokenize"):
            body, i = read_group(tex, i)
            text = re.sub(r"\\([_%&#$])", r"\1", body)
            emit("<code>%s</code>" % html.escape(text))
        elif name == "url":
            body, i = read_group(tex, i)
            emit('<a href="%s">%s</a>' % (html.escape(body), html.escape(body)))
        elif name == "href":
            url, i = read_group(tex, i)
            body, i = read_group(tex, i)
            url = url.replace("\\#", "#").replace("\\%", "%").replace("\\_", "_")
            if url.startswith("mailto:"):
                emit(self.inline(body))
            else:
                emit('<a href="%s">%s</a>' % (html.escape(url), self.inline(body)))
        elif name == "texorpdfstring":
            body, i = read_group(tex, i)
            _, i = read_group(tex, i)
            emit(self.inline(body))
        elif name in ("textup", "textrm", "textnormal", "mbox", "text", "textsf", "textmd", "hbox"):
            body, i = read_group(tex, i)
            emit(self.inline(body))
        elif name == "shortstack":
            _, i = read_optional(tex, i)
            body, i = read_group(tex, i)
            emit(self.inline(body))
        elif name == "parbox":
            _, i = read_optional(tex, i)
            _, i = read_group(tex, i)
            body, i = read_group(tex, i)
            emit(self.inline(body))
        elif name == "verbatimblock":
            n, i = read_group(tex, i)
            emit('<pre class="verbatim">%s</pre>' % html.escape(self.verbatim[int(n)].rstrip("\n")))
        elif name in ("footnotemark", "thanks", "footnote"):
            _, i = read_optional(tex, i)
            if name != "footnotemark":
                _, i = read_group(tex, i)
        elif name == "newblock":
            plain.append(" ")
        elif name in ("quad", "qquad", "enspace", "thinspace"):
            plain.append(" ")
        elif name in SYMBOLS:
            plain.append(SYMBOLS[name])
        elif name in LETTERS:
            plain.append(LETTERS[name])
            if i < len(tex) and tex[i] == " ":
                i += 1
        elif name in DROP:
            if name == "embedfile":
                _, i = read_optional(tex, i)
            for _ in range(DROP[name]):
                _, i = read_group(tex, i)
        elif name in IGNORE or name in STYLES:
            pass
        else:
            body, j = read_group(tex, i)
            if body is not None:
                emit(self.inline(body))
                i = j
        return i

    # -- blocks -----------------------------------------------------------------

    BLOCK = re.compile(
        r"\\(?P<sec>section|subsection|subsubsection|paragraph)(?P<star>\*?)(?![A-Za-z])"
        r"|\\begin\{(?P<env>[A-Za-z*]+)\}"
        r"|\\\[(?P<disp>)"
        r"|(?P<par>\n[ \t]*\n\s*|\\par(?![A-Za-z]))"
        r"|\\(?P<item>item)(?![A-Za-z])"
        r"|\\(?P<bib>bibliography)\{[^}]*\}")

    def blocks(self, tex, lead=None):
        """HTML for a run of paragraphs. Displays and lists stay inside their
        paragraph; theorems, proofs, headings, tables and figures end it."""
        out, para = [], []
        state = dict(lead=lead)

        def text(fragment):
            if fragment.strip() or state["lead"]:
                if state["lead"]:
                    para.append(state["lead"] + " ")
                    state["lead"] = None
                para.append(self.inline(fragment))

        def close():
            content = "".join(para).strip()
            if content:
                out.append('<div class="p">%s</div>' % content)
            para.clear()

        def block(markup):
            close()
            out.append(markup)

        i = 0
        while True:
            match = self.BLOCK.search(tex, i)
            if not match:
                text(tex[i:])
                break
            text(tex[i:match.start()])
            i = match.end()
            g = next(name for name, value in match.groupdict().items() if value is not None)
            if g == "par":
                close()
            elif g == "disp":
                end = tex.index("\\]", i)
                if state["lead"]:
                    text("")
                body = tex[i:end]
                if "\\begin{tikzcd}" in body:
                    para.append(self.diagram(body, len(self.paper["diagrams"])))
                    self.paper["diagrams"].append(body)
                else:
                    para.append(self.display("\\[", body, None))
                i = end + 2
            elif g == "item":
                text("")  # stray \item outside a list
            elif g == "bib":
                if self.paper["bibliography_html"]:
                    self.sections.append(dict(id="references", number="", title="References", level=1))
                block(self.paper["bibliography_html"])
            elif g == "sec":
                close()
                i = self.heading(match, tex, i, out, state)
            else:
                env = match.group("env")
                body_start = i
                end, after = matching_end(tex, env, body_start)
                body = tex[body_start:end]
                i = after
                if env in DISPLAYS:
                    if state["lead"]:
                        text("")
                    marker, rest = take_marker(body, 0)
                    para.append(self.display(env, body[rest:], marker[1] if marker else None))
                elif env in ("enumerate", "itemize"):
                    if state["lead"]:
                        text("")
                    para.append(self.listing(env, body))
                elif env in self.theorems:
                    block(self.theorem(env, body))
                elif env == "proof":
                    block(self.proof(body))
                elif env == "abstract":
                    block('<section class="abstract"><h2 class="abstract-head">Abstract</h2>%s</section>'
                          % self.blocks(body))
                elif env == "table":
                    block(self.table_float(body))
                elif env == "figure":
                    block(self.figure(body))
                elif env == "center":
                    block('<div class="center">%s</div>' % self.blocks(body))
                elif env == "minipage":
                    _, k = read_optional(body, 0)
                    width, k = read_group(body, k)
                    frac = re.match(r"\s*([\d.]+)\\(?:textwidth|linewidth|columnwidth)", width or "")
                    basis = "%.0f%%" % (100 * float(frac.group(1))) if frac else "100%"
                    block('<div class="minipage" style="--mp:%s">%s</div>' % (basis, self.blocks(body[k:])))
                elif env == "tikzpicture":
                    block(self.tikz(body))
                elif env == "tabular":
                    block(self.tabular(body))
                elif env in ("quote", "quotation"):
                    block("<blockquote>%s</blockquote>" % self.blocks(body))
                elif env == "document":
                    block(self.blocks(body))
                else:
                    text(body)
        close()
        return "".join(out)

    def heading(self, match, tex, i, out, state):
        level = match.group("sec")
        marker, i = take_marker(tex, i)
        _, i = read_optional(tex, i)
        title, i = read_group(tex, i)
        label = re.match(r"\s*\\label\{([^}]*)\}", tex[i:])
        if label:
            i += label.end()
        title_html = self.inline(self.protect_math(title) if "\x00" not in title else title)
        if level == "paragraph":
            state["lead"] = '<strong class="runin">%s</strong>' % title_html
            return i
        number = marker[1] if marker else ""
        ident = label.group(1) if label else "sec-" + (number or re.sub(r"\W+", "-", title).strip("-").lower())
        tag = {"section": "h2", "subsection": "h3", "subsubsection": "h4"}[level]
        self.sections.append(dict(id=ident, number=number, title=title_html,
                                  level={"section": 1, "subsection": 2, "subsubsection": 3}[level]))
        out.append('<%s class="h" id="%s">%s<span class="h-text">%s</span></%s>'
                   % (tag, html.escape(ident), '<span class="h-num">%s</span>' % number if number else "",
                      title_html, tag))
        return i

    def theorem(self, env, body):
        marker, j = take_marker(body, 0)
        number = marker[1] if marker else ""
        title, j = read_optional(body, j)
        label = re.match(r"\s*\\label\{([^}]*)\}", body[j:])
        word, style = self.theorems[env]
        ident = "%s-%s-%s" % (self.paper["key"], env, number)
        anchor = label.group(1) if label else ident
        self.statement_ids[ident] = anchor
        head = '<span class="thm-name">%s %s</span>' % (word, number)
        if title:
            title_html = self.inline(title)
            self.titles[ident] = title_html
            head += ' <span class="thm-title">(%s)</span>' % title_html
        head = '<span class="thm-head">%s.</span>' % head
        return ('<section class="thm thm-%s" id="%s" data-stmt="%s" data-kind="%s">%s</section>'
                % (style, html.escape(anchor), ident, env, self.blocks(body[j:], lead=head)))

    def proof(self, body):
        title, j = read_optional(body, 0)
        head = '<span class="proof-head">%s.</span>' % (self.inline(title) if title else "Proof")
        inner = self.blocks(body[j:], lead=head)
        qed = '<span class="qed" aria-label="End of proof"></span>'
        if inner.endswith("</div>"):
            inner = inner[:-len("</div>")] + qed + "</div>"
        else:
            inner += '<div class="p">%s</div>' % qed
        return '<div class="proof">%s</div>' % inner

    def listing(self, env, body):
        _, j = read_optional(body, 0)
        body, cuts, depth = body[j:], [], 0
        for match in re.finditer(r"\\(begin|end)\{(enumerate|itemize)\}|\\item(?![A-Za-z])", body):
            if match.group(1):
                depth += 1 if match.group(1) == "begin" else -1
            elif depth == 0:
                cuts.append(match.start())
        items = [body[a + len("\\item"):b] for a, b in zip(cuts, cuts[1:] + [len(body)])]
        out = []
        for item in items:
            marker, k = take_marker(item, 0)
            label = marker[1] if marker else ""
            custom, k2 = read_optional(item, k)
            if custom is not None:
                k = k2
            anchor = re.match(r"\s*\\label\{([^}]*)\}", item[k:])
            ident = ' id="%s"' % html.escape(anchor.group(1)) if anchor else ""
            out.append('<li%s><span class="li-label">%s</span><div class="li-body">%s</div></li>'
                       % (ident, self.inline(label), self.blocks(item[k:])))
        tag = "ol" if env == "enumerate" else "ul"
        return '<%s class="list">%s</%s>' % (tag, "".join(out), tag)

    def tabular(self, body):
        spec, j = read_group(body, 0)
        aligns = [c for c in re.sub(r"@\{[^}]*\}|p\{[^}]*\}|\|", "", spec or "") if c in "lcr"]
        rows, out, rule = split_top(body[j:], "\\\\"), [], False
        header_done = "\\midrule" not in body
        for row in rows:
            rules = re.findall(r"\\(toprule|midrule|bottomrule|hline)", row)
            row = re.sub(r"\\(toprule|midrule|bottomrule|hline)", "", row)
            if rules and not row.strip():
                rule = True
                if "midrule" in rules:
                    header_done = True
                continue
            if "midrule" in rules:
                header_done = True
            rule = rule or bool({"midrule", "hline"} & set(rules))
            cells = split_top(row, "&")
            if not "".join(cells).strip():
                continue
            tag = "td" if header_done else "th"
            html_cells = []
            for k, cell in enumerate(cells):
                span = re.match(r"\s*\\multicolumn\{(\d+)\}\{[^}]*\}", cell)
                extra = ""
                if span:
                    content, _ = read_group(cell, span.end())
                    cell, extra = content, ' colspan="%s"' % span.group(1)
                align = aligns[k] if k < len(aligns) else "l"
                html_cells.append('<%s class="a%s"%s>%s</%s>' % (tag, align, extra, self.inline(cell.strip()), tag))
            out.append('<tr%s>%s</tr>' % (' class="rule"' if rule else "", "".join(html_cells)))
            rule = False
        return '<div class="table-scroll"><table class="tab">%s</table></div>' % "".join(out)

    def caption(self, body):
        match = re.search(r"\\caption(?![A-Za-z])", body)
        if not match:
            return None, None, body
        marker, j = take_marker(body, match.end())
        text, k = read_group(body, j)
        label = re.match(r"\s*\\label\{([^}]*)\}", body[k:])
        end = k + (label.end() if label else 0)
        rest = body[:match.start()] + body[end:]
        return (marker[1] if marker else ""), (text, label.group(1) if label else None), rest

    def table_float(self, body):
        _, j = read_optional(body, 0)
        number, (text, label), rest = self.caption(body[j:])
        inner = self.blocks(rest)
        cap = '<figcaption><span class="cap-num">Table %s.</span> %s</figcaption>' % (number, self.inline(text))
        ident = ' id="%s"' % html.escape(label) if label else ""
        return '<figure class="float table"%s>%s%s</figure>' % (ident, inner, cap)

    def figure(self, body):
        _, j = read_optional(body, 0)
        number, (text, label), rest = self.caption(body[j:])
        cap = '<figcaption><span class="cap-num">Figure %s.</span> %s</figcaption>' % (number, self.inline(text))
        ident = ' id="%s"' % html.escape(label) if label else ""
        self.in_figure = True
        try:
            inner = '<div class="fig-body">%s</div>' % self.blocks(rest)
        except tikz_html.Unsupported as error:
            warn("Figure %s: %s; using the image cut from the PDF instead" % (number, error))
            inner = self.figure_image("figure", number, text)
        finally:
            self.in_figure = False
        return '<figure class="float fig"%s>%s%s</figure>' % (ident, inner, cap)

    def tikz(self, body):
        """A tikzpicture drawn as SVG with HTML labels. Inside a figure an
        unsupported picture makes the whole figure fall back to the PDF."""
        try:
            return tikz_html.picture(body, self.inline)
        except tikz_html.Unsupported as error:
            if self.in_figure:
                raise
            warn("A picture outside a figure: %s; it is left out" % error)
            return '<div class="fig-missing">This picture is in the PDF.</div>'

    def diagram(self, body, k):
        """A displayed tikz-cd diagram as a grid, or the image cut from the PDF."""
        match = re.search(r"\\begin\{tikzcd\}(.*)\\end\{tikzcd\}", body, re.S)
        try:
            return '<div class="eq cd-wrap">%s</div>' % tikz_html.cd_matrix(match.group(1), self.math_tex)
        except tikz_html.Unsupported as error:
            warn("Diagram %d: %s; using the image cut from the PDF instead" % (k + 1, error))
            return self.figure_image("diagram", k, None)

    def figure_image(self, kind, number, caption):
        found = self.figure_images(kind, number)
        if not found:
            return '<div class="fig-missing">%s %s is in the PDF.</div>' % (kind.capitalize(), number)
        path, width, height = found
        alt = "Figure %s" % number if kind == "figure" else "Commutative diagram"
        return ('<img class="fig-img" src="%s" alt="%s" width="%d" height="%d" loading="lazy">'
                % (path, alt, width, height))


# ---------------------------------------------------------------------------
# Figures from the PDF

def crop_figures(pdf_path, figures, diagrams, out_dir, prefix):
    """Cut each float figure (above its caption) and each displayed diagram
    (after the text that precedes it) from the PDF as a PNG image."""
    import pymupdf

    doc = pymupdf.open(pdf_path)
    names = doc.resolve_names()
    made = {}

    def save(pno, rect, name):
        rect = rect & doc[pno].rect
        pix = doc[pno].get_pixmap(matrix=pymupdf.Matrix(3.5, 3.5), clip=rect, alpha=False)
        pix.save(out_dir / name)
        return name, round(rect.width * 4 / 3), round(rect.height * 4 / 3)

    def elements(page):
        """Drawings and text lines; text lines that are body text or headings
        (wide, or set larger than the body) are marked as stops."""
        rects = [(pymupdf.Rect(d["rect"]), False) for d in page.get_drawings()]
        for block in page.get_text("dict")["blocks"]:
            for line in block.get("lines", []):
                spans = [s for s in line["spans"] if s["text"].strip()]
                if spans:
                    r = pymupdf.Rect(line["bbox"])
                    stop = (r.width > 0.8 * (page.rect.width - 144) and r.height < 16) or \
                        max(s["size"] for s in spans) >= 11.5
                    rects.append((r, stop))
        return rects

    for number in figures:
        dest = names.get("figure.%s" % number)
        if not dest:
            continue
        page = doc[dest["page"]]
        caption = next((r for r in page.search_for("Figure %s:" % number)), None)
        if caption is None:
            continue
        above = sorted(((r, stop) for r, stop in elements(page) if r.y1 <= caption.y0 + 1 and r.y0 >= 50),
                       key=lambda e: -e[0].y1)
        box = None
        for r, stop in above:
            if stop:
                break  # body text or a heading above the float
            box = pymupdf.Rect(r) if box is None else box | r
        if box is None:
            continue
        made[("figure", number)] = save(dest["page"], box + (-6, -6, 6, 4),
                                        "%s-figure-%s.png" % (prefix, number))
    for k, (before, after) in diagrams.items():
        for pno in range(doc.page_count):
            page = doc[pno]
            hits = page.search_for(before)
            if not hits:
                continue
            start = hits[-1].y1
            rest = sorted(((r, stop) for r, stop in elements(page) if r.y0 > start + 1),
                          key=lambda e: e[0].y0)
            box = None
            for r, stop in rest:
                if stop or (box is not None and r.y0 > box.y1 + 24):
                    break  # body text or a heading after the display
                if after and page.search_for(after, clip=r + (-2, -2, 2, 2)):
                    break
                box = pymupdf.Rect(r) if box is None else box | r
            if box is not None:
                made[("diagram", k)] = save(pno, box + (-8, -6, 8, 6), "%s-diagram-%d.png" % (prefix, k + 1))
            break
    return made


def check_pdf(pdf_path, numbering, theorems):
    """Theorem, equation and section numbers must match the PDF's destinations."""
    import pymupdf

    names = pymupdf.open(pdf_path).resolve_names()
    problems = []
    pdf_thms = {k for k in names if k.split(".", 1)[0] in theorems}
    ours = {"%s.%s" % (s["kind"], s["number"]) for s in numbering.statements}
    if pdf_thms != ours:
        problems.append("statements only in the PDF: %s; only in the source: %s"
                        % (sorted(pdf_thms - ours)[:8], sorted(ours - pdf_thms)[:8]))
    pdf_eqs = {k.split(".", 1)[1] for k in names if k.startswith("equation.")}
    if pdf_eqs != set(numbering.equations):
        problems.append("equations only in the PDF: %s; only in the source: %s"
                        % (sorted(pdf_eqs - set(numbering.equations))[:8],
                           sorted(set(numbering.equations) - pdf_eqs)[:8]))
    pdf_secs = {k.split(".", 1)[1] for k in names if k.startswith(("section.", "subsection.", "appendix.",
                                                                    "subsubsection."))}
    ours = {n for _, n in numbering.sections}
    if not ours <= pdf_secs:
        problems.append("sections not in the PDF: %s" % sorted(ours - pdf_secs)[:8])
    return problems


# ---------------------------------------------------------------------------

def plain_title(tex):
    tex = re.sub(r"\\texorpdfstring\{((?:[^{}]|\{[^{}]*\})*)\}\{((?:[^{}]|\{[^{}]*\})*)\}", r"\2", tex)
    return " ".join(re.sub(r"\\[A-Za-z]+\s*|[{}]", "", tex).split())


def convert(tex_path, entries, key, pdf_path=None, figure_dir=None):
    """The paper as HTML with its outline and KaTeX macros. Exits if its
    numbered statements differ from coverage.json or, given the PDF, if its
    numbers differ from the PDF's."""
    tex_path = Path(tex_path)
    source, verbatim = load(tex_path)
    preamble, _, body = source.partition("\\begin{document}")
    body = body.split("\\end{document}")[0]
    theorems = theorem_styles(preamble)
    macros = checker.parse_macros(source)
    macros["\\textup"] = "\\textrm{#1}"
    bbl = tex_path.with_suffix(".bbl")
    bib = bibliography(bbl.read_text()) if bbl.exists() else []

    numbering = Numbering(body, theorems)
    listed = [(e["kind"], e["number"]) for e in entries]
    found = [(s["kind"], s["number"]) for s in numbering.statements]
    problems = []
    if listed != found:
        first = next((k for k, (a, b) in enumerate(zip(listed, found)) if a != b), min(len(listed), len(found)))
        problems.append("%d numbered statements in the source, %d in coverage.json; first difference at "
                        "position %d: %s vs %s" % (len(found), len(listed), first + 1,
                                                   found[first:first + 1], listed[first:first + 1]))
    for entry, statement in zip(entries, numbering.statements):
        if entry["label"] and statement["label"] != entry["label"]:
            problems.append("%s %s is labelled %s in the source, %s in coverage.json"
                            % (entry["kind"], entry["number"], statement["label"], entry["label"]))
    if pdf_path and Path(pdf_path).exists():
        problems += check_pdf(pdf_path, numbering, theorems)
    fail(problems, "%s does not match coverage.json or its PDF" % tex_path)

    annotated = numbering.annotate(body)
    paper = dict(key=key, diagrams=[])

    diagram_anchors = []
    for match in re.finditer(r"\\\[\s*\\begin\{tikzcd\}", annotated):
        before = plain_title(annotated[max(0, match.start() - 400):match.start()])
        before = " ".join(before.split()[-5:])
        after = plain_title(annotated[matching_end(annotated, "tikzcd", match.end())[1]:][:300])
        after = " ".join(re.sub(r"^\\\]|[^\w\s-]", " ", after).split()[:2])
        diagram_anchors.append((before, after))
    made = {}

    def figure_images(kind, number):
        """Cut a figure or diagram from the PDF, only when it cannot be drawn."""
        if (kind, number) not in made and pdf_path and Path(pdf_path).exists() and figure_dir is not None:
            figure_dir.mkdir(parents=True, exist_ok=True)
            made.update(crop_figures(pdf_path, [number] if kind == "figure" else [],
                                     {number: diagram_anchors[number]} if kind == "diagram" else {},
                                     figure_dir, key))
        found = made.get((kind, number))
        return (figure_dir.name + "/" + found[0], found[1], found[2]) if found else None

    conv = Converter(paper, numbering, theorems, bib, verbatim, figure_images)
    paper["bibliography_html"] = bibliography_html(conv, bib)
    annotated = conv.protect_math(annotated)

    title = re.search(r"\\title\{", preamble)
    title_tex, _ = checker.read_group(preamble, title.end() - 1) if title else ("", 0)
    author = re.search(r"\\author\{", preamble)
    author_tex, _ = checker.read_group(preamble, author.end() - 1) if author else ("", 0)
    affiliations = [conv.inline(conv.protect_math(t)) for t in re.findall(r"\\thanks\{([^}]*)\}", author_tex)]
    authors = []
    for part in author_tex.split("\\and"):
        lines = [conv.inline(conv.protect_math(l)).strip() for l in split_top(part, "\\\\")]
        lines = [l for l in lines if l]
        if lines:
            authors.append('<span class="author"><span class="author-name">%s</span>%s</span>' % (
                lines[0], "".join('<span class="author-mail">%s</span>' % l for l in lines[1:])))
    head = ('<header class="title-block"><h1 class="doc-title">%s</h1><div class="authors">%s</div>%s</header>'
            % (conv.inline(title_tex).strip(), "".join(authors),
               "".join('<p class="affil">%s</p>' % a for a in affiliations)))
    content = conv.blocks(annotated)
    chapters, current = [], []
    for piece in re.split(r'(?=<h2 class="h")', content):
        if piece.startswith('<h2 class="h"'):
            if current:
                chapters.append(current)
            current = [piece]
        else:
            current.append(piece)
    chapters.append(current)
    html_out = head + "".join('<section class="chapter">%s</section>' % "".join(c) for c in chapters if c)
    missing = [e for e in entries if "%s-%s-%s" % (key, e["kind"], e["number"]) not in conv.statement_ids]
    fail(["%s %s" % (e["kind"], e["number"]) for e in missing], "%s: statements not rendered" % tex_path)
    return dict(html=html_out, sections=conv.sections, macros=macros,
                anchors=conv.statement_ids, titles=conv.titles,
                figures=sorted(name for name, _, _ in made.values()))


def bibliography_html(conv, bib):
    if not bib:
        return ""
    items = "".join('<li id="bib-%s"><span class="bib-label">[%s]</span><span class="bib-text">%s</span></li>'
                    % (html.escape(k), html.escape(label), conv.inline(conv.protect_math(body)))
                    for k, label, body in bib)
    return '<h2 class="h" id="references"><span class="h-text">References</span></h2><ol class="bib">%s</ol>' % items
