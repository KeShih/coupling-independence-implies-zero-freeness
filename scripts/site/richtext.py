"""Typeset the plain-text notes of coverage.json and the Lean docstrings.

Both mix three things: English, formulas written in Unicode with TeX-like
sub- and superscripts (x ∈ (0,1], R_ρ < ∞, Z_G(q; x), ‖h‖₂²), and Lean names
(card_hardList_of_succ_le, τ.toPinningData, lem:soft-stationary). rich()
returns HTML in which formulas become <span class="m">TeX</span> for KaTeX,
Lean names become <code>, and everything else stays text. Backtick segments
of docstrings are code or a formula as a whole. The page shows the original
text wherever KaTeX cannot typeset a formula.
"""
import html
import re
import unicodedata

GREEK = "αβγδεζηθικλμνξοπρστυφχψωϵϑϱϕϖΓΔΘΛΞΠΣΥΦΨΩ"
SUBSCRIPTS = dict(zip("₀₁₂₃₄₅₆₇₈₉₊₋₌₍₎ₐₑₒₓₕₖₗₘₙₚₛₜᵢⱼᵤᵥ", "0123456789+-=()aeoxhklmnpstijuv"))
SUPERSCRIPTS = dict(zip("⁰¹²³⁴⁵⁶⁷⁸⁹⁺⁻⁼⁽⁾ⁱⁿ", "0123456789+-=()in"))
SYMBOLS = {
    "∈": r"\in ", "∉": r"\notin ", "≤": r"\le ", "≥": r"\ge ", "≠": r"\ne ", "⊆": r"\subseteq ",
    "⊂": r"\subset ", "⊇": r"\supseteq ", "∪": r"\cup ", "∩": r"\cap ", "→": r"\to ", "↦": r"\mapsto ",
    "↓": r"\downarrow ", "↑": r"\uparrow ", "∞": r"\infty ", "·": r"\cdot ", "×": r"\times ", "‖": r"\| ",
    "⪰": r"\succeq ", "⪯": r"\preceq ", "∑": r"\sum ", "∏": r"\prod ", "∘": r"\circ ", "≈": r"\approx ",
    "∼": r"\sim ", "~": r"\sim ", "−": "-", "–": "-", "∅": r"\emptyset ", "∀": r"\forall ", "∃": r"\exists ",
    "↔": r"\leftrightarrow ", "⟨": r"\langle ", "⟩": r"\rangle ", "∂": r"\partial ", "…": r"\dots ",
    "ℂ": r"\mathbb{C}", "ℝ": r"\mathbb{R}", "ℕ": r"\mathbb{N}", "ℤ": r"\mathbb{Z}", "ℚ": r"\mathbb{Q}",
    "𝒢": r"\mathcal{G}", "𝓛": r"\mathcal{L}", "𝒰": r"\mathcal{U}", "ℓ": r"\ell ", "√": r"\sqrt",
    "⊈": r"\nsubseteq ", "≰": r"\nleq ", "≱": r"\ngeq ", "≮": r"\nless ", "≯": r"\ngtr ",
    "∧": r"\land ", "∨": r"\lor ", "¬": r"\neg ", "⌊": r"\lfloor ", "⌋": r"\rfloor ", "⌈": r"\lceil ", "⌉": r"\rceil ",
}
ACCENTS = {"̃": r"\tilde", "̲": r"\underline", "̂": r"\hat", "̄": r"\bar", "̇": r"\dot"}
OPERATORS = {"max": r"\max", "min": r"\min", "sup": r"\sup", "inf": r"\inf", "log": r"\log", "exp": r"\exp",
             "liminf": r"\liminf", "limsup": r"\limsup", "lim": r"\lim", "deg": r"\deg", "det": r"\det"}
NAMED = {"Ham", "Var", "Pr", "Cov", "TV", "dist", "girth", "diag", "tr", "Loss", "Gain", "Credit", "SB", "Jh"}
ENGLISH_SHORT = {"of", "in", "at", "on", "to", "is", "as", "by", "an", "or", "if", "be", "we", "it", "no",
                 "so", "up", "do", "and", "the", "for", "with", "from", "are", "its", "per", "via"}
LABEL = re.compile(r"(?:lem|thm|def|prop|cor|rem|eq|sec|app|tab|fig|case):[\w-]+")
IDENT_CHARS = r"A-Za-z0-9'" + GREEK + "₀-₉"


def is_lean_name(word):
    """A Lean declaration or field name rather than a formula."""
    if LABEL.fullmatch(word):
        return True
    if re.search(r"[a-z][A-Z]", word) and re.fullmatch(r"[\w.'" + GREEK + "]+", word):
        return True  # camelCase
    parts = re.split(r"[._]", word)
    if "." in word and len(parts) > 1 and all(parts) and sum(len(p) >= 2 for p in parts) >= 1 \
            and re.fullmatch(r"[\w.'" + GREEK + "]+", word) and not re.fullmatch(r"[\d.]+", word):
        return True  # dotted name
    if "_" in word and sum(len(p) >= 2 and p.isalpha() for p in parts) >= 2:
        return True  # snake_case
    return bool(re.fullmatch(r"[A-Z][a-z]+[A-Z]\w*|[A-Za-z]+\d+[A-Za-z]*", word)) and word not in NAMED


# ---------------------------------------------------------------------------
# To TeX

def to_tex(s):
    """A formula written in Unicode as TeX."""
    s = unicodedata.normalize("NFD", s)
    for base, whole in (("=", "≠"), ("∈", "∉"), ("⊆", "⊈"), ("≤", "≰"), ("≥", "≱"), ("<", "≮"), (">", "≯")):
        s = s.replace(base + "\u0338", whole)  # NFD splits the negated relations; keep them whole
    s = re.sub(r"[_^]\s*$", "", s)
    out, i = [], 0
    while i < len(s):
        c = s[i]
        nxt = s[i + 1] if i + 1 < len(s) else ""
        if nxt in ACCENTS:  # a letter with a combining accent
            out.append("%s{%s}" % (ACCENTS[nxt], c))
            i += 2
            continue
        if c in SUBSCRIPTS or c in SUPERSCRIPTS:
            table, mark = (SUBSCRIPTS, "_") if c in SUBSCRIPTS else (SUPERSCRIPTS, "^")
            run = ""
            while i < len(s) and s[i] in table:
                run += table[s[i]]
                i += 1
            out.append("%s{%s}" % (mark, run))
            continue
        if c in "_^":
            out.append(c)
            i += 1
            if i < len(s) and s[i] == "{":
                depth, j = 0, i
                while j < len(s):
                    depth += {"{": 1, "}": -1}.get(s[j], 0)
                    if depth == 0:
                        break
                    j += 1
                out.append("{" + to_tex(s[i + 1:j]) + "}")
                i = j + 1
            else:
                m = re.match(r"[A-Za-z]{2,}", s[i:])
                if m:
                    out.append(r"{\mathrm{%s}}" % m.group())
                    i += m.end()
                elif i < len(s):
                    sub = to_tex(s[i])
                    out.append("{%s}" % sub)
                    i += 1
            continue
        if c == "√":
            i += 1
            if i < len(s) and s[i] == "(":
                depth, j = 0, i
                while j < len(s):
                    depth += {"(": 1, ")": -1}.get(s[j], 0)
                    if depth == 0:
                        break
                    j += 1
                out.append(r"\sqrt{%s}" % to_tex(s[i + 1:j]))
                i = j + 1
            else:
                m = re.match(r"[A-Za-z0-9" + GREEK + "]", s[i:])
                out.append(r"\sqrt{%s}" % (m.group() if m else ""))
                i += m.end() if m else 0
            continue
        if c in "{}":
            out.append("\\" + c)
            i += 1
            continue
        if c in SYMBOLS:
            out.append(SYMBOLS[c])
            i += 1
            continue
        m = re.match(r"[A-Za-z]{2,}", s[i:])
        if m:
            word = m.group()
            out.append(OPERATORS.get(word, r"\mathrm{%s}" % word))
            i += m.end()
            if i + 1 < len(s) and s[i] == " " and re.match(r"[A-Za-z0-9(" + GREEK + "]", s[i + 1]):
                out.append(r"\;")
            continue
        if c in "%#&$":
            out.append("\\" + c)
        elif c == "\\":
            out.append(r"\backslash ")
        else:
            out.append(c)
        i += 1
    return "".join(out).strip()


# ---------------------------------------------------------------------------
# Finding formulas in prose

ATOM = re.compile(
    r"(?P<tick>`[^`]*`)"
    r"|(?P<name>(?:lem|thm|def|prop|cor|rem|eq|sec|app|tab|fig|case):[\w-]+"
    r"|[" + IDENT_CHARS + r"]+(?:[._][" + IDENT_CHARS + r"]+)+)"
    r"|(?P<word>[A-Za-z]{2,})"
    r"|(?P<space>\s+)"
    r"|(?P<char>.)", re.S)
STRONG = set("∈∉≤≥≠⊆⊂⊇∪∩→↦↓↑∞·×‖⪰⪯∑∏∘≈∼√<>=_^+/") | set(SUBSCRIPTS) | set(SUPERSCRIPTS) | set(GREEK) \
    | set("ℂℝℕℤℚ𝒢𝓛𝒰ℓ∅") | set(ACCENTS)
MATHY = STRONG | set("()[]{}|,;:0123456789.−-'!") | set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")


def classify(tokens):
    """Each token as ('text'|'code'|'math'|'space', string)."""
    out = []
    for kind, tok in tokens:
        if kind == "tick":
            inner = tok[1:-1]
            out.append(("code" if tick_is_code(inner) else "mathtick", inner))
        elif kind == "name":
            if is_lean_name(tok):
                out.append(("code", tok))
            else:
                out.append(("math", tok))
        elif kind == "word":
            if is_lean_name(tok):
                out.append(("code", tok))
            elif tok in OPERATORS or tok in NAMED or (len(tok) == 2 and tok.lower() not in ENGLISH_SHORT
                                                     and not tok.islower()):
                out.append(("mathword", tok))
            else:
                out.append(("text", tok))
        elif kind == "space":
            out.append(("space", tok))
        else:
            out.append(("math" if tok in MATHY else "text", tok))
    return out


def tick_is_code(inner):
    if LABEL.search(inner) or re.search(r":=|=>|\bfun\b|\bType\b|\bProp\b| \^ |\bchoose\b", inner):
        return True
    for word in re.findall(r"[" + IDENT_CHARS + r"]+(?:[._][" + IDENT_CHARS + r"]+)*", inner):
        if is_lean_name(word):
            return True
        if re.fullmatch(r"[A-Za-z]{3,}", word) and word not in OPERATORS and word not in NAMED:
            return True
    return False


def rich(text):
    """HTML for a note or docstring."""
    if not text:
        return ""
    toks = classify([(m.lastgroup, m.group()) for m in ATOM.finditer(text)])
    out, k = [], 0
    while k < len(toks):
        kind, tok = toks[k]
        if kind == "code":
            out.append("<code>%s</code>" % html.escape(tok))
            k += 1
        elif kind == "mathtick":
            out.append(math_span(tok))
            k += 1
        elif kind in ("math", "mathword"):
            j, depth = k, 0
            while j < len(toks):
                jk, jt = toks[j]
                if jk in ("math", "mathword"):
                    if jt in ",;" and depth <= 0 and j > k and j + 1 < len(toks) and toks[j + 1][0] == "space":
                        break  # a list separator in the sentence, not in the formula
                    depth += balance(jt)
                elif not (jk == "space" and j + 1 < len(toks) and toks[j + 1][0] in ("math", "mathword")
                          and "\n" not in jt):
                    break
                j += 1
            j = max(j, k + 1)
            run = "".join(t for _, t in toks[k:j])
            lead, core, trail = split_run(run)
            if core and strong(core):
                out.append(html.escape(lead) + math_span(core) + html.escape(trail))
            else:
                out.append(html.escape(run))
            k = j
        else:
            out.append(html.escape(tok))
            k += 1
    return re.sub(r"\*\*(.+?)\*\*", r"<strong>\1</strong>", "".join(out))


def split_run(run):
    """Peel sentence punctuation and unbalanced brackets off a formula run."""
    lead = re.match(r"^[\s,;:.]*", run).group()
    run = run[len(lead):]
    trail = ""
    while run:
        if run[-1] in " ,;:.!":
            trail = run[-1] + trail
            run = run[:-1]
            continue
        if run[-1] in ")]" and balance(run) < 0:
            trail = run[-1] + trail
            run = run[:-1]
            continue
        break
    while run and run[0] in "([" and balance(run) > 0:
        lead += run[0]
        run = run[1:]
    return lead, run, trail


def balance(s):
    return s.count("(") + s.count("[") - s.count(")") - s.count("]")


def strong(core):
    """A run counts as a formula only with an operator, a script, a Greek
    letter, a function application, an interval, or a named operator."""
    if any(c in STRONG for c in core):
        return True
    if re.search(r"(?<![A-Za-z])[A-Za-z]\(", core):
        return True
    if re.search(r"[\[(]\s*[-\d.]+\s*,\s*[-\d.∞]+\s*[\])]", core):
        return True
    if re.search(r"\b(?:%s)\b" % "|".join(sorted(OPERATORS) + sorted(NAMED)), core):
        return True
    return False


def math_span(src):
    tex = to_tex(src)
    return '<span class="m" data-src="%s">%s</span>' % (html.escape(src, quote=True), html.escape(tex, quote=False))
