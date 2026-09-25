#!/usr/bin/env python3
"""Build docs/index.html, a reader that sets each paper, rendered from its LaTeX
source, beside the Lean declarations of the numbered statement being read.

Run from the repository root:

    pip install pymupdf
    python3 scripts/site/build_reader.py

Nothing needs to be compiled. The script reads docs/coverage.json, the Lean
sources and, for each paper, its LaTeX source with the .bbl of a pdflatex
run (paper/CI2ZF-main and paper/CI2ZF-appendix) and the compiled PDF
(docs/main.pdf and docs/appendix.pdf). paper_html.py renders the source,
numbers it as LaTeX does, and stops the build if a numbered statement differs
from coverage.json or a theorem, equation or section number differs from the
PDF's hyperref destinations. Figures and tikz-cd diagrams are drawn from
their TikZ source by tikz_html.py; one it cannot read is cut from the PDF into
docs/figures instead.
A paper whose source is absent is listed statement by statement. Lean
declarations are located by scanning the sources for their namespaces and
declaration keywords. Source links are pinned to the last commit that
changed the Lean sources, so commit Lean changes first.

The statement-by-statement checker built by build.py lives at docs/checker.html;
the reader links each headline result to its card there.
"""
import argparse
import datetime
import json
import re
import sys
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import build as checker  # noqa: E402  (statuses, headline cards, cited results)
import richtext  # noqa: E402

REPO = checker.REPO
TEMPLATE = Path(__file__).resolve().parent / "reader.html"
PAPERS = {
    "main": dict(title="Coupling Independence Implies Zero-Freeness", short="Main paper",
                 tex="paper/CI2ZF-main/main.tex", pdf="docs/main.pdf"),
    "companion": dict(title="Further Potts Zero-Free Regions from Coupling Independence",
                      short="Companion", tex="paper/CI2ZF-appendix/main.tex", pdf="docs/appendix.pdf"),
}
AUTHORS = "Shuai Shao and Ke Shi"
SIGNATURE_LINES = 40

# ---------------------------------------------------------------------------
# Lean sources

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom)\b\s*"
    r"(?P<name>[^\s:({\[]+)?")
CONTINUATION = ("|", "where", "deriving", "termination_by", "decreasing_by", ":=")


def index_file(path):
    """The named declarations of one Lean file, with full names and line ranges.
    A declaration starts at its docstring or attributes and ends at the last code
    line before the next top-level command."""
    lines = path.read_text().splitlines()
    stack, decls = [], []
    comment, lead, cur, last = 0, None, None, 0
    for i, line in enumerate(lines):
        if comment:
            comment = max(comment + line.count("/-") - line.count("-/"), 0)
            continue
        stripped = line.strip()
        top = not line[:1].isspace()
        if top and stripped.startswith("/-"):
            if cur is not None:
                cur["end"], cur = last + 1, None
            if stripped.startswith("/--"):
                lead = i
            comment = max(stripped.count("/-") - stripped.count("-/"), 0)
            last = i
            continue
        if not top or not stripped:
            if stripped and not stripped.startswith("--"):
                last = i
            continue
        if stripped.startswith("--"):
            continue
        if cur is not None and not stripped.startswith(CONTINUATION):
            cur["end"], cur = last + 1, None
        match = DECL.match(stripped)
        if match and match.group("name"):
            name = match.group("name")
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join([c for comps in stack for c in comps] + [name])
            cur = dict(name=full, kind=match.group("kind"), start=(i if lead is None else lead) + 1)
            decls.append(cur)
            lead, last = None, i
            continue
        if stripped.startswith("@["):
            lead = i if lead is None else lead
            last = i
            continue
        lead = None
        words = stripped.split()
        if words[0] == "namespace":
            stack.append(words[1].split("."))
        elif words[0] == "section" or stripped.startswith("noncomputable section"):
            stack.append([])
        elif words[0] == "end" and stack:
            stack.pop()
        last = i
    if cur is not None:
        cur["end"] = last + 1
    return decls


def lean_index():
    found = {}
    for path in sorted((REPO / "CI2ZF").rglob("*.lean")):
        rel = path.relative_to(REPO).as_posix()
        for decl in index_file(path):
            decl["path"] = rel
            found.setdefault(decl["name"], decl)
    return found


def lean_excerpt(decl):
    """Docstring and statement of a declaration; theorems stop before the proof."""
    lines = (REPO / decl["path"]).read_text().splitlines()
    block = "\n".join(lines[decl["start"] - 1:decl["end"]])
    doc = None
    match = re.match(r"\s*/--(.*?)-/\s*\n?", block, re.S)
    if match:
        doc = " ".join(match.group(1).split())
        block = block[match.end():]
    if decl["kind"] in ("theorem", "lemma"):
        end = re.search(r":=(?:\s*by)?[ \t]*(?:\n|$)", block)
        cut = end.start() if end else block.find(":=")
        if cut >= 0:
            block = block[:cut]
    code = textwrap.dedent(block).strip("\n").rstrip().splitlines()
    more = max(len(code) - SIGNATURE_LINES, 0)
    return doc, "\n".join(code[:SIGNATURE_LINES]), more


# ---------------------------------------------------------------------------
# Data

def build_data(args):
    if checker.git("status", "--porcelain", "--", "CI2ZF", "CI2ZF.lean"):
        sys.exit("Commit the Lean sources first, so that source links are pinned.")
    commit = checker.git("log", "-1", "--format=%h", "--abbrev=7", "--", "CI2ZF", "CI2ZF.lean",
                         "lakefile.toml", "lean-toolchain", "lake-manifest.json")
    coverage = json.loads((REPO / checker.COVERAGE).read_text())
    record = json.loads((REPO / "docs/verification.json").read_text())
    index = lean_index()

    unknown = sorted({n for entry in coverage for n in entry["lean"] if n not in index})
    if unknown:
        sys.exit("Lean declarations not found in the sources: " + ", ".join(unknown))

    cards = {}
    for result in checker.RESULTS:
        for source, label in result["paper"]:
            cards.setdefault((source, label), result["id"])

    decls = {}
    for name in dict.fromkeys(n for entry in coverage for n in entry["lean"]):
        decl = index[name]
        doc, code, more = lean_excerpt(decl)
        decls[name] = dict(short=checker.short(name), kind=decl["kind"], path=decl["path"],
                           start=decl["start"], end=decl["end"], doc=richtext.rich(doc), code=code, more=more)

    papers = {}
    for key, meta in PAPERS.items():
        entries = [e for e in coverage if e["paper"] == key]
        tex = REPO / getattr(args, key + "_tex")
        pdf = REPO / meta["pdf"]
        body = None
        if tex.exists():
            import paper_html
            body = paper_html.convert(tex, entries, key, pdf if pdf.exists() else None,
                                      REPO / "docs" / "figures")
        statements = []
        for entry in entries:
            statements.append(dict(
                id="%s-%s-%s" % (key, entry["kind"], entry["number"]),
                kind=entry["kind"], word=checker.ENV_WORDS[entry["kind"]], number=entry["number"],
                title=entry["title"], label=entry["label"], status=entry["status"],
                note=richtext.rich(entry["note"]), lean=entry["lean"], card=cards.get((key, entry["label"]))))
            if body and statements[-1]["id"] in body.get("titles", {}):
                statements[-1]["title_html"] = body["titles"][statements[-1]["id"]]
        papers[key] = dict(key=key, title=meta["title"], short=meta["short"], authors=AUTHORS,
                           pdf=pdf.relative_to(REPO / "docs").as_posix() if pdf.exists() else None,
                           statements=statements, **(body or {}))

    statuses = {k: dict(label=v[0], glyph=v[1], tone=v[2], meaning=v[3])
                for k, v in checker.STATUSES.items()}
    cited = [dict(id=c["id"], short=c["short"], source=c["source"], url=c["url"],
                  lean=[checker.short(n) for n in c["proof"]][:2]) for c in checker.CITED]
    return dict(
        commit=commit, github=checker.GITHUB, built=datetime.date.today().isoformat(),
        verification=dict(date=record["date"], lean=record["lean_version"],
                          mathlib=record["mathlib_version"],
                          declarations=record["audited_project_declarations"],
                          modules=record["joint_import_closure_files"],
                          axioms=record["allowed_axioms"], command=record["command"],
                          passed=record["passed"]),
        statuses=statuses, papers=papers, decls=decls, cited=cited,
        default="main" if papers["main"].get("html") or not papers["companion"].get("html")
        else "companion")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--main-tex", default=PAPERS["main"]["tex"],
                        help="main .tex file of the main paper, with its .aux and .bbl beside it")
    parser.add_argument("--companion-tex", default=PAPERS["companion"]["tex"],
                        help="main .tex file of the companion, with its .aux and .bbl beside it")
    parser.add_argument("--out", default="docs/index.html", help="output path, relative to the repository")
    args = parser.parse_args()
    data = build_data(args)
    payload = json.dumps(data, ensure_ascii=False, separators=(",", ":")).replace("</", "<\\/")
    page = TEMPLATE.read_text().replace("@@DATA@@", payload)
    (REPO / args.out).write_text(page)
    for key, paper in data["papers"].items():
        print("%s: %d statements, %s" % (key, len(paper["statements"]),
                                         "rendered from LaTeX" if paper.get("html") else "no LaTeX source"))
    print("Wrote %s with %d Lean declarations, pinned to %s" % (args.out, len(data["decls"]), data["commit"]))


if __name__ == "__main__":
    main()
