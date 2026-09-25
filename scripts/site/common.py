#!/usr/bin/env python3
"""Data and helpers shared by the reader's builders, build_reader.py and
paper_html.py: the formalization statuses, the cited results the library
proves, glosses of the paper's notation, and a few LaTeX helpers."""
import re
import subprocess
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
GITHUB = "https://github.com/KeShih/coupling-independence-implies-zero-freeness"

# Results the papers cite. "statement" lists the Lean propositions that express
# them, "proof" the Lean theorems that prove them, and "targets" the proofs
# whose use marks a result as depending on the citation (default: "proof").
CITED = [
    dict(id="cffgzz", short="CFFGZZ Thm 20",
         statement=["ZeroFreeness.Potts.ExternalCriticalHardColouringTheorem",
                    "ZeroFreeness.Potts.CriticalHardColouringInput"],
         proof=["ZeroFreeness.Potts.external_critical_hard_colouring_theorem",
                "ZeroFreeness.Potts.critical_hard_colouring_input",
                "ZeroFreeness.Appendix.CV.option_root_ci_critical"],
         targets=["ZeroFreeness.Appendix.CV.option_root_ci_critical"],
         source="Chen, Feng, Guo, Zhang, Zou, Deterministic counting from coupling "
                "independence, arXiv:2410.23225v2, Theorem 20",
         url="https://arxiv.org/abs/2410.23225v2",
         meaning="Hard-colouring coupling independence at x = 0 on all graphs of maximum "
                 "degree at most Δ, for arbitrary pinnings, needed at q = 11Δ/6. "
                 "CriticalHardColouringInput is the same bound on boundary-count data.",
         route="Lean does not follow the citation. It extends the Carlson–Vigoda contraction "
               "of Appendix A to q ≥ 11Δ/6 for every Δ ≥ 6, with the same constant "
               "409060125/50858 (option_root_ci_critical). Integer equality 6q = 11Δ forces "
               "Δ ≥ 6, so this covers every critical case."),
    dict(id="clmm-10", short="CLMM Eq. (10)",
         statement=["ZeroFreeness.Appendix.CLMM.Literature"],
         proof=["ZeroFreeness.Appendix.CLMM.Eq10.sphere_estimate_proof", "ZeroFreeness.Appendix.CLMM.literature"],
         targets=["ZeroFreeness.Appendix.CLMM.Eq10.sphere_estimate_proof"],
         source="Chen, Liu, Mani, Moitra, Strong spatial mixing for colorings on trees and "
                "its algorithmic applications, arXiv:2304.01954v3, Equation (10), from "
                "Lemmas 5.19 and 5.20",
         url="https://arxiv.org/abs/2304.01954v3",
         meaning="The formalized interface gives the fixed-base-graph sphere estimate in the "
                 "relative-SSM regime beyond a chosen cutting depth K₀, under all further "
                 "pinnings.",
         route="As in CLMM, through Lemmas 5.19 and 5.20. Lemma 5.19 becomes a finite-sum "
               "decomposition over sphere configurations, and Lemma 5.20 bounds the total "
               "variation by 2ε. The ball around the root is read as a cavity tree; the girth "
               "is used for two facts only: no edge inside a distance layer, and unique parents."),
    dict(id="clmm-513", short="CLMM Lemma 5.13",
         statement=[],
         proof=["ZeroFreeness.Appendix.CLMM.Lemma513.sphere_to_coupling"],
         source="Chen, Liu, Mani, Moitra, arXiv:2304.01954v3, Condition 5.12 and Lemma 5.13",
         url="https://arxiv.org/abs/2304.01954v3",
         meaning="In the positive-activity branch (x > 0, Δ ≥ 3, R ≥ 2), sphere influence "
                 "decay below 1/(8R log Δ) gives the Hamming coupling bound 2Δ^R for the "
                 "two root-child laws.",
         route="As in CLMM, by strong induction on the number of free vertices. If no sphere "
               "vertex is free, the two laws agree off the ball. Otherwise the proof conditions "
               "on the free sphere vertex of least total variation through a maximal coupling; "
               "the conditioned laws are smaller instances. 1 + log ℓ replaces the harmonic "
               "number H_ℓ. The separate zero-temperature colouring endpoint is outside this "
               "formalized proposition."),
    dict(id="clmm-87", short="CLMM Lemma 8.7",
         statement=["ZeroFreeness.Appendix.Girth.CavityTree.CLMMInfluenceIdentity"],
         proof=["ZeroFreeness.Appendix.Girth.CavityTree.clmmInfluenceIdentity"],
         source="Chen, Liu, Mani, Moitra, arXiv:2304.01954v3, Lemma 8.7",
         url="https://arxiv.org/abs/2304.01954v3",
         meaning="The tree influence–Jacobian factorization, summed over a whole tree level.",
         route="Proved from the actual finite-tree Gibbs law, one level at a time."),
    dict(id="bbr-26", short="BBR Prop 2.6(i)",
         statement=["ZeroFreeness.Appendix.BBR.Literature"],
         proof=["ZeroFreeness.Appendix.BBR.proposition_2_6_i_holds", "ZeroFreeness.Appendix.BBR.literature"],
         targets=["ZeroFreeness.Appendix.BBR.proposition_2_6_i_holds"],
         source="Bencs, Berrekkal, Regts, Near optimal bounds for weak and strong spatial "
                "mixing for the anti-ferromagnetic Potts model on trees, Electron. J. Probab. "
                "30 (2025), paper 65, Proposition 2.6(i)",
         url="https://doi.org/10.1214/25-EJP1327",
         meaning="The segment-weight bound for cavity messages, at BBR's printed hypothesis "
                 "Δ ≥ q + 3 and, as the companion extends it, at Δ ≥ q + 2. BBR.Literature "
                 "bundles the printed form with Theorem 2.5.",
         route="Follows BBR Section 4 under the printed hypotheses, but two uses of the "
               "concavity of log, a chord bound and Jensen's inequality, replace their Lemma "
               "4.1 and Lemma 4.2(i); Lemma 4.3 is proved from a derivative. The application "
               "handles the degree-gap-two cases arithmetically; GapTwo reruns the same proof "
               "under Δ ≥ q + 2 (proposition_2_6_i_of_gap_two)."),
    dict(id="bbr-25", short="BBR Thm 2.5",
         statement=[],
         proof=["ZeroFreeness.Appendix.BBR.theorem_2_5_holds"],
         source="Bencs, Berrekkal, Regts, Electron. J. Probab. 30 (2025), paper 65, Theorem 2.5",
         url="https://doi.org/10.1214/25-EJP1327",
         meaning="The squared-norm contraction of the square-root message recursion; the "
                 "theorem_2_5 field of BBR.Literature.",
         route="As in BBR Section 3: the mean value theorem along the segment between the two "
               "message vectors, Cauchy–Schwarz, and the pointwise Jacobian bound."),
]

# The paper's notation: Lean name, TeX symbol and a gloss.
GLOSSARY = [
    ("ZeroFreeness.Potts.normalizedPolynomial", r"\widehat Z^{\tau}_{G}",
     "The normalized pinned polynomial: one monomial per colouring of the free vertices, "
     "counting free–pinned and free–free monochromatic edges."),
    ("ZeroFreeness.Potts.normalizedPartition", r"\widehat Z^{\tau}_{G}(z)", "Its value at z ∈ ℂ."),
    ("ZeroFreeness.Potts.fullPolynomial", r"Z^{\tau}_{G}",
     "The ordinary pinned polynomial, which also counts monochromatic edges inside the pinned set."),
    ("ZeroFreeness.Potts.fullPartition", r"Z^{\tau}_{G}(z)", "Its value at z ∈ ℂ."),
    ("PottsCI.PartialColouring", r"\tau\colon\Lambda\to[q]",
     "A pinning: a finite domain and a colour for each of its vertices. No properness is required."),
    ("PottsCI.PartialColouring.pinnedConflictCount", r"m_G(\tau)",
     "The number of monochromatic edges with both ends pinned."),
    ("ZeroFreeness.pottsInterval", r"[0,1]\subset\mathbb C",
     "Its open ε-neighbourhood Metric.thickening ε pottsInterval is the paper's U_ε([0, 1])."),
    ("ZeroFreeness.Potts.UniformPottsZeroFree", r"\forall G\in\mathcal G_\Delta\ \forall\tau",
     "The conclusion of Theorem 1.1 for one radius ε, uniformly over graphs and pinnings."),
    ("PottsCI.PinningData", r"(G^{\tau},\,b^{\tau})",
     "A residual instance: the free graph together with the boundary counts b^τ_u(c)."),
    ("PottsCI.PartialColouring.toPinningData", r"(G^{\tau},\,b^{\tau})",
     "The residual instance of an original graph and pinning; its graph is G[V ∖ Λ]."),
    ("ZeroFreeness.Potts.rootChildData", r"\tau^{r=a}",
     "The child instance obtained by pinning the free root r to a; it lives on V^τ ∖ {r}."),
    ("ZeroFreeness.Potts.GraphClassRootCouplingBound", r"\text{Definition 2.2 at one } x",
     "Coupling independence with constant cost at activity x, over every graph of the class."),
    ("PottsCI.FinDist.W", r"W_{1,d}", "The transport (Wasserstein-1) distance between finite laws."),
    ("PottsCI.ham", r"\mathrm{Ham}", "The Hamming distance between configurations."),
    ("ZeroFreeness.Potts.GraphClass", r"\mathcal G",
     "A class of finite simple graphs closed under induced subgraphs."),
    ("ZeroFreeness.Potts.GraphClassTransferInputs", r"\text{(i), (ii) of Theorem 1.2}",
     "Coupling independence at x = 0 and on every [δ, 1]."),
    ("ZeroFreeness.Appendix.Girth.UniformResidualGirthPottsZeroFree", r"\operatorname{girth}(G^\tau)\ge g",
     "The conclusion of the girth rows, with girth required only of the free graph."),
    ("ZeroFreeness.Appendix.BBR.start", r"x_0", "The left end of the BBR interval, 3/4 at (q, Δ) = (3, 4)."),
    ("ZeroFreeness.Appendix.BBR.intervalStart", r"x_0",
     "1 − (q/Δ)(1 − k/Δ)² (Δ − k)/(Δ − k/2)."),
    ("ZeroFreeness.Appendix.BBR.parameter", r"k", "k = e(Δ − q/2)/(Δ − q)."),
    ("ZeroFreeness.Appendix.Girth.girthFiveCIThreshold", r"\Delta_5(\delta)",
     "The girth-five degree threshold, explicit in Lean."),
    ("ZeroFreeness.Appendix.Girth.girthFiveThreshold", r"\Delta_0(\delta)",
     "⌈4096(1 + δ)e^{2/δ}/δ⁴⌉, as in the companion."),
    ("ZeroFreeness.LeeYang.normalizedFieldPartition", r"\widehat Z^{\tau}_{G}(\lambda)",
     "The normalized pinned partition function with one field per free vertex and colour."),
    ("ZeroFreeness.LeeYang.UniformVertexFieldZeroFree", r"|\lambda_{u,c}-1|\le\theta",
     "The Lee–Yang polydisc conclusion, uniform over graphs and pinnings."),
    ("ZeroFreeness.Holant.Signature", r"f",
     "A symmetric Boolean signature: nonnegative, log-concave, interval support, f(0) > 0."),
]

# The status of every numbered statement of both papers, with the Lean names that
# state it ("lean"), the definitions a reader needs to read them ("defs") and a
# note, is recorded in docs/coverage.json. Each status has a text
# label, a glyph (decoration only), a tone for the glyph, and a meaning.
COVERAGE = "docs/coverage.json"
STATUSES = {
    "formalized": ("Formalized", "✓", "good",
                   "Lean states and proves it at the paper's strength; the note names any claim about "
                   "cited work that is left out."),
    "formalized-equivalent": ("Equivalent form", "≃", "good",
                              "Lean proves an equivalent form; the note gives the step between the two."),
    "formalized-narrowed": ("Narrowed in paper", "✎", "good",
                            "The paper's statement is narrowed to what Lean proves, the only case its proofs "
                            "use; the note gives the edit."),
    "definition": ("Definition", "≔", "muted",
                   "Made in Lean by the declarations listed; the note records any difference."),
    "remark": ("Remark", "¶", "muted", "A remark that makes no claim of its own."),
    "not-formalized": ("Not formalized", "✗", "bad", "The paper states it, but no Lean declaration does."),
}


def short(name):
    for prefix in ("ZeroFreeness.", "PottsCI."):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name

def git(*args):
    return subprocess.run(["git", *args], cwd=REPO, capture_output=True, text=True,
                          check=True).stdout.strip()


KIND_WORDS = {
    "theorem": ("Theorem", "Theorems"), "lemma": ("Lemma", "Lemmas"),
    "proposition": ("Proposition", "Propositions"), "corollary": ("Corollary", "Corollaries"),
    "definition": ("Definition", "Definitions"), "remark": ("Remark", "Remarks"),
    "section": ("Section", "Sections"), "subsection": ("Section", "Sections"),
    "subsubsection": ("Section", "Sections"), "appendix": ("Appendix", "Appendices"),
    "subappendix": ("Appendix", "Appendices"), "table": ("Table", "Tables"),
    "figure": ("Figure", "Figures"), "equation": ("Equation", "Equations"),
    "enumi": ("item", "items"),
}
ENV_WORDS = {"theorem": "Theorem", "lemma": "Lemma", "proposition": "Proposition",
             "corollary": "Corollary", "definition": "Definition", "remark": "Remark"}


def read_group(text, i):
    """Return the contents of the brace group starting at text[i] and the index after it."""
    assert text[i] == "{"
    depth, j = 0, i
    while True:
        if text[j] == "\\":
            j += 2
            continue
        if text[j] == "{":
            depth += 1
        elif text[j] == "}":
            depth -= 1
            if depth == 0:
                return text[i + 1:j], j + 1
        j += 1


def parse_macros(tex):
    preamble = tex.split("\\begin{document}")[0]
    macros = {}
    for match in re.finditer(r"\\(newcommand|renewcommand|DeclareMathOperator)\*?\{\\([A-Za-z]+)\}",
                             preamble):
        kind, name = match.groups()
        i = match.end()
        arity = re.match(r"\[(\d)\]", preamble[i:])
        if arity:
            i += arity.end()
        if i >= len(preamble) or preamble[i] != "{":
            continue
        body, _ = read_group(preamble, i)
        macros["\\" + name] = "\\operatorname{%s}" % body if kind == "DeclareMathOperator" else body
    return macros


def and_join(items):
    items = list(items)
    if len(items) <= 1:
        return "".join(items)
    if len(items) == 2:
        return " and ".join(items)
    return ", ".join(items[:-1]) + ", and " + items[-1]


# ---------------------------------------------------------------------------
# Page
