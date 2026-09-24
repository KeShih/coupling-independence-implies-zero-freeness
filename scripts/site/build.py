#!/usr/bin/env python3
"""Build docs/index.html, a visual guide for checking the Lean statements
against the two papers.

Run from the repository root after the library is built:

    python3 scripts/site/build.py --paper ../main.tex --companion ../companion

Everything on the Lean side is read from the compiled environment:
signatures, source ranges, axioms, and the literature hypotheses each
statement takes. The paper side is extracted from the LaTeX sources, with
numbers and citation labels taken from their .aux and .bbl files. Source
links are pinned to the current commit, so commit Lean changes first.
"""
import argparse
import datetime
import html
import json
import re
import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
GITHUB = "https://github.com/KeShih/coupling-independence-implies-zero-freeness"
KATEX = "https://cdn.jsdelivr.net/npm/katex@0.16.11/dist"

# ---------------------------------------------------------------------------
# What to show

CHECKS = [
    "Hypotheses and parameter ranges match the paper",
    "Quantifier order: constants are chosen before the graph, pinning and activity",
    "The Lean objects are the paper's objects (see the definitions below)",
    "Only the listed literature results are assumed",
]

LITERATURE = [
    dict(id="cffgzz", short="CFFGZZ Thm 20",
         lean=["CI2ZF.Potts.ExternalCriticalHardColouringTheorem",
               "CI2ZF.Potts.CriticalHardColouringInput"],
         source="Chen, Feng, Guo, Zhang, Zou, Deterministic counting from coupling "
                "independence, arXiv:2410.23225v2, Theorem 20",
         url="https://arxiv.org/abs/2410.23225v2",
         meaning="Hard-colouring coupling independence at x = 0 on all graphs of maximum "
                 "degree at most Δ, for arbitrary pinnings. CriticalHardColouringInput is "
                 "the same bound on boundary-count data, derived from it by "
                 "ExternalCriticalHardColouringTheorem.to_normalizedInput."),
    dict(id="clmm-lit", short="CLMM Eq. (10), Lemma 5.13",
         lean=["CI2ZF.Appendix.CLMM.Literature"],
         source="Chen, Liu, Mani, Moitra, Strong spatial mixing for colorings on trees and "
                "its algorithmic applications, arXiv:2304.01954v3, Equation (10) (from "
                "Lemmas 5.19 and 5.20) and Lemma 5.13",
         url="https://arxiv.org/abs/2304.01954v3",
         meaning="Two fields: tree influence decay and relative spatial mixing give decay "
                 "on spheres of a fixed base graph under all further pinnings; sphere decay "
                 "gives a Hamming coupling bound 2Δ^R."),
    dict(id="clmm-513", short="CLMM Lemma 5.13",
         lean=["CI2ZF.Appendix.Girth.SphereCouplingInput"],
         source="Chen, Liu, Mani, Moitra, arXiv:2304.01954v3, Condition 5.12 and Lemma 5.13",
         url="https://arxiv.org/abs/2304.01954v3",
         meaning="Only the sphere-to-coupling half of CLMM.Literature."),
    dict(id="clmm-87", short="CLMM Lemma 8.7",
         lean=["CI2ZF.Appendix.Girth.CavityTree.CLMMInfluenceIdentity"],
         source="Chen, Liu, Mani, Moitra, arXiv:2304.01954v3, Lemma 8.7",
         url="https://arxiv.org/abs/2304.01954v3",
         meaning="The tree influence–Jacobian factorization, summed over a whole tree level."),
    dict(id="bbr", short="BBR Prop 2.6(i), Thm 2.5",
         lean=["CI2ZF.Appendix.BBR.Literature"],
         source="Bencs, Berrekkal, Regts, Near optimal bounds for weak and strong spatial "
                "mixing for the anti-ferromagnetic Potts model on trees, Electron. J. Probab. "
                "30 (2025), paper 65, Proposition 2.6(i) and Theorem 2.5",
         url="https://doi.org/10.1214/25-EJP1327",
         meaning="The segment-weight bound, used only at its printed hypothesis Δ ≥ q + 3, "
                 "and the squared-norm contraction of cavity messages."),
]

RESULTS = [
    dict(id="thm-intro-main", group="main", paper=[("main", "thm:intro-main")],
         lean=["CI2ZF.Potts.potts_main_theorem", "CI2ZF.Potts.potts_main_strict"],
         defs=["CI2ZF.Potts.UniformPottsZeroFree"],
         hyp_notes={"cffgzz": "only when 6q = 11Δ"},
         notes=["The literature input is requested only on the line 6q = 11Δ, the equality case "
                "of the theorem.",
                "Graphs range over finite types with every degree at most Δ; the pinning is any "
                "PartialColouring, improper ones included.",
                "UniformPottsZeroFree bundles the three conclusions: the normalized polynomial has "
                "no zeros, the full polynomial vanishes only at 0, and its multiplicity there is "
                "m_G(τ)."]),
    dict(id="thm-potts-transfer", group="main", paper=[("main", "thm:potts-transfer")],
         lean=["CI2ZF.Potts.graph_class_potts_transfer_of_bounded"],
         defs=["CI2ZF.Potts.GraphClass", "CI2ZF.Potts.GraphClassTransferInputs"],
         notes=["GraphClass asks for closure under pullback along embeddings: induced subgraphs, "
                "relabelled copies included.",
                "The coupling bounds are required only when both child laws are well defined, "
                "which q ≥ Δ + 1 guarantees.",
                "Lean does not need Δ ≥ 2."]),
    dict(id="def-potts-ci", group="main", paper=[("main", "def:potts-ci")],
         lean=["CI2ZF.Potts.GraphClassRootCouplingBound", "CI2ZF.Potts.RootCouplingBound"],
         defs=["CI2ZF.Potts.rootChildData", "PottsCI.FinDist.W", "PottsCI.ham"],
         notes=["GraphClassRootCouplingBound is the definition on original graphs and pinnings; "
                "RootCouplingBound states the same bound on boundary-count data and is what the "
                "proofs use.",
                "Both laws are normalized child Gibbs laws on V^τ ∖ {r}, compared in the Hamming "
                "Wasserstein distance."]),
    dict(id="thm-strict-ci", group="main", paper=[("main", "thm:strict-ci")],
         lean=["CI2ZF.Potts.root_strict_ci", "CI2ZF.Potts.root_strict_uniform_ci"],
         defs=["CI2ZF.ciBound", "CI2ZF.ciGap"],
         notes=["ciBound q Δ x is 2(1−x)Δ / (q − (11/6)(1−x)Δ) and ciGap q Δ is q/Δ − 11/6, "
                "as in the paper."]),
    dict(id="prop-hard-one-step", group="main", paper=[("main", "prop:hard-one-step")],
         lean=["CI2ZF.conditionalHardCouplingEstimate"],
         defs=["CI2ZF.ConditionalHardCouplingEstimate"],
         notes=["rootFreeCoinCount counts the edges at v that are active on at least one side, "
                "which is Σ_c |N_c|; rootCommonListCount is ℓ = |L_{X,v} ∩ L_{Y,v}|.",
                "The coupling itself is constructed in Lean; nothing about it is assumed."]),
    dict(id="prop-full-interval-hci", group="main", paper=[("main", "prop:full-interval-hci")],
         lean=["CI2ZF.Potts.root_positive_ci"],
         notes=["Lean does not need Δ ≥ 2."]),
    dict(id="cor-critical-line-input", group="main", paper=[("main", "cor:critical-line-input")],
         lean=["CI2ZF.Potts.critical_transfer_coupling_inputs",
               "CI2ZF.Potts.root_critical_uniform_ci"],
         defs=["CI2ZF.Potts.CriticalHardColouringInput"],
         notes=["The x = 0 bound is the named input CriticalHardColouringInput; "
                "ExternalCriticalHardColouringTheorem.to_normalizedInput derives it from the "
                "original-graph form of CFFGZZ Theorem 20.",
                "root_critical_uniform_ci gives the constant 12/(11δ) on [δ, 1]."]),
    dict(id="prop-field-transfer", group="main", paper=[("main", "prop:field-transfer")],
         lean=["CI2ZF.LeeYang.graph_class_normalized_field_transfer"],
         defs=["CI2ZF.LeeYang.normalizedFieldPartition"],
         notes=["θ is chosen after the class F. The paper's θ(q, Δ, C₀) follows by applying the "
                "theorem to the union of all classes with constant C₀.",
                "Lean uses the closed polydisc ‖λ − 1‖ ≤ θ and does not need Δ ≥ 2."]),
    dict(id="thm-lee-yang", group="main", paper=[("main", "thm:lee-yang")],
         lean=["CI2ZF.LeeYang.near_vigoda_vertex_field_zero_free",
               "CI2ZF.LeeYang.cv_vertex_field_zero_free",
               "CI2ZF.LeeYang.high_girth_original_field_transfer",
               "CI2ZF.LeeYang.high_girth_residual_original_field_transfer"],
         defs=["CI2ZF.LeeYang.UniformVertexFieldZeroFree"],
         hyp_notes={"cffgzz": "regime (i), only at (Δ, q) = (6j, 11j) with j ≤ 20"},
         notes=["Regime (i) assumes CFFGZZ Theorem 20 only at (Δ, q) = (6j, 11j), j ≤ 20; "
                "regime (ii) assumes nothing.",
                "Regime (iii) uses the large-girth row's CLMM inputs (Lemma 8.7, Equation (10), "
                "Lemma 5.13) instead of the x = 0 results cited in the paper's proof. The residual "
                "version needs girth only of G^τ."]),
    dict(id="cor-edge-lee-yang", group="main", paper=[("main", "cor:edge-lee-yang")],
         lean=["CI2ZF.LeeYang.edge_lee_yang"],
         notes=["No CWZZ input: the line-graph coupling bound Δ − 1 at x = 0 is proved in Lean."]),
    dict(id="thm-holant-box", group="main", paper=[("main", "thm:holant-box")],
         lean=["CI2ZF.Holant.exists_uniform_holant_polytube"],
         defs=["CI2ZF.Holant.Signature", "CI2ZF.Holant.graphPartition"],
         notes=["Lean allows any Δ and any R ≥ 0.",
                "The Chen–Gu coupling bound used in the proof is proved with the paper's constant."]),
    dict(id="cor-bmatching", group="main", paper=[("main", "cor:bmatching-short")],
         lean=["CI2ZF.Holant.bmatching_uniform_polytube", "CI2ZF.Holant.bmatching_orthant"]),
    dict(id="cor-bcover", group="main", paper=[("main", "cor:bcover-short")],
         lean=["CI2ZF.Holant.bcover_uniform_polytube", "CI2ZF.Holant.bcover_orthant"],
         defs=["CI2ZF.Holant.bcoverWidth"],
         notes=["bcover_uniform_polytube is stated as ∀ λ₋ λ₊ ∃ ε. That the width does not depend "
                "on λ₊ is true (bcoverWidth ignores its upper argument, and bcover_orthant uses "
                "this) but is not part of that theorem's type."]),

    dict(id="near-vigoda", group="appendix", title="Near-Vigoda regime",
         table="Δ ≥ 2, q ≥ (11/6 − 1/84000)Δ; zero-free near [0, 1]",
         paper=[("companion", "thm:potts-ci-regimes"), ("companion", "lem:int-reduction"),
                ("companion", "thm:additional-potts-zf")],
         lean=["CI2ZF.Appendix.near_vigoda_transfer_inputs",
               "CI2ZF.Appendix.near_vigoda_noncritical_uniform_ci",
               "CI2ZF.Appendix.near_vigoda_zero_free", "CI2ZF.Appendix.integer_reduction"],
         hyp_notes={"cffgzz": "only at (Δ, q) = (6j, 11j) with j ≤ 20"},
         notes=["CFFGZZ Theorem 20 is requested only at (Δ, q) = (6j, 11j) with j ≤ 20; for "
                "Δ ≥ 125 the Carlson–Vigoda theorem is used instead.",
                "integer_reduction is Lemma 4.3 of the companion, word for word.",
                "At the critical pairs the constant on [δ, 1] is 12/(11δ) "
                "(root_critical_uniform_ci)."]),
    dict(id="cv", group="appendix", title="Carlson–Vigoda regime",
         table="Δ ≥ 125, q ≥ 1.809Δ; zero-free near [0, 1]",
         paper=[("companion", "thm:cv-ci"), ("companion", "thm:additional-potts-zf")],
         lean=["CI2ZF.Appendix.CV.root_coupling", "CI2ZF.Appendix.CV.option_root_ci",
               "CI2ZF.Appendix.CV.zero_free"],
         defs=["CI2ZF.Appendix.CV.ciConstant"],
         notes=["The constant is ciConstant = 409060125/50858 < 8043.19, as in the companion.",
                "No literature input: the contraction is proved in Lean and x = 0 follows by "
                "finite-state continuity, so neither CV2024 nor CFFGZZ is assumed.",
                "The coupling theorems are stated on boundary-count data (PinningData (Option O) C), "
                "which covers every (G, τ, r)."]),
    dict(id="large-girth", group="appendix", title="Large-girth regime",
         table="Δ ≥ 3, q ≥ Δ + 3, girth(G^τ) ≥ g*(q, Δ); zero-free near [0, 1]",
         paper=[("companion", "thm:high-girth-soft-ci"), ("companion", "thm:additional-potts-zf")],
         lean=["CI2ZF.Appendix.Girth.high_girth_coupling",
               "CI2ZF.Appendix.Girth.high_girth_residual_original_zero_free"],
         defs=["CI2ZF.Appendix.Girth.UniformResidualGirthPottsZeroFree"],
         notes=["CLMM Lemma 8.7 enters in its level-summed form, and the sphere estimate needs "
                "strong spatial mixing only beyond a fixed depth K₀; the companion justifies both "
                "in the proof of its Lemma 6.10.",
                "Girth is required only of the free graph. Lean transfers on residual instances "
                "directly instead of using the pinned-leaf realization."]),
    dict(id="high-temperature", group="appendix", title="High-temperature regime",
         table="Δ ≥ 2, q > (11/6)(1 − x*)Δ, x* ∈ (0, 1]; zero-free near [x*, 1]",
         paper=[("companion", "cor:intro-high-temperature")],
         lean=["CI2ZF.Appendix.high_temperature_graph_coupling",
               "CI2ZF.Appendix.high_temperature_zero_free"],
         notes=["Lean needs neither Δ ≥ 2 nor x* ≤ 1, and one ε serves the normalized and the "
                "full polynomial.",
                "The coupling constant is the companion's C* = 2(1 − x*)Δ / (q − (11/6)(1 − x*)Δ)."]),
    dict(id="bbr", group="appendix", title="BBR interval",
         table="q ≥ 3, Δ/q ≥ (e − 1/2)/(e − 1), girth(G^τ) ≥ g_BBR(q, Δ); zero-free near [x₀, 1]",
         paper=[("companion", "thm:intro-bbr-interval"), ("companion", "thm:bbr-large-girth-ci")],
         lean=["CI2ZF.Appendix.BBR.high_girth_coupling",
               "CI2ZF.Appendix.BBR.high_girth_residual_original_zero_free"],
         defs=["CI2ZF.Appendix.BBR.start", "CI2ZF.Appendix.BBR.intervalStart",
               "CI2ZF.Appendix.BBR.parameter"],
         notes=["BBR Proposition 2.6(i) is used only at its printed hypothesis Δ ≥ q + 3. The four "
                "pairs with Δ = q + 2, and (q, Δ) = (3, 4), are handled by internal arithmetic; "
                "the companion instead extends BBR's proof to Δ = q + 2.",
                "The BBR influence identity (companion Lemma 7.3) is proved in Lean."]),
    dict(id="edge-potts", group="appendix", title="Edge-Potts regime",
         table="Δ ≥ 2, q ≥ 3Δ; the polynomial of the line graph L(G); zero-free near [0, 1]",
         paper=[("companion", "thm:soft-edge-ci"), ("companion", "cor:soft-edge-zf")],
         lean=["CI2ZF.Appendix.Edge.root_children_ci", "CI2ZF.Appendix.Edge.edge_potts_zero_free"],
         defs=["CI2ZF.Appendix.Edge.edgeGraphClass"],
         notes=["Lean uses finite slot approximations and a limit instead of the countable "
                "exact-slot representation (companion Lemma 8.3); x = 0 follows by continuity.",
                "The transfer runs on line graphs with degree bound 2Δ − 2."]),
    dict(id="girth-five", group="appendix", title="Girth-five regime",
         table="0 < δ ≤ 1, Δ ≥ Δ₅(δ), q ≥ (1 + δ)Δ, girth(G^τ) ≥ 5; zero-free near [0, 1]",
         paper=[("companion", "thm:girth5-ci"), ("companion", "thm:unrestricted-girth5"),
                ("companion", "thm:potts-gap-girth5")],
         lean=["CI2ZF.Appendix.Girth.girth_five_coupling",
               "CI2ZF.Appendix.Girth.girth_five_residual_original_zero_free",
               "CI2ZF.Appendix.Girth.girth_five_closed_poincare"],
         defs=["CI2ZF.Appendix.Girth.girthFiveCIThreshold",
               "CI2ZF.Appendix.Girth.girthFiveThreshold"],
         notes=["Δ₅(δ) is explicit: the maximum of ⌈4096(1 + δ)e^{2/δ}/δ⁴⌉ and "
                "⌈covarianceDegreeThreshold δ⌉. The companion's Δ₅ is existential with Δ₅ ≥ Δ₀.",
                "Theorem 9.7 is stated in Poincaré form; x = 0 follows by continuity.",
                "The coupling theorem is stated on residual instances, which covers every "
                "(G, τ, r)."]),
]

GLOSSARY = [
    ("CI2ZF.Potts.normalizedPolynomial", r"\widehat Z^{\tau}_{G}",
     "The normalized pinned polynomial: one monomial per colouring of the free vertices, "
     "counting free–pinned and free–free monochromatic edges."),
    ("CI2ZF.Potts.normalizedPartition", r"\widehat Z^{\tau}_{G}(z)", "Its value at z ∈ ℂ."),
    ("CI2ZF.Potts.fullPolynomial", r"Z^{\tau}_{G}",
     "The ordinary pinned polynomial, which also counts monochromatic edges inside the pinned set."),
    ("CI2ZF.Potts.fullPartition", r"Z^{\tau}_{G}(z)", "Its value at z ∈ ℂ."),
    ("PottsCI.PartialColouring", r"\tau\colon\Lambda\to[q]",
     "A pinning: a finite domain and a colour for each of its vertices. No properness is required."),
    ("PottsCI.PartialColouring.pinnedConflictCount", r"m_G(\tau)",
     "The number of monochromatic edges with both ends pinned."),
    ("CI2ZF.pottsInterval", r"[0,1]\subset\mathbb C",
     "Its open ε-neighbourhood Metric.thickening ε pottsInterval is the paper's U_ε([0, 1])."),
    ("CI2ZF.Potts.UniformPottsZeroFree", r"\forall G\in\mathcal G_\Delta\ \forall\tau",
     "The conclusion of Theorem 1.1 for one radius ε, uniformly over graphs and pinnings."),
    ("PottsCI.PinningData", r"(G^{\tau},\,b^{\tau})",
     "A residual instance: the free graph together with the boundary counts b^τ_u(c)."),
    ("PottsCI.PartialColouring.toPinningData", r"(G^{\tau},\,b^{\tau})",
     "The residual instance of an original graph and pinning; its graph is G[V ∖ Λ]."),
    ("CI2ZF.Potts.rootChildData", r"\tau^{r=a}",
     "The child instance obtained by pinning the free root r to a; it lives on V^τ ∖ {r}."),
    ("CI2ZF.Potts.GraphClassRootCouplingBound", r"\text{Definition 2.2 at one } x",
     "Coupling independence with constant cost at activity x, over every graph of the class."),
    ("PottsCI.FinDist.W", r"W_{1,d}", "The transport (Wasserstein-1) distance between finite laws."),
    ("PottsCI.ham", r"\mathrm{Ham}", "The Hamming distance between configurations."),
    ("CI2ZF.Potts.GraphClass", r"\mathcal G",
     "A class of finite simple graphs closed under induced subgraphs."),
    ("CI2ZF.Potts.GraphClassTransferInputs", r"\text{(i), (ii) of Theorem 1.2}",
     "Coupling independence at x = 0 and on every [δ, 1]."),
    ("CI2ZF.Appendix.Girth.UniformResidualGirthPottsZeroFree", r"\operatorname{girth}(G^\tau)\ge g",
     "The conclusion of the girth rows, with girth required only of the free graph."),
    ("CI2ZF.Appendix.BBR.start", r"x_0", "The left end of the BBR interval, 3/4 at (q, Δ) = (3, 4)."),
    ("CI2ZF.Appendix.BBR.intervalStart", r"x_0",
     "1 − (q/Δ)(1 − k/Δ)² (Δ − k)/(Δ − k/2)."),
    ("CI2ZF.Appendix.BBR.parameter", r"k", "k = e(Δ − q/2)/(Δ − q)."),
    ("CI2ZF.Appendix.Girth.girthFiveCIThreshold", r"\Delta_5(\delta)",
     "The girth-five degree threshold, explicit in Lean."),
    ("CI2ZF.Appendix.Girth.girthFiveThreshold", r"\Delta_0(\delta)",
     "⌈4096(1 + δ)e^{2/δ}/δ⁴⌉, as in the companion."),
    ("CI2ZF.LeeYang.normalizedFieldPartition", r"\widehat Z^{\tau}_{G}(\lambda)",
     "The normalized pinned partition function with one field per free vertex and colour."),
    ("CI2ZF.LeeYang.UniformVertexFieldZeroFree", r"|\lambda_{u,c}-1|\le\theta",
     "The Lee–Yang polydisc conclusion, uniform over graphs and pinnings."),
    ("CI2ZF.Holant.Signature", r"f",
     "A symmetric Boolean signature: nonnegative, log-concave, interval support, f(0) > 0."),
]

# ---------------------------------------------------------------------------
# Lean side

LEAN_TEMPLATE = r"""import CI2ZF
import Lean
open Lean Meta

def siteNames : Array Name := #[@@NAMES@@]

#eval show MetaM Unit from do
  let env ← getEnv
  for n in siteNames do
    match env.find? n with
    | none => IO.println (Json.compress (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)]))
    | some ci =>
      let sig ← PrettyPrinter.ppSignature n
      let rng ← findDeclarationRanges? n
      let modName : String := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i.toNat]!).toString
        | none => ""
      let axs ← collectAxioms n
      let used := ci.type.getUsedConstants.map (·.toString)
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "structure"
        | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
      let (l0, l1) := match rng with
        | some r => (r.range.pos.line, r.range.endPos.line)
        | none => (0, 0)
      IO.println (Json.compress (Json.mkObj [("name", toJson n.toString), ("kind", toJson kind),
        ("module", toJson modName), ("start", toJson l0), ("end", toJson l1),
        ("signature", toJson (sig.fmt.pretty 96)), ("axioms", toJson (axs.map (·.toString))),
        ("used", toJson used)]))
"""


def lean_extract(names):
    source = LEAN_TEMPLATE.replace("@@NAMES@@", ", ".join("`" + n for n in names))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as handle:
        handle.write(source)
        path = handle.name
    try:
        run = subprocess.run(["bash", "scripts/lake.sh", "env", "lean", path], cwd=REPO,
                             capture_output=True, text=True)
    finally:
        Path(path).unlink()
    if run.returncode != 0:
        sys.exit("Lean extraction failed:\n" + run.stdout + run.stderr)
    data = {}
    for line in run.stdout.splitlines():
        if line.startswith("{"):
            entry = json.loads(line)
            data[entry["name"]] = entry
    missing = [n for n in names if n not in data or data[n].get("missing")]
    if missing:
        sys.exit("Unknown Lean declarations: " + ", ".join(missing))
    return data


def module_file(module):
    return Path(*module.split(".")).with_suffix(".lean")


def lean_excerpt(info):
    lines = (REPO / module_file(info["module"])).read_text().splitlines()
    block = "\n".join(lines[info["start"] - 1:info["end"]])
    doc = None
    match = re.match(r"\s*/--(.*?)-/\s*\n?", block, re.S)
    if match:
        doc = " ".join(match.group(1).split())
        block = block[match.end():]
    if info["kind"] == "theorem":
        cut = block.find(":=")
        if cut >= 0:
            block = block[:cut]
    return doc, textwrap.dedent(block).strip("\n").rstrip()


def doc_html(doc):
    parts = doc.split("`")
    return "".join(("<code>%s</code>" if k % 2 else "%s") % html.escape(part)
                   for k, part in enumerate(parts))


def short(name):
    for prefix in ("CI2ZF.", "PottsCI."):
        if name.startswith(prefix):
            return name[len(prefix):]
    return name


def git(*args):
    return subprocess.run(["git", *args], cwd=REPO, capture_output=True, text=True,
                          check=True).stdout.strip()


# ---------------------------------------------------------------------------
# Paper side: numbers, citation labels, statements and LaTeX to HTML

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


class Paper:
    def __init__(self, name, tex, aux, bbl):
        self.name = name
        self.tex = tex
        self.nums, self.kinds = {}, {}
        for match in re.finditer(r"\\newlabel\{([^}]*)\}\{\{((?:[^{}]|\{[^{}]*\})*)\}", aux):
            label, value = match.groups()
            if label.endswith("@cref"):
                kind = re.match(r"\[([^\]]*)\]", value)
                if kind:
                    self.kinds[label[:-5]] = kind.group(1)
            else:
                self.nums[label] = value
        self.cites = {}
        for match in re.finditer(r"\\bibitem\[((?:[^\]{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\]\{([^}]*)\}", bbl):
            label = re.sub(r"\\etalchar\{([^}]*)\}", r"\1", match.group(1))
            self.cites[match.group(2)] = label.replace("{", "").replace("}", "")
        self.macros = parse_macros(tex)

    def number(self, label):
        num = self.nums.get(label, "??")
        return re.sub(r"\\[A-Za-z]+\s*|[{}]", "", num)

    def statement(self, label):
        at = self.tex.find("\\label{%s}" % label)
        if at < 0:
            sys.exit(f"Label {label} not found in the {self.name}")
        env, begin = max(((e, self.tex.rfind("\\begin{%s}" % e, 0, at)) for e in ENV_WORDS),
                         key=lambda pair: pair[1])
        end = self.tex.find("\\end{%s}" % env, at)
        body = self.tex[begin + len("\\begin{%s}" % env):end]
        title = None
        if body.startswith("["):
            depth, pos = 0, 1
            while not (body[pos] == "]" and depth == 0):
                depth += {"{": 1, "}": -1}.get(body[pos], 0)
                pos += 1
            title, body = body[1:pos], body[pos + 1:]
        return env, title, body


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


MATH_ENVS = r"equation\*?|align\*?|gather\*?|multline\*?"


class TexToHtml:
    def __init__(self, paper):
        self.paper = paper

    def refs(self, labels, eq_style=False):
        groups = []
        for label in labels:
            label = label.strip()
            num, kind = self.paper.number(label), self.paper.kinds.get(label, "")
            if kind == "equation" or eq_style:
                num = "(%s)" % num
            words = KIND_WORDS.get(kind, ("", ""))
            if groups and groups[-1][0] == words:
                groups[-1][1].append(num)
            else:
                groups.append((words, [num]))
        parts = []
        for (single, plural), nums in groups:
            word = single if len(nums) == 1 else plural
            parts.append((word + " " if word and not eq_style else "") + and_join(nums))
        return and_join(parts)

    def cite(self, keys, note_html):
        labels = [html.escape(self.paper.cites.get(k.strip(), k.strip())) for k in keys.split(",")]
        return "[" + ", ".join(labels) + (", " + note_html if note_html else "") + "]"

    def math(self, body):
        body = re.sub(r"\\label\{[^}]*\}|\\nonumber|\\notag", "", body)
        body = re.sub(r"\\eqref\{([^}]*)\}", lambda m: self.refs([m.group(1)], True), body)
        body = re.sub(r"\\[Cc]ref\{([^}]*)\}",
                      lambda m: "\\text{%s}" % self.refs(m.group(1).split(",")), body)
        return body

    def convert(self, tex, block=True):
        tex = "\n".join(re.sub(r"(?<!\\)%.*", "", line) for line in tex.split("\n"))
        segments = []

        def keep(body, display):
            segments.append((self.math(body), display))
            return "\x00%d\x00" % (len(segments) - 1)

        def env(match):
            name, body = match.group(1).rstrip("*"), match.group(2)
            if name in ("align", "multline", "gather"):
                body = "\\begin{%s}%s\\end{%s}" % (
                    "aligned" if name == "align" else "gathered", body,
                    "aligned" if name == "align" else "gathered")
            return keep(body, True)

        tex = re.sub(r"\\begin\{(%s)\}(.*?)\\end\{\1\}" % MATH_ENVS, env, tex, flags=re.S)
        tex = re.sub(r"\\\[(.*?)\\\]", lambda m: keep(m.group(1), True), tex, flags=re.S)
        tex = re.sub(r"\$\$(.*?)\$\$", lambda m: keep(m.group(1), True), tex, flags=re.S)
        tex = re.sub(r"\\\((.*?)\\\)", lambda m: keep(m.group(1), False), tex, flags=re.S)
        tex = re.sub(r"(?<!\\)\$(.+?)(?<!\\)\$", lambda m: keep(m.group(1), False), tex, flags=re.S)
        out = self.text(tex)
        out = re.sub(r"\x00(\d+)\x00", lambda m: self.render_math(*segments[int(m.group(1))]), out)
        if not block:
            return " ".join(out.split())
        paragraphs = [p.strip() for p in re.split(r"\n\s*\n", out) if p.strip()]
        return "".join('<div class="para">%s</div>' % p for p in paragraphs)

    @staticmethod
    def render_math(body, display):
        body = html.escape(body.strip(), quote=False)
        return "\\[%s\\]" % body if display else "\\(%s\\)" % body

    def text(self, tex):
        out, plain, lists = [], [], []
        i = 0

        def flush():
            if plain:
                run = "".join(plain)
                run = run.replace("---", "\u2014").replace("--", "\u2013")
                run = run.replace("``", "\u201c").replace("''", "\u201d").replace("~", "\u00a0")
                out.append(html.escape(run, quote=False))
                plain.clear()

        def emit(markup):
            flush()
            out.append(markup)

        def arg(j):
            while j < len(tex) and tex[j] in " \t":
                j += 1
            if j < len(tex) and tex[j] == "{":
                return read_group(tex, j)
            return "", j

        def optional(j):
            if j < len(tex) and tex[j] == "[":
                depth, k = 0, j + 1
                while not (tex[k] == "]" and depth == 0):
                    depth += {"{": 1, "}": -1}.get(tex[k], 0)
                    k += 1
                return tex[j + 1:k], k + 1
            return None, j

        while i < len(tex):
            c = tex[i]
            if c == "\x00":
                end = tex.index("\x00", i + 1)
                emit(tex[i:end + 1])
                i = end + 1
            elif c == "\\":
                match = re.match(r"\\([A-Za-z]+)\*?|\\(.)", tex[i:])
                i += match.end()
                symbol = match.group(2)
                if symbol is not None:
                    if symbol == "\\":
                        emit("<br>")
                    else:
                        plain.append({",": "\u2009", ";": " ", " ": " ", "!": ""}.get(symbol, symbol))
                    continue
                name = match.group(1)
                if name in ("Cref", "cref", "ref", "eqref"):
                    labels, i = arg(i)
                    plain.append(self.refs(labels.split(","), name == "eqref"))
                elif name == "cite":
                    note, i = optional(i)
                    keys, i = arg(i)
                    emit(self.cite(keys, self.text(note) if note else None))
                elif name in ("emph", "textit"):
                    body, i = arg(i)
                    emit("<em>%s</em>" % self.text(body))
                elif name == "textbf":
                    body, i = arg(i)
                    emit("<strong>%s</strong>" % self.text(body))
                elif name in ("texttt", "nolinkurl", "path"):
                    body, i = arg(i)
                    emit("<code>%s</code>" % html.escape(body))
                elif name == "url":
                    body, i = arg(i)
                    emit('<a href="%s">%s</a>' % (html.escape(body), html.escape(body)))
                elif name == "href":
                    url, i = arg(i)
                    body, i = arg(i)
                    emit('<a href="%s">%s</a>' % (html.escape(url), self.text(body)))
                elif name == "texorpdfstring":
                    body, i = arg(i)
                    _, i = arg(i)
                    emit(self.text(body))
                elif name in ("label", "vspace", "hspace", "footnote", "index"):
                    _, i = arg(i)
                elif name == "begin":
                    env, i = arg(i)
                    _, i = optional(i)
                    if env in ("enumerate", "itemize"):
                        lists.append(False)
                        emit('<ol class="roman">' if env == "enumerate" else "<ul>")
                elif name == "end":
                    env, i = arg(i)
                    if env in ("enumerate", "itemize") and lists:
                        opened = lists.pop()
                        emit(("</li>" if opened else "") + ("</ol>" if env == "enumerate" else "</ul>"))
                elif name == "item":
                    label, i = optional(i)
                    opened = lists[-1] if lists else False
                    if lists:
                        lists[-1] = True
                    tag = '<li data-label="%s">' % html.escape(self.plain(label)) if label else "<li>"
                    emit(("</li>" if opened else "") + tag)
                elif name in ("quad", "qquad"):
                    plain.append(" ")
                elif name in ("smallskip", "medskip", "bigskip", "noindent", "par", "newline",
                              "centering", "leavevmode"):
                    pass
                else:
                    body, j = arg(i)
                    if j != i:
                        emit(self.text(body))
                        i = j
            elif c in "{}":
                i += 1
            else:
                plain.append(c)
                i += 1
        flush()
        return "".join(out)

    def plain(self, tex):
        return re.sub(r"<[^>]+>", "", self.text(tex))


def and_join(items):
    items = list(items)
    if len(items) <= 1:
        return "".join(items)
    if len(items) == 2:
        return " and ".join(items)
    return ", ".join(items[:-1]) + ", and " + items[-1]


# ---------------------------------------------------------------------------
# Page

def e(text):
    return html.escape(text, quote=True)


def statement_html(papers, converters, source, label):
    paper, conv = papers[source], converters[source]
    env, title, body = paper.statement(label)
    ref = "%s %s" % (ENV_WORDS[env], paper.number(label))
    where = "Main paper" if source == "main" else "Companion"
    title_html = conv.convert(title, block=False) if title else ""
    return ref, title_html, where, conv.convert(body)


def decl_html(info, commit, lit_by_name):
    doc, code = lean_excerpt(info)
    path = module_file(info["module"]).as_posix()
    url = "%s/blob/%s/%s#L%d-L%d" % (GITHUB, commit, path, info["start"], info["end"])
    axioms = info["axioms"]
    standard = set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}
    badges = ['<span class="badge good" title="%s"><span aria-hidden="true">✓</span> Standard axioms only</span>'
              % e(", ".join(axioms) or "no axioms") if standard else
              '<span class="badge bad"><span aria-hidden="true">!</span> Axioms: %s</span>' % e(", ".join(axioms))]
    for lit in sorted({lit_by_name[u]["id"] for u in info["used"] if u in lit_by_name}):
        entry = next(x for x in LITERATURE if x["id"] == lit)
        badges.append('<a class="badge hyp" href="#lit-%s"><span class="dot" aria-hidden="true"></span>'
                      'Assumes %s</a>' % (lit, e(entry["short"])))
    return f"""
<div class="decl">
  <div class="decl-head"><code class="decl-name">{e(short(info["name"]))}</code>
    <span class="kind">{e(info["kind"])}</span>
    <a class="src" href="{e(url)}">{e(Path(path).name)} · lines {info["start"]}–{info["end"]}</a></div>
  {'<p class="doc">%s</p>' % doc_html(doc) if doc else ''}
  <pre class="lean"><code>{e(code)}</code></pre>
  <details class="elab"><summary>Elaborated type</summary><pre class="lean"><code>{e(info["signature"])}</code></pre></details>
  <div class="badges">{" ".join(badges)}</div>
</div>"""


def build(args):
    if git("status", "--porcelain", "--", "CI2ZF", "CI2ZF.lean"):
        sys.exit("Commit the Lean sources first, so that source links are pinned.")
    commit = git("rev-parse", "--short=7", "HEAD")
    record = json.loads((REPO / "docs/verification.json").read_text())

    paper_tex = Path(args.paper).read_text()
    companion_dir = Path(args.companion)
    companion_main = (companion_dir / "main.tex").read_text()
    inputs = re.findall(r"\\input\{([^}]*)\}", companion_main)
    companion_tex = companion_main + "\n".join(
        (companion_dir / (name if name.endswith(".tex") else name + ".tex")).read_text()
        for name in inputs)
    papers = {
        "main": Paper("main paper", paper_tex, Path(args.paper).with_suffix(".aux").read_text(),
                      Path(args.paper).with_suffix(".bbl").read_text()),
        "companion": Paper("companion", companion_tex, (companion_dir / "main.aux").read_text(),
                           (companion_dir / "main.bbl").read_text()),
    }
    converters = {k: TexToHtml(p) for k, p in papers.items()}
    macros = dict(papers["main"].macros)
    macros.update(papers["companion"].macros)
    macros["\\textup"] = "\\textrm{#1}"

    names = []
    for result in RESULTS:
        names += result["lean"] + result.get("defs", [])
    names += [n for lit in LITERATURE for n in lit["lean"]] + [g[0] for g in GLOSSARY]
    names = list(dict.fromkeys(names))
    info = lean_extract(names)
    lit_by_name = {n: lit for lit in LITERATURE for n in lit["lean"]}

    # matrix and cards
    used_by = {lit["id"]: [] for lit in LITERATURE}
    rows, cards = [], {"main": [], "appendix": []}
    total_checks = 0
    for result in RESULTS:
        statements = [statement_html(papers, converters, src, label) for src, label in result["paper"]]
        ref, title_html = statements[0][0], statements[0][1] or e(result.get("title", ""))
        if result["group"] == "appendix":
            ref, title_html = "Appendix A", e(result["title"])
        plain_title = re.sub(r"<[^>]+>|\\[()]", "", title_html)
        hyps = set()
        for name in result["lean"]:
            hyps |= {lit_by_name[u]["id"] for u in info[name]["used"] if u in lit_by_name}
        for lit in hyps:
            used_by[lit].append(result)
        search = " ".join([ref, re.sub(r"<[^>]+>", "", title_html), *result["lean"]]).lower()
        cells = []
        for lit in LITERATURE:
            if lit["id"] in hyps:
                note = result.get("hyp_notes", {}).get(lit["id"], "")
                assuming = [short(n) for n in result["lean"]
                            if any(lit_by_name.get(u, {}).get("id") == lit["id"] for u in info[n]["used"])]
                cells.append('<td class="cell on" tabindex="0" data-tip-value="Assumed%s" '
                             'data-tip-label="%s · %s"><span class="dot" aria-hidden="true"></span>'
                             '<span class="sr">assumed</span></td>'
                             % (e(" (" + note + ")") if note else "", e(lit["short"]),
                                e(", ".join(assuming))))
            else:
                cells.append('<td class="cell"><span class="sr">not assumed</span></td>')
        count = ('<span class="none"><span aria-hidden="true">✓</span> none</span>' if not hyps
                 else "%d" % len(hyps))
        rows.append('<tr data-result="%s" data-group="%s" data-search="%s"><th scope="row">'
                    '<a href="#%s"><span class="rref">%s</span> %s</a></th>%s<td class="count">%s</td></tr>'
                    % (result["id"], result["group"], e(search), result["id"], e(ref), title_html,
                       "".join(cells), count))

        paper_html = "".join(
            '<details class="stmt"%s><summary><span class="sref">%s</span> · %s%s</summary>'
            '<div class="tex">%s</div></details>'
            % (" open" if k == 0 else "", e(sref), where, (" · " + stitle) if stitle and k else "", body)
            for k, (sref, stitle, where, body) in enumerate(statements))
        if result.get("table"):
            paper_html = ('<p class="table-row"><span class="label">Table A.1</span> %s</p>'
                          % e(result["table"])) + paper_html
        lean_html = "".join(decl_html(info[n], commit, lit_by_name) for n in result["lean"])
        if result.get("defs"):
            lean_html += '<p class="defs">Definitions: %s</p>' % ", ".join(
                '<a href="#def-%s"><code>%s</code></a>' % (e(n), e(short(n))) for n in result["defs"])
        notes = "".join("<li>%s</li>" % e(n) for n in result.get("notes", []))
        checks = "".join(
            '<label class="check"><input type="checkbox" data-key="%s:%d"> <span>%s</span></label>'
            % (result["id"], k, e(text)) for k, text in enumerate(CHECKS))
        total_checks += len(CHECKS)
        cards[result["group"]].append(f"""
<article class="card result" id="{result['id']}" data-result="{result['id']}" data-group="{result['group']}" data-search="{e(search)}" data-title="{e(html.unescape(plain_title))}">
  <header class="card-head">
    <div><div class="ref">{e(ref)}</div><h3>{title_html}</h3></div>
    <div class="card-progress"><span class="k">0</span> of {len(CHECKS)} checked</div>
  </header>
  <div class="cols">
    <section class="side paper"><h4>Paper</h4>{paper_html}</section>
    <section class="side leanside"><h4>Lean</h4>{lean_html}</section>
  </div>
  {'<section class="notes"><h4>What to look at</h4><ul>%s</ul></section>' % notes if notes else ''}
  <section class="checks"><h4>Your checks</h4>{checks}
    <textarea data-note="{result['id']}" rows="2" placeholder="Notes on this result (saved in this browser)"></textarea>
  </section>
</article>""")

    head = "".join('<th scope="col"><a href="#lit-%s" title="%s">%s</a></th>'
                   % (lit["id"], e(lit["source"]), e(lit["short"])) for lit in LITERATURE)
    matrix = ('<table class="matrix"><thead><tr><th scope="col">Result</th>%s<th scope="col">Inputs</th>'
              '</tr></thead><tbody>%s</tbody></table>' % (head, "".join(rows)))

    glossary = []
    for name, notation, meaning in GLOSSARY:
        doc, code = lean_excerpt(info[name])
        path = module_file(info[name]["module"]).as_posix()
        url = "%s/blob/%s/%s#L%d-L%d" % (GITHUB, commit, path, info[name]["start"], info[name]["end"])
        glossary.append(f"""
<div class="gl-row" id="def-{e(name)}">
  <div class="gl-meta"><code class="decl-name">{e(short(name))}</code>
    <div class="notation">\\({e(notation)}\\)</div><p>{e(meaning)}</p>
    <a class="src" href="{e(url)}">{e(Path(path).name)} · lines {info[name]["start"]}–{info[name]["end"]}</a></div>
  <pre class="lean"><code>{e(code)}</code></pre>
</div>""")

    literature = []
    for lit in LITERATURE:
        users = used_by[lit["id"]]
        decls = "".join(decl_html(info[n], commit, lit_by_name) for n in lit["lean"])
        literature.append(f"""
<article class="card lit" id="lit-{lit['id']}">
  <header class="card-head"><div><div class="ref">Literature hypothesis</div><h3>{e(lit['short'])}</h3></div></header>
  <p class="source"><a href="{e(lit['url'])}">{e(lit['source'])}</a></p>
  <p>{e(lit['meaning'])}</p>
  <p class="users">Assumed by: {", ".join('<a href="#%s">%s</a>' % (r['id'], e(r.get('title') or r['id'])) for r in users) or 'no mapped result'}</p>
  {decls}
</article>""")

    tiles = [
        ("Build jobs", f"{record['build_jobs']:,}", "warnings are errors"),
        ("Audited declarations", f"{record['audited_project_declarations']:,}", "transitive axiom check"),
        ("Library modules", f"{record['joint_import_closure_files']:,}", "all reachable from CI2ZF"),
        ("Axioms used", str(len(record["allowed_axioms"])), " · ".join(record["allowed_axioms"])),
        ("Results mapped", str(len(RESULTS)), f"{len(names)} Lean declarations linked"),
    ]
    tiles_html = "".join('<div class="tile"><div class="tile-label">%s</div><div class="tile-value">%s</div>'
                         '<div class="tile-sub">%s</div></div>' % (e(a), e(b), e(c)) for a, b, c in tiles)

    page = PAGE
    for key, value in {
        "@@COMMIT@@": e(commit), "@@COMMITURL@@": e(f"{GITHUB}/tree/{commit}"),
        "@@REPO@@": e(GITHUB), "@@DATE@@": e(datetime.date.today().isoformat()),
        "@@VERIFIED@@": e(record["date"]), "@@TILES@@": tiles_html, "@@MATRIX@@": matrix,
        "@@MAIN@@": "".join(cards["main"]), "@@APPENDIX@@": "".join(cards["appendix"]),
        "@@GLOSSARY@@": "".join(glossary), "@@LITERATURE@@": "".join(literature),
        "@@TOTAL@@": str(total_checks), "@@MACROS@@": json.dumps(macros).replace("</", "<\\/"),
        "@@KATEX@@": KATEX, "@@CHECKS@@": json.dumps(CHECKS),
    }.items():
        page = page.replace(key, value)
    out = REPO / args.out
    out.write_text(page)
    (out.parent / ".nojekyll").write_text("")
    print(f"Wrote {out.relative_to(REPO)}: {len(RESULTS)} results, {len(names)} declarations, "
          f"commit {commit}")


PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Lean ↔ paper checker · Coupling Independence Implies Zero-Freeness</title>
<link rel="stylesheet" href="@@KATEX@@/katex.min.css">
<script defer src="@@KATEX@@/katex.min.js"></script>
<script defer src="@@KATEX@@/contrib/auto-render.min.js"></script>
<script>
  (function () {
    var t = localStorage.getItem("ci2zf-theme");
    if (t === "light" || t === "dark") document.documentElement.dataset.theme = t;
  })();
</script>
<style>
:root {
  color-scheme: light;
  --page: #f9f9f7; --surface: #fcfcfb; --ink: #0b0b0b; --ink-2: #52514e; --muted: #898781;
  --grid: #e1e0d9; --axis: #c3c2b7; --border: rgba(11, 11, 11, 0.10);
  --accent: #2a78d6; --track: #cde2fb; --good: #0ca30c; --good-ink: #006300; --bad: #d03b3b;
  --code-bg: #f2f1ed; --link: #1c5cab; --wash: rgba(42, 120, 214, 0.07);
}
@media (prefers-color-scheme: dark) {
  :root:where(:not([data-theme="light"])) {
    color-scheme: dark;
    --page: #0d0d0d; --surface: #1a1a19; --ink: #ffffff; --ink-2: #c3c2b7; --muted: #898781;
    --grid: #2c2c2a; --axis: #383835; --border: rgba(255, 255, 255, 0.10);
    --accent: #3987e5; --track: #184f95; --good: #0ca30c; --good-ink: #0ca30c; --bad: #d03b3b;
    --code-bg: #232322; --link: #86b6ef; --wash: rgba(57, 135, 229, 0.12);
  }
}
:root[data-theme="dark"] {
  color-scheme: dark;
  --page: #0d0d0d; --surface: #1a1a19; --ink: #ffffff; --ink-2: #c3c2b7; --muted: #898781;
  --grid: #2c2c2a; --axis: #383835; --border: rgba(255, 255, 255, 0.10);
  --accent: #3987e5; --track: #184f95; --good: #0ca30c; --good-ink: #0ca30c; --bad: #d03b3b;
  --code-bg: #232322; --link: #86b6ef; --wash: rgba(57, 135, 229, 0.12);
}
* { box-sizing: border-box; }
html { scroll-padding-top: 64px; }
body { margin: 0; background: var(--page); color: var(--ink);
  font: 15px/1.55 system-ui, -apple-system, "Segoe UI", sans-serif; }
a { color: var(--link); text-decoration: none; }
a:hover { text-decoration: underline; }
code, pre { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 12.5px; }
.wrap { max-width: 1240px; margin: 0 auto; padding: 0 20px; }
.topbar { position: sticky; top: 0; z-index: 5; background: var(--page); border-bottom: 1px solid var(--grid); }
.topbar .wrap { display: flex; align-items: center; gap: 18px; height: 52px; }
.topbar .brand { font-weight: 600; white-space: nowrap; }
.topbar nav { display: flex; gap: 14px; overflow-x: auto; font-size: 14px; }
.topbar nav a { color: var(--ink-2); white-space: nowrap; }
.topbar .spacer { flex: 1; }
button, .btn { font: inherit; font-size: 13px; color: var(--ink); background: var(--surface);
  border: 1px solid var(--border); border-radius: 8px; padding: 5px 10px; cursor: pointer; }
button:hover { background: var(--wash); }
button[aria-pressed="true"] { border-color: var(--accent); box-shadow: inset 0 0 0 1px var(--accent); }
header.hero { padding: 28px 0 8px; }
header.hero h1 { font-size: 26px; line-height: 1.25; margin: 0 0 6px; font-weight: 650; }
header.hero p { margin: 4px 0; color: var(--ink-2); max-width: 820px; }
.tiles { display: grid; grid-template-columns: repeat(auto-fit, minmax(190px, 1fr)); gap: 12px; margin: 18px 0; }
.tile { background: var(--surface); border: 1px solid var(--border); border-radius: 10px; padding: 14px 16px; }
.tile-label { font-size: 13px; color: var(--ink-2); }
.tile-value { font-size: 28px; font-weight: 600; line-height: 1.2; margin-top: 2px; }
.tile-sub { font-size: 12px; color: var(--muted); margin-top: 2px; }
.progress { display: flex; align-items: center; gap: 14px; background: var(--surface);
  border: 1px solid var(--border); border-radius: 10px; padding: 12px 16px; }
.progress .label { font-size: 13px; color: var(--ink-2); white-space: nowrap; }
.progress .value { font-weight: 600; white-space: nowrap; }
.meter { flex: 1; height: 8px; border-radius: 4px; background: var(--track); overflow: hidden; }
.meter > span { display: block; height: 100%; width: 0; background: var(--accent); border-radius: 4px; }
.filters { display: flex; flex-wrap: wrap; align-items: center; gap: 8px; margin: 18px 0 8px; }
.filters input[type="search"] { font: inherit; font-size: 14px; color: var(--ink); background: var(--surface);
  border: 1px solid var(--border); border-radius: 8px; padding: 5px 10px; min-width: 260px; }
.filters label { font-size: 13px; color: var(--ink-2); display: flex; align-items: center; gap: 6px; }
h2 { font-size: 19px; margin: 34px 0 6px; font-weight: 650; }
h2 + .lede { margin-top: 0; color: var(--ink-2); max-width: 860px; }
.card { background: var(--surface); border: 1px solid var(--border); border-radius: 12px; padding: 18px 20px; margin: 14px 0; }
.card-head { display: flex; justify-content: space-between; align-items: flex-start; gap: 12px; }
.card-head .ref { font-size: 12px; letter-spacing: .02em; text-transform: uppercase; color: var(--muted); font-weight: 600; }
.card-head h3 { margin: 2px 0 0; font-size: 18px; font-weight: 600; }
.card-progress { font-size: 13px; color: var(--ink-2); white-space: nowrap; }
.card.done .card-progress { color: var(--good-ink); }
.card.done .card-progress::before { content: "✓ "; }
.cols { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 20px; margin-top: 12px; }
@media (max-width: 960px) { .cols { grid-template-columns: minmax(0, 1fr); } }
.side h4, .notes h4, .checks h4 { font-size: 12px; text-transform: uppercase; letter-spacing: .04em; color: var(--muted); margin: 0 0 8px; font-weight: 600; }
details.stmt { border-top: 1px solid var(--grid); padding: 8px 0; }
details.stmt:first-of-type { border-top: 0; padding-top: 0; }
details summary { cursor: pointer; color: var(--ink-2); font-size: 13.5px; }
details summary .sref { color: var(--ink); font-weight: 600; }
.tex { margin-top: 8px; overflow-x: auto; }
.tex .para { margin: 0 0 8px; }
.tex ol.roman { list-style: none; counter-reset: r; padding-left: 2.2em; margin: 6px 0; }
.tex ol.roman > li { counter-increment: r; position: relative; margin: 2px 0; }
.tex ol.roman > li::before { content: "(" counter(r, lower-roman) ")"; position: absolute; left: -2.2em; color: var(--ink-2); }
.tex li[data-label]::before { content: attr(data-label) !important; }
.table-row { margin: 0 0 10px; font-size: 14px; }
.table-row .label { font-size: 12px; font-weight: 600; color: var(--muted); margin-right: 6px; text-transform: uppercase; letter-spacing: .03em; }
.decl { border-top: 1px solid var(--grid); padding: 10px 0; }
.decl:first-of-type { border-top: 0; padding-top: 0; }
.decl-head { display: flex; flex-wrap: wrap; align-items: baseline; gap: 8px; }
.decl-name { font-weight: 600; font-size: 13px; }
.kind { font-size: 12px; color: var(--muted); }
.src { font-size: 12.5px; margin-left: auto; }
.doc { color: var(--ink-2); margin: 6px 0; font-size: 14px; }
pre.lean { background: var(--code-bg); border-radius: 8px; padding: 10px 12px; margin: 8px 0; overflow-x: auto; line-height: 1.45; }
details.elab summary { font-size: 12.5px; }
.badges { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 6px; }
.badge { display: inline-flex; align-items: center; gap: 6px; font-size: 12.5px; padding: 2px 9px; border-radius: 999px;
  border: 1px solid var(--border); color: var(--ink-2); background: var(--surface); }
.badge.good span[aria-hidden] { color: var(--good); font-weight: 700; }
.badge.bad span[aria-hidden] { color: var(--bad); font-weight: 700; }
.badge .dot, .matrix .dot { display: inline-block; width: 10px; height: 10px; border-radius: 50%; background: var(--accent);
  box-shadow: 0 0 0 2px var(--surface); }
.defs { font-size: 13px; color: var(--ink-2); margin: 8px 0 0; }
.notes ul { margin: 0; padding-left: 20px; color: var(--ink); }
.notes li { margin: 3px 0; }
.notes, .checks { margin-top: 14px; border-top: 1px solid var(--grid); padding-top: 12px; }
.check { display: flex; align-items: flex-start; gap: 8px; margin: 4px 0; font-size: 14px; cursor: pointer; }
.check input { margin-top: 4px; accent-color: var(--accent); }
.checks textarea { width: 100%; margin-top: 8px; font: inherit; font-size: 14px; color: var(--ink);
  background: var(--page); border: 1px solid var(--border); border-radius: 8px; padding: 8px 10px; resize: vertical; }
.matrix-wrap { background: var(--surface); border: 1px solid var(--border); border-radius: 12px; overflow-x: auto; }
table.matrix { border-collapse: collapse; width: 100%; font-size: 14px; }
.matrix th, .matrix td { padding: 7px 12px; border-bottom: 1px solid var(--grid); }
.matrix thead th { font-size: 12.5px; font-weight: 600; color: var(--ink-2); text-align: center; vertical-align: bottom; white-space: nowrap; }
.matrix thead th:first-child { text-align: left; }
.matrix tbody th { text-align: left; font-weight: 500; }
.matrix tbody th a { color: var(--ink); }
.matrix .rref { color: var(--muted); font-size: 12.5px; font-weight: 600; margin-right: 4px; }
.matrix td.cell { text-align: center; width: 110px; }
.matrix td.cell.on { cursor: default; }
.matrix td.cell.on:hover, .matrix td.cell.on:focus { background: var(--wash); outline: none; }
.matrix td.cell.on:focus-visible { box-shadow: inset 0 0 0 2px var(--accent); }
.matrix td.count { text-align: center; color: var(--ink-2); white-space: nowrap; }
.matrix .none span[aria-hidden] { color: var(--good); font-weight: 700; }
.matrix tbody tr:hover { background: var(--wash); }
.matrix tbody tr:last-child th, .matrix tbody tr:last-child td { border-bottom: 0; }
.sr { position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0); white-space: nowrap; }
#tip { position: fixed; z-index: 20; max-width: 340px; background: var(--surface); color: var(--ink);
  border: 1px solid var(--border); border-radius: 8px; padding: 8px 10px; box-shadow: 0 6px 24px rgba(0,0,0,.14);
  font-size: 13px; pointer-events: none; }
#tip strong { display: block; font-size: 14px; }
#tip div { color: var(--ink-2); }
.gl-row { display: grid; grid-template-columns: minmax(0, 5fr) minmax(0, 7fr); gap: 16px; padding: 14px 0; border-top: 1px solid var(--grid); }
.gl-row:first-child { border-top: 0; }
.gl-row pre.lean { align-self: start; margin: 0; }
@media (max-width: 960px) { .gl-row { grid-template-columns: minmax(0, 1fr); } }
.gl-meta p { margin: 4px 0; color: var(--ink-2); font-size: 14px; }
.notation { margin: 4px 0; }
.lit .source { font-size: 14px; }
.lit .users { font-size: 14px; color: var(--ink-2); }
.repro pre { background: var(--code-bg); border-radius: 8px; padding: 10px 12px; overflow-x: auto; }
footer { color: var(--muted); font-size: 13px; padding: 30px 0 50px; }
.hidden { display: none !important; }
@media print { .topbar, .filters, .checks textarea { display: none; } .card { break-inside: avoid; } }
</style>
</head>
<body>
<div class="topbar"><div class="wrap">
  <span class="brand">CI2ZF · Lean ↔ paper</span>
  <nav aria-label="Sections"><a href="#status">Status</a><a href="#matrix">Hypotheses</a><a href="#main">Main paper</a><a href="#appendix">Appendix A</a><a href="#definitions">Definitions</a><a href="#literature">Literature</a><a href="#reproduce">Reproduce</a></nav>
  <span class="spacer"></span>
  <button id="theme" type="button" title="Switch colour theme">Theme: auto</button>
</div></div>

<main class="wrap">
<header class="hero" id="status">
  <h1>Checking the Lean formalization against the paper</h1>
  <p>For each result of <em>Coupling Independence Implies Zero-Freeness</em> and its companion paper, this page shows the paper's statement next to the Lean statement that proves it, the literature results the Lean statement assumes, and its axioms. Everything on the Lean side is read from the compiled library at commit <a href="@@COMMITURL@@"><code>@@COMMIT@@</code></a>, and every source link points to that commit.</p>
  <p>Tick the checks as you go. Your ticks and notes stay in this browser; <em>Export review</em> saves them as a Markdown file you can send to a coauthor.</p>
</header>

<div class="tiles">@@TILES@@</div>
<div class="progress" role="group" aria-label="Review progress">
  <span class="label">Review progress</span>
  <div class="meter" role="progressbar" aria-valuemin="0" aria-valuemax="@@TOTAL@@" aria-valuenow="0" id="meter"><span></span></div>
  <span class="value" id="progress-text">0 of @@TOTAL@@ checks</span>
</div>

<div class="filters" role="search">
  <button type="button" data-filter="all" aria-pressed="true">All</button>
  <button type="button" data-filter="main" aria-pressed="false">Main paper</button>
  <button type="button" data-filter="appendix" aria-pressed="false">Appendix A</button>
  <input type="search" id="q" placeholder="Filter by result or Lean name" aria-label="Filter by result or Lean name">
  <label><input type="checkbox" id="open-only"> Only unfinished</label>
  <span class="spacer" style="flex:1"></span>
  <button type="button" id="export">Export review</button>
  <button type="button" id="reset">Reset</button>
</div>

<h2 id="matrix">Literature hypotheses by result</h2>
<p class="lede">A dot means the Lean statement takes that published result as an explicit hypothesis. Nothing else is assumed: the axiom audit allows only Lean's standard axioms. Hover or focus a dot for the declarations involved.</p>
<div class="matrix-wrap">@@MATRIX@@</div>

<h2 id="main">Main paper</h2>
<p class="lede">Theorem numbers follow the current version of <em>Coupling Independence Implies Zero-Freeness</em>.</p>
@@MAIN@@

<h2 id="appendix">Appendix A: further Potts regimes</h2>
<p class="lede">The precise statements are in the companion paper, <em>Further Potts Zero-Free Regions from Coupling Independence</em>, included in the repository as <a href="appendix.pdf">appendix.pdf</a>. Each regime has a coupling-independence theorem and a zero-free theorem.</p>
@@APPENDIX@@

<h2 id="definitions">Definitions used in the statements</h2>
<p class="lede">The Lean objects the statements are written in, next to the paper's notation.</p>
<div class="card">@@GLOSSARY@@</div>

<h2 id="literature">Literature hypotheses</h2>
<p class="lede">The exact Lean propositions that stand for cited results. They are theorem hypotheses, not axioms, so a Lean proof only shows that the conclusion follows from them.</p>
@@LITERATURE@@

<h2 id="reproduce">Reproduce</h2>
<div class="card repro">
<p>Last full verification: @@VERIFIED@@. From a clone of <a href="@@REPO@@">the repository</a>:</p>
<pre><code>lake exe cache get
LEAN_NUM_THREADS=2 bash scripts/check-all.sh</code></pre>
<p>This builds the library with warnings treated as errors and audits the transitive axioms of every project declaration. <a href="verification.json">verification.json</a> records the source hashes and the result. To regenerate this page after changing the Lean sources or the papers, commit the Lean changes and run</p>
<pre><code>python3 scripts/site/build.py --paper ../main.tex --companion ../companion</code></pre>
</div>
</main>
<footer class="wrap">Generated @@DATE@@ from commit <a href="@@COMMITURL@@">@@COMMIT@@</a> by <code>scripts/site/build.py</code>.</footer>
<div id="tip" role="tooltip" hidden></div>

<script>
(function () {
  var COMMIT = "@@COMMIT@@", CHECKS = @@CHECKS@@;
  var store = window.localStorage, prefix = "ci2zf-review:" + COMMIT + ":";
  var root = document.documentElement, themeButton = document.getElementById("theme");
  function showTheme() { themeButton.textContent = "Theme: " + (root.dataset.theme || "auto"); }
  themeButton.addEventListener("click", function () {
    var next = { "": "light", light: "dark", dark: "" }[root.dataset.theme || ""];
    if (next) { root.dataset.theme = next; store.setItem("ci2zf-theme", next); }
    else { delete root.dataset.theme; store.removeItem("ci2zf-theme"); }
    showTheme();
  });
  showTheme();

  var boxes = Array.prototype.slice.call(document.querySelectorAll("input[data-key]"));
  var notes = Array.prototype.slice.call(document.querySelectorAll("textarea[data-note]"));
  boxes.forEach(function (b) { b.checked = store.getItem(prefix + b.dataset.key) === "1"; });
  notes.forEach(function (t) { t.value = store.getItem(prefix + "note:" + t.dataset.note) || ""; });
  function update() {
    var done = 0;
    document.querySelectorAll("article.result").forEach(function (card) {
      var own = card.querySelectorAll("input[data-key]"), k = 0;
      own.forEach(function (b) { if (b.checked) k++; });
      card.querySelector(".card-progress .k").textContent = k;
      card.classList.toggle("done", k === own.length);
      done += k;
    });
    var total = boxes.length;
    document.querySelector("#meter > span").style.width = (100 * done / total) + "%";
    document.getElementById("meter").setAttribute("aria-valuenow", done);
    document.getElementById("progress-text").textContent = done + " of " + total + " checks";
    applyFilters();
  }
  boxes.forEach(function (b) {
    b.addEventListener("change", function () {
      if (b.checked) store.setItem(prefix + b.dataset.key, "1"); else store.removeItem(prefix + b.dataset.key);
      update();
    });
  });
  notes.forEach(function (t) {
    t.addEventListener("input", function () { store.setItem(prefix + "note:" + t.dataset.note, t.value); });
  });

  var group = "all", query = document.getElementById("q"), openOnly = document.getElementById("open-only");
  function visible(el) {
    var card = document.getElementById(el.dataset.result);
    var matchGroup = group === "all" || el.dataset.group === group;
    var q = query.value.trim().toLowerCase();
    var matchQuery = !q || el.dataset.search.indexOf(q) >= 0;
    var matchOpen = !openOnly.checked || !card.classList.contains("done");
    return matchGroup && matchQuery && matchOpen;
  }
  function applyFilters() {
    document.querySelectorAll("[data-result]").forEach(function (el) {
      el.classList.toggle("hidden", !visible(el));
    });
  }
  document.querySelectorAll("button[data-filter]").forEach(function (b) {
    b.addEventListener("click", function () {
      group = b.dataset.filter;
      document.querySelectorAll("button[data-filter]").forEach(function (o) {
        o.setAttribute("aria-pressed", o === b ? "true" : "false");
      });
      applyFilters();
    });
  });
  query.addEventListener("input", applyFilters);
  openOnly.addEventListener("change", applyFilters);

  document.getElementById("reset").addEventListener("click", function () {
    if (!confirm("Clear all ticks and notes for this commit?")) return;
    boxes.forEach(function (b) { b.checked = false; store.removeItem(prefix + b.dataset.key); });
    notes.forEach(function (t) { t.value = ""; store.removeItem(prefix + "note:" + t.dataset.note); });
    update();
  });
  document.getElementById("export").addEventListener("click", function () {
    var lines = ["# Lean review, commit " + COMMIT, ""];
    document.querySelectorAll("article.result").forEach(function (card) {
      lines.push("## " + card.querySelector(".ref").textContent + ": " + card.dataset.title);
      card.querySelectorAll("input[data-key]").forEach(function (b, i) {
        lines.push("- [" + (b.checked ? "x" : " ") + "] " + CHECKS[i]);
      });
      var note = card.querySelector("textarea").value.trim();
      if (note) lines.push("", "Notes: " + note);
      lines.push("");
    });
    var blob = new Blob([lines.join("\n")], { type: "text/markdown" });
    var a = document.createElement("a");
    a.href = URL.createObjectURL(blob);
    a.download = "ci2zf-review-" + COMMIT + ".md";
    document.body.appendChild(a); a.click(); a.remove();
  });

  var tip = document.getElementById("tip");
  function show(cell) {
    tip.replaceChildren();
    var v = document.createElement("strong"); v.textContent = cell.dataset.tipValue;
    var l = document.createElement("div"); l.textContent = cell.dataset.tipLabel;
    tip.appendChild(v); tip.appendChild(l); tip.hidden = false;
    var r = cell.getBoundingClientRect(), w = tip.offsetWidth, h = tip.offsetHeight;
    var x = Math.min(Math.max(8, r.left + r.width / 2 - w / 2), window.innerWidth - w - 8);
    var y = r.top - h - 8 < 8 ? r.bottom + 8 : r.top - h - 8;
    tip.style.left = x + "px"; tip.style.top = y + "px";
  }
  function hide() { tip.hidden = true; }
  document.querySelectorAll("td.cell.on").forEach(function (c) {
    c.addEventListener("pointerenter", function () { show(c); });
    c.addEventListener("focus", function () { show(c); });
    c.addEventListener("pointerleave", hide);
    c.addEventListener("blur", hide);
  });
  window.addEventListener("scroll", hide, { passive: true });

  update();
  function renderMath() {
    if (!window.renderMathInElement) return;
    renderMathInElement(document.body, {
      delimiters: [{ left: "\\[", right: "\\]", display: true }, { left: "\\(", right: "\\)", display: false }],
      macros: @@MACROS@@, throwOnError: false, strict: "ignore",
      ignoredTags: ["script", "noscript", "style", "textarea", "pre", "code", "option"]
    });
  }
  if (document.readyState === "complete") renderMath(); else window.addEventListener("load", renderMath);
})();
</script>
</body>
</html>
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--paper", default=str(REPO.parent / "main.tex"),
                        help="main.tex of the paper (its .aux and .bbl must sit beside it)")
    parser.add_argument("--companion", default=str(REPO.parent / "companion"),
                        help="directory of the companion paper (with main.tex, main.aux, main.bbl)")
    parser.add_argument("--out", default="docs/index.html", help="output path, relative to the repository")
    build(parser.parse_args())


if __name__ == "__main__":
    main()
