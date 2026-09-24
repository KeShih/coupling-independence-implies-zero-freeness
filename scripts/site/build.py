#!/usr/bin/env python3
"""Build docs/index.html, a visual guide for checking the Lean statements
against the two papers.

Run from the repository root after the library is built:

    python3 scripts/site/build.py --paper ../main.tex --companion ../companion

Everything on the Lean side is read from the compiled environment:
signatures, source ranges, axioms, and the cited results each proof
depends on. The paper side is extracted from the LaTeX sources, with
numbers and citation labels taken from their .aux and .bbl files. Source
links are pinned to the last commit that changed the Lean sources, so
commit Lean changes first.
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

# Results the papers cite. "statement" lists the Lean propositions that express
# them, "proof" the Lean theorems that prove them, and "targets" the proofs
# whose use marks a result as depending on the citation (default: "proof").
CITED = [
    dict(id="cffgzz", short="CFFGZZ Thm 20",
         statement=["CI2ZF.Potts.ExternalCriticalHardColouringTheorem",
                    "CI2ZF.Potts.CriticalHardColouringInput"],
         proof=["CI2ZF.Potts.external_critical_hard_colouring_theorem",
                "CI2ZF.Potts.critical_hard_colouring_input",
                "CI2ZF.Appendix.CV.option_root_ci_critical"],
         targets=["CI2ZF.Appendix.CV.option_root_ci_critical"],
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
         statement=["CI2ZF.Appendix.CLMM.Literature"],
         proof=["CI2ZF.Appendix.CLMM.Eq10.sphere_estimate_proof", "CI2ZF.Appendix.CLMM.literature"],
         targets=["CI2ZF.Appendix.CLMM.Eq10.sphere_estimate_proof"],
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
         proof=["CI2ZF.Appendix.CLMM.Lemma513.sphere_to_coupling"],
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
         statement=["CI2ZF.Appendix.Girth.CavityTree.CLMMInfluenceIdentity"],
         proof=["CI2ZF.Appendix.Girth.CavityTree.clmmInfluenceIdentity"],
         source="Chen, Liu, Mani, Moitra, arXiv:2304.01954v3, Lemma 8.7",
         url="https://arxiv.org/abs/2304.01954v3",
         meaning="The tree influence–Jacobian factorization, summed over a whole tree level.",
         route="Proved from the actual finite-tree Gibbs law, one level at a time."),
    dict(id="bbr-26", short="BBR Prop 2.6(i)",
         statement=["CI2ZF.Appendix.BBR.Literature"],
         proof=["CI2ZF.Appendix.BBR.proposition_2_6_i_holds", "CI2ZF.Appendix.BBR.literature"],
         targets=["CI2ZF.Appendix.BBR.proposition_2_6_i_holds"],
         source="Bencs, Berrekkal, Regts, Near optimal bounds for weak and strong spatial "
                "mixing for the anti-ferromagnetic Potts model on trees, Electron. J. Probab. "
                "30 (2025), paper 65, Proposition 2.6(i)",
         url="https://doi.org/10.1214/25-EJP1327",
         meaning="The segment-weight bound for cavity messages, used only at its printed "
                 "hypothesis Δ ≥ q + 3. BBR.Literature bundles it with Theorem 2.5.",
         route="Follows BBR Section 4 under the printed hypotheses, but two uses of the "
               "concavity of log, a chord bound and Jensen's inequality, replace their Lemma "
               "4.1 and Lemma 4.2(i); Lemma 4.3 is proved from a derivative. The application "
               "handles separate degree-gap-two cases arithmetically rather than extending "
               "the published proposition."),
    dict(id="bbr-25", short="BBR Thm 2.5",
         statement=[],
         proof=["CI2ZF.Appendix.BBR.theorem_2_5_holds"],
         source="Bencs, Berrekkal, Regts, Electron. J. Probab. 30 (2025), paper 65, Theorem 2.5",
         url="https://doi.org/10.1214/25-EJP1327",
         meaning="The squared-norm contraction of the square-root message recursion; the "
                 "theorem_2_5 field of BBR.Literature.",
         route="As in BBR Section 3: the mean value theorem along the segment between the two "
               "message vectors, Cauchy–Schwarz, and the pointwise Jacobian bound."),
]

RESULTS = [
    dict(id="thm-intro-main", group="main", paper=[("main", "thm:intro-main")],
         lean=["CI2ZF.Potts.potts_main_theorem", "CI2ZF.Potts.potts_main_strict"],
         defs=["CI2ZF.Potts.UniformPottsZeroFree"],
         notes=["On the line 6q = 11Δ, where the paper cites CFFGZZ Theorem 20, Lean uses the "
                "Carlson–Vigoda contraction on the critical line instead; the theorem has no "
                "hypothesis beyond the paper's.",
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
         lean=["CI2ZF.Potts.critical_line_transfer_coupling_inputs",
               "CI2ZF.Potts.root_critical_uniform_ci"],
         defs=["CI2ZF.Potts.CriticalHardColouringInput"],
         notes=["The x = 0 bound, for which the paper cites CFFGZZ Theorem 20, is "
                "critical_hard_colouring_input, proved by the Carlson–Vigoda contraction on the "
                "critical line.",
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
         notes=["No regime takes a hypothesis. At the critical pairs (Δ, q) = (6j, 11j) of "
                "regime (i), the x = 0 bound comes from the Carlson–Vigoda contraction on the "
                "critical line.",
                "Regime (iii) uses the large-girth coupling theorem, with its CLMM results "
                "(Lemma 8.7, Equation (10), Lemma 5.13) proved in Lean, instead of the x = 0 "
                "results cited in the paper's proof. The residual version needs girth only of "
                "G^τ."]),
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
               "CI2ZF.Appendix.near_vigoda_uniform_ci",
               "CI2ZF.Appendix.near_vigoda_zero_free", "CI2ZF.Appendix.integer_reduction"],
         notes=["At the critical pairs (Δ, q) = (6j, 11j), j ≤ 20, where the companion cites "
                "CFFGZZ Theorem 20, Lean uses the Carlson–Vigoda contraction on the critical "
                "line; for Δ ≥ 125 it uses the Carlson–Vigoda theorem.",
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
                "The same contraction holds on the critical line q ≥ 11Δ/6 for every Δ ≥ 6, "
                "with the same constant (Regime, option_root_ci_critical).",
                "The coupling theorems are stated on boundary-count data (PinningData (Option O) C), "
                "which covers every (G, τ, r)."]),
    dict(id="large-girth", group="appendix", title="Large-girth regime",
         table="Δ ≥ 3, q ≥ Δ + 3, girth(G^τ) ≥ g*(q, Δ); zero-free near [0, 1]",
         paper=[("companion", "thm:high-girth-soft-ci"), ("companion", "thm:additional-potts-zf")],
         lean=["CI2ZF.Appendix.Girth.high_girth_coupling",
               "CI2ZF.Appendix.Girth.high_girth_residual_original_zero_free"],
         defs=["CI2ZF.Appendix.Girth.UniformResidualGirthPottsZeroFree"],
         notes=["CLMM Lemma 8.7, Equation (10) and Lemma 5.13 are proved in Lean. Lemma 8.7 is "
                "used in its level-summed form, and Equation (10) needs strong spatial mixing only "
                "beyond a fixed depth K₀; the companion justifies both in the proof of its "
                "Lemma 6.10.",
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

# Phrase-by-phrase correspondences. Each paper quote must occur verbatim in the
# statement with that label, and each Lean quote in the displayed Lean source
# (whitespace aside); the build fails otherwise. A paper quote starting with
# "math:" is rendered as a formula. A row with no paper quote is a Lean
# hypothesis that the paper's statement does not contain.

def pair(label, paper, lean, code, note=""):
    return dict(label=label, paper=paper, lean=lean, code=[code] if isinstance(code, str) else code,
                note=note)


MAIN = "CI2ZF.Potts.potts_main_theorem"
UZF = "CI2ZF.Potts.UniformPottsZeroFree"
TRANSFER = "CI2ZF.Potts.graph_class_potts_transfer_of_bounded"
INPUTS = "CI2ZF.Potts.GraphClassTransferInputs"
RCB = "CI2ZF.Potts.GraphClassRootCouplingBound"
STRICT = "CI2ZF.Potts.root_strict_ci"
HARD = "CI2ZF.ConditionalHardCouplingEstimate"
POS = "CI2ZF.Potts.root_positive_ci"
CRIT = "CI2ZF.Potts.critical_line_transfer_coupling_inputs"
FIELD = "CI2ZF.LeeYang.graph_class_normalized_field_transfer"
LYNV = "CI2ZF.LeeYang.near_vigoda_vertex_field_zero_free"
LYHG = "CI2ZF.LeeYang.high_girth_original_field_transfer"
UVF = "CI2ZF.LeeYang.UniformVertexFieldZeroFree"
EDGELY = "CI2ZF.LeeYang.edge_lee_yang"
HOLANT = "CI2ZF.Holant.exists_uniform_holant_polytube"
BMATCH = "CI2ZF.Holant.bmatching_uniform_polytube"
BCOVER = "CI2ZF.Holant.bcover_uniform_polytube"
NVZF = "CI2ZF.Appendix.near_vigoda_zero_free"
NVCI = "CI2ZF.Appendix.near_vigoda_transfer_inputs"
CVCI = "CI2ZF.Appendix.CV.option_root_ci"
HGCI = "CI2ZF.Appendix.Girth.high_girth_coupling"
HTZF = "CI2ZF.Appendix.high_temperature_zero_free"
BBRZF = "CI2ZF.Appendix.BBR.high_girth_residual_original_zero_free"
EDGECI = "CI2ZF.Appendix.Edge.root_children_ci"
EDGEZF = "CI2ZF.Appendix.Edge.edge_potts_zero_free"
G5CI = "CI2ZF.Appendix.Girth.girth_five_coupling"
ZERO_FREE_MATH = r"math:\nZpin{G}{\tau}(z)\ne0 \qquad\text{for every }z\in\mathcal U_\eps([0,1])."
CONSEQUENTLY = (r"Consequently, \(\Zpin{G}{\tau}(z)=z^{m_G(\tau)}\nZpin{G}{\tau}(z)\) has no zeros in the same "
                r"neighbourhood except, when \(m_G(\tau)\ge1\), a zero of multiplicity \(m_G(\tau)\) at \(z=0\).")
FULL_ZEROS = ["fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G",
              "(fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G"]

PAIRS = {
    "thm-intro-main": [
        pair("thm:intro-main", r"Let \(q,\Deg\) be integers with \(\Deg\ge2\)", MAIN, "(q Δ : ℕ) (hΔ : 2 ≤ Δ)",
             "The colours are Fin q."),
        pair("thm:intro-main", r"\(q\ge11\Deg/6\)", MAIN, "(hq : 11 * Δ ≤ 6 * q)",
             "The same inequality with denominators cleared."),
        pair("thm:intro-main", r"There exists \(\eps=\eps(q,\Deg)>0\) such that", MAIN,
             "∃ eps > 0, UniformPottsZeroFree.{u, 0} (Fin q) Δ eps",
             "ε is chosen before any graph or pinning, so it depends only on q and Δ."),
        pair("thm:intro-main", r"for every finite simple graph \(G\) of maximum degree at most \(\Deg\) and every pinning \(\tau\)",
             UZF, "∀ {V : Type u} [Fintype V] (G : SimpleGraph V), (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C",
             "Any finite vertex type and any partial colouring, proper or not."),
        pair("thm:intro-main", ZERO_FREE_MATH, UZF,
             "(∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0)",
             "thickening eps pottsInterval is the open ε-neighbourhood of [0, 1] in ℂ."),
        pair("thm:intro-main", CONSEQUENTLY, UZF, FULL_ZEROS, "pinnedConflictCount is m_G(τ)."),
    ],
    "thm-potts-transfer": [
        pair("thm:potts-transfer", r"\(q\ge\Deg+1\)", TRANSFER, "(hq : Δ + 1 ≤ Fintype.card C)",
             "q is Fintype.card C, the number of colours. Lean does not need Δ ≥ 2."),
        pair("thm:potts-transfer", r"let \(\mathcal G\) be a class of finite simple graphs of maximum degree at most "
             r"\(\Deg\) that is closed under taking induced subgraphs", TRANSFER,
             ["(F : GraphClass.{u})",
              "(hdegree : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G → ∀ w, G.degree w ≤ Δ)"],
             "A GraphClass is closed under induced subgraphs by definition."),
        pair("thm:potts-transfer", r"\(\mathcal G\) satisfies coupling independence at \(x=0\) with constant \(C_0\)",
             INPUTS, "hard : ∃ cost : ℝ, GraphClassRootCouplingBound F C PinningData.hardParameter cost",
             "hardParameter is the activity x = 0."),
        pair("thm:potts-transfer", r"for every \(\delta\in(0,1]\), it satisfies coupling independence on "
             r"\([\delta,1]\) with a finite constant \(C_\delta\)", INPUTS,
             "positive : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∃ cost : ℝ, ∀ x : PinningData.NonnegativeParameter, "
             "(x : ℝ) ∈ Set.Icc delta 1 → GraphClassRootCouplingBound F C x cost"),
        pair("thm:potts-transfer", r"Then there is \(\eps>0\) such that, for every \(G\in\mathcal G\) and every pinning \(\tau\),",
             TRANSFER, "∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G → ∀ tau : PartialColouring V C,"),
        pair("thm:potts-transfer", ZERO_FREE_MATH, TRANSFER,
             "(∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0)"),
        pair("thm:potts-transfer", CONSEQUENTLY, TRANSFER, FULL_ZEROS),
    ],
    "def-potts-ci": [
        pair("def:potts-ci", r"for every \(G\in\mathcal G\), every pinning \(\tau\), every \(r\in V^\tau\), all "
             r"\(a,b\in\colours\)", RCB,
             "∀ {A : Type u} [Fintype A] (G : SimpleGraph A), F.contains G → ∀ (tau : PartialColouring A C) "
             "(r : tau.FreeVertex) (a b : C)", "r ranges over the free vertices."),
        pair("def:potts-ci", r"and every \(x\in J\)", RCB, "(x : PinningData.NonnegativeParameter)",
             "The Lean definition is the bound at one activity; coupling independence on J quantifies it over J, "
             "as GraphClassTransferInputs does."),
        pair("def:potts-ci", r"the two pinned laws are well defined", RCB,
             ["(ha : 0 < (rootChildData tau G r a).partition x)", "(hb : 0 < (rootChildData tau G r b).partition x)"],
             "Lean assumes the two partition functions are positive rather than asserting it; for q ≥ Δ + 1 they "
             "always are."),
        pair("def:potts-ci", r"math:\WHam\!\left( \mupin{G}{\tau^{r=a}}{x}, \mupin{G}{\tau^{r=b}}{x} \right)\le C.",
             RCB, "W ham ((rootChildData tau G r a).gibbs x x.property ha) ((rootChildData tau G r b).gibbs x x.property hb) ≤ cost",
             "W ham is the Hamming Wasserstein distance."),
        pair("def:potts-ci", r"Both laws live on the common free set \(V^\tau\setminus\{r\}\)",
             "CI2ZF.Potts.rootChildData", "PinningData (RootRemaining tau r) C",
             "Both child instances live on RootRemaining tau r, the free vertices other than r."),
    ],
    "thm-strict-ci": [
        pair("thm:strict-ci", r"\(\Deg\ge2\) and \(q>11\Deg/6\)", STRICT,
             ["(hΔ : 2 ≤ Δ)", "(hq : (11 / 6 : ℝ) * Δ < Fintype.card C)"]),
        pair("thm:strict-ci", r"for every \(G\in\Gdeg\), every pinning \(\tau\), every \(x\in[0,1]\), every "
             r"\(r\in V^\tau\), and all \(a,b\in\colours\)", STRICT,
             ["(tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)",
              "(hdegree : ∀ v, G.degree v ≤ Δ)", "(x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1)"]),
        pair("thm:strict-ci", r"math:\le \frac{2(1-x)\Deg}{q-(11/6)(1-x)\Deg}", STRICT, "≤ ciBound (Fintype.card C) Δ x",
             "ciBound q Δ x is this fraction; see the definitions."),
        pair("thm:strict-ci", r"math:\le\frac2{\gapq}", "CI2ZF.Potts.root_strict_uniform_ci",
             "≤ 2 / ciGap (Fintype.card C) Δ", "ciGap q Δ is γ₀ = q/Δ − 11/6."),
    ],
    "prop-hard-one-step": [
        pair("prop:hard-one-step", r"The updates admit a coupling \((X',Y')\), with \(X'\sim\flip_{F_X}(X,\cdot)\) "
             r"and \(Y'\sim\flip_{F_Y}(Y,\cdot)\)", HARD,
             ["hardStep (activeHardListInstance I (activatedSet I X ω)) X",
              "hardStep (activeHardListInstance I (activatedSet I Y ω)) Y"],
             "hardStep F X is the hard flip update Φ_F(X, ·); activatedSet I X ω is the hard instance chosen by the "
             "common coins ω."),
        pair(None, None, HARD, ["X v ≠ Y v → (∀ u, u ≠ v → X u = Y u) →", "∀ ω : I.Constraint → Bool,"],
             "From the paragraph before the proposition: X and Y differ exactly at v, and ω is the common activation "
             "outcome 𝒜."),
        pair("prop:hard-one-step", r"math:nq\,\E[\Ham(X',Y')-1\mid\mathcal A]", HARD,
             "((Fintype.card V : ℝ) * Fintype.card C) * (W ham (hardStep (activeHardListInstance I (activatedSet I X ω)) X) "
             "(hardStep (activeHardListInstance I (activatedSet I Y ω)) Y) - 1)",
             "The expectation under the best coupling is the Wasserstein distance W ham; n = |V| and q = |C|."),
        pair("prop:hard-one-step", r"math:\le\frac{11}{6}\sum_c|N_c|-\ell.", HARD,
             "≤ (11 / 6 : ℝ) * rootFreeCoinCount I v ω - rootCommonListCount I X Y v ω",
             "rootFreeCoinCount counts the edges at v active on at least one side, which is Σ_c |N_c|; "
             "rootCommonListCount is ℓ."),
        pair(None, None, "CI2ZF.conditionalHardCouplingEstimate",
             "(I : PinningData V C) : ConditionalHardCouplingEstimate I",
             "Proved for every instance; the coupling is constructed in the proof."),
    ],
    "prop-full-interval-hci": [
        pair("prop:full-interval-hci", r"For every \(G\in\Gdeg\), every pinning \(\tau\), every \(r\in V^\tau\), all "
             r"\(a,b\in\colours\)", POS,
             ["(tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)",
              "(hdegree : ∀ v, G.degree v ≤ Δ)"]),
        pair("prop:full-interval-hci", r"every \(x\in(0,1]\) satisfying \(q>(11/6)(1-x)\Deg\)", POS,
             "{x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hq : (11 / 6 : ℝ) * (1 - x) * Δ < Fintype.card C)"),
        pair("prop:full-interval-hci", r"math:\le\frac{2(1-x)\Deg}{q-(11/6)(1-x)\Deg}.", POS,
             "≤ ciBound (Fintype.card C) Δ x"),
        pair("prop:full-interval-hci", r"Let \(q,\Deg\) be positive integers with \(\Deg\ge2\).", None, None,
             "Not needed in Lean."),
        pair("prop:full-interval-hci", r"If \(q>11\Deg/6\), the bound \eqref{eq:vigoda-master-ci} also holds at \(x=0\).",
             STRICT, "(hq : (11 / 6 : ℝ) * Δ < Fintype.card C) (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1)",
             "The case x = 0 is part of root_strict_ci, whose activity ranges over all of [0, 1]."),
    ],
    "cor-critical-line-input": [
        pair("cor:critical-line-input", r"\(\Deg\ge2\) and \(q=11\Deg/6\)", CRIT,
             "(hΔ : 2 ≤ Δ) (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)"),
        pair("cor:critical-line-input", r"Then \(\Gdeg\) satisfies coupling independence at \(x=0\) with a finite constant",
             "CI2ZF.Potts.critical_hard_colouring_input", "CriticalHardColouringInput.{u, v} C Δ hcolours",
             "The paper's proof cites CFFGZZ Theorem 20 here. Lean proves the bound with the Carlson–Vigoda "
             "contraction on the critical line; Δ ≥ 6 holds there by critical_line_degree_ge_six."),
        pair("cor:critical-line-input", r"for every \(\delta\in(0,1]\) it satisfies coupling independence on "
             r"\([\delta,1]\) with constant \(12/(11\delta)\)", "CI2ZF.Potts.root_critical_uniform_ci",
             ["(hx : (x : ℝ) ∈ Set.Icc δ 1)", "≤ 12 / (11 * δ)"]),
        pair(None, None, CRIT, "TransferCouplingInputs.{u, v} C Δ hcolours",
             "The conclusion packages both bounds as the inputs of the transfer theorem."),
    ],
    "prop-field-transfer": [
        pair("prop:field-transfer", r"\(q\ge\Deg+1\)", FIELD, "(hq : Δ + 1 ≤ Fintype.card C)",
             "Lean does not need Δ ≥ 2."),
        pair("prop:field-transfer", r"let \(\mathcal G\subseteq\Gdeg\) be closed under taking induced subgraphs and "
             r"satisfy \(C_0\)-coupling independence at \(x=0\)", FIELD,
             ["(F : GraphClass.{u})", "(cost : ℝ) (hCI : GraphClassRootCouplingBound F C PinningData.hardParameter cost)"],
             "The degree bound is imposed on each graph in the conclusion rather than on the class."),
        pair("prop:field-transfer", r"There is \(\theta=\theta(q,\Deg,C_0)\in(0,1/2]\)", FIELD,
             "∃ θ > 0, θ ≤ (1 / 2 : ℝ)", "θ is chosen after the class F."),
        pair("prop:field-transfer", r"for every \(G\in\mathcal G\) and every pinning \(\tau\)", FIELD,
             "F.contains G → (∀ v, G.degree v ≤ Δ) → ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ)",
             "ℓ is the field λ."),
        pair("prop:field-transfer", r"math:\nZpin{G}{\tau}(\lambda)\ne0 \qquad\text{whenever }|\lambda_{u,c}-1|<\theta "
             r"\quad(u\in V^\tau,\ c\in\colours).", FIELD,
             "(∀ (v : tau.FreeVertex) c, ‖ℓ v.val c - 1‖ ≤ θ) → normalizedFieldPartition tau G ℓ ≠ 0",
             "Lean uses the closed polydisc, which is stronger."),
    ],
    "thm-lee-yang": [
        pair("thm:lee-yang", r"\(q\ge(11/6-1/84000)\Deg\)", LYNV,
             "(hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C)", "Regime (i)."),
        pair("thm:lee-yang", r"\(\Deg\ge125\) and \(q\ge1.809\Deg\)", "CI2ZF.LeeYang.cv_vertex_field_zero_free",
             "(hΔ : 125 ≤ Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)", "Regime (ii)."),
        pair("thm:lee-yang", r"\(\Deg\ge3\) and \(q\ge\Deg+3\)", LYHG,
             "(hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C)", "Regime (iii)."),
        pair("thm:lee-yang", r"there is an integer \(g_{\rm LY}=g_{\rm LY}(q,\Deg)\ge3\) for which we put "
             r"\(\mathcal G=\Gdegg{g_{\rm LY}}\)", LYHG, ["∃ g : ℕ, 3 ≤ g ∧", "(g : ℕ∞) ≤ G.egirth →"],
             "egirth is the girth, infinite for forests."),
        pair("thm:lee-yang", r"In each case there is \(\theta=\theta(q,\Deg)\in(0,1/2]\)", LYNV,
             "∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧ UniformVertexFieldZeroFree.{u,v} C Δ θ"),
        pair("thm:lee-yang", r"math:\nZpin{G}{\tau}(\lambda)\ne0 \qquad\text{whenever }|\lambda_{u,c}-1|<\theta "
             r"\quad(u\in V^\tau,\ c\in\colours).", UVF,
             "(∀ (v : tau.FreeVertex) c, ‖ℓ v.val c - 1‖ ≤ θ) → normalizedFieldPartition tau G ℓ ≠ 0",
             "Regimes (i) and (ii) use the closed polydisc; regime (iii) states the open one."),
        pair("thm:lee-yang", r"For a proper pinning, the corresponding statement for \(\Zpin{G}{\tau}(\lambda)\) follows",
             UVF, "((∀ v : tau.domain, ℓ v.val (tau.colour v) ≠ 0) → (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G))"),
    ],
    "cor-edge-lee-yang": [
        pair("cor:edge-lee-yang", r"\(\Deg\ge2\) and \(q\ge3\Deg\)", EDGELY, "(hΔ : 2 ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)"),
        pair("cor:edge-lee-yang", r"There exists \(\theta=\theta(q,\Deg)\in(0,1/2]\)", EDGELY, "∃ θ > 0, θ ≤ (1 / 2 : ℝ)"),
        pair("cor:edge-lee-yang", r"for every finite simple graph \(G=(V,E)\) of maximum degree at most \(\Deg\) and "
             r"every edge-colour pinning \(\tau\)", EDGELY,
             "∀ {V : Type u} [Fintype V] (G : SimpleGraph V), (∀ v, G.degree v ≤ Δ) → ∀ (tau : PartialColouring "
             "G.edgeSet C) (ℓ : G.edgeSet → C → ℂ)", "An edge-colour pinning is a partial colouring of G.edgeSet."),
        pair("cor:edge-lee-yang", r"math:\widehat Z_G^{\mathrm{edge},\tau}(\lambda)\ne0 \qquad\text{whenever}\qquad "
             r"\abs{\lambda_{e,c}-1}<\theta \quad(e\in E\setminus\Lambda_E,\ c\in\colours).", EDGELY,
             "(∀ (e : tau.FreeVertex) c, ‖ℓ e.val c - 1‖ ≤ θ) → normalizedFieldPartition tau G.lineGraph ℓ ≠ 0",
             "The edge-colour polynomial is the vertex-colour polynomial of the line graph."),
        pair("cor:edge-lee-yang", r"For a proper pinning, \(Z_G^{\mathrm{edge},\tau}(\lambda)\ne0\) when the same "
             r"condition is imposed at every edge-colour pair.", EDGELY,
             "((∀ e : tau.domain, ℓ e.val (tau.colour e) ≠ 0) → (fullFieldPartition tau G.lineGraph ℓ ≠ 0 ↔ "
             "ProperPinning tau G.lineGraph))"),
    ],
    "thm-holant-box": [
        pair("thm:holant-box", r"a finite family \(\mathcal F\) of log-concave symmetric Boolean signatures "
             r"satisfying \(f(0)>0\) for every \(f\in\mathcal F\)", HOLANT, "(F : Finset Signature)",
             "Signature bundles symmetry, log-concavity, interval support and f(0) > 0."),
        pair("thm:holant-box", r"For every \(R>0\), there is \(\eps=\eps(\Deg,\mathcal F,R)>0\)", HOLANT,
             "{R : ℝ} (hR : 0 ≤ R) : ∃ ε : ℝ, 0 < ε ∧", "Lean also allows R = 0 and any Δ."),
        pair("thm:holant-box", r"For every finite simple graph \(G=(V,E)\) of maximum degree at most \(\Deg\), "
             r"every assignment \((f_v)_{v\in V}\) with \(f_v\in\mathcal F\) of arity \(\deg_G(v)\)", HOLANT,
             "∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V), (∀ v, G.degree v ≤ Δ) → ∀ f : V → "
             "Signature, (∀ v, f v ∈ F) → (∀ v, (f v).arity = G.degree v) →"),
        pair("thm:holant-box", r"math:Z_{G,\mathbf f}(\mathbf z)\ne0 \qquad\text{whenever}\qquad "
             r"\mathbf z\in\mathcal U_\eps([0,R])^E.", HOLANT,
             "(∀ e ∈ G.edgeFinset, ∃ x : ℝ, x ∈ Icc 0 R ∧ ‖z e - (x : ℂ)‖ < ε) → graphPartition G (complexValues f) z ≠ 0",
             "Each edge activity is within ε of its own point of [0, R]."),
    ],
    "cor-bmatching": [
        pair("cor:bmatching-short", r"Fix an integer \(\Deg\ge2\) and \(R>0\). There is \(\eps=\eps(\Deg,R)>0\)",
             BMATCH, "(Δ : ℕ) {R : ℝ} (hR : 0 < R) : ∃ ε > 0,"),
        pair("cor:bmatching-short", r"every integer vector \(\mathbf b=(b_v)_{v\in V}\) with \(0\le b_v\le\deg_G(v)\)",
             BMATCH, "∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →"),
        pair("cor:bmatching-short", r"whenever \(\mathbf z\in\mathcal U_\eps([0,R])^E\)", BMATCH,
             "∀ z ∈ edgePolytube G.edgeFinset ε 0 R, matchingPartition graphIncidence G.edgeFinset b z ≠ 0",
             "matchingPartition is the b-matching polynomial."),
    ],
    "cor-bcover": [
        pair("cor:bcover-short", r"Fix an integer \(\Deg\ge2\) and \(0<\lambda_-\le\lambda_+<\infty\). There is "
             r"\(\eps=\eps(\Deg,\lambda_-)>0\)", BCOVER, "(Δ : ℕ) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) : ∃ ε > 0,",
             "Here a = λ₋ and c = λ₊. The remarks explain how the width depends on λ₊."),
        pair("cor:bcover-short", r"whenever \(\mathbf z\in\mathcal U_\eps([\lambda_-,\lambda_+])^E\)", BCOVER,
             "∀ z ∈ edgePolytube G.edgeFinset ε a c, coverPartition graphIncidence G.edgeFinset b z ≠ 0"),
    ],
    "near-vigoda": [
        pair("thm:additional-potts-zf", r"\(q\ge(11/6-1/84000)\Deg\)", NVZF,
             "(hΔ : 2 ≤ Δ) (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C)", "Regime (i) of Theorem 4.1."),
        pair("thm:additional-potts-zf", r"There exists \(\eps=\eps(q,\Deg)>0\)", NVZF,
             "∃ eps > 0, UniformPottsZeroFree.{u,v} C Δ eps", "The same conclusion as Theorem 1.1 of the main paper."),
        pair("thm:potts-ci-regimes", r"There exists \(C_0=C_0(q,\Deg)<\infty\) such that \(\mathcal G\) satisfies "
             r"\(C_0\)-coupling independence at \(x=0\), and for every \(\delta\in(0,1]\) there exists "
             r"\(C_\delta=C_\delta(q,\Deg)<\infty\) such that it satisfies \(C_\delta\)-coupling independence on "
             r"\([\delta,1]\).", NVCI, "∃ hcolours : Δ + 1 ≤ Fintype.card C, TransferCouplingInputs.{u,v} C Δ hcolours"),
        pair("thm:potts-ci-regimes", r"The same is true in the noncritical cases of regime~\textup{(i)}.",
             "CI2ZF.Appendix.near_vigoda_uniform_ci",
             "∀ x : PinningData.NonnegativeParameter, (x : ℝ) ≤ 1 → RootCouplingBound.{u,v} C Δ hcolours x cost",
             "One constant for every x ∈ [0, 1], and Lean proves it in every case of regime (i), the critical "
             "pairs included."),
        pair("thm:potts-ci-regimes", r"the endpoint bound is supplied independently by the hard-colouring coupling theorem",
             "CI2ZF.Potts.critical_hard_colouring_input", "CriticalHardColouringInput.{u, v} C Δ hcolours",
             "The companion cites CFFGZZ Theorem 20 for this endpoint bound; Lean proves it with the "
             "Carlson–Vigoda contraction on the critical line."),
        pair("lem:int-reduction", r"Let \(\Deg\) and \(q\) be integers with \(3\le\Deg\le124\)",
             "CI2ZF.Appendix.integer_reduction", "{Δ q : ℕ} (hΔ : 3 ≤ Δ) (hΔmax : Δ ≤ 124)"),
        pair("lem:int-reduction", r"Then either \(q>11\Deg/6\), or \((\Deg,q)=(6j,11j)\) for some integer \(1\le j\le20\).",
             "CI2ZF.Appendix.integer_reduction",
             "(11 / 6 : ℝ) * Δ < q ∨ ∃ j : ℕ, 1 ≤ j ∧ j ≤ 20 ∧ Δ = 6 * j ∧ q = 11 * j"),
    ],
    "cv": [
        pair("thm:cv-ci", r"\(\Deg\ge125\) and \(q\ge1.809\,\Deg\)", CVCI,
             "{Δ : ℕ} (hΔ : 125 ≤ Δ) (hd : I.DegreeBound Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)"),
        pair("thm:cv-ci", r"For every \(G\in\Gdeg\), every pinning \(\tau\), every \(x\in[0,1]\), every "
             r"\(r\in V^\tau\), and all \(a,b\in\colours\)", CVCI,
             ["(I : PinningData (Option O) C)", "(a b : C) (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1)"],
             "A graph with a pinning and a root is encoded as a residual instance on Option O, the root being none; "
             "this covers every (G, τ, r)."),
        pair("thm:cv-ci", r"math:\le \frac{2}{m_0\delta_{\rm CV}} =\frac{409060125}{50858}<8043.19.", CVCI, "≤ ciConstant",
             "ciConstant is 409060125/50858; ciConstant_bounds proves that it is below 8043.19."),
        pair("thm:additional-potts-zf", r"\(\Deg\ge125\) and \(q\ge1.809\Deg\)", "CI2ZF.Appendix.CV.zero_free",
             "(hΔ : 125 ≤ Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) : ∃ eps > 0, UniformPottsZeroFree.{u,v} C Δ eps",
             "Regime (ii) of Theorem 4.1, with no literature hypothesis."),
    ],
    "large-girth": [
        pair("thm:high-girth-soft-ci", r"Let $q,\Deg$ be integers with $\Deg\ge3$ and $q\ge\Deg+3$.", HGCI,
             "(Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C)"),
        pair("thm:high-girth-soft-ci", r"There exist $g_*=g_*(q,\Deg)\ge3$ and $C_*=C_*(q,\Deg)<\infty$", HGCI,
             "∃ (g : ℕ) (K : ℝ), 3 ≤ g ∧ 0 ≤ K ∧",
             "Both constants are chosen before x, the graph and the pinning."),
        pair("thm:high-girth-soft-ci", r"the bound below holds for every $x\in[0,1]$", HGCI,
             "∀ x : PinningData.NonnegativeParameter, (x : ℝ) ≤ 1 →"),
        pair("thm:high-girth-soft-ci", r"every pinning $\tau$ with \(\operatorname{girth}(G^\tau)\ge g_*\)", HGCI,
             "(largeGirthFamily.{u,v} C g).RootCouplingBound Δ (by omega) x K",
             "largeGirthFamily C g consists of the residual instances whose free graph has girth at least g."),
        pair("thm:additional-potts-zf", r"with the additional condition \(\operatorname{girth}(G^\tau)\ge g_*\) in "
             r"regime~\textup{(iii)}", "CI2ZF.Appendix.Girth.high_girth_residual_original_zero_free",
             "∃ g : ℕ, 3 ≤ g ∧ ∃ eps > 0, UniformResidualGirthPottsZeroFree.{u,v} C Δ g eps",
             "The girth condition is on the free graph only; see UniformResidualGirthPottsZeroFree."),
    ],
    "high-temperature": [
        pair("cor:intro-high-temperature", r"fix \(x_*\in(0,1]\)", HTZF, "{x₀ : ℝ} (hx₀ : 0 < x₀)",
             "x₀ is x*. Lean needs neither x₀ ≤ 1 nor Δ ≥ 2."),
        pair("cor:intro-high-temperature", r"math:q>\frac{11}{6}(1-x_*)\Deg,", HTZF,
             "(hq : (11 / 6 : ℝ) * (1 - x₀) * Δ < Fintype.card C)"),
        pair("cor:intro-high-temperature", r"then there is \(\eps=\eps(q,\Deg,x_*)>0\) such that, for every finite "
             r"simple graph \(G\) of maximum degree at most \(\Deg\) and every pinning \(\tau\)", HTZF,
             "∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), (∀ v, G.degree v ≤ Δ) → ∀ tau : "
             "PartialColouring V C,"),
        pair("cor:intro-high-temperature", r"math:\nZpin{G}{\tau}(z)\ne0 \qquad\text{for every }z\in\mathcal U_\eps([x_*,1]).",
             HTZF, "∀ z ∈ thickening eps (Complex.ofReal '' Icc x₀ 1), normalizedPartition tau G z ≠ 0 ∧ "
             "fullPartition tau G z ≠ 0",
             "One ε serves the normalized and the full polynomial; the companion shrinks ε below x* for the latter."),
        pair(None, None, "CI2ZF.Appendix.high_temperature_graph_coupling",
             "(2 * (1 - x₀) * Δ / ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x₀) * Δ))",
             "The coupling constant C* of the companion's proof, valid on [x*, 1]."),
    ],
    "bbr": [
        pair("thm:intro-bbr-interval", r"math:q\ge3, \qquad \frac{\Deg}{q}\ge\frac{e-1/2}{e-1}.", BBRZF,
             "(hq : 3 ≤ Fintype.card C) (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)"),
        pair("thm:intro-bbr-interval", r"If \((q,\Deg)=(3,4)\), put \(x_0:=3/4\).", "CI2ZF.Appendix.BBR.start",
             "if q = 3 ∧ Δ = 4 then 3 / 4 else intervalStart q Δ"),
        pair("thm:intro-bbr-interval", r"math:k:=e\frac{\Deg-q/2}{\Deg-q}, \qquad x_0:=1-\frac q\Deg "
             r"\left(1-\frac{k}{\Deg}\right)^2 \frac{\Deg-k}{\Deg-k/2}.", "CI2ZF.Appendix.BBR.intervalStart",
             "1 - q / Δ * (1 - parameter q Δ / Δ) ^ 2 * (Δ - parameter q Δ) / (Δ - parameter q Δ / 2)",
             "parameter q Δ is k = e(Δ − q/2)/(Δ − q)."),
        pair("thm:intro-bbr-interval", r"there are \(g_{\rm BBR}=g_{\rm BBR}(q,\Deg)\ge3\) and \(\eps=\eps(q,\Deg)>0\)",
             BBRZF, "∃ g : ℕ, 3 ≤ g ∧ ∃ eps > 0,"),
        pair("thm:intro-bbr-interval", r"every pinning \(\tau\) with \(\operatorname{girth}(G^\tau)\ge g_{\rm BBR}\)",
             BBRZF, "(g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth →",
             "(tau.toPinningData G).graph is the free graph G^τ."),
        pair("thm:intro-bbr-interval", r"math:\nZpin{G}{\tau}(z)\ne0 \qquad\text{for every }z\in\mathcal U_\eps([x_0,1]).",
             BBRZF, "∀ z ∈ thickening eps (Complex.ofReal '' Icc (start (Fintype.card C) Δ) 1), normalizedPartition "
             "tau G z ≠ 0 ∧ fullPartition tau G z ≠ 0", "One ε serves the normalized and the full polynomial."),
        pair("thm:bbr-large-girth-ci", r"every \(x\in[x_0,1]\)", "CI2ZF.Appendix.BBR.high_girth_coupling",
             "∀ (x : ℝ) (hx : 0 < x), x ∈ Icc (start (Fintype.card C) Δ) 1 →"),
    ],
    "edge-potts": [
        pair("thm:soft-edge-ci", r"\(q\ge3\Deg\)", EDGECI,
             "(hΔ : 1 ≤ Δ) (hdegree : ∀ v, G.degree v ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)"),
        pair("thm:soft-edge-ci", r"every edge-colour pinning \(\tau\), every \(x\in[0,1]\), every free edge "
             r"\(i\in E\setminus\operatorname{dom}\tau\), and all \(a,b\in\colours\)", EDGECI,
             ["(τ : PartialColouring G.edgeSet C) (r : τ.FreeVertex) (a b : C)",
              "(x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1)"], "The free edge i is r."),
        pair("thm:soft-edge-ci", r"math:\WHam\!\left( (\edgegibbs{G}{x})^{\tau,i=a}, (\edgegibbs{G}{x})^{\tau,i=b} "
             r"\right) \le\Deg-1.", EDGECI, ["W ham ((rootChildData τ G.lineGraph r a).gibbs x x.property", "≤ (Δ : ℝ) - 1"],
             "The edge-colour laws are the vertex-colour laws of the line graph G.lineGraph."),
        pair("cor:soft-edge-zf", r"\(\Deg\ge2\) and \(q\ge3\Deg\)", EDGEZF, "(hΔ : 2 ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C)"),
        pair("cor:soft-edge-zf", r"math:\nZpin{L(G)}{\tau}(z)\ne0 \qquad\text{whenever }\dist(z,[0,1])<\eps.", EDGEZF,
             "(∀ z ∈ thickening eps pottsInterval, normalizedPartition τ G.lineGraph z ≠ 0)"),
        pair("cor:soft-edge-zf", r"its order of vanishing there is \(m_{L(G)}(\tau)\)", EDGEZF,
             "(fullPolynomial τ G.lineGraph).rootMultiplicity 0 = τ.pinnedConflictCount G.lineGraph"),
    ],
    "girth-five": [
        pair("thm:girth5-ci", r"For every fixed $0<\delta\le1$ there is a threshold $\Deg_5(\delta)\ge\Deg_0(\delta)$",
             G5CI, "{δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hThreshold : girthFiveCIThreshold δ ≤ Δ)",
             "Lean's Δ₅(δ) is the explicit girthFiveCIThreshold δ, which is at least Δ₀(δ)."),
        pair("thm:girth5-ci", r"$q\ge(1+\delta)\Deg$", G5CI, "(hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ))"),
        pair("thm:girth5-ci", r"every graph $G\in\Gdeg$ and pinning $\tau$ with $\operatorname{girth}(G^\tau)\ge5$", G5CI,
             "∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C), I.DegreeBound Δ → 5 ≤ I.graph.egirth →",
             "The pinned graph with its root is a residual instance on Option O."),
        pair("thm:girth5-ci", r"for every $r\in V^\tau$, all $c,d\in\colours$, and every $x\in[0,1]$", G5CI,
             ["∀ (x : ℝ) (hx : 0 ≤ x), x ≤ 1 →", "∀ (a b : C)"]),
        pair("thm:girth5-ci", r"math:\WHam\!\left( \mupin{G}{\tau^{r=c}}{x}, \mupin{G}{\tau^{r=d}}{x} "
             r"\right)\le C_5(q,\Deg,\delta)<\infty", G5CI,
             ["∃ cost : ℝ, 0 ≤ cost ∧", "W ham ((optionChildData I a).gibbs x hx ha) ((optionChildData I b).gibbs x hx hb) ≤ cost"],
             "One constant for all graphs, pinnings and activities."),
        pair("thm:unrestricted-girth5", r"There exists $\eps_5=\eps_5(q,\Deg,\delta)>0$",
             "CI2ZF.Appendix.Girth.girth_five_residual_original_zero_free",
             "∃ eps > 0, UniformResidualGirthPottsZeroFree.{u,v} C Δ 5 eps",
             "Girth at least five of the free graph; no short-cycle counts are assumed."),
        pair("thm:potts-gap-girth5", r"math:\mathcal L^2\succeq\gamma_\delta \mathcal L, \qquad "
             r"\gamma_\delta=\frac{\delta}{4(2+\delta)}.", "CI2ZF.Appendix.Girth.girth_five_closed_poincare",
             "GraphProjections.spectralGap δ * variance (I.gibbs x hx hZ) f ≤ ∑ v, expectReal (I.gibbs x hx hZ) "
             "(fun σ => (f σ - GraphHeatBath.projection I x hx hlocal v f σ) ^ 2)",
             "The equivalent Poincaré form: spectralGap δ is γ_δ, and the right side is the Dirichlet form of the "
             "rate-one Glauber dynamics."),
    ],
}

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

def libraryResult (env : Environment) (self d : Name) : MetaM Bool := do
  if d == self || d.isInternal || isPrivateName d then return false
  let s := d.toString
  unless s.startsWith "CI2ZF." || s.startsWith "PottsCI." do return false
  let last := match d with
    | .str _ l => l
    | _ => ""
  for p in ["match_", "proof_", "eq_", "_", "inst"] do
    if last.startsWith p then return false
  if (env.getProjectionFnInfo? d).isSome then return false
  if ← isInstance d then return false
  match env.find? d with
  | some (.thmInfo _) => return true
  | some (.defnInfo _) => return true
  | _ => return false

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => ""

def citedTargets : Array Name := #[@@TARGETS@@]

/-- The proofs of cited results that `start` depends on, through the types
and values of library constants (auxiliary ones included). -/
def reachedTargets (env : Environment) (start : Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[start]
  let mut found : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if n != start && citedTargets.contains n then found := found.push n
    if let some ci := env.find? n then
      let cs := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
      for c in cs do
        let s := c.toString
        if (s.startsWith "CI2ZF." || s.startsWith "PottsCI.") && !seen.contains c then
          stack := stack.push c
  return found

#eval show MetaM Unit from do
  let env ← getEnv
  for n in siteNames do
    match env.find? n with
    | none => IO.println (Json.compress (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)]))
    | some ci =>
      let sig ← PrettyPrinter.ppSignature n
      let rng ← findDeclarationRanges? n
      let modName := moduleOf env n
      let axs ← collectAxioms n
      let used := ci.type.getUsedConstants.map (·.toString)
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .inductInfo _ => "structure"
        | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque" | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor" | .quotInfo _ => "quotient"
      let (l0, l1) := match rng with
        | some r => (r.range.pos.line, r.range.endPos.line)
        | none => (0, 0)
      let direct ← match ci with
        | .thmInfo t => t.value.getUsedConstants.filterM (libraryResult env n)
        | _ => pure #[]
      let mut deps : Array Json := #[]
      for d in direct do
        let r ← findDeclarationRanges? d
        let doc ← findDocString? env d
        let (d0, d1) := match r with
          | some r => (r.range.pos.line, r.range.endPos.line)
          | none => (0, 0)
        let dkind := match env.find? d with
          | some (.thmInfo _) => "theorem"
          | _ => "def"
        deps := deps.push (Json.mkObj [("name", toJson d.toString), ("kind", toJson dkind), ("module", toJson (moduleOf env d)),
          ("start", toJson d0), ("end", toJson d1), ("doc", toJson (doc.getD ""))])
      IO.println (Json.compress (Json.mkObj [("name", toJson n.toString), ("kind", toJson kind),
        ("module", toJson modName), ("start", toJson l0), ("end", toJson l1),
        ("signature", toJson (sig.fmt.pretty 96)), ("axioms", toJson (axs.map (·.toString))),
        ("used", toJson used), ("deps", Json.arr deps),
        ("cited", toJson ((reachedTargets env n).map (·.toString)))]))
"""


def lean_extract(names, targets):
    source = (LEAN_TEMPLATE.replace("@@NAMES@@", ", ".join("`" + n for n in names))
              .replace("@@TARGETS@@", ", ".join("`" + n for n in targets)))
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
        end = re.search(r":=(?:\s*by)?[ \t]*(?:\n|$)", block)
        cut = end.start() if end else block.find(":=")
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


def source_url(commit, module, start, end):
    return "%s/blob/%s/%s#L%d-L%d" % (GITHUB, commit, module_file(module).as_posix(), start, end)


def first_sentence(doc):
    doc = " ".join(doc.split())
    match = re.match(r"(.+?\.)(\s|$)", doc)
    return (match.group(1) if match else doc)[:220]


def norm(text):
    return " ".join(text.split())


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


def cited_in_type(info, by_statement):
    """Cited results whose Lean statement occurs in the type: hypotheses."""
    return [c for c in CITED if any(by_statement.get(u) is c for u in info["used"])]


def cited_in_proof(info, by_target):
    """Cited results whose Lean proof the declaration depends on."""
    return [c for c in CITED if any(by_target.get(t) is c for t in info.get("cited", []))]


def decl_html(info, commit, index, show_cited=True):
    by_statement, by_target = index
    doc, code = lean_excerpt(info)
    path = module_file(info["module"]).as_posix()
    url = "%s/blob/%s/%s#L%d-L%d" % (GITHUB, commit, path, info["start"], info["end"])
    axioms = info["axioms"]
    standard = set(axioms) <= {"propext", "Classical.choice", "Quot.sound"}
    badges = ['<span class="badge good" title="%s"><span aria-hidden="true">✓</span> Standard axioms only</span>'
              % e(", ".join(axioms) or "no axioms") if standard else
              '<span class="badge bad"><span aria-hidden="true">!</span> Axioms: %s</span>' % e(", ".join(axioms))]
    if show_cited:
        for c in cited_in_type(info, by_statement):
            badges.append('<a class="badge bad" href="#lit-%s"><span aria-hidden="true">!</span>'
                          'Assumes %s</a>' % (c["id"], e(c["short"])))
        for c in cited_in_proof(info, by_target):
            badges.append('<a class="badge hyp" href="#lit-%s"><span class="dot" aria-hidden="true"></span>'
                          'Uses %s, proved in Lean</a>' % (c["id"], e(c["short"])))
    return f"""
<div class="decl">
  <div class="decl-head"><code class="decl-name">{e(short(info["name"]))}</code>
    <span class="kind">{e(info["kind"])}</span>
    <a class="src" href="{e(url)}">{e(Path(path).name)} · lines {info["start"]}–{info["end"]}</a></div>
  {'<p class="doc">%s</p>' % doc_html(doc) if doc else ''}
  <pre class="lean"><code>{e(code)}</code></pre>
  <details class="elab"><summary>Elaborated type</summary><pre class="lean"><code>{e(info["signature"])}</code></pre></details>
  <div class="badges">{" ".join(badges)}</div>
  {uses_html(info, commit)}
</div>"""


def uses_html(info, commit):
    deps = [d for d in info.get("deps") or [] if d["kind"] == "theorem"]
    if info["kind"] != "theorem" or not deps:
        return ""
    items = "".join(
        '<li><a href="%s"><code>%s</code></a>%s</li>'
        % (e(source_url(commit, d["module"], d["start"], d["end"])), e(short(d["name"])),
           ' <span class="ud">%s</span>' % doc_html(first_sentence(d["doc"])) if d["doc"] else "")
        for d in deps)
    word = "lemma" if len(deps) == 1 else "lemmas"
    return ('<details class="uses"><summary>The proof applies %d library %s directly</summary><ul>%s</ul></details>'
            % (len(deps), word, items))


def check_quotes(papers, info):
    """Every quotation in PAIRS must occur verbatim in its source. Returns their number."""
    problems, count = [], 0
    bodies = {}
    for result in RESULTS:
        for src, label in result["paper"]:
            env, title, body = papers[src].statement(label)
            bodies[label] = norm((title or "") + " " + body)
    for rid, rows in PAIRS.items():
        labels = {label for _, label in next(r for r in RESULTS if r["id"] == rid)["paper"]}
        for row in rows:
            if row["paper"]:
                if row["label"] not in labels:
                    problems.append(f"{rid}: {row['label']} is not one of this result's statements")
                quote = norm(row["paper"][5:] if row["paper"].startswith("math:") else row["paper"])
                if quote not in bodies.get(row["label"], ""):
                    problems.append(f"{rid}: paper quote not found in {row['label']}: {quote[:80]}")
                count += 1
            if row["lean"]:
                _, code = lean_excerpt(info[row["lean"]])
                for fragment in row["code"]:
                    if norm(fragment) not in norm(code):
                        problems.append(f"{rid}: Lean quote not found in {row['lean']}: {fragment[:80]}")
                    count += 1
    if problems:
        sys.exit("Quotations that do not match their sources:\n  " + "\n  ".join(problems))
    return count


def correspondence_html(result, papers, converters, info, first_label):
    rows = PAIRS.get(result["id"], [])
    if not rows:
        return ""
    body = []
    for row in rows:
        if row["paper"]:
            source = next(src for src, label in result["paper"] if label == row["label"])
            conv = converters[source]
            if row["paper"].startswith("math:"):
                paper = TexToHtml.render_math(conv.math(row["paper"][5:]), False)
            else:
                paper = conv.convert(row["paper"], block=False)
            if row["label"] != first_label:
                env, _, _ = papers[source].statement(row["label"])
                paper = '<span class="from">%s %s</span>%s' % (
                    ENV_WORDS[env], e(papers[source].number(row["label"])), paper)
        else:
            paper = '<span class="absent">Not in the statement</span>'
        if row["lean"]:
            lean = '<span class="from">%s</span>%s' % (
                e(short(row["lean"])), "".join("<code>%s</code>" % e(f) for f in row["code"]))
        else:
            lean = '<span class="absent">Not needed in Lean</span>'
        body.append('<tr><td class="p">%s</td><td class="l">%s</td><td class="n">%s</td></tr>'
                    % (paper, lean, e(row["note"])))
    return ('<section class="corr"><h4>How the statements correspond</h4><table>'
            '<thead><tr><th scope="col">Paper</th><th scope="col">Lean</th><th scope="col">Remark</th></tr></thead>'
            '<tbody>%s</tbody></table></section>' % "".join(body))


def build(args):
    if git("status", "--porcelain", "--", "CI2ZF", "CI2ZF.lean"):
        sys.exit("Commit the Lean sources first, so that source links are pinned.")
    commit = git("log", "-1", "--format=%h", "--abbrev=7", "--", "CI2ZF", "CI2ZF.lean",
                 "lakefile.toml", "lean-toolchain", "lake-manifest.json")
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
    names += [n for c in CITED for n in c["statement"] + c["proof"]] + [g[0] for g in GLOSSARY]
    names += [row["lean"] for rows in PAIRS.values() for row in rows if row["lean"]]
    names = list(dict.fromkeys(names))
    by_target = {t: c for c in CITED for t in c.get("targets", c["proof"])}
    by_statement = {n: c for c in CITED for n in c["statement"]}
    index = (by_statement, by_target)
    info = lean_extract(names, list(by_target))
    quotes = check_quotes(papers, info)

    # matrix and cards
    used_by = {c["id"]: [] for c in CITED}
    rows, cards = [], {"main": [], "appendix": []}
    for result in RESULTS:
        statements = [statement_html(papers, converters, src, label) for src, label in result["paper"]]
        ref, title_html = statements[0][0], statements[0][1] or e(result.get("title", ""))
        if result["group"] == "appendix":
            ref, title_html = "Appendix A", e(result["title"])
        plain_title = re.sub(r"<[^>]+>|\\[()]", "", title_html)
        result["_label"] = result.get("title") or ref
        for name in result["lean"]:
            for c in cited_in_type(info[name], by_statement):
                print(f"warning: {name} takes {c['short']} as a hypothesis", file=sys.stderr)
        uses = [c for c in CITED if any(c in cited_in_proof(info[n], by_target) for n in result["lean"])]
        for c in uses:
            used_by[c["id"]].append(result)
        search = " ".join([ref, re.sub(r"<[^>]+>", "", title_html), *result["lean"]]).lower()
        cells = []
        for c in CITED:
            if c in uses:
                via = [short(n) for n in result["lean"] if c in cited_in_proof(info[n], by_target)]
                cells.append('<td class="cell on" tabindex="0" data-tip-value="Proved in Lean, used by the proof" '
                             'data-tip-label="%s · %s"><span class="dot" aria-hidden="true"></span>'
                             '<span class="sr">used</span></td>' % (e(c["short"]), e(", ".join(via))))
            else:
                cells.append('<td class="cell"><span class="sr">not used</span></td>')
        count = ('<span class="none">none</span>' if not uses else "%d" % len(uses))
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
        lean_html = "".join(decl_html(info[n], commit, index) for n in result["lean"])
        if result.get("defs"):
            lean_html += '<p class="defs">Definitions: %s</p>' % ", ".join(
                '<a href="#def-%s"><code>%s</code></a>' % (e(n), e(short(n))) for n in result["defs"])
        notes = "".join("<li>%s</li>" % e(n) for n in result.get("notes", []))
        first_label = result["paper"][0][1]
        corr = correspondence_html(result, papers, converters, info, first_label)
        cards[result["group"]].append(f"""
<article class="card result" id="{result['id']}" data-result="{result['id']}" data-group="{result['group']}" data-search="{e(search)}" data-title="{e(html.unescape(plain_title))}">
  <header class="card-head">
    <div><div class="ref">{e(ref)}</div><h3>{title_html}</h3></div>
  </header>
  <div class="cols">
    <section class="side paper"><h4>Paper</h4>{paper_html}</section>
    <section class="side leanside"><h4>Lean</h4>{lean_html}</section>
  </div>
  {corr}
  {'<section class="notes"><h4>Remarks</h4><ul>%s</ul></section>' % notes if notes else ''}
</article>""")

    head = "".join('<th scope="col"><a href="#lit-%s" title="%s">%s</a></th>'
                   % (c["id"], e(c["source"]), e(c["short"])) for c in CITED)
    matrix = ('<table class="matrix"><thead><tr><th scope="col">Result</th>%s<th scope="col">Cited</th>'
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
    for c in CITED:
        users = used_by[c["id"]]
        statement = "".join(decl_html(info[n], commit, index, False) for n in c["statement"])
        proof = "".join(decl_html(info[n], commit, index, False) for n in c["proof"])
        user_links = ", ".join('<a href="#%s">%s</a>' % (r["id"], e(r["_label"])) for r in users)
        literature.append(f"""
<article class="card lit" id="lit-{c['id']}">
  <header class="card-head"><div><div class="ref">Cited result</div><h3>{e(c['short'])}</h3></div></header>
  <p class="source"><a href="{e(c['url'])}">{e(c['source'])}</a></p>
  <p>{e(c['meaning'])}</p>
  <p class="route"><strong>Lean proof.</strong> {e(c['route'])}</p>
  <p class="users">Used by the proofs of: {user_links or 'no result shown on this page'}</p>
  {'<h4 class="sub">Lean statement</h4>' + statement if statement else ''}
  <h4 class="sub">Lean proof</h4>{proof}
</article>""")

    tiles = [
        ("Build jobs", f"{record['build_jobs']:,}", "warnings are errors"),
        ("Audited declarations", f"{record['audited_project_declarations']:,}", "transitive axiom check"),
        ("Library modules", f"{record['joint_import_closure_files']:,}", "all reachable from CI2ZF"),
        ("Axioms used", str(len(record["allowed_axioms"])), " · ".join(record["allowed_axioms"])),
        ("Verified quotations", f"{quotes:,}", f"in {sum(len(v) for v in PAIRS.values())} correspondences"),
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
        "@@MACROS@@": json.dumps(macros).replace("</", "<\\/"), "@@KATEX@@": KATEX,
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
  --serif: "Copernicus", "Tiempos Text", "Tiempos Headline", ui-serif, "New York", Georgia, Cambria, "Times New Roman", serif;
  --sans: "Styrene B", "Styrene A", ui-sans-serif, system-ui, -apple-system, "Segoe UI", Helvetica, Arial, sans-serif;
  --mono: ui-monospace, "SF Mono", SFMono-Regular, Menlo, Consolas, monospace;
  --page: #faf9f5; --surface: #ffffff; --surface-2: #f5f4ee; --code-bg: #f0eee6;
  --ink: #141413; --ink-2: #5e5d59; --muted: #87867f; --grid: #e8e6dc; --border: #e3e1d7;
  --accent: #c96442; --accent-ink: #a9502f; --accent-wash: rgba(201, 100, 66, 0.07); --track: #f1ddd3;
  --good: #0ca30c; --good-ink: #006300; --bad: #d03b3b;
  --btn: #141413; --btn-ink: #faf9f5;
  --shadow: 0 1px 2px rgba(20, 20, 19, 0.05), 0 10px 28px rgba(20, 20, 19, 0.08);
}
@media (prefers-color-scheme: dark) {
  :root:where(:not([data-theme="light"])) {
    color-scheme: dark;
    --page: #262624; --surface: #30302e; --surface-2: #2b2b29; --code-bg: #1f1e1d;
    --ink: #faf9f5; --ink-2: #c2c0b6; --muted: #9c9a92; --grid: #3d3d3a; --border: rgba(250, 249, 245, 0.10);
    --accent: #d57250; --accent-ink: #e8a08a; --accent-wash: rgba(213, 114, 80, 0.13); --track: #5a3426;
    --good: #0ca30c; --good-ink: #0ca30c; --bad: #d03b3b;
    --btn: #faf9f5; --btn-ink: #141413;
    --shadow: 0 1px 2px rgba(0, 0, 0, 0.25), 0 10px 28px rgba(0, 0, 0, 0.35);
  }
}
:root[data-theme="dark"] {
  color-scheme: dark;
  --page: #262624; --surface: #30302e; --surface-2: #2b2b29; --code-bg: #1f1e1d;
  --ink: #faf9f5; --ink-2: #c2c0b6; --muted: #9c9a92; --grid: #3d3d3a; --border: rgba(250, 249, 245, 0.10);
  --accent: #d57250; --accent-ink: #e8a08a; --accent-wash: rgba(213, 114, 80, 0.13); --track: #5a3426;
  --good: #0ca30c; --good-ink: #0ca30c; --bad: #d03b3b;
  --btn: #faf9f5; --btn-ink: #141413;
  --shadow: 0 1px 2px rgba(0, 0, 0, 0.25), 0 10px 28px rgba(0, 0, 0, 0.35);
}
* { box-sizing: border-box; }
html { scroll-padding-top: 76px; }
body { margin: 0; background: var(--page); color: var(--ink); font: 15.5px/1.6 var(--sans);
  -webkit-font-smoothing: antialiased; text-rendering: optimizeLegibility; }
a { color: var(--accent-ink); text-decoration: underline; text-underline-offset: 3px;
  text-decoration-thickness: 1px; text-decoration-color: color-mix(in srgb, var(--accent-ink) 35%, transparent); }
a:hover { text-decoration-color: var(--accent-ink); }
:focus-visible { outline: 2px solid var(--accent); outline-offset: 2px; border-radius: 6px; }
code, pre { font-family: var(--mono); font-size: 12.5px; }
:not(pre) > code { background: var(--code-bg); border-radius: 5px; padding: 1px 5px; }
.wrap { max-width: 1200px; margin: 0 auto; padding: 0 28px; }
.eyebrow, .side h4, .notes h4, .corr h4, .card-head .ref {
  font: 600 11.5px/1.4 var(--sans); letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); margin: 0 0 10px; }
.topbar { position: sticky; top: 0; z-index: 5; border-bottom: 1px solid var(--grid);
  background: color-mix(in srgb, var(--page) 86%, transparent); backdrop-filter: saturate(1.2) blur(12px); }
.topbar .wrap { display: flex; align-items: center; gap: 22px; height: 60px; }
.brand { display: flex; align-items: center; gap: 8px; font-weight: 600; white-space: nowrap; letter-spacing: -0.005em; }
.brand .spark { color: var(--accent); font-size: 19px; line-height: 1; }
.brand .brand-sub { color: var(--ink-2); font-weight: 500; }
.topbar nav { display: flex; gap: 18px; overflow-x: auto; font-size: 14px; }
.topbar nav a { color: var(--ink-2); text-decoration: none; white-space: nowrap; }
.topbar nav a:hover { color: var(--ink); }
.topbar .spacer, .filters .spacer { flex: 1; }
button { font: 500 13.5px/1 var(--sans); color: var(--ink); background: var(--surface); cursor: pointer;
  border: 1px solid var(--border); border-radius: 999px; padding: 9px 15px; transition: background .15s, border-color .15s; }
button:hover { background: var(--surface-2); border-color: color-mix(in srgb, var(--ink) 18%, transparent); }
button.chip[aria-pressed="true"] { background: var(--ink); color: var(--page); border-color: var(--ink); }
button.primary { background: var(--btn); color: var(--btn-ink); border-color: var(--btn); }
button.primary:hover { background: var(--btn); opacity: 0.88; }
button.ghost { background: transparent; }
header.hero { padding: 64px 0 18px; }
header.hero h1 { font: 400 clamp(34px, 4.6vw, 50px)/1.1 var(--serif); letter-spacing: -0.018em; margin: 0 0 18px; max-width: 900px; }
header.hero p { margin: 8px 0; color: var(--ink-2); font-size: 17px; line-height: 1.6; max-width: 780px; }
.tiles { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: 14px; margin: 34px 0 16px; }
.tile { background: var(--surface); border: 1px solid var(--border); border-radius: 16px; padding: 18px 20px; }
.tile-label { font-size: 13px; color: var(--ink-2); }
.tile-value { font: 500 32px/1.15 var(--sans); letter-spacing: -0.015em; margin-top: 6px; }
.tile-sub { font-size: 12px; color: var(--muted); margin-top: 4px; }
.filters { display: flex; flex-wrap: wrap; align-items: center; gap: 8px; margin: 22px 0 6px; }
.filters input[type="search"] { font: 14px var(--sans); color: var(--ink); background: var(--surface);
  border: 1px solid var(--border); border-radius: 999px; padding: 9px 16px; min-width: 280px; }
.filters input[type="search"]:focus { outline: 2px solid var(--accent); outline-offset: 1px; }
.filters label { font-size: 13.5px; color: var(--ink-2); display: flex; align-items: center; gap: 7px; margin-left: 6px; }
input[type="checkbox"] { accent-color: var(--accent); width: 16px; height: 16px; }
h2 { font: 400 32px/1.2 var(--serif); letter-spacing: -0.012em; margin: 64px 0 10px; }
h2 + .lede { margin: 0 0 8px; color: var(--ink-2); font-size: 16px; max-width: 820px; }
.card { background: var(--surface); border: 1px solid var(--border); border-radius: 20px; padding: 26px 30px; margin: 18px 0; }
.card-head { display: flex; justify-content: space-between; align-items: flex-start; gap: 16px; }
.card-head .ref { margin-bottom: 4px; }
.card-head h3 { margin: 0; font: 400 25px/1.25 var(--serif); letter-spacing: -0.01em; }
.cols { display: grid; grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); gap: 26px; margin-top: 18px; }
@media (max-width: 980px) { .cols { grid-template-columns: minmax(0, 1fr); } }
.side.paper { background: var(--surface-2); border-radius: 16px; padding: 18px 20px; align-self: start; }
.side.leanside { padding-top: 18px; }
details.stmt { border-top: 1px solid var(--grid); padding: 10px 0 2px; }
details.stmt:first-of-type { border-top: 0; padding-top: 0; }
details summary { cursor: pointer; color: var(--ink-2); font-size: 14px; }
details summary::marker { color: var(--muted); }
details summary .sref { color: var(--ink); font-weight: 600; }
.tex { margin-top: 10px; overflow-x: auto; font: 16.5px/1.65 var(--serif); color: var(--ink); }
.tex .katex { font-size: 1.07em; }
.tex .para { margin: 0 0 10px; }
.tex ol.roman { list-style: none; counter-reset: r; padding-left: 2.3em; margin: 6px 0 10px; }
.tex ol.roman > li { counter-increment: r; position: relative; margin: 3px 0; }
.tex ol.roman > li::before { content: "(" counter(r, lower-roman) ")"; position: absolute; left: -2.3em; color: var(--ink-2); }
.tex li[data-label]::before { content: attr(data-label) !important; }
.table-row { margin: 0 0 14px; font-size: 14px; color: var(--ink); }
.table-row .label { font: 600 11.5px var(--sans); letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted); margin-right: 8px; }
.decl { border-top: 1px solid var(--grid); padding: 14px 0; }
.decl:first-of-type { border-top: 0; padding-top: 0; }
.decl-head { display: flex; flex-wrap: wrap; align-items: baseline; gap: 8px; }
.decl-name { font-weight: 600; font-size: 13px; background: none !important; padding: 0 !important; }
.kind { font-size: 12px; color: var(--muted); }
.src { font-size: 12.5px; margin-left: auto; }
.doc { color: var(--ink-2); margin: 6px 0; font-size: 14px; }
pre.lean { background: var(--code-bg); border-radius: 12px; padding: 12px 14px; margin: 10px 0; overflow-x: auto; line-height: 1.5; }
details.elab summary { font-size: 13px; }
.badges { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 8px; }
.badge { display: inline-flex; align-items: center; gap: 6px; font-size: 12.5px; padding: 3px 11px; border-radius: 999px;
  border: 1px solid var(--border); color: var(--ink-2); background: var(--surface-2); text-decoration: none; }
a.badge:hover { border-color: var(--accent); }
.badge.good span[aria-hidden] { color: var(--good); font-weight: 700; }
.badge.bad span[aria-hidden] { color: var(--bad); font-weight: 700; }
.badge.hyp { color: var(--ink); }
.badge .dot, .matrix .dot { display: inline-block; width: 10px; height: 10px; border-radius: 50%; background: var(--accent);
  box-shadow: 0 0 0 2px var(--surface); }
.defs { font-size: 13.5px; color: var(--ink-2); margin: 10px 0 0; }
.defs a { text-decoration: none; }
.notes { margin-top: 20px; border-top: 1px solid var(--grid); padding-top: 16px; }
.notes ul { margin: 0; padding-left: 20px; }
.notes li { margin: 5px 0; }
.notes li::marker { color: var(--accent); }
.matrix-wrap { background: var(--surface); border: 1px solid var(--border); border-radius: 20px; overflow-x: auto; margin-top: 18px; }
table.matrix { border-collapse: collapse; width: 100%; font-size: 14px; }
.matrix th, .matrix td { padding: 10px 14px; border-bottom: 1px solid var(--grid); }
.matrix thead th { font: 600 12.5px/1.3 var(--sans); color: var(--ink-2); text-align: center; vertical-align: bottom; padding-top: 16px; max-width: 132px; }
.matrix thead th:first-child { text-align: left; padding-left: 22px; }
.matrix thead th a { color: var(--ink-2); text-decoration: none; }
.matrix thead th a:hover { color: var(--ink); }
.matrix tbody th { text-align: left; font-weight: 400; padding-left: 22px; min-width: 300px; }
.matrix tbody th a { color: var(--ink); text-decoration: none; font: 15.5px/1.4 var(--serif); }
.matrix tbody th a:hover { color: var(--accent-ink); }
.matrix .rref { font: 600 11px var(--sans); letter-spacing: 0.06em; text-transform: uppercase; color: var(--muted); margin-right: 6px; }
.matrix td.cell { text-align: center; width: 112px; }
.matrix td.cell.on:hover, .matrix td.cell.on:focus { background: var(--accent-wash); outline: none; }
.matrix td.cell.on:focus-visible { box-shadow: inset 0 0 0 2px var(--accent); }
.matrix td.count { text-align: center; color: var(--ink-2); white-space: nowrap; padding-right: 22px; }
.matrix .none span[aria-hidden] { color: var(--good); font-weight: 700; }
.matrix tbody tr:hover { background: var(--accent-wash); }
.matrix tbody tr:last-child th, .matrix tbody tr:last-child td { border-bottom: 0; }
.sr { position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0); white-space: nowrap; }
#tip { position: fixed; z-index: 20; max-width: 340px; background: var(--surface); color: var(--ink);
  border: 1px solid var(--border); border-radius: 12px; padding: 10px 12px; box-shadow: var(--shadow);
  font-size: 13px; pointer-events: none; }
#tip strong { display: block; font-size: 14px; }
#tip div { color: var(--ink-2); }
.gl-row { display: grid; grid-template-columns: minmax(0, 5fr) minmax(0, 7fr); gap: 20px; padding: 18px 0; border-top: 1px solid var(--grid); }
.gl-row:first-child { border-top: 0; padding-top: 4px; }
.gl-row pre.lean { align-self: start; margin: 0; }
@media (max-width: 980px) { .gl-row { grid-template-columns: minmax(0, 1fr); } }
.gl-meta p { margin: 6px 0; color: var(--ink-2); font-size: 14px; }
.notation { margin: 6px 0 4px; font: 17px var(--serif); }
.lit .source { font: 16px/1.55 var(--serif); }
.lit .users { font-size: 14px; color: var(--ink-2); }
.lit .route { font-size: 15px; line-height: 1.55; }
.lit h4.sub { font: 600 12px var(--sans); letter-spacing: 0.08em; text-transform: uppercase; color: var(--muted);
  margin: 20px 0 4px; }
.repro pre { background: var(--code-bg); border-radius: 12px; padding: 12px 14px; overflow-x: auto; }
footer { color: var(--muted); font-size: 13px; padding: 36px 0 64px; margin-top: 48px; border-top: 1px solid var(--grid); }
.corr { margin-top: 22px; border-top: 1px solid var(--grid); padding-top: 16px; }
.corr table { width: 100%; border-collapse: collapse; }
.corr thead th { font: 600 11.5px/1.4 var(--sans); letter-spacing: 0.08em; text-transform: uppercase;
  color: var(--muted); text-align: left; padding: 0 16px 8px 0; }
.corr td { vertical-align: top; padding: 11px 16px 11px 0; border-top: 1px solid var(--grid); }
.corr td.p { width: 36%; font: 15.5px/1.55 var(--serif); }
.corr td.l { width: 40%; }
.corr td.l code { display: block; white-space: pre-wrap; word-break: break-word; background: var(--code-bg);
  border-radius: 8px; padding: 6px 10px; margin: 0 0 5px; font-size: 12.5px; line-height: 1.5; }
.corr td.n { color: var(--ink-2); font-size: 13.5px; line-height: 1.5; }
.corr .from { display: block; font: 600 11px/1.5 var(--sans); letter-spacing: 0.05em; color: var(--muted); margin-bottom: 3px; }
.corr td.p .from { text-transform: uppercase; }
.corr .absent { color: var(--muted); font: italic 13.5px var(--sans); }
@media (max-width: 820px) {
  .corr thead { display: none; }
  .corr tr, .corr td { display: block; width: auto !important; }
  .corr td { border-top: 0; padding: 4px 0; }
  .corr tr { border-top: 1px solid var(--grid); padding: 8px 0; }
}
details.uses { margin-top: 10px; }
details.uses summary { font-size: 13px; }
details.uses ul { list-style: none; margin: 8px 0 0; padding: 0; }
details.uses li { margin: 5px 0; font-size: 13.5px; line-height: 1.45; }
details.uses li a { text-decoration: none; }
details.uses .ud { color: var(--ink-2); }
.hidden { display: none !important; }
@media print { .topbar, .filters { display: none; } .card { break-inside: avoid; } }
</style>
</head>
<body>
<div class="topbar"><div class="wrap">
  <span class="brand"><span class="spark" aria-hidden="true">✻</span>CI2ZF <span class="brand-sub">Lean ↔ paper</span></span>
  <nav aria-label="Sections"><a href="#status">Status</a><a href="#matrix">Cited results</a><a href="#main">Main paper</a><a href="#appendix">Appendix A</a><a href="#definitions">Definitions</a><a href="#literature">Their proofs</a><a href="#reproduce">Reproduce</a></nav>
  <span class="spacer"></span>
  <button id="theme" type="button" title="Switch colour theme">Theme: auto</button>
</div></div>

<main class="wrap">
<header class="hero" id="status">
  <div class="eyebrow">Lean formalization · commit @@COMMIT@@</div>
  <h1>The paper and its Lean formalization, side by side</h1>
  <p>For each headline result represented by a card on this page, the paper's statement is shown next to its corresponding Lean declaration. A table then matches the two phrase by phrase. The cards list the cited ingredients tracked by the formalization and the library lemmas each proof applies; the cited-results section records the formalized scope of those ingredients.</p>
  <p>Nothing on the Lean side is written by hand: signatures, axioms and dependencies are read from the compiled library at commit <a href="@@COMMITURL@@"><code>@@COMMIT@@</code></a>, and every source link points to that commit. Every quotation in the correspondence tables is checked verbatim against the paper's LaTeX and the Lean source when the page is built.</p>
</header>

<div class="tiles">@@TILES@@</div>

<div class="filters" role="search">
  <button type="button" class="chip" data-filter="all" aria-pressed="true">All</button>
  <button type="button" class="chip" data-filter="main" aria-pressed="false">Main paper</button>
  <button type="button" class="chip" data-filter="appendix" aria-pressed="false">Appendix A</button>
  <input type="search" id="q" placeholder="Filter by result or Lean name" aria-label="Filter by result or Lean name">
</div>

<h2 id="matrix">Cited results used by each proof</h2>
<p class="lede">A dot means that the Lean proof of the result depends, through the library, on the Lean proof of that cited ingredient. No paper-facing theorem takes a cited ingredient as a hypothesis; internal helper bundles may retain the formalized ingredient as a parameter. The axiom audit allows only Lean's standard axioms. Hover or focus a dot for the declarations involved.</p>
<div class="matrix-wrap">@@MATRIX@@</div>

<h2 id="main">Main paper</h2>
<p class="lede">Theorem numbers follow the current version of <em>Coupling Independence Implies Zero-Freeness</em>.</p>
@@MAIN@@

<h2 id="appendix">Appendix A: further Potts regimes</h2>
<p class="lede">The precise statements are in the companion paper, <em>Further Potts Zero-Free Regions from Coupling Independence</em>, included in the repository as <a href="appendix.pdf">appendix.pdf</a>. Each regime has a coupling-independence theorem and a zero-free theorem.</p>
@@APPENDIX@@

<h2 id="definitions">Definitions used in the statements</h2>
<p class="lede">The Lean objects the statements are written in, next to the paper's notation.</p>
<div class="card glossary">@@GLOSSARY@@</div>

<h2 id="literature">Cited results and their Lean proofs</h2>
<p class="lede">Each cited ingredient tracked by this formalization, the Lean proposition that expresses its formalized scope, and the Lean theorem that proves it. Where the Lean proof takes a different route from the cited paper, the card says so.</p>
@@LITERATURE@@

<h2 id="reproduce">Reproduce</h2>
<div class="card repro">
<p>Last full verification: @@VERIFIED@@. From a clone of <a href="@@REPO@@">the repository</a>:</p>
<pre><code>lake exe cache get
LEAN_NUM_THREADS=2 bash scripts/check-all.sh</code></pre>
<p>This builds the library with warnings treated as errors and audits the transitive axioms of every project declaration. <a href="verification.json">verification.json</a> records the source hashes and the result. To regenerate this page after changing the Lean sources or the papers, commit the Lean changes and run the command below; it stops if any quotation no longer matches its source.</p>
<pre><code>python3 scripts/site/build.py --paper ../main.tex --companion ../companion</code></pre>
</div>
</main>
<footer class="wrap">Generated @@DATE@@ from the Lean sources at commit <a href="@@COMMITURL@@">@@COMMIT@@</a> by <code>scripts/site/build.py</code>.</footer>
<div id="tip" role="tooltip" hidden></div>

<script>
(function () {
  var root = document.documentElement, themeButton = document.getElementById("theme");
  function showTheme() { themeButton.textContent = "Theme: " + (root.dataset.theme || "auto"); }
  themeButton.addEventListener("click", function () {
    var next = { "": "light", light: "dark", dark: "" }[root.dataset.theme || ""];
    if (next) { root.dataset.theme = next; localStorage.setItem("ci2zf-theme", next); }
    else { delete root.dataset.theme; localStorage.removeItem("ci2zf-theme"); }
    showTheme();
  });
  showTheme();

  var group = "all", query = document.getElementById("q");
  function applyFilters() {
    var q = query.value.trim().toLowerCase();
    document.querySelectorAll("[data-result]").forEach(function (el) {
      var show = (group === "all" || el.dataset.group === group) && (!q || el.dataset.search.indexOf(q) >= 0);
      el.classList.toggle("hidden", !show);
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
