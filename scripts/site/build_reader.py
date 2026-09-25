#!/usr/bin/env python3
"""Build docs/index.html, a reader that sets each paper, rendered from its LaTeX
source, beside the Lean statement of the numbered statement being read.

Run from the repository root:

    pip install pymupdf
    python3 scripts/site/build_reader.py

Nothing needs to be compiled. The script reads docs/coverage.json, the Lean
sources and, for each paper, its LaTeX source with the .bbl of a pdflatex
run (paper/main and paper/companion) and the compiled PDF
(docs/main.pdf and docs/appendix.pdf). paper_html.py renders the source,
numbers it as LaTeX does, and stops the build if a numbered statement differs
from coverage.json or a theorem, equation or section number differs from the
PDF's hyperref destinations. Figures and tikz-cd diagrams are drawn from
their TikZ source by tikz_html.py; one it cannot read is cut from the PDF into
docs/figures instead.
A paper whose source is absent is listed statement by statement. Lean
declarations are located by scanning the sources for their namespaces and
declaration keywords.

For each statement the panel shows the declarations in its coverage entry's
"lean" list as code, without their docstrings, and the definitions in its
"defs" list as rows with the paper's symbol and a gloss. The glosses come from
GLOSSARY in common.py and from DEFINITIONS below, which overrides it. Source
links are pinned to the last commit that changed the Lean sources, so commit
Lean changes first.
"""
import argparse
import datetime
import json
import re
import sys
import textwrap
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402  (statuses, cited results, glossary, LaTeX helpers)
import richtext  # noqa: E402

REPO = common.REPO
TEMPLATE = Path(__file__).resolve().parent / "reader.html"
PAPERS = {
    "main": dict(title="Coupling Independence Implies Zero-Freeness", short="Main paper",
                 tex="paper/main/main.tex", pdf="docs/main.pdf"),
    "companion": dict(title="Further Potts Zero-Free Regions from Coupling Independence",
                      short="Companion", tex="paper/companion/main.tex", pdf="docs/appendix.pdf"),
}
AUTHORS = "Shuai Shao and Ke Shi"
SIGNATURE_LINES = 40

# Definitions listed under a statement: Lean name -> (the paper's symbol in TeX,
# a one-line gloss in the paper's terms). Names missing here fall back to the
# GLOSSARY in common.py; the build stops if a listed definition has neither.
DEFINITIONS = {
    "PottsCI.FinDist.Coupling": (r"\Gamma(\mu,\nu)",
        "Couplings of μ and ν: nonnegative matrices with row sums μ and column sums ν."),
    "PottsCI.PartialColouring.freeGraph": (r"G^{\tau}",
        "The free graph G[V ∖ Λ], induced on the unpinned vertices."),
    "PottsCI.PinningData.Constraint": (r"\mathcal E_\tau",
        "The labelled constraints: free edges and individually labelled free–pinned edges."),
    "PottsCI.PinningData.DegreeBound": (r"\deg_{G^{\tau}}(u)+\sum_{c}b^{\tau}_{u}(c)\le\Delta",
        "At every free vertex, free degree plus number of pinned neighbours is at most Δ."),
    "PottsCI.PinningData.activeMass": (r"\textstyle\sum_\sigma J(A,\sigma)",
        "The total joint weight of the active set A: its unnormalized probability."),
    "PottsCI.PinningData.gibbs": (r"\mu^{\tau}_{G,x}",
        "The normalized Potts Gibbs law of the pinned instance at activity x."),
    "PottsCI.PinningData.hardList": (r"L^{\tau}(u)",
        "The hard effective list: the colours that no pinned neighbour of u carries."),
    "PottsCI.PinningData.hardParameter": ("x=0",
        "The activity x = 0, at which the Gibbs law is the hard-colouring law."),
    "PottsCI.PinningData.nonnegativeGibbs": (r"\mu^{\tau}_{G,x}",
        "The normalized Gibbs law at activity x ≥ 0; at x = 0 it is the hard-colouring law."),
    "PottsCI.PinningData.partition": (r"\widehat Z^{\tau}_{G}(x)",
        "The normalized pinned partition function of the instance at a real activity x."),
    "PottsCI.PinningData.spinLawGivenActive": (r"\Pr[\sigma\mid A]",
        "The law of σ given A under the joint weight J(A,σ) = x^{M−|A|}(1−x)^{|A|}1[σ ∈ Ω_{F_A}]."),
    "PottsCI.PinningData.uniformHardFibre": (r"\mathrm{Unif}(\Omega_{F_A})",
        "The uniform law on colourings satisfying every constraint in A, that is, on Ω_{F_A}."),
    "PottsCI.Vigoda.HardListInstance": ("F=(W,E,L)",
        "A hard list instance: a graph with a list of allowed colours at each vertex."),
    "PottsCI.Vigoda.RootLocalPair": ("(F_X,F_Y)",
        "The instances agree off v, and at v except for colours a and b; both colourings proper."),
    "PottsCI.Vigoda.activeHardListInstance": ("F_A",
        "The hard list instance of an active set: its free edges and shortened lists."),
    "PottsCI.Vigoda.flipSet": (r"\text{the }\{X_u,c\}\text{-component of }u",
        "The vertices of the {X_u, c}-alternating component of u, which a proposal (u, c) swaps."),
    "PottsCI.Vigoda.hardStep": (r"\Phi_F",
        "One step of the hard list-flip kernel Φ_F with Vigoda's profile p."),
    "PottsCI.WeightAdmissible": (r"w\ge0,\ \textstyle\sum_\omega w(\omega)>0",
        "Nonnegative weights with positive total, so that they can be normalized."),
    "PottsCI.graphPathMetric": ("d",
        "The shortest-path metric: the infimum of the ℓ-lengths of walks between two states."),
    "PottsCI.normLaw": (r"\mu^{(i)}_x",
        "The normalized law w/∑w of admissible weights w (a fixed default law otherwise)."),
    "ZeroFreeness.Appendix.BBR.contractionRate": (r"\theta",
        "θ = √κ = √((Δ − 1)/Δ)."),
    "ZeroFreeness.Appendix.BBR.contractionSquare": (r"\kappa",
        "The contraction factor κ = (Δ − 1)/Δ."),
    "ZeroFreeness.Appendix.BBR.jacobianBlock": (r"J_{u\leftarrow v}",
        "The Jacobian block of the recursion at u in the message of child v, in closed form."),
    "ZeroFreeness.Appendix.BBR.messageDistance": (r"\|R_r-R'_r\|_2^2",
        "The squared Euclidean distance between the two root messages."),
    "ZeroFreeness.Appendix.BBR.pointCoefficient": ("a_v",
        "The pointwise weight a_v = ((1 − x)/e)·ℓ_x(R_v)² of a child message."),
    "ZeroFreeness.Appendix.BBR.projection": (r"\Bigl(I_q-\frac{RR^{\mathsf T}}{S(R)}\Bigr)y",
        "The projection of y orthogonal to R; divided coordinatewise by R_r it is Q_r y."),
    "ZeroFreeness.Appendix.BBR.relativeConstant": (r"C_{\mathsf{SM}}",
        "C_SM = 4q√(Δq)·x₀^{−3Δ/2}·κ^{−1}, as in the paper."),
    "ZeroFreeness.Appendix.BBR.response": ("y_r",
        "The level perturbation D_v z_v propagated up to the root by the Jacobian blocks."),
    "ZeroFreeness.Appendix.BBR.segmentWeightSquare": ("L_x(R,R')^2",
        "The squared segment weight: the maximum of S(R_t)/S_i(R_t)² over t ∈ [0,1] and colours i."),
    "ZeroFreeness.Appendix.BBR.totalInfluenceConstant": ("C_0",
        "The constant C₀ of the proposition, evaluated at x₀."),
    "ZeroFreeness.Appendix.CLMM.SameDomain": (r"R,R'\ \text{jointly realizable}",
        "Same free tree and same number of pins at each vertex; pin colours may differ."),
    "ZeroFreeness.Appendix.CLMM.TreeRelative": (r"\left|\frac{p_v(c)}{p'_v(c)}-1\right|\le C_{\mathsf{SM}}(1-\delta)^K",
        "Ratio-form relative SSM error at most Bρ^K at every tree depth K ≥ K₀, K ≥ 2."),
    "ZeroFreeness.Appendix.CLMM.TreeTID": (r"\mathcal I_\ell(r;\tau)\le C_{\mathsf{INFL}}(1-\delta)^\ell",
        "Level-ℓ tree total influence at most Aρ^ℓ for every ℓ ≥ 1, on trees of maximum degree Δ."),
    "ZeroFreeness.Appendix.CV.GlobalChoice": (r"\text{chosen indices in }\Gamma_c",
        "For each colour and side, a chosen root neighbour of that colour, when one exists."),
    "ZeroFreeness.Appendix.CV.MeetsRoot": (r"S\in\mathcal B_a,\ S\in\mathcal B_b",
        "S meets an active c-coloured root neighbour in F; this defines 𝓑_a and 𝓑_b."),
    "ZeroFreeness.Appendix.CV.activityCoins": (r"(\omega_k)_{k\in\mathcal E_\tau}",
        "Independent coins on the labelled constraints, each equal to one with probability 1 − x."),
    "ZeroFreeness.Appendix.CV.adjacentHardCoupling": (r"(X_1,Y_1)\mid\omega",
        "The completed coupling of the two hard steps, for the active instances drawn with coins ω."),
    "ZeroFreeness.Appendix.CV.blockerCount": ("b_{X,Y}(v,u)",
        "Union blocker count at u for the disagreement v; for adjacent X, Y it is r_u + e_u."),
    "ZeroFreeness.Appendix.CV.crossCredit": (r"\textstyle\sum_{(u,w)}\theta x^{t_w}",
        "The (u, w)-credits θx^{t_w}, paid when the output pair is the same-neighbour move at u."),
    "ZeroFreeness.Appendix.CV.edgeLength": (r"\ell_x^{G,\tau}",
        "1 − (17/(200q))𝒮_out(X,Y), which for adjacent X, Y is 1 − (17/(200q))Σ_u s_u."),
    "ZeroFreeness.Appendix.CV.freshIncrementAt": (r"s^{\rm out}_u-s_u\ (\text{fresh moves})",
        "Gain of the u-discount over s_u when one blocker of u gets a fresh colour."),
    "ZeroFreeness.Appendix.CV.fullHardPartial": (r"\boldsymbol\pi",
        "The partial coupling matrix of Definition 5.8, before completion."),
    "ZeroFreeness.Appendix.CV.gammaSet": (r"\Gamma_c",
        "Neighbours u of v with X_u = Y_u = c whose root edge is active on both sides."),
    "ZeroFreeness.Appendix.CV.geometricMetric": (r"d_x^{G,\tau}",
        "The shortest-path metric generated by the edge lengths ℓ_x on configurations."),
    "ZeroFreeness.Appendix.CV.hardCommonOffRootPartial": (r"\boldsymbol\pi^{\mathrm{sync}}",
        "The partial coupling pairing each common off-root move with its counterpart, the rest unassigned."),
    "ZeroFreeness.Appendix.CV.hardStep": (r"\Phi^{\boldsymbol P}_F",
        "One hard list-flip step with the Carlson–Vigoda profile P; from X it is the move law κ_X."),
    "ZeroFreeness.Appendix.CV.metricLower": ("m_0",
        "m₀ = 1724/1809, the lower bound on every edge length."),
    "ZeroFreeness.Appendix.CV.outputScore": (r"\mathcal S_{\rm out}(\sigma,\sigma')",
        "Sum of θx^{b(y,w)} over disagreements y and endpoint-common neighbours w; Σ_u s_u when adjacent."),
    "ZeroFreeness.Appendix.CV.pathMetric": ("d",
        "The shortest-path metric: the infimum of ℓ-lengths of routes of one-coordinate steps."),
    "ZeroFreeness.Appendix.CV.rootEventMass": (r"\Pr(E_v\mid F_X,F_Y)",
        "Coupling mass of output pairs in which v is recoloured on at least one side."),
    "ZeroFreeness.Appendix.CV.rootFixedBadMass": (r"\Pr\big(E_v^{\mathsf c}\cap\{X_1(w)=Y_1(w)\notin T\}^{\mathsf c}\big)",
        "Mass of output pairs keeping both root colours in which w stops being a common non-T colour."),
    "ZeroFreeness.Appendix.CV.safeActivation": (r"\mathcal U_u",
        "Coins with vu active and every T-blocker edge and target deletion at u inactive."),
    "ZeroFreeness.Appendix.CV.singleBlockerEvent": (r"\mathsf{SB}_u",
        "Coins: vu and exactly one other free T-blocker edge at u active, other target constraints inactive."),
    "ZeroFreeness.Appendix.CV.targetConstraints": (r"\mathcal O_w",
        "Target constraints at w: free edges to T-coloured vertices, pinned constraints deleting a or b."),
    "ZeroFreeness.Appendix.CV.xFamilyRows": (r"\text{family }c\ (X\text{-side outputs})",
        "X-side outputs of family c: regular-colour moves for c ∉ T, root-colour moves for c ∈ T."),
    "ZeroFreeness.Appendix.Edge.OneLabel.CW": ("W_{1,F}",
        "The transport distance between countable laws: the infimum of expected cost over couplings."),
    "ZeroFreeness.Appendix.Edge.OneLabel.addB": (r"B^\alpha",
        "The occupied-label family B with the label α added at v."),
    "ZeroFreeness.Appendix.Edge.SlotModel.Bounds": (r"\text{(load), (fibre), (slack)}",
        "The load, fibre and slack bounds on the data (F, B) at degree bound Δ."),
    "ZeroFreeness.Appendix.Edge.SlotModel.Reachable": (r"(F,B)\text{ reachable from }(F_0,\varnothing)",
        "Data obtained from (F₀, ∅) by successively pinning admissible positive-activity states."),
    "ZeroFreeness.Appendix.Edge.SlotModel.colourFibreLaw": (r"\nu_{F_0,\varnothing}\text{ on the fibre of }\phi",
        "The initial lifted law restricted to lifted states whose colour projection is φ."),
    "ZeroFreeness.Appendix.Edge.edgeSlotModel": (r"w_e(c,r,s)=x^{b_u^\tau(c)+b_v^\tau(c)}\kappa_r\kappa_s",
        "The slot lift of the pinned edge-Potts model, with these activities on lifted states (c, r, s)."),
    "ZeroFreeness.Appendix.Edge.oneLabelBound": (r"\frac{\Delta-1}{2}\Bigl[1-\Bigl(\frac{\Delta-1}{\Delta}\Bigr)^n\Bigr]",
        "The one-label bound on T_n; it vanishes at n = 0."),
    "ZeroFreeness.Appendix.Girth.CavityTree": (r"(\mathcal T_\tau,\tau)",
        "A rooted free tree whose vertices carry the colour counts of their pinned neighbours."),
    "ZeroFreeness.Appendix.Girth.CavityTree.Agreement": (r"\tau\cup\omega\ \text{vs.}\ \tau\cup\omega'",
        "Two trees identical on their first k levels, with equal degrees and pinned-neighbour totals at level k."),
    "ZeroFreeness.Appendix.Girth.CavityTree.Level": (r"\{v:\operatorname{dist}(r,v)=k\}",
        "The free vertices at distance k from the root r of the tree."),
    "ZeroFreeness.Appendix.Girth.CavityTree.influenceBlock": (r"\Psi_{r,v}(a,c)",
        "The influence block μ_v^{τ^{r=a}}(c) − μ_v^τ(c) of the finite tree Gibbs law."),
    "ZeroFreeness.Appendix.Girth.CavityTree.levelTotalVariation": (r"\sum_{\operatorname{dist}(r,v)=\ell}\|\mu_v^{\tau^{r=a}}-\mu_v^{\tau^{r=b}}\|_{\mathrm{TV}}",
        "The level-ℓ total influence of the root for one pair of root colours a, b."),
    "ZeroFreeness.Appendix.Girth.CavityTree.probability": ("p_v(c)",
        "The root's one-site marginal of colour c, computed by the tree recursion."),
    "ZeroFreeness.Appendix.Girth.CavityTree.totalInfluenceConstant": ("C_0",
        "C₀ = Δe^{1/12}√q(1 + √q)²/3."),
    "ZeroFreeness.Appendix.Girth.ConditionalStar": (r"\mu(c,\sigma)",
        "A conditional star: centre weights a_c, leaf cavity laws p_i, and s ∈ [0,1]."),
    "ZeroFreeness.Appendix.Girth.ConditionalStar.SchurParameters": (r"0<\delta\le1,\ \Delta\ge\Delta_0(\delta),\ d\le\Delta",
        "The star hypotheses: δ, Δ ≥ Δ₀(δ), d ≤ Δ, palette budget, and s p_i(c), s ν(c) ≤ B_SG."),
    "ZeroFreeness.Appendix.Girth.ConditionalStar.SchurParameters.bound": ("r_*",
        "d κ(1 + ω_SG)^{d−1}/c_δ, with B_SG = 1/(δΔ)."),
    "ZeroFreeness.Appendix.Girth.ConditionalStar.SchurParameters.singletonError": (r"\varepsilon_1",
        "The singleton error ε₁, zero when d ≤ 1; η = r_* + ε₁."),
    "ZeroFreeness.Appendix.Girth.ConditionalStar.rawStarDefect": (r"\langle f,(T_\beta-\tfrac12Q+\tfrac{\theta}{2d}\sum_i\beta_i^2Q_i)f\rangle_\mu",
        "The quadratic form of T_β − ½Q + (θ/2d)Σ_i β_i²Q_i at f, in L²(μ)."),
    "ZeroFreeness.Appendix.Girth.CovarianceScale": (r"(\delta,\Delta,q)",
        "δ, Δ, q with q ≥ (1+δ)Δ, and the constants B, V_π, V_M, E_Δ, b_Δ, g_Δ built from them."),
    "ZeroFreeness.Appendix.Girth.GraphStar.model": (r"\mu(c,\sigma)",
        "The conditional star at v given σ off the star, from a residual instance."),
    "ZeroFreeness.Appendix.Girth.GraphTwoLayer.First": ("U=N_H(v)",
        "The neighbours of the root v."),
    "ZeroFreeness.Appendix.Girth.GraphTwoLayer.Second": ("S=S_2^H(v)",
        "Vertices outside U with a neighbour in U; the third clause identifies them with S₂^H(v)."),
    "ZeroFreeness.Appendix.Girth.GraphTwoLayer.model": (r"\nu=\mu_{I-v}",
        "ν = μ_{I−v} disintegrated over σ_S, with the conditional laws π_u^ξ and ν_O^ξ."),
    "ZeroFreeness.Appendix.Girth.InsertionModel.CovarianceEstimates": (r"\|\beta_{u,c}\|_{L^2(\nu)}\le b_\Delta,\ \|\operatorname{Cov}_\nu(G)\|_{2\to2}\le g_\Delta^2",
        "The bounds π_{u,c} ≤ B, Var π_{u,c} ≤ V_π, Var M_c ≤ V_M, |log T_c/Q_c| ≤ E_Δ, ‖β_{u,c}‖ ≤ b_Δ, covariance ≤ g_Δ²."),
    "ZeroFreeness.Appendix.Girth.LocalRecursion": (r"(a_v,\,(m_i)_{i},\,\underline A_v)",
        "A non-root recursion step: weights a_v, child inputs m_i ≤ B_i, and a palette bound A̲_v."),
    "ZeroFreeness.Appendix.Girth.LocalRecursion.childEntropy": (r"\zeta_i",
        "The entropy correction ζ_i of child i; its weight is w_i = (1 − ζ_i)^{−1/2}."),
    "ZeroFreeness.Appendix.Girth.LocalRecursion.law": ("p_v",
        "The parent law p_v produced by the recursion step."),
    "ZeroFreeness.Appendix.Girth.MessageDomain": (r"\mathcal D_s",
        "Messages with every coordinate in [0, 1/4] and total mass at most s."),
    "ZeroFreeness.Appendix.Girth.OperatorGap.glauberLaplacian": (r"\mathcal L",
        "The rate-one heat-bath Glauber Laplacian Σ_v (I − P_v) on the supported L² space."),
    "ZeroFreeness.Appendix.Girth.blockAction": ("J^p_v h",
        "The transformed Jacobian J^p_v, given by its explicit entries, applied to a block vector h = (h_i)."),
    "ZeroFreeness.Appendix.Girth.cavityLawNN": ("r",
        "The cavity colour law of v after deleting the edge vw, given σ."),
    "ZeroFreeness.Appendix.Girth.decayRate": (r"\rho",
        "The contraction rate ρ = exp(−4/(81q)) < 1."),
    "ZeroFreeness.Appendix.Girth.edgeResponse": ("T_r h",
        "(T_r h)(t) = (⟨r,h⟩ − s r(t)h(t))/(1 − s r(t))."),
    "ZeroFreeness.Appendix.Girth.largeGirthFamily": (r"\{\operatorname{girth}(G^{\tau})\ge g\}",
        "Residual instances whose free graph G^τ has girth at least g."),
    "ZeroFreeness.Appendix.Girth.messageCap": ("B_v",
        "The cap ξ_v/(A̲_v − 1 + ξ_v) on the marginals at a non-root vertex."),
    "ZeroFreeness.Appendix.Girth.messageMarginal": ("p_v(c)",
        "The parent marginal given by the scaled recursion from colour weights a and child messages m_i."),
    "ZeroFreeness.Appendix.Girth.messageOddsBound": (r"\xi_v/(\underline A_v-1)",
        "The odds bound ξ_v/(A − 1), where ξ_v = (4/3)^{4d/(A−1)}."),
    "ZeroFreeness.Appendix.Girth.messagePotential": (r"\phi",
        "The potential φ(t) = 2 artanh √t, applied coordinatewise."),
    "ZeroFreeness.Appendix.Girth.neighbourConditional": (r"\pi_u^{\xi}",
        "The conditional marginal of σ_u given σ_S = ξ."),
    "ZeroFreeness.Appendix.Girth.oneEdgeConstant": (r"L_\Delta",
        "(1 + √(q/(m+1)))/m; the lemma uses m = q − Δ."),
    "ZeroFreeness.Appendix.Girth.projectedEdgeOperator": (r"\Pi T_r\Pi",
        "T_r compressed by the projection Π orthogonal to constants, on Euclidean ℝ^q."),
    "ZeroFreeness.Appendix.Girth.rootInfluenceAction": (r"D_r^{-1}J_{r,u}\,h",
        "The root factor −(I_q − 1_q p_r^T) diag(√m_{u→r}) applied to a vector h."),
    "ZeroFreeness.Appendix.Girth.scaledRowFactor": (r"\frac{\sqrt s\,(1-p)}{1-sp}",
        "The diagonal chain-rule factor turning J^p_v into Ĵ_v, whose output is m_v = sp_v."),
    "ZeroFreeness.Appendix.Girth.transformedBlock": ("(J^p_{v,i})_{c,b}",
        "The entry γ(c)(p(b) − 1_{b=c})√m_i(b) of J^p_{v,i}, where γ(c) = √p(c)/(1 − p(c))."),
    "ZeroFreeness.Holant.NormalizedInstance": (r"H=(W,F),\ (g_w)_{w\in W}",
        "A Holant instance with each signature's arity equal to its vertex degree and g_w(0) = 1."),
    "ZeroFreeness.Holant.NormalizedInstance.OneSurvives": (r"g_u(1)\,g_v(1)>0",
        "Both endpoint signatures of e are positive at 1, so the 1-child is defined."),
    "ZeroFreeness.Holant.coverPartition": (r"Z^{\mathrm{cover}}_{G,\mathbf b}(\mathbf z)",
        "Sum over edge sets S with deg_S(v) ≥ b_v of ∏_{e∈S} z_e."),
    "ZeroFreeness.Holant.edgeOrthantNeighborhood": (r"\bigcup_{R>0}\mathcal U_{\varepsilon(R)}([0,R])^E",
        "The union over R > 0 of the polytubes U_{ε(R)}([0, R])^E for a width function ε."),
    "ZeroFreeness.Holant.edgePolytube": (r"\mathcal U_\varepsilon([a,b])^E",
        "Activity vectors with every edge coordinate within ε of the real interval [a, b]."),
    "ZeroFreeness.Holant.graphPartition": (r"Z_{G,\mathbf f}(\mathbf z)",
        "The Holant polynomial: sum over edge sets S of ∏_v f_v(deg_S v) ∏_{e∈S} z_e."),
    "ZeroFreeness.Holant.holantWidth": (r"\varepsilon(\Delta,\mathcal F,R)",
        "The Holant polytube width R ↦ ε(Δ, 𝓕, R), independent of the graph."),
    "ZeroFreeness.Holant.matchingPartition": (r"Z^{\mathrm{match}}_{G,\mathbf b}(\mathbf z)",
        "Sum over edge sets S with deg_S(v) ≤ b_v of ∏_{e∈S} z_e."),
    "ZeroFreeness.Holant.residualFamily": (r"\mathcal F_{\rm res}",
        "All normalized residuals g(k) = f(j+k)/f(j), 0 ≤ k ≤ r, of signatures f ∈ 𝓕."),
    "ZeroFreeness.Holant.star": (r"K_{1,\Delta}",
        "The star: one centre adjacent to Δ leaves, and no other edges."),
    "ZeroFreeness.LeeYang.fullFieldPartition": (r"Z^{\tau}_{G}(\lambda)",
        "The pinned field polynomial: proper colourings extending τ, weighted by the fields at all vertices."),
    "ZeroFreeness.PartialCoupling": (r"\boldsymbol\pi=(\pi_{M,N})",
        "A partial coupling matrix: nonnegative entries, row sums ≤ κ_X and column sums ≤ κ_Y."),
    "ZeroFreeness.PartialCoupling.complete": (r"\pi_{M,N}+\alpha_M\beta_N/R",
        "The product completion: adds α_M β_N / R to every entry, giving a coupling."),
    "ZeroFreeness.Potts.ExternalCriticalHardColouringTheorem": (r"\mathcal G_\Delta\ \text{CI at } x=0",
        "Coupling independence at x = 0 with some finite constant, over graphs of maximum degree ≤ Δ."),
    "ZeroFreeness.Potts.FlipProfile": (r"\rho=(\rho_s)_{s\ge1}",
        "A flip profile: numbers 0 ≤ ρ_s ≤ 1 for every s ≥ 1."),
    "ZeroFreeness.Potts.FlipProfile.R": (r"R_\rho",
        "R_ρ = sup_{s≥1} s ρ_s."),
    "ZeroFreeness.Potts.HasSmallResponseLog": (r"\left|\operatorname{Log}\frac{f(z)/f(x)}{g(z)/g(x)}\right|\le\alpha",
        "A logarithm of (f(z)/f(x))/(g(z)/g(x)), analytic on |z − x| < r, zero at x, of modulus ≤ α."),
    "ZeroFreeness.Potts.PinningFamily.PositiveRootCouplingBound": (r"W_{1,\mathrm{Ham}}\bigl(\mu^{\tau^{r=a}},\mu^{\tau^{r=b}}\bigr)\le K",
        "Coupling independence with cost K at activity x for every root-pinned instance of the family of degree at most Δ."),
    "ZeroFreeness.Potts.PinningFamily.RootCouplingBound": (r"W_{1,\mathrm{Ham}}\bigl(\mu^{\tau^{r=a}}_{G,x},\mu^{\tau^{r=b}}_{G,x}\bigr)\le K",
        "Coupling independence with cost K at activity x, over every instance of the family with degree bound Δ."),
    "ZeroFreeness.Potts.PositiveIntervalCI": (r"C\text{-coupling independence on }[\delta,1]",
        "Coupling independence with constant C at every x ∈ [δ,1], over every graph of the class."),
    "ZeroFreeness.Potts.RootCouplingBound": (r"W_{1,\mathrm{Ham}}\big(\mu_{G,x}^{\tau^{r=a}},\mu_{G,x}^{\tau^{r=b}}\big)\le C",
        "C-coupling independence at x over 𝒢_Δ, stated on root-conditioned residual instances."),
    "ZeroFreeness.Potts.Soft.softKernelOf": (r"\sigma\mapsto\textstyle\sum_A \Pr[A\mid\sigma]\,H_A(\sigma,\cdot)",
        "Draws A from its law given σ, applies the hard kernel of A, and forgets A."),
    "ZeroFreeness.Potts.actualRootChildGibbs": (r"\mu^{\tau^{r=a}}_{G,x}",
        "The normalized Gibbs law of τ^{r=a} on V^τ ∖ {r}, also at x = 0."),
    "ZeroFreeness.Potts.addBoundary": (r"\text{plus system}",
        "The system with one more labelled free–pinned edge, forbidding colour a at r."),
    "ZeroFreeness.Potts.boundaryExcess": ("k",
        "The number of labelled free–pinned edges of J in excess of those of I."),
    "ZeroFreeness.Potts.flipFibreKernel": (r"\Phi^\rho_{F_A}",
        "The hard flip kernel Φ^ρ_{F_A} of the active set A."),
    "ZeroFreeness.Potts.flipKernel": (r"\Phi_F^{\rho}",
        "The hard list-flip transition of profile ρ on a hard list instance F."),
    "ZeroFreeness.Potts.fullPartition": (r"Z^{\tau}_{G}(z)",
        "The ordinary pinned partition function, evaluated at z ∈ ℂ."),
    "ZeroFreeness.Potts.kappa": (r"\kappa_x",
        "κ_x = (q − (11/6)(1 − x)Δ)/q."),
    "ZeroFreeness.Potts.normalizedPartition": (r"\widehat Z^{\tau}_{G}(z)",
        "The normalized pinned partition function, evaluated at z ∈ ℂ."),
    "ZeroFreeness.Potts.optionChildData": (r"\tau^{r=a}",
        "The child instance obtained by pinning the root none to a; it lives on O = V^τ ∖ {r}."),
    "ZeroFreeness.Potts.optionMiddleData": ("I-v",
        "The instance I − v: the root and its edges deleted, other boundary counts kept."),
    "ZeroFreeness.Potts.pinVertex": (r"\tau^{v=a}",
        "The child pinning τ ∪ {v ↦ a}: τ with the free vertex v pinned to a."),
    "ZeroFreeness.Potts.positiveRootChildGibbs": (r"\mu^{\tau^{r=a}}_{G,x}",
        "The normalized Gibbs law of τ^{r=a} on V^τ ∖ {r}, for x > 0."),
    "ZeroFreeness.Potts.profileStep": (r"\Phi^\rho_F\ (W\neq\varnothing)",
        "One update on nonempty W: a uniform proposal (u,c) ∈ W × [q], then the swap rule."),
    "ZeroFreeness.Potts.rootDeletedData": (r"\tau^{r=a}",
        "The child instance obtained by pinning the free vertex r to a; it lives on V^τ ∖ {r}."),
    "ZeroFreeness.Potts.softFlipKernel": (r"K_{x,\rho}^{G,\tau}",
        "The soft flip kernel: sample the active set given σ, apply Φ^ρ_{F_A}, forget A."),
    "ZeroFreeness.Potts.softVigoda": (r"K_x^{G,\tau}",
        "The soft flip kernel with Vigoda's profile p, for x ∈ (0,1]."),
    "ZeroFreeness.RootComponentGeometry.rootFamily": (r"\{X_v,c\}\text{-components of }F-v",
        "The distinct {X_v, c}-components of F − v that contain a c-coloured neighbour of v."),
    "ZeroFreeness.activatedSet": ("A_X",
        "The constraints whose coin is one and that X satisfies."),
    "ZeroFreeness.activationLaw": (r"\Pr[A\mid\sigma]",
        "The law of the active set given σ: each satisfied constraint independently with probability 1 − x."),
    "ZeroFreeness.centeredAverageLogRatio": (r"\operatorname{Log}\frac{\mathbb E_{\nu_0}[e^{h+\eta}]}{\mathbb E_{\nu_1}[e^{h+\eta'}]}",
        "An explicit Log of the ratio: difference of principal logs of the anchor-centred averages."),
    "ZeroFreeness.ciBound": (r"\frac{2(1-x)\Delta}{q-(11/6)(1-x)\Delta}",
        "The paper's coupling-independence bound at activity x."),
    "ZeroFreeness.ciGap": (r"\gamma_0",
        "γ₀ = q/Δ − 11/6, the relative gap above the line q = 11Δ/6."),
    "ZeroFreeness.commonCoinLaw": (r"\omega\sim\operatorname{Bernoulli}(1-x)^{\otimes K}",
        "One independent coin per labelled constraint; here each is one with probability 1 − x."),
    "ZeroFreeness.hamDrift": (r"\mathrm{Ham}(U,Z)-1",
        "The Hamming increment of an output pair, relative to the initial distance one."),
    "ZeroFreeness.pottsInterval": (r"[0,1]\subset\mathbb C",
        "The real interval [0, 1] in ℂ; thickening ε pottsInterval is U_ε([0, 1])."),
    "ZeroFreeness.rootCommonListCount": (r"\ell",
        "ℓ = |L_{X,v} ∩ L_{Y,v}|, the colours allowed at v on both sides."),
    "ZeroFreeness.rootFreeCoinCount": (r"\textstyle\sum_c|N_c|",
        "The free edges at v whose coin is one, i.e. active on at least one side."),
}

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
    for path in sorted((REPO / "ZeroFreeness").rglob("*.lean")):
        rel = path.relative_to(REPO).as_posix()
        for decl in index_file(path):
            decl["path"] = rel
            found.setdefault(decl["name"], decl)
    return found


def lean_excerpt(decl):
    """The statement of a declaration, without its docstring; theorems stop
    before the proof. Returns the code and the number of lines cut from it."""
    lines = (REPO / decl["path"]).read_text().splitlines()
    block = "\n".join(lines[decl["start"] - 1:decl["end"]])
    match = re.match(r"\s*/--(.*?)-/\s*\n?", block, re.S)
    if match:
        block = block[match.end():]
    if decl["kind"] in ("theorem", "lemma"):
        end = re.search(r":=(?:\s*by)?[ \t]*(?:\n|$)", block)
        cut = end.start() if end else block.find(":=")
        if cut >= 0:
            block = block[:cut]
    code = textwrap.dedent(block).strip("\n").rstrip().splitlines()
    more = max(len(code) - SIGNATURE_LINES, 0)
    return "\n".join(code[:SIGNATURE_LINES]), more


# ---------------------------------------------------------------------------
# Data

def build_data(args):
    if common.git("status", "--porcelain", "--", "ZeroFreeness", "ZeroFreeness.lean"):
        sys.exit("Commit the Lean sources first, so that source links are pinned.")
    commit = common.git("log", "-1", "--format=%h", "--abbrev=7", "--", "ZeroFreeness", "ZeroFreeness.lean",
                         "lakefile.toml", "lean-toolchain", "lake-manifest.json")
    coverage = json.loads((REPO / common.COVERAGE).read_text())
    record = json.loads((REPO / "docs/verification.json").read_text())
    index = lean_index()

    listed = [n for entry in coverage for n in entry["lean"] + entry["defs"]]
    unknown = sorted({n for n in listed if n not in index})
    if unknown:
        sys.exit("Lean declarations not found in the sources: " + ", ".join(unknown))
    glosses = {name: (symbol, gloss) for name, symbol, gloss in common.GLOSSARY}
    glosses.update(DEFINITIONS)
    unglossed = sorted({n for entry in coverage for n in entry["defs"] if n not in glosses})
    if unglossed:
        sys.exit("Definitions without a gloss in DEFINITIONS: " + ", ".join(unglossed))

    decls = {}
    for name in dict.fromkeys(listed):
        decl = index[name]
        code, more = lean_excerpt(decl)
        decls[name] = dict(short=common.short(name), kind=decl["kind"], path=decl["path"],
                           start=decl["start"], end=decl["end"], code=code, more=more)

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
                kind=entry["kind"], word=common.ENV_WORDS[entry["kind"]], number=entry["number"],
                title=entry["title"], label=entry["label"], status=entry["status"],
                note=richtext.rich(entry["note"]), lean=entry["lean"],
                defs=[dict(name=n, symbol=glosses[n][0], gloss=richtext.rich(glosses[n][1])) for n in entry["defs"]]))
            if body and statements[-1]["id"] in body.get("titles", {}):
                statements[-1]["title_html"] = body["titles"][statements[-1]["id"]]
        papers[key] = dict(key=key, title=meta["title"], short=meta["short"], authors=AUTHORS,
                           pdf=pdf.relative_to(REPO / "docs").as_posix() if pdf.exists() else None,
                           statements=statements, **(body or {}))

    statuses = {k: dict(label=v[0], glyph=v[1], tone=v[2], meaning=v[3])
                for k, v in common.STATUSES.items()}
    # Each cited result links to the Lean theorem that proves it.
    cited = []
    for c in common.CITED:
        proof = index[c["proof"][0]]
        cited.append(dict(short=c["short"], source=c["source"],
                          proof=dict(path=proof["path"], start=proof["start"], end=proof["end"])))
    return dict(
        commit=commit, github=common.GITHUB, built=datetime.date.today().isoformat(),
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
