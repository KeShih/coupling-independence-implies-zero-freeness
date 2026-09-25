# Potts appendix: theorem status and cited results

The [module guide](README.md) lists the seven regional entry points. The
[documentation index](../README.md) covers the main-text Potts, Holant, and
Lee–Yang proofs.

The regional entry point is `ZeroFreeness/Potts/Regions.lean`.
Run `bash scripts/check-appendix.sh` to compile its full dependency closure
with warnings treated as errors and audit every imported project declaration.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The formalized versions of the cited ingredients listed below are proved in
the library, so no regional endpoint takes a literature parameter.

## Regional endpoints

The table records the regional conclusions. None of them takes a literature
hypothesis; the sections below list the cited results each proof uses and
where they are proved, together with the modules that state the companion's
other numbered lemmas. [Scope of the coverage](#scope-of-the-coverage)
summarizes the coverage of every numbered statement.

| Region | Coupling independence | Uniform zero-free conclusion |
| --- | --- | --- |
| Edge-Potts, maximum original degree Δ≥2 and q ≥ 3Δ | `Edge.root_children_ci`: actual root-conditioned edge-colour Gibbs laws have Hamming transportation distance at most Δ−1, for every x in [0,1] | `Edge.edge_potts_zero_free`, including arbitrary edge pinning and the exact forced-zero multiplicity at zero |
| Large girth, Δ ≥ 3 and q ≥ Δ+3 | `Girth.high_girth_coupling`: a girth threshold and one coupling constant work uniformly in graph size, pinning, and x in [0,1] | `Girth.high_girth_zero_free` and `Girth.high_girth_residual_original_zero_free`, with girth required only of the free residual graph, including arbitrary improper pinning and the exact forced-zero multiplicity |
| General-graph high temperature, x₀>0 and q>11(1−x₀)Δ/6 | `high_temperature_graph_coupling`: the explicit constant 2(1−x₀)Δ / (q−11(1−x₀)Δ/6) works on [x₀,1] | `high_temperature_zero_free`, for both normalized and full partition functions, without a hard-colouring feasibility bound |
| BBR large-girth interval, q≥3 and Δ/q≥(e−1/2)/(e−1) | `BBR.high_girth_coupling`: one girth threshold and one CI constant work on the entire closed interval [`BBR.start q Δ`,1] | `BBR.high_girth_zero_free` and `BBR.high_girth_residual_original_zero_free`, for both normalized and full partition functions, with girth required only of the free residual graph; `BBR.high_girth_original_zero_free_and_responses` adds the actual one-root response logarithms |
| Carlson–Vigoda, Δ≥125 and q≥1.809Δ | `CV.option_root_ci` and `CV.root_coupling`: actual normalized root-child laws have Hamming transport at most 409060125/50858 < 8043.19, uniformly on [0,1] | `CV.zero_free`: the full original-graph statement, arbitrary pinning, normalized nonvanishing and exact forced-zero multiplicity |
| Near-Vigoda, Δ≥2 and q≥(11/6−1/84000)Δ | `near_vigoda_uniform_ci`: one constant on [0,1], via the exact integer reduction `nearVigoda_regime_cases` to the proved strict-Vigoda and CV regimes and twenty critical pairs, which use the CV contraction on the critical line; `near_vigoda_transfer_inputs` gives the hard-endpoint and every-[δ,1] coupling inputs | `near_vigoda_zero_free`: the full uniform original-graph statement on [0,1] |
| Girth 5, 0<δ≤1, Δ≥`Girth.girthFiveCIThreshold δ`, and q≥(1+δ)Δ | `Girth.girth_five_coupling`: one finite constant for every size, pinning, and x in [0,1] | `Girth.girth_five_zero_free` and `Girth.girth_five_residual_original_zero_free`, with girth required only of the free residual graph |

Names in the table are relative to `ZeroFreeness.Appendix`.

### Edge-Potts proof and cited results

No cited result is used. The proof constructs weighted finite
slot models, proves their actual conditional Gibbs identities, exposure
couplings and recursive transport bound, proves real-rooted finite slot
approximations, projects to the finite colour space and passes to the limit.
The zero-free corollary uses the already formalized graph-class transfer theorem.

The countable slot lemmas are also proved as stated.
[`Slots/SlotLift.lean`](../../ZeroFreeness/Coupling/Edge/Slots/SlotLift.lean) proves
Lemma 8.3 (`lem:slot-fact`), the countable slot representation
`Edge.slot_representation` for every `0 < x < 1`, by compactness from the
finite real-rooted approximants rather than by the paper's
Hadamard-factorization argument, and Lemma 8.4 (`lem:edge-slot-lift`), the
exact lift `Edge.lem_edge_slot_lift` on `C × ℕ × ℕ` with exact colour
projection. [`Slots/OneLabel.lean`](../../ZeroFreeness/Coupling/Edge/Slots/OneLabel.lean)
proves Lemma 8.5 (`lem:edge-one-label`), `Edge.OneLabel.edge_one_label`, on
the countable slot model, by lumping all slots from `N` on into one and
letting `N → ∞`.

### Large-girth proof and cited results

The proof uses three general CLMM2023 ingredients, each with a proved Lean
version:

- Lemma 8.7, the exact tree influence–Jacobian factorization, stated as
  `CavityTree.CLMMInfluenceIdentity` and proved as
  `CavityTree.clmmInfluenceIdentity` in
  [`Tree/InfluenceIdentity.lean`](../../ZeroFreeness/Coupling/Girth/Tree/InfluenceIdentity.lean)
  from the actual finite-tree Gibbs law.
- Equation (10), derived from Lemmas 5.19/5.20, giving the graph sphere
  influence estimate. It is the single field `sphere_estimate` of
  `CLMM.Literature`, proved as `CLMM.Eq10.sphere_estimate_proof` in
  [`CLMM/SphereEstimate.lean`](../../ZeroFreeness/Coupling/CLMM/SphereEstimate.lean)
  and packaged as `CLMM.literature`. The ball–tree correspondence uses
  girth only to exclude edges inside a distance layer and to make parents
  unique.
- Lemma 5.13, converting sphere decay to the Hamming coupling bound
  `2Δ^R`, proved as `CLMM.Lemma513.sphere_to_coupling` in
  [`CLMM/SphereCoupling.lean`](../../ZeroFreeness/Coupling/CLMM/SphereCoupling.lean).
  `CLMM.FixedAmbientSphereDecay` fixes the base graph before quantifying
  over all further pinnings: every sphere is measured in that same base
  graph, as required by Condition 5.12.

These statements concern actual finite Potts/Gibbs distributions. They do not
assume this appendix's local contraction, tree decay, coupling independence,
or zero-free conclusion. All q ≥ Δ+3 estimates, a uniform burn-in, graph CI,
the x=0 and x=1 endpoints, and normalized/original partition semantics are
proved in Lean. `CLMM.eventual_transfer` takes the Equation (10) bundle as
its argument `clmm`; `Girth.high_girth_soft_coupling`,
`Girth.high_girth_coupling`, `Girth.high_girth_zero_free`,
`Girth.high_girth_original_zero_free` and
`Girth.high_girth_residual_original_zero_free` pass `CLMM.literature C` and
take no literature parameter.

Companion Lemma 6.10 (`lem:hg-eventual-transfer`), as the companion now
states it for the Potts family at positive activity `x ∈ J ⊆ (0,1]`, is
proved in
[`Transfer/PottsTransfer.lean`](../../ZeroFreeness/Potts/Regions/Girth/Transfer/PottsTransfer.lean)
with no literature parameter: `Girth.potts_eventual_transfer` in the
library's `Option` form, `Girth.potts_eventual_transfer_source` for an
arbitrary free source vertex, and `Girth.potts_eventual_transfer_uniform`
with the girth threshold and constant depending only on
`(q, Δ, C_INFL, C_SM, δ, K₀)`.
[`Tree/SingleEdge.lean`](../../ZeroFreeness/Coupling/Girth/Tree/SingleEdge.lean)
proves the observation before Lemma 6.9 that ratio-form relative SSM cannot
start at distance one uniformly in `x` (`Girth.no_uniform_distance_one`).

`Girth.high_girth_residual_original_zero_free` states the original pinned
polynomial result with girth required only after pinning. For BBR the
corresponding entry point is `BBR.high_girth_residual_original_zero_free`;
its radius is reduced to exclude zero, so both the normalized and full
polynomials are nonzero throughout the stated positive-temperature neighbourhood.

### High-temperature proof and cited results

No cited result is used. The concrete positive-activity
Vigoda coupling supplies the explicit CI constant. The positive-base
graph-family response induction supplies the uniform complex neighbourhood.
The proof does not impose q≥Δ+1 and permits arbitrary improper pinning.

### BBR proof and cited results

The BBR route uses four cited ingredients, each with a proved Lean version: BBR
Proposition 2.6(i) and Theorem 2.5, stated in `BBR.Literature` with their
published hypotheses, and CLMM Equation (10) and Lemma 5.13 as above.

- `BBR.theorem_2_5_holds`, in
  [`BBR/Theorem25.lean`](../../ZeroFreeness/Coupling/BBR/Theorem25.lean), follows
  BBR Section 3: the mean value theorem along the segment `sR + (1−s)R'`,
  Cauchy–Schwarz, and the pointwise Jacobian bound `differential_contraction`.
- `BBR.proposition_2_6_i_holds`, in
  [`BBR/Proposition26.lean`](../../ZeroFreeness/Coupling/BBR/Proposition26.lean),
  follows BBR Section 4, except that two uses of the concavity of `log`, a
  chord bound and Jensen's inequality in AM–GM form, replace BBR's Lemma 4.1
  (smoothing) and Lemma 4.2(i). Lemma 4.3 is proved by a derivative argument.

`BBR.literature` bundles both proofs. The internal BBR lemmas take
`(bbr : Literature C)`; `BBR.high_girth_coupling`, `BBR.high_girth_zero_free`,
`BBR.high_girth_original_zero_free_and_responses` and
`BBR.high_girth_residual_original_zero_free` pass `BBR.literature C` and
`CLMM.literature C` and take no literature parameter.

The square-root influence–Jacobian identity is proved from actual finite
Gibbs conditional expectations and the explicit local projection/Jacobian
algebra. This connects the message/Gibbs correspondence and exact
derivatives to the response at every tree level; see
[`BBR/InfluenceIdentity.lean`](../../ZeroFreeness/Coupling/BBR/InfluenceIdentity.lean).
Interval-wide contraction,
tree influence and relative spatial decay, and the positive zero-free
transfer are derived from the four cited results. The exceptional
(q,Δ)=(3,4) interval and all degree-gap-two parameter cases, which lie
outside the printed degree range of Proposition 2.6(i), are handled directly
in the application. Separately,
[`BBR/GapTwo.lean`](../../ZeroFreeness/Coupling/BBR/GapTwo.lean) proves the
conclusion of Proposition 2.6(i) for `Δ ≥ q + 2`
(`BBR.proposition_2_6_i_of_gap_two`), the range in which the companion
asserts that BBR's proof is valid. It uses the library's proof, which
needs only `q + 2 ≤ Δ`, and does not check BBR's own argument. From it,
`BBR.contraction_certificate_of_gap_two` derives the certificate of
Lemma 7.1 (`lem:bbr-certificate`) for every `Δ ≥ q + 2`.
[`BBR/RoundedInterval.lean`](../../ZeroFreeness/Coupling/BBR/RoundedInterval.lean)
proves the comparison after Theorem 4.6: `[x₀, 1]` contains BBR's rounded
interval, which is empty at `(q,Δ)=(3,4)` (`BBR.rounded_interval_subset`,
`BBR.rounded_interval_three_four_empty`). The ordinary `q ≥ Δ+3` large-girth
route uses the separate CLMM identity `CavityTree.clmmInfluenceIdentity`.

### Carlson–Vigoda proof and cited results

No cited result is used. The proof uses the actual CV flip
profile, common-coin activation, feasible component couplings, the complete
low-multiplicity certificate checked by Lean's kernel, weighted configuration
paths, and the true output-score discount. The final geometric drift feeds
weighted path coupling and a two-metric stationary comparison. Finite-state
continuity gives x=0, while x=1 is the common product law. The bound and its
uniform complex corollary do not retain any matching, drift, contraction,
stationarity, or hard-colouring hypothesis.

The lemmas of the CV appendix are also stated one by one.
[`CV/ClosedKernel.lean`](../../ZeroFreeness/Coupling/CV/ClosedKernel.lean) defines the
closed-interval kernel `CV.cvKernel`, equal to `softCVKernel` on `(0,1)`, and
proves Theorem 5.25 (`CV.cv_contraction`) and Lemma 5.26
(`CV.cv_child_middle_ham`, `CV.cv_child_middle_metric`) for every
`x ∈ (0,1]`, including `x = 1`. For Definition 5.3 it proves the coefficient
`(P₂ − P₃)/2 = 17/200` (`CV.cv_coefficient`), defines the hard metric
`CV.hardMetric` and proves `d_x → d_hard` as `x ↓ 0`
(`CV.geometricMetric_tendsto_hardMetric_cv`). The one-lemma modules are
[`RootLocalStructure`](../../ZeroFreeness/Coupling/CV/RootLocalStructure.lean)
(Lemma 5.6, `CV.cv_root_local_structure`),
[`MovePartition`](../../ZeroFreeness/Coupling/CV/MovePartition.lean) (Lemma 5.7,
`CV.cv_move_partition`), [`FreshGain`](../../ZeroFreeness/Coupling/CV/FreshGain.lean)
(Lemma 5.12, `CV.cv_fresh`),
[`ExpectedLoss`](../../ZeroFreeness/Coupling/CV/ExpectedLoss.lean) (Lemma 5.14,
`CV.cv_expected`), [`HighColours`](../../ZeroFreeness/Coupling/CV/HighColours.lean)
(Lemma 5.21, `CV.cv_high_bulk`, `CV.cv_high_missing`) and
[`Assembly`](../../ZeroFreeness/Coupling/CV/Assembly.lean) (Lemma 5.23,
`CV.cv_assembly_1809`). `ZeroFreeness.Potts.softCVKernel_reversible_irreducible`
gives reversibility and irreducibility of the soft CV kernel.

The contraction is proved on the two-branch regime `CV.Regime Δ q`,
`(Δ ≥ 125 ∧ q ≥ 1.809Δ) ∨ (Δ ≥ 6 ∧ q ≥ 11Δ/6)`, in
[`CV/Scalar.lean`](../../ZeroFreeness/Coupling/CV/Scalar.lean). On the critical
branch the scalar closure holds with the same gap 59/226125, so the
constant 409060125/50858 is unchanged. `CV.option_root_ci_critical` states
the critical branch. The main theorem uses it on the line `q = 11Δ/6`
through `ZeroFreeness.Potts.critical_hard_colouring_input`, and near-Vigoda uses it
directly at its critical pairs.

### Near-Vigoda proof and cited results

The exact integer reduction leaves only (Δ,q)=(6j,11j), 1≤j≤20, below degree
125. The paper cites CFFGZZ Theorem 20 at those points. Lean instead uses
the Carlson–Vigoda contraction on the critical line,
`CV.option_root_ci_critical`, since Δ = 6j ≥ 6. All other cases use the
proved strict-Vigoda or CV theorem. `near_vigoda_uniform_ci`,
`near_vigoda_transfer_inputs` and `near_vigoda_zero_free` take no
critical-pairs or literature hypothesis.

Remark 4.4 (`rem:critical-scope`) is formalized in
[`CriticalScope.lean`](../../ZeroFreeness/Potts/Theorems/CriticalScope.lean): every
critical integer pair is `(6j,11j)` (`ZeroFreeness.Potts.critical_line_pairs`), the
list slack is at least `5Δ/6` for arbitrary pinnings
(`ZeroFreeness.Potts.hardList_slack_critical`), the `x = 0` law is uniform on proper
list colourings (`ZeroFreeness.Potts.gibbs_zero_uniform`), and the `x = 0` coupling
input holds on original graphs along the whole critical line
(`ZeroFreeness.Potts.critical_line_hard_endpoint`). The remark's claim that
CFFGZZ Theorem 20 and Proposition 22 apply is a statement about the cited
paper and is not formalized; Lean proves the same bound by the CV
contraction.

### Girth-five proof and cited results

The only cited result is
[CLMM2023, Condition 5.12 and Lemma 5.13](https://arxiv.org/html/2304.01954v3),
the fixed-base-graph, all-pinnings sphere-to-coupling statement, proved as
`CLMM.Lemma513.sphere_to_coupling`. The proof is a strong induction on the
number of free vertices. When the sphere has no free vertex, the two laws
share their marginal off the ball. Otherwise it conditions on the sphere
vertex of least total variation through a maximal coupling, and the
conditioned laws are smaller instances, with the same root or rerooted at
that vertex. The Lean bound uses `1 + log ℓ` where the written proof uses
harmonic numbers. The formalized statement is the positive-activity branch
with positive sphere-decay error; it does not reproduce the separate
zero-temperature colouring endpoint. It assumes none of the spectral gap,
covariance
bounds, response induction, weighted-source estimate, or girth-five
coupling conclusion.

The following are also proved internally:

- Supported conditional-star operators, product decompositions, additive
  compression and the full unequal-incidence Schur-complement inequality.
- The global rate-one Glauber spectral estimate and actual Poincaré
  inequality, including the hard endpoint by finite-law continuity.
- The actual two-layer insertion law, keeping the full dependent shell and
  exterior source; local and global covariance estimates and insertion errors.
- Doob conditioning under successive pinnings, exact root-response identities,
  and simultaneous finite-size induction for the two response norms.
- A degree threshold depending only on δ, finite simultaneous response
  constants, and the weighted-source bound on the full physical interval.
- Fixed-base-graph sphere decay, radius selection, the hard endpoint coupling
  limit, graph-family complex transfer, and original partition semantics.

The explicit final threshold is the maximum of the spectral threshold
`girthFiveThreshold δ` and the natural ceiling of
`covarianceDegreeThreshold δ`. No extra bound on five-cycle or six-cycle
counts is imposed. The public original-graph result requires girth only
of `(tau.toPinningData G).graph`; pinned vertices may lie on shorter cycles.

The Section 9 lemmas are also stated at their written strength.
[`Covariance/Graph/Disintegration.lean`](../../ZeroFreeness/Coupling/Girth/Covariance/Graph/Disintegration.lean)
proves Lemma 9.1 (`Girth.second_layer_disintegration`) for every `x ≥ 0`,
including the hard-colouring law at `x = 0`.
[`Covariance/Insertion/OneEdgeOperator.lean`](../../ZeroFreeness/Coupling/Girth/Covariance/Insertion/OneEdgeOperator.lean)
proves Lemma 9.2 (`Girth.girth5_one_edge`) for `0 ≤ x ≤ 1`.
[`Spectral/OperatorGap.lean`](../../ZeroFreeness/Coupling/Girth/Spectral/OperatorGap.lean)
proves Theorem 9.7 in operator form, `𝓛² ⪰ γ_δ 𝓛` on the supported `L²`
space for every `x ∈ [0,1]` (`Girth.OperatorGap.potts_gap_girth5`).

[`Girth/CommonThreshold.lean`](../../ZeroFreeness/Potts/Regions/Girth/CommonThreshold.lean)
proves the footnote to main-paper Table A.1: one girth threshold serves both
the coupling-independence and the zero-free statement, for large girth,
the BBR interval and girth five (`Girth.high_girth_common_threshold`,
`Girth.bbr_common_threshold`, `Girth.girth_five_common_threshold`).

## Scope of the coverage

Every numbered theorem, lemma, proposition and corollary of the companion
has a Lean counterpart; the [coverage table](../coverage.json) gives the status
and Lean names of each of its 75 numbered statements. Two lemmas are
formalized in the narrowed form the companion now states:

- Lemma 6.10 (`lem:hg-eventual-transfer`) is stated for the Potts family at
  positive activity `x ∈ J ⊆ (0,1]`, the only case the companion uses, and
  proved as
  `Girth.potts_eventual_transfer_uniform` and its two companions.
- The `k`-fold clause of Lemma 3.6 (`lem:boundary-sensitivity`) counts
  labelled free–pinned edges, as in the main text, and is proved as
  `ZeroFreeness.Potts.lem_boundary_sensitivity`.

Only citation-level claims remain unformalized: that CFFGZZ Theorem 20 and
Proposition 22 apply in Remark 4.4, that the hard metric of
Definition 5.3 is literally Eq. (2) of Carlson and Vigoda (2024), and the
literature attributions of Remarks 4.2 and 4.9. Algorithmic and FPTAS
claims are outside the scope of a Lean statement.

The regional BBR proof uses independent arithmetic certificates for the
small degree-gap-two cases; `BBR/GapTwo.lean` also proves Proposition 2.6(i)
itself at gap two. Three cited ingredients are formalized by a route
different from the cited proof: the critical-line hard bound by the CV contraction
rather than the CFFGZZ argument, BBR Proposition 2.6(i) by concavity of
`log` rather than BBR's Lemmas 4.1 and 4.2(i), and CLMM Lemma 5.13 with
`1 + log ℓ` rather than harmonic numbers. Where a Lean proof of one of the
companion's own statements takes a different route, such as the compactness
proof of Lemma 8.3, the note in the coverage table says so.

## Recorded verification

The complete single-library check, including the main text and all seven
appendix regions, passes **4066 build jobs** and the transitive axiom
audit of **11313 project declarations**. Only `propext`,
`Classical.choice`, and `Quot.sound` are used. The check includes the
modules that prove the six cited results, `Coupling/CV/Scalar`, `Coupling/CV/RootCI`,
`Coupling/Girth/Tree/InfluenceIdentity`, `Coupling/CLMM/SphereCoupling`,
`Coupling/CLMM/SphereEstimate`, `Coupling/BBR/Theorem25` and
`Coupling/BBR/Proposition26`, and the modules that state the remaining
numbered statements. The [module guide](README.md#companion-statements-in-dedicated-modules) lists the companion's dedicated modules, and the [coverage table](../coverage.json) gives the Lean names of every numbered statement of both papers. See the [verification record](../verification.json)
for recorded source hashes and the source scan, and the
[provenance index](../provenance/README.md) for earlier records.
