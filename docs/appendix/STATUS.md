# Potts appendix: theorem status and cited results

The [module guide](README.md) lists the seven regional entry points. The
[documentation index](../README.md) covers the main-text Potts, Holant, and
Lee–Yang proofs.

The regional entry point is `CI2ZF/Potts/Regions.lean`.
Run `bash scripts/check-appendix.sh` to compile its full dependency closure
with warnings treated as errors and audit every imported project declaration.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The formalized versions of the cited ingredients listed below are proved in
the library, so no regional endpoint takes a literature parameter.

## Regional endpoints

The table records the regional conclusions. None of them takes a literature
hypothesis; the sections below list the cited results each proof uses and
where they are proved. The auxiliary and generalization limits are recorded in
[Scope of the coverage](#scope-of-the-coverage).

| Region | Coupling independence | Uniform zero-free conclusion |
| --- | --- | --- |
| Edge-Potts, maximum original degree Δ≥2 and q ≥ 3Δ | `Edge.root_children_ci`: actual root-conditioned edge-colour Gibbs laws have Hamming transportation distance at most Δ−1, for every x in [0,1] | `Edge.edge_potts_zero_free`, including arbitrary edge pinning and the exact forced-zero multiplicity at zero |
| Large girth, Δ ≥ 3 and q ≥ Δ+3 | `Girth.high_girth_coupling`: a girth threshold and one coupling constant work uniformly in graph size, pinning, and x in [0,1] | `Girth.high_girth_zero_free` and `Girth.high_girth_residual_original_zero_free`, with girth required only of the free residual graph, including arbitrary improper pinning and the exact forced-zero multiplicity |
| General-graph high temperature, x₀>0 and q>11(1−x₀)Δ/6 | `high_temperature_graph_coupling`: the explicit constant 2(1−x₀)Δ / (q−11(1−x₀)Δ/6) works on [x₀,1] | `high_temperature_zero_free`, for both normalized and full partition functions, without a hard-colouring feasibility bound |
| BBR large-girth interval, q≥3 and Δ/q≥(e−1/2)/(e−1) | `BBR.high_girth_coupling`: one girth threshold and one CI constant work on the entire closed interval [`BBR.start q Δ`,1] | `BBR.high_girth_zero_free` and `BBR.high_girth_residual_original_zero_free`, for both normalized and full partition functions, with girth required only of the free residual graph; `BBR.high_girth_original_zero_free_and_responses` adds the actual one-root response logarithms |
| Carlson–Vigoda, Δ≥125 and q≥1.809Δ | `CV.option_root_ci` and `CV.root_coupling`: actual normalized root-child laws have Hamming transport at most 409060125/50858 < 8043.19, uniformly on [0,1] | `CV.zero_free`: the full original-graph statement, arbitrary pinning, normalized nonvanishing and exact forced-zero multiplicity |
| Near-Vigoda, Δ≥2 and q≥(11/6−1/84000)Δ | `near_vigoda_uniform_ci`: one constant on [0,1], via the exact integer reduction `nearVigoda_regime_cases` to the proved strict-Vigoda and CV regimes and twenty critical pairs, which use the CV contraction on the critical line; `near_vigoda_transfer_inputs` gives the hard-endpoint and every-[δ,1] coupling inputs | `near_vigoda_zero_free`: the full uniform original-graph statement on [0,1] |
| Girth 5, 0<δ≤1, Δ≥`Girth.girthFiveCIThreshold δ`, and q≥(1+δ)Δ | `Girth.girth_five_coupling`: one finite constant for every size, pinning, and x in [0,1] | `Girth.girth_five_zero_free` and `Girth.girth_five_residual_original_zero_free`, with girth required only of the free residual graph |

Names in the table are relative to `CI2ZF.Appendix`.

### Edge-Potts proof and cited results

No cited result is used. The proof constructs weighted finite
slot models, proves their actual conditional Gibbs identities, exposure
couplings and recursive transport bound, proves real-rooted finite slot
approximations, projects to the finite colour space and passes to the limit.
The zero-free corollary uses the already formalized graph-class transfer theorem.

### Large-girth proof and cited results

The proof uses three general CLMM2023 ingredients, each with a proved Lean
version:

- Lemma 8.7, the exact tree influence–Jacobian factorization, stated as
  `CavityTree.CLMMInfluenceIdentity` and proved as
  `CavityTree.clmmInfluenceIdentity` in
  [`Tree/InfluenceIdentity.lean`](../../CI2ZF/Coupling/Girth/Tree/InfluenceIdentity.lean)
  from the actual finite-tree Gibbs law.
- Equation (10), derived from Lemmas 5.19/5.20, giving the graph sphere
  influence estimate. It is the single field `sphere_estimate` of
  `CLMM.Literature`, proved as `CLMM.Eq10.sphere_estimate_proof` in
  [`CLMM/SphereEstimate.lean`](../../CI2ZF/Coupling/CLMM/SphereEstimate.lean)
  and packaged as `CLMM.literature`. The ball–tree correspondence uses
  girth only to exclude edges inside a distance layer and to make parents
  unique.
- Lemma 5.13, converting sphere decay to the Hamming coupling bound
  `2Δ^R`, proved as `CLMM.Lemma513.sphere_to_coupling` in
  [`CLMM/SphereCoupling.lean`](../../CI2ZF/Coupling/CLMM/SphereCoupling.lean).
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
  [`BBR/Theorem25.lean`](../../CI2ZF/Coupling/BBR/Theorem25.lean), follows
  BBR Section 3: the mean value theorem along the segment `sR + (1−s)R'`,
  Cauchy–Schwarz, and the pointwise Jacobian bound `differential_contraction`.
- `BBR.proposition_2_6_i_holds`, in
  [`BBR/Proposition26.lean`](../../CI2ZF/Coupling/BBR/Proposition26.lean),
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
[`BBR/InfluenceIdentity.lean`](../../CI2ZF/Coupling/BBR/InfluenceIdentity.lean).
Interval-wide contraction,
tree influence and relative spatial decay, and the positive zero-free
transfer are derived from the four cited results. The exceptional
(q,Δ)=(3,4) interval and all degree-gap-two parameter cases, which lie
outside the degree range of Proposition 2.6(i), are handled directly in
the application; this does not extend the published Proposition 2.6(i)
statement. The ordinary `q ≥ Δ+3` large-girth route uses the separate
CLMM identity `CavityTree.clmmInfluenceIdentity`.

### Carlson–Vigoda proof and cited results

No cited result is used. The proof uses the actual CV flip
profile, common-coin activation, feasible component couplings, the complete
low-multiplicity certificate checked by Lean's kernel, weighted configuration
paths, and the true output-score discount. The final geometric drift feeds
weighted path coupling and a two-metric stationary comparison. Finite-state
continuity gives x=0, while x=1 is the common product law. The bound and its
uniform complex corollary do not retain any matching, drift, contraction,
stationarity, or hard-colouring hypothesis.

The contraction is proved on the two-branch regime `CV.Regime Δ q`,
`(Δ ≥ 125 ∧ q ≥ 1.809Δ) ∨ (Δ ≥ 6 ∧ q ≥ 11Δ/6)`, in
[`CV/Scalar.lean`](../../CI2ZF/Coupling/CV/Scalar.lean). On the critical
branch the scalar closure holds with the same gap 59/226125, so the
constant 409060125/50858 is unchanged. `CV.option_root_ci_critical` states
the critical branch. The main theorem uses it on the line `q = 11Δ/6`
through `CI2ZF.Potts.critical_hard_colouring_input`, and near-Vigoda uses it
directly at its critical pairs.

### Near-Vigoda proof and cited results

The exact integer reduction leaves only (Δ,q)=(6j,11j), 1≤j≤20, below degree
125. The paper cites CFFGZZ Theorem 20 at those points. Lean instead uses
the Carlson–Vigoda contraction on the critical line,
`CV.option_root_ci_critical`, since Δ = 6j ≥ 6. All other cases use the
proved strict-Vigoda or CV theorem. `near_vigoda_uniform_ci`,
`near_vigoda_transfer_inputs` and `near_vigoda_zero_free` take no
critical-pairs or literature hypothesis.

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

## Scope of the coverage

These statuses concern the seven Potts regional endpoints and the proofs
used to obtain them. They do not claim a theorem-by-theorem formalization
of every auxiliary statement or every generalization in the appendix.

- The paper's eventual-transfer lemma covers general pinning/subgraph-closed
  pairwise spin-system families, including hard constraints with separate
  feasibility assumptions. `CLMM.eventual_transfer` is the positive-activity
  Potts specialization needed for the regional conclusions here.
- The edge-Potts proof constructs finite positive slot laws and passes to
  the finite-colour Gibbs-law limit. It does not separately prove the
  paper's countable exact-slot representation lemma or its entire-function
  factorization argument.

The BBR proof also uses independent arithmetic certificates for the small
degree-gap-two cases. Three cited ingredients are formalized by a route
different from the cited proof: the critical-line hard bound by the CV contraction
rather than the CFFGZZ argument, BBR Proposition 2.6(i) by concavity of
`log` rather than BBR's Lemmas 4.1 and 4.2(i), and CLMM Lemma 5.13 with
`1 + log ℓ` rather than harmonic numbers. Thus the regional conclusions can
be proved by a different internal argument without reproducing each
intermediate proof path in the paper.

## Recorded verification

The complete single-library check, including the main text and all seven
appendix regions, passed **4040 build jobs** and the transitive axiom
audit of **10372 project declarations** on 2026-09-25. Only `propext`,
`Classical.choice`, and `Quot.sound` were used. This run includes the
five modules that prove the cited results:
`Coupling/Girth/Tree/InfluenceIdentity`, `Coupling/CLMM/SphereCoupling`,
`Coupling/CLMM/SphereEstimate`, `Coupling/BBR/Theorem25` and
`Coupling/BBR/Proposition26`. See the [verification record](../verification.json)
for recorded source hashes and the source scan, the
[previous record](../provenance/pre-near-vigoda-ci-20260924-verification.json),
the [pre-closure snapshot](../provenance/pre-bbr-influence-20260910-verification.json),
and [the earlier verification](../provenance/lee-yang-verification.json).
