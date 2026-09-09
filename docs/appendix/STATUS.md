# Appendix Potts proofs

The completed-region entry point is `CI2ZF/Appendix/CompletedRegions.lean`.
Run `bash scripts/check-appendix.sh` to compile its full dependency closure
with warnings treated as errors and audit every imported project declaration.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Literature results are explicit proposition parameters, not added axioms.

## Completed regions

| Region | Coupling independence | Uniform zero-free conclusion |
| --- | --- | --- |
| Edge-Potts, maximum original degree Δ≥2 and q ≥ 3Δ | `Edge.root_children_ci`: actual root-conditioned edge-colour Gibbs laws have Hamming transportation distance at most Δ−1, for every x in [0,1] | `Edge.edge_potts_zero_free`, including arbitrary edge pinning and the exact forced-zero multiplicity at zero |
| Large girth, Δ ≥ 3 and q ≥ Δ+3 | `Girth.high_girth_coupling`: a girth threshold and one coupling constant work uniformly in graph size, pinning, and x in [0,1] | `Girth.high_girth_zero_free` and `Girth.high_girth_original_zero_free`, including arbitrary improper pinning and the exact forced-zero multiplicity |
| General-graph high temperature, x₀>0 and q>11(1−x₀)Δ/6 | `high_temperature_graph_coupling`: the explicit constant 2(1−x₀)Δ / (q−11(1−x₀)Δ/6) works on [x₀,1] | `high_temperature_zero_free`, for both normalized and full partition functions, without a hard-colouring feasibility bound |
| BBR large-girth interval, q≥3 and Δ/q≥(e−1/2)/(e−1) | `BBR.high_girth_coupling`: one girth threshold and one CI constant work on the entire closed interval [`BBR.start q Δ`,1] | `BBR.high_girth_zero_free` and `BBR.high_girth_original_zero_free_and_responses`, including actual one-root response logarithms |
| Carlson–Vigoda, Δ≥125 and q≥1.809Δ | `CV.option_root_ci` and `CV.root_coupling`: actual normalized root-child laws have Hamming transport at most 409060125/50858 < 8043.19, uniformly on [0,1] | `CV.zero_free`: the full original-graph statement, arbitrary pinning, normalized nonvanishing and exact forced-zero multiplicity |
| Near-Vigoda, Δ≥2 and q≥(11/6−1/84000)Δ | `Regimes` proves the exact integer reduction to the proved strict/CV regimes and at most twenty critical-line hard-colouring inputs | `near_vigoda_zero_free`: the full uniform original-graph statement on [0,1] |
| Girth 5, 0<δ≤1, Δ≥`Girth.girthFiveCIThreshold δ`, and q≥(1+δ)Δ | `Girth.girth_five_coupling`: one finite constant for every size, pinning, and x in [0,1] | `Girth.girth_five_zero_free` and `Girth.girth_five_residual_original_zero_free`, with girth required only of the free residual graph |

Names in the table are relative to `CI2ZF.Appendix`.

### Edge-Potts proof and external inputs

No unproved external theorem is required. The proof constructs weighted finite
slot models, proves their actual conditional Gibbs identities, exposure
couplings and recursive transport bound, proves real-rooted finite slot
approximations, projects to the finite colour space and passes to the limit.
The zero-free corollary uses the already formalized graph-class transfer theorem.

### Large-girth proof and external inputs

Only explicitly cited general CLMM2023 results remain as named parameters:

- `CavityTree.CLMMInfluenceIdentity.factorization`: Lemma 8.7, the exact tree
  influence–Jacobian factorization.
- `CLMM.Literature`: Equation (10), derived from Lemmas 5.19/5.20, giving the
  graph sphere influence estimate, and Lemma 5.13, converting sphere decay to
  a Hamming coupling bound. `CLMM.FixedAmbientSphereDecay` fixes the base
  graph before quantifying over all further pinnings: every sphere is
  measured in that same base graph, as required by Condition 5.12.

The interfaces concern actual finite Potts/Gibbs distributions. They do not
assume this appendix's local contraction, tree decay, coupling independence,
or zero-free conclusion. All q ≥ Δ+3 estimates, a uniform burn-in, graph CI,
the x=0 and x=1 endpoints, and normalized/original partition semantics are
proved in Lean.

`Girth.high_girth_residual_original_zero_free` states the original pinned
polynomial result with girth required only after pinning. For BBR the
corresponding entry point is `BBR.high_girth_residual_original_zero_free`;
its radius is reduced to exclude zero, so both the normalized and full
polynomials are nonzero throughout the stated positive-temperature neighbourhood.

### High-temperature proof and external inputs

No unproved external result is required. The concrete positive-activity
Vigoda coupling supplies the explicit CI constant. The positive-base
graph-family response induction supplies the uniform complex neighbourhood.
The proof does not impose q≥Δ+1 and permits arbitrary improper pinning.

### BBR proof and external inputs

`BBR.Literature` records BBR Proposition 2.6(i) and Theorem 2.5 with their
published hypotheses. `BBR.InfluenceIdentity` records the general CLMM
Lemma 8.7 influence–Jacobian identity in square-root message coordinates.
The same `CLMM.Literature` graph-transfer inputs listed above are retained.
The message/Gibbs correspondence, exact derivatives, interval-wide
contraction, tree influence and relative spatial decay, and the positive
zero-free transfer are proved internally. The exceptional (q,Δ)=(3,4)
interval and all degree-gap-two parameter cases are proved internally.

### Carlson–Vigoda proof and external inputs

No unproved external result is required. The proof uses the actual CV flip
profile, common-coin activation, feasible component couplings, the complete
low-multiplicity certificate checked by Lean's kernel, weighted configuration
paths, and the true output-score discount. The final geometric drift feeds
weighted path coupling and a two-metric stationary comparison. Finite-state
continuity gives x=0, while x=1 is the common product law. The bound and its
uniform complex corollary do not retain any matching, drift, contraction,
stationarity, or hard-colouring hypothesis.

### Near-Vigoda proof and external inputs

The exact integer reduction leaves only (Δ,q)=(6j,11j), 1≤j≤20, below degree
125. At those points, the parameter is the explicitly cited CFFGZZ Theorem 20
hard-colouring coupling result on actual original graphs and arbitrary
pinning. Its conversion to normalized boundary-count laws is already proved
in the main text. All other cases use the internally proved strict-Vigoda or
CV theorem. No appendix-specific conclusion is assumed as a literature input.

### Girth-five proof and external input

The only literature parameter is `Girth.SphereCouplingInput`, precisely the
fixed-base-graph, all-pinnings sphere-to-coupling statement of
[CLMM2023, Condition 5.12 and Lemma 5.13](https://arxiv.org/html/2304.01954v3).
The interface uses actual Potts laws and positive sphere-decay error. It
does not assume the spectral gap, covariance bounds, response induction,
weighted-source estimate, or the girth-five coupling conclusion.

The following are proved internally:

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

## Verification

The current combined check, including the main-text independent-colour-field
Lee–Yang proof, passed **4034 build jobs** and the transitive audit of
**9620 project declarations** on 2026-09-09. Only `propext`,
`Classical.choice`, and `Quot.sound` were used. The source scan covered the
joint **489-file** proof closure and found no forbidden proof constructs;
all ten compatibility imports were also built. See the
[machine-readable verification record](VERIFICATION.json) for source hashes,
precise scope, and the earlier Appendix migration verification.
