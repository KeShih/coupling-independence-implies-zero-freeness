# Appendix Potts milestones

The completed-region entry point is `CI2ZF/Appendix/CompletedRegions.lean`.
Run `bash scripts/check-appendix.sh` to compile its full dependency closure
with warnings treated as errors and audit every imported project declaration.
Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed.
Literature results are explicit proposition parameters, not added axioms.

## Completed regions

| Region | Coupling independence | Uniform zero-free conclusion |
| --- | --- | --- |
| Edge-Potts, maximum original degree Δ and q ≥ 3Δ | `Edge.root_children_ci`: actual root-conditioned edge-colour Gibbs laws have Hamming transportation distance at most Δ−1, for every x in [0,1] | `Edge.edge_potts_zero_free`, including arbitrary edge pinning and the exact forced-zero multiplicity at zero |
| Large girth, Δ ≥ 3 and q ≥ Δ+3 | `Girth.high_girth_coupling`: a girth threshold and one coupling constant work uniformly in graph size, pinning, and x in [0,1] | `Girth.high_girth_zero_free` and `Girth.high_girth_original_zero_free`, including arbitrary improper pinning and the exact forced-zero multiplicity |
| General-graph high temperature, x₀>0 and q>11(1−x₀)Δ/6 | `high_temperature_graph_coupling`: the explicit constant 2(1−x₀)Δ / (q−11(1−x₀)Δ/6) works on [x₀,1] | `high_temperature_zero_free`, for both normalized and full partition functions, without a hard-colouring feasibility bound |
| BBR large-girth interval, q≥3 and Δ/q≥(e−1/2)/(e−1) | `BBR.high_girth_coupling`: one girth threshold and one CI constant work on the entire closed interval [`BBR.start q Δ`,1] | `BBR.high_girth_zero_free` and `BBR.high_girth_original_zero_free_and_responses`, including actual one-root response logarithms |

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
  a Hamming coupling bound.

The interfaces concern actual finite Potts/Gibbs distributions. They do not
assume this appendix's local contraction, tree decay, coupling independence,
or zero-free conclusion. All q ≥ Δ+3 estimates, a uniform burn-in, graph CI,
the x=0 and x=1 endpoints, and normalized/original partition semantics are
proved in Lean.

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

## Work in progress

The CV q/Δ≈1.809 region and fixed girth 5 region are
still being assembled. Their intermediate modules in the repository are not
claimed as completed-region theorems by this milestone.
