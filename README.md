# Coupling Independence Implies Zero-Freeness — Lean

This repository formalizes the Potts and Holant sections of the main text of *Coupling Independence Implies Zero-Freeness*. The status of each model is reported separately; completion of one does not imply completion of the other.

**Potts: the uniform zero-free main theorem at the strict threshold `q > 11Δ/6`, and the transfer theorem for arbitrary graph families closed under induced subgraphs, are complete. The concrete coupling-independence proof, joint induction at both endpoints, uniform radius, and neighborhood patching have all been checked by Lean. The equality case retains only an explicitly identified external hard-coloring CI input on original finite graphs with arbitrary pinning.** No axioms or placeholder proofs conceal unfinished steps.

**Holant: the main-text section is fully formalized.** The residual lemma, concrete CI bound, uniform complex polytube theorem, open orthant and uniform diagonal neighborhoods, and all main-text corollaries for b-matchings and b-edge covers have been proved. The final entry points retain no unproved external inputs. All 46 Holant modules are included in the library build and axiom audit.

## Appendix Potts results

All seven regions have completed coupling-independence and uniform zero-free
theorems: edge-Potts, general-graph high temperature, large-girth `q ≥ Δ+3`,
the BBR interval, Carlson–Vigoda, near-Vigoda, and unrestricted girth 5 at
`q ≥ (1+δ)Δ` for a degree threshold depending only on δ.
See [APPENDIX_STATUS.md](APPENDIX_STATUS.md) for exact statements, the
complete internal girth-five proof, and the explicitly named literature
inputs. Run `bash scripts/check-appendix.sh` for the completed-region build
and transitive axiom audit. Girth conditions in the paper-facing results
apply to the free residual graph after arbitrary pinning.

## Proved Potts results

| Paper content | Lean file and principal results |
| --- | --- |
| Complex partition polynomial on actual finite simple graphs with arbitrary pinning, consistent with the real model | `CI2ZF/PottsModel.lean`: `normalizedPartition_ofReal` |
| Removal of the forced zero factors contributed by pinned-only monochromatic edges, with identities valid at zero | Same file: `fullPolynomial_eq`, `fullPartition_eq` |
| Hard feasibility when q ≥ Δ+1, and nonvanishing of the normalized partition function at every nonnegative real parameter | Same file: `exists_hardAdmissible_of_succ_le`, `normalizedPartition_nonnegative_ne_zero` |
| The main-text recursion that pins one additional vertex, including normalized children for blocked colors | Same file: `normalizedPartition_pinVertex_recursion`, `rootChildPartition_zero_ne_zero` |
| Complex averaging lemma: both averages are nonzero, with Log comparison bound 2A W+4δ | `CI2ZF/PaperComplexAverage.lean`: `paper_complex_average` |
| Normalized Log branch obtained by simultaneous scaling from zero | Same file: `differentiableOn_scaledCenteredAverageLogRatio`, `exp_scaledCenteredAverageLogRatio` |
| Actual marginal distributions on disjoint shells satisfy Σ W ≤ global W, yielding a shell with small W | `CI2ZF/ShellMarginals.lean`: `sum_W_shellMarginal_le`, `exists_low_W_shellMarginal` |
| Uniform relative perturbation control for a finite family of local polynomials; patching the neighborhoods of zero and positive temperature | `CI2ZF/LocalStability.lean`: `finite_polynomial_relative_stability`, `patch_endpoint_and_positive` |
| Existence and uniqueness of normalized analytic logarithms on nonvanishing disks | `CI2ZF/AnalyticLog.lean`; the interface for actual Potts instances is in `CI2ZF/PottsAnalytic.lean` |
| The multiplicity at zero of the original pinned partition polynomial is exactly the number of pinned-only monochromatic edges | `CI2ZF/PottsAnalytic.lean`: `fullPolynomial_rootMultiplicity_zero` |
| For each fixed graph and pinning, some positive zero-free radius exists around [0,1] | `CI2ZF/FixedGraph.lean`: `fixed_instance_zero_free`, `fixed_instance_zero_free_of_vigoda` |
| Realization of every boundary-count datum by independently pinned leaves, preserving the degree bound and girth | `CI2ZF/PinningLeafRealization.lean`, `PinningLeafCycles.lean`, `PinningLeafGirth.lean`: `realization`, `exists_bounded_girth_realization` |

These theorems allow arbitrary pinning; the pinned part need not itself be a proper coloring. Normalization is defined directly through a finite polynomial, without division by zero at the origin.

The complex averaging lemma retains the amplitude condition in the main text, without imposing an additional small-norm condition on the original h. The proof first centers both averages around 1 using a common shift, then controls the difference of their principal logarithms. The scaled branch vanishes at parameter zero and exponentiates to the ratio of the original averages. The finite transport distance is `PottsCI.FinDist.W`, defined as the infimum of coupling costs. This is an implementation for finite distributions; it is not connected to mathlib's general measure-theoretic Wasserstein interface. The proof does not assume that an optimal coupling exists.

## The concrete Potts coupling-independence proof

This proof uses actual finite graphs, list constraints, and the transition probabilities of `hardStep` / `softVigodaKernel` throughout.

| Step | Results checked by Lean |
| --- | --- |
| Preservation of legality, reversibility, and stationarity for concrete hard component flips | `PottsCI/Vigoda/ComponentCoupling.lean` |
| Exact transition mass `p_s/(nq)` for feasible components, and holding mass at least `1/q` | `CI2ZF/HardMoveMass.lean` |
| Actual joint distribution under common Bernoulli activation, expected edge count, and root-list budget | `CommonCoins`, `ActivationLaw`, `ActivationAverage`, `ActiveDegree` |
| Perturbation bounds for hard and soft transitions after adding one actual boundary constraint | `HardFlipBoundary`, `BoundaryActivation`, `SoftFlipBoundary` |
| The actual root-deleted model and boundary comparison for two additional pinnings | `RootChildren`, `RootBoundary` |
| Common flips away from the root, complete root-component pairing, and concrete residual matching allocated by neighbor | `HardConditionalCoupling`, `HardRootAllocation`, `HardRegularAllocation` |
| Exhaustive classification of all remaining positive-probability transitions | `HardMoveClassification.hardCommon_residual_exhaustion` |
| Full `11m/6−allowed` bound for ordinary colors, covering 0/1/2/≥3 neighbors and blocked cases | `RegularColourTwo.perColourCharge_le` |
| Concrete matching rules, capacities, combination, and full cost bound for the two root colors | `HardRootColours`, `RootColourCharge.rootColourCharge_le` |
| Allocations for all colors simultaneously respect transition-probability capacities; product completion gives a full coupling | `HardRootColourSeparation.fullHardPartial` / `fullHardCoupling` |
| Total charge over all colors is at most `11/6 × unionDegree − commonListCard` | `HardChargeSum.sum_hardColourCharge_le` |
| Exact identities connecting actual transition states, distinct components, and scalar residual/share terms | `HardRegularRates`, `HardIncidenceRates`, `HardPieceSums` |

The numerical certificates use the actual Vigoda profile `1, 13/42, 1/6, 2/21, 1/21, 1/84, 0, …`. The proof first establishes that truncating sizes at seven preserves the full charge expression, then checks the finite integer cases in the Lean kernel. It uses neither `native_decide` nor trusted numerical output from external Python code.

`HardCouplingCost.hardStep_W_drift_le` completes the global cost summation and directly establishes the conditional drift bound for the actual hard kernel. `PottsCITheorem.conditionalHardCouplingEstimate` applies it to common activation. The following theorems in `PottsCITheorem.lean` discharge the final hard-coupling input of the conditional interface in `RootCI.lean`:

- `root_strict_ci`: for `q > 11Δ/6` and `x∈[0,1]`, the Hamming Wasserstein distance between the actual root-conditional distributions is at most `2(1−x)Δ / (q−11(1−x)Δ/6)`.
- `root_strict_uniform_ci`: the uniform constant `2/(q/Δ−11/6)` throughout the same strict regime, quantified over all finite graphs and arbitrary pinning, including x=0, x=1, and an empty remaining graph.
- `root_critical_uniform_ci`: when `q=11Δ/6`, the bound `12/(11δ)` on every interval `[δ,1]` with `δ>0`.

These theorems do not require callers to supply matching, capacity, drift, contraction, or stationarity assumptions. Zero-temperature CI at the critical equality is retained as an explicit external input, as authorized for this formalization. It cannot be obtained by sending δ to zero in the divergent bound `12/(11δ)`. See [EXTERNAL_INPUTS.md](EXTERNAL_INPUTS.md) for the exact interface and source.

`PositiveExactCI.lean` also proves the standalone positive-temperature statement: `root_positive_exact_ci` needs `0 < x ≤ 1` and a positive contraction denominator, without the strict color threshold. Its critical specialization `root_critical_exact_ci` gives `12(1−x)/(11x)`.

`OptionCI.lean` extends the same complete result to `PinningData (Option O) C` with arbitrary boundary-color counts: `none` is the root, and `O` is the common set of remaining vertices. This interface retains the degree bounds and permits repeated boundary counts, allowing it to be used for smaller instances after separation. `RootGibbsSemantics.lean` proves the relationship between these normalized distributions and the conditional weights of the original graph: they agree directly at positive activity; at zero, the original conditional distribution requires the pinned part to be feasible, while the normalized child is defined for every pinning.

## Separator identities on Potts graphs

`Separator.lean` proves the interior–exterior factorization directly from the original finite partition sum, using an explicit vertex decomposition `U ⊕ (S ⊕ O)` and the actual absence of U–O edges. The identity holds over any commutative semiring, including complex activities and zero.

`SeparatorResponse.lean` expresses the complex partition-function response as an average of products of interior and exterior responses under the actual Gibbs shell marginal. `SeparatorExterior.lean` further identifies the exterior factor as the partition function of a genuinely smaller `PinningData` instance on O, with S–O edges represented by boundary-color counts. The separator identity is proved rather than supplied as an assumption.

`BoundedLocalFamily.lean` proves a concrete finite encoding of the family of local polynomials: with at most B free vertices and maximum degree at most Δ, there are at most `q^B` monomials, each of degree at most `2BΔ`. Thus `bounded_local_potts_relative_stability` gives a radius depending only on the number of colors, Δ, B, the compact set of real base points, and the error tolerance. It quantifies over all vertex types and arbitrary pinning; finiteness is proved rather than assumed.

The following connections from the concrete model to the analytic estimates are also complete:

| Step | Files and proved content |
| --- | --- |
| Actual BFS balls and spheres, ball-size bounds, absence of interior–exterior edges, empty spheres, and finite components | `BFSShells`, `BFSShellMarginals` |
| Applying the proved CI bound to BFS in the parent graph to obtain a sphere with small transport cost between actual root-child marginals | `OptionShellMarginals.strict_root_exists_low_sphere`, covering both endpoints of the strict regime |
| Invariance of finite products and partition functions under graph relabeling; preservation of degree bounds under BFS relabeling | `SeparatorRelabel`, `SeparatorDegree` |
| Root-component factorization and cancellation of the common exterior factor of the two children | `ComponentFactorization`, `RootComponentFactorization` |
| Monomial representation and finite encoding of the actual interior factor, uniform stability at positive temperature, and additive error at zero | `SeparatorInsidePolynomial`; a fixed shell need not be feasible at zero |
| Uniform local stability yields a small analytic Log throughout the activity disk | `LocalResponseLog.bounded_inside_positive_log_stability` |
| Unpinning one shell vertex gives a strictly smaller actual model | `OptionPinning`, `ExteriorRepinning` |
| Smaller root-response bounds give the full Hamming Lipschitz bound for exterior responses through uniqueness of analytic branches | `ExteriorAnalyticResponses`, `HammingResponses` |
| Hard-count comparison `Z_d(0) ≤ q^Δ Z_e(0)` for actual root children | `HardCountComparison`, proved by local recoloring and an injection between counted configurations |
| Single-coordinate comparison of actual hard shell weights and a feasible anchor | `ExteriorHardComparison`, `SeparatorHardAnchor` |
| Uniform bound `q^(N+s) H^s exp(αs) |z|` for the finite defect sum at the hard endpoint | `HardEndpointRelativeError`, retaining the anchor-response factor |
| The actual hard separator response equals a feasible main average plus a defect term | `SeparatorHardResponse`, without division by a possibly vanishing interior factor |
| Lower bound on the modulus of the main average, and control of the relative defect and correction Log | `HardMainPerturbation` |
| Bounds for the average Log at positive temperature and the hard endpoint, continued in the actual activity variable | `AnalyticComplexAverage`, `HardAnalyticAverage` |
| Nonvanishing of the actual parent recursion given small child-response Logs | `PositiveParent`, `HardParent`; available root colors and the hard-count ratio at the hard endpoint are proved internally |
| Actual parent recursion for arbitrary boundary-count data, over any commutative semiring | `OptionPartition.option_parent_partition` |
| Nonvanishing of the actual hard separator instance given exterior coordinate-response bounds | `HardSeparatorStep`, with the anchor, hard-weight, and defect-bound inputs discharged |

The one-step lemmas in this table retain appropriate hypotheses about smaller instances. `UniformInduction`, `PositiveUniformTransfer`, and `HardUniformTransfer` discharge those hypotheses by strong induction on actual instances. The final `PottsMainTheorem` requires no complex nonvanishing or response bounds from the caller.

## The uniform Potts main theorem

`fixed_instance_zero_free_of_vigoda` proves the fixed-instance conclusion under the main-text parameter conditions, but its quantifiers are ordered as follows:

$$
\forall G,\tau,\quad \exists\varepsilon(G,\tau)>0,\quad
\widetilde Z_G^\tau(z)\ne0\quad
(\mathrm{dist}(z,[0,1])<\varepsilon(G,\tau)).
$$

`strict_potts_zero_free` proves the stronger statement in which the radius is chosen before quantifying over all graphs and pinnings:

$$
\exists\varepsilon(q,\Delta)>0,\quad \forall G,\tau,\quad
\widetilde Z_G^\tau(z)\ne0\quad
(\mathrm{dist}(z,[0,1])<\varepsilon(q,\Delta)).
$$

The fixed-instance conclusion requires only q ≥ Δ+1; the uniform conclusion uses the full CI argument. `CI2ZF/PottsMainTheorem.lean` contains `strict_potts_zero_free` with no external CI assumption. `CI2ZF/PottsExternalTheorem.lean` supplies the public weak-inequality theorem `potts_zero_free_from_external`: its only external input is hard-coloring CI on original graphs, and it is needed only in the equality branch. The result also identifies the forced zero of the unnormalized partition function and its exact multiplicity.

The paper-facing entry points `potts_main_theorem (q Δ : ℕ)` and `potts_main_strict` use the color set `Fin q` and the integer thresholds `11 * Δ ≤ 6 * q` and `11 * Δ < 6 * q`. Color nonemptiness is derived from the hypotheses. Only the equality branch of `potts_main_theorem` requests the original-graph external CI input.

| Completed connection | Modules |
| --- | --- |
| BFS separation in the same parent graph and identification of actual Gibbs marginals | `OptionBFSSplit`, `OptionBFSMarginals`, `OptionBFSCardinality`, `GenericGibbsRelabel` |
| Actual analytic response bounds for large components at positive and zero temperature | `PositiveSeparatorLog`, `HardSeparatorLog`, `PositiveBFSResponseStep`, `HardBFSResponseStep` |
| Graph-independent depth, volume, logarithmic budgets, and local radii | `TransferScales`, `UniformLocalLogs`, `TransferLocalControls` |
| Arbitrary-root relabeling, reduction of small components, and parent recursion | `RootOptionRelabel`, `OptionComponentFactorization`, `OptionParentNonzero` |
| Simultaneous strong induction on the actual number of free vertices | `UniformInduction`, `InductionComponentSteps`, `InductionParentSteps` |
| Complete induction at both endpoints and the conclusion for the original graph | `PositiveUniformTransfer`, `HardUniformTransfer`, `UniformZeroFreePackaging`, `PottsMainTheorem` |
| Standalone positive-temperature transfer and actual original-graph `pinVertex` responses, without an extra color threshold | `PositiveFamilyTransfer`, `PositiveGraphClassTransfer` |

## Potts transfer for general graph families

`graph_class_potts_transfer_of_bounded` in `GraphClassPottsTransfer.lean` proves the paper's `thm:potts-transfer`: for `q ≥ Δ+1` and an induced-subgraph-closed family of graphs with maximum degree at most Δ, hard-endpoint CI and uniform CI on positive compact intervals for all pinnings of original graphs imply a complex zero-free neighborhood uniform over the family. `GraphClass` expresses closure under induced pullback by arbitrary embeddings, including relabeling.

`AmbientRealization` retains the actual ambient graph, an embedding of the free vertices, and the partial coloring; vertices no longer needed are removed by passing to induced subgraphs. `PinningRestriction` proves composition of further pinning and deletion. `FamilyInduction` and `FamilyBFSResponseSteps` provide actual family-membership proofs for every smaller instance, and `FamilyUniformTransfer` completes both strong inductions within the family. `GraphClassCoupling` transports the original-graph CI bound through actual Gibbs relabeling and Hamming transport. This proof does not require the family to be closed under attaching leaves, or strengthen its CI hypothesis to arbitrary boundary-count data.

The standalone positive-temperature response lemma is also complete as `GraphClass.positive_interval_zero_free_and_responses` in `PositiveGraphClassTransfer.lean`. It returns a uniform nonvanishing neighborhood and analytic root-quotient responses for original graphs and arbitrary pinning. It requires a nonempty color set and actual positive-temperature CI, without the hard-coloring feasibility threshold `q ≥ Δ+1`.

See [EXTERNAL_INPUTS.md](EXTERNAL_INPUTS.md) for the external theorem boundary and [POTTS_PROOF_MAP.md](POTTS_PROOF_MAP.md) for the label-by-label correspondence. The general profile-ρ tools are instantiated with the concrete Vigoda profile needed for the main proof; this is not a claim to formalize every independent profile variant in the paper.

## The uniform Holant zero-free proof

`HolantModel.lean` defines the Boolean Holant partition function as a sum over edge subsets of an actual finite graph. Each vertex signature depends only on the number of selected incident edges. `Signature` records finite arity, nonnegativity, support with no internal gaps, log-concavity, and `f(0)>0`. For a finite signature family F and degree bound Δ, the radius depends only on F, Δ, and the real-box upper bound R. It is chosen before quantifying over graphs, vertex signatures, and independent edge activities.

| Step | Files and principal entry points |
| --- | --- |
| Initial-interval support, cross-ratio monotonicity, composition of normalized residuals, and a finite closed residual family | `HolantSignatures.lean`: `ratio_cross_le`, `shift_monotonicity`, `normalizedResidual_comp`, `residualFamily_closed` |
| Actual normalized models, zero/one children after edge deletion, recovery of the unnormalized model, and the dead-edge case | `HolantResidualModel.lean`: `complexPartition_deletion`, `complexPartition_dead_edge`, `complexPartition_normalize` |
| Recursive endpoint coupling of actual Gibbs distributions and the exact CI constant | `HolantCouplingTheorem.lean`: `residual_family_sharp_child_W_le` |
| Degree bound for the line graph, actual spheres and bounded local balls, and selection of a sphere with small transport cost | `HolantGeometry.lean`, `HolantAmbientGraph.lean`, `HolantShellSelection.lean`, `HolantShellCostSelection.lean` |
| Actual interior–exterior separator identities, common feasible shell states, and actual marginals of both children | `HolantSeparator.lean`, `HolantInstanceSeparator.lean`, `HolantShellMarginals.lean` |
| Local polynomial coefficient bounds, multilinear perturbation bounds, and uniform numerical budgets | `HolantCoefficientBounds.lean`, `HolantSeparatorCoefficients.lean`, `HolantPolynomialStability.lean`, `HolantTransferParameters.lean` |
| Construction of actual exterior analytic Logs from smaller instances, and accumulation of responses along feasible Boolean paths | `HolantInductiveExterior.lean`, `HolantSupportGeometry.lean`, `HolantShellLipschitz.lean` |
| Actual separator errors for both children, analytic continuation of averages, and nonvanishing of the parent recursion | `HolantSeparatorEstimates.lean`, `HolantSeparatorResponse.lean`, `HolantAnalyticContinuation.lean`, `HolantPathParent.lean` |
| The response induction step using these concrete objects | `HolantUniformResponse.lean`: `uniform_response_step` |
| Simultaneous induction on the number of remaining edges for nonvanishing and child Log-response bounds | `HolantStrongInduction.lean`: `path_simultaneous_of_response_step` |
| Final entry points that discharge the response-step callback and all smaller-instance hypotheses, choosing the radius before all graphs | `HolantTheorem.lean`: `uniform_path_nonzero_and_response`, `exists_uniform_holant_polytube` |
| Lifting the path theorem to the original partition function, polytubes, orthants, and diagonal neighborhoods | `HolantTubeTheorem.lean`, `HolantPolytube.lean` |
| Model identities and reusable applications for capacitated matchings and complementary edge covers | `HolantCapacities.lean`, `HolantApplications.lean` |
| All main-text corollaries, with the application-interface inputs discharged | `HolantCorollaries.lean`: `holant_orthant`, `holant_uniform_diagonal`, `bmatching_uniform_polytube`, `bmatching_orthant`, `bmatching_uniform_diagonal`, `bcover_uniform_polytube`, `bcover_orthant`, `bcover_uniform_diagonal` |

Holant CI is also proved entirely within the library; the final theorems require no external CI assumption. The proof uses actual `signatureGibbs` weights, normalized zero/one child distributions, recursive coupling of residual mass, and the finite-distribution distance `FinDist.W`. If A is the maximum of 0 and the first-order signature values in the normalized residual family, `residual_family_sharp_child_W_le` gives the constant from the main text:

$$
C=2\bigl((1+A^2R)^\Delta-1\bigr).
$$

Zero-activity coordinates are handled directly through the actual distributions and zero-weight events; activities need not be strictly positive. The identity between the symmetric-difference cost on edge subsets and the Boolean Hamming cost is also proved.

`HolantUniformResponse.lean` applies this CI bound to actual sphere marginals and constructs a common finite shell state space, separator coefficients, and exterior responses. A uniform growth bound for residual signatures controls the local coefficients. An explicit multilinear estimate bounds the perturbation error of local polynomials, allowing some local factors to vanish at the real base point. The required feasible anchors, positive weight of the empty state, actual exterior models, and smaller bridge instances corresponding to adjacent states are all derived from the model definitions; callers do not supply them as assumptions.

The geometry is organized in a way equivalent to the main-text argument: the line graph of the original graph is fixed as an ambient graph, and each step intersects its spheres with the current set of remaining edges. Deleted edges and nonedge coordinates do not contribute to the partition function. The ambient degree is still bounded by `2(Δ−1)`, and the local ball-size bound depends only on Δ and the sphere depth. Spheres whose intersection is empty are treated as valid separators in the same construction. This avoids rebuilding distances in every recursive instance or introducing a separate local proof branch for empty spheres. Strict decreases in the edge counts of exterior and bridge instances, the absence of interior–exterior edges, and the actual shell transport bound are each proved in Lean.

`HolantStrongInduction.lean` is a general assembly lemma that retains a response-step callback. `HolantTheorem.lean` discharges that callback using `uniform_response_step`, simultaneously proving nonvanishing of the remaining instances and bounds on normalized analytic Log responses. The final path theorem retains only the signature family, graph degree bound, real-box range, and constructed uniform numerical parameters. It retains no coupling, separator-identity, exterior-Log, or smaller-instance nonvanishing assumptions. Empty edge sets and dead edges are handled by the same induction.

For any finite signature family F, the quantifier order is

$$
\forall\Delta\in\mathbb N,\ R\ge0,\quad
\exists\varepsilon(F,\Delta,R)>0,\quad
\forall G,f,\boldsymbol{x},\boldsymbol{z},\quad
\left(\boldsymbol{x}\in[0,R]^{E(G)}\quad\land\quad
|z_e-x_e|<\varepsilon\ \forall e\right)
\Longrightarrow Z_{G,f}(\boldsymbol{z})\ne0,
$$

where G is a finite simple graph of maximum degree at most Δ, with vertex signatures from F whose arities equal the corresponding degrees. This is a statement about independent activities with a radius uniform over the entire graph family. The lemmas in `HolantTubeTheorem.lean` whose names end in `_of_paths` perform the geometric lifting. Their path input is discharged by the final entry point; it is not an additional zero-free assumption.

`HolantPolytube.lean` takes the union of the real-box polytubes over R to obtain an open neighborhood of the entire nonnegative orthant: the coordinate product is taken for one common R before taking the union over R. Diagonal specialization gives an open subset of the complex plane containing the nonnegative real axis and common to all graphs. `HolantCapacities.lean` identifies the capacity signatures with the actual b-matching polynomial and proves the reciprocal-activity identity for b-covers by complementing the edge set. The cover application uses the proved reciprocal polytube bound on strictly positive real activity intervals. Its assumptions include that each vertex demand is at most its degree.

## Building and verification

Pinned versions: Lean **4.33.1** and mathlib **v4.33.1**, commit `0df444a360eaa60ab8c11dca51a86af692955474`. Other dependencies are recorded in `lake-manifest.json`.

After installing the Lean version manager elan, run the following from the repository root. `lean-toolchain` selects the required version:

```bash
lake exe cache get
./scripts/check.sh
```

The check script first builds all proofs imported by `CI2ZF.lean`, then runs `AxiomAudit.lean`. Both steps treat warnings as errors. The axiom audit traverses every declaration in the `CI2ZF` and `PottsCI` namespaces and checks its transitive axiom dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed; any other dependency causes failure. The proof library does not import the audit program.

The default aggregate imports **197 project Lean source files**, counting the root `CI2ZF.lean`; `AxiomAudit.lean` is run separately, making 198 source files for the proof-and-audit closure. All 46 Holant modules and the completed Potts family/ambient modules are reachable from the aggregate entry point. The 75 existing files under `CI2ZF/Appendix/` are preserved as additional source and remain outside the default aggregate build and audit. A successful default check does not certify those unimported Appendix files.

The full publishing-checkout check on **2026-09-09**, with the final Potts and Holant entry points imported, passed the build (**3665 jobs**) and the transitive axiom audit of **4014 project declarations**. The 197 imported project source files were also scanned for placeholder proofs and unsafe declarations. These counts describe the entire imported library, not the number of theorems in the paper. Holant comprises 46 modules and 8076 lines of Lean source, all reachable from the aggregate entry point. Per-file records and the earlier Holant-stage verification snapshot are in `holant-source-manifest.json`.

On the development machine, the official Lean compiler is installed locally in `.tools/`, and `scripts/lake.sh` selects it automatically without changing the global Lean environment. `.tools/`, `.lake/`, and caches are not part of the source distribution. On other machines, install the dependencies using the Lean/Lake version specified by `lean-toolchain`, then run the same check script.

## Provenance and scope

`CI2ZF/` contains new proofs for the current main text. The general residual-completion foundation in `PartialCoupling.lean` was adapted from the earlier project and extended. Eleven modules in `PottsCI/`, covering finite distributions, path coupling, the graph model, pinning, activity constraints, the concrete Vigoda kernel, and stationary-distribution comparison, were reused from the earlier `CI2ZF/anc/lean-potts-ci` project. Lean 4.33.1 compatibility issues and component-geometry proof issues were fixed during integration. Hashes of the files before import are recorded in `legacy-source-manifest.json`; provenance of the current paper sources and toolchain is recorded in `source-manifest.json`.

The reused general `SoftKernel` interface is instantiated with the concrete Vigoda kernel in `Vigoda/ComponentCoupling`, where its stationarity is proved. Applications of endpoint continuity and stationary comparison are in `CouplingIndependence` and `RootCI`. The public critical hard-endpoint premise is `ExternalCriticalHardColouringTheorem` on original graphs. `PottsExternalTheorem.lean` derives the internal `CriticalHardColouringInput` through the leaf realization and actual Gibbs-law transport; no custom axiom has been added.

The completed scope is the main-text Potts theorem, its general graph-family transfer and standalone positive-temperature response theorem, and the Holant proof described above. Unimported Appendix sources and other extensions not listed here, including external fields and high-girth zero-free results, are not certified by the default check. The proved girth-preservation lemma for the leaf realization is part of the main-text model construction; it does not by itself establish those high-girth extensions.
