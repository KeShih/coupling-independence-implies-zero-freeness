# Cited results and their Lean proofs

Six of the ingredients that the written proofs cite from the literature have standalone Lean statements about actual finite Potts models. Each formalized statement is proved in the library. No paper-facing theorem takes one of them as a hypothesis, and none of the proofs introduces an `axiom`, uses `sorry`, or bypasses the Lean kernel. The formalized statements can use adapted hypotheses, parameter ranges, or proof routes; the scope of each is stated below.

## Hard-colouring coupling independence at the critical threshold

Source: [Chen–Feng–Guo–Zhang–Zou, *Deterministic counting from coupling independence*, arXiv:2410.23225v2, Theorem 20](https://arxiv.org/html/2410.23225v2). The theorem's second parameter regime gives a finite Hamming coupling-independence constant depending only on `q, Δ` when `Δ ≥ 3` and `q ≥ (11/6 − ε₀)Δ`. This includes the critical equality, where the main-text proof cites it for the hard endpoint. Its proof explicitly permits partial colourings that are not proper and defines the conditional laws through the remaining list-colouring model.

The Lean proof does not follow the cited one. It extends the Carlson–Vigoda contraction to the two-branch regime `CI2ZF.Appendix.CV.Regime Δ q`, namely `(Δ ≥ 125 ∧ q ≥ 1.809Δ) ∨ (Δ ≥ 6 ∧ q ≥ 11Δ/6)`, in [`CI2ZF/Coupling/CV/Scalar.lean`](../CI2ZF/Coupling/CV/Scalar.lean). On the critical branch the scalar closure holds with the same gap `59/226125`, so the CI constant `ciConstant = 409060125/50858` is unchanged. `CI2ZF.Appendix.CV.option_root_ci_critical` in [`CI2ZF/Coupling/CV/RootCI.lean`](../CI2ZF/Coupling/CV/RootCI.lean) bounds the Hamming transport between the actual normalized root-child laws for `Δ ≥ 6`, `q ≥ 11Δ/6` and every activity in `[0,1]`. `CriticalLineArithmetic` proves that the integer equality `6q = 11Δ` forces Δ to be a positive multiple of six, so `Δ ≥ 6` covers every critical case.

[`CI2ZF/Potts/Theorems/PottsExternalTheorem.lean`](../CI2ZF/Potts/Theorems/PottsExternalTheorem.lean) proves both forms of the input. `critical_hard_colouring_input` gives the internal boundary-count form `CriticalHardColouringInput`, and `critical_line_transfer_coupling_inputs` combines it with the proved positive-temperature bound. `external_critical_hard_colouring_theorem` proves the original-graph form `ExternalCriticalHardColouringTheorem` for `Δ ≥ 6` and `q ≥ 11Δ/6`, through the relabelling lemma `root_W_le_of_option_relabel` in [`GraphClassCoupling.lean`](../CI2ZF/Potts/Geometry/GraphClassCoupling.lean).

`ExternalCriticalHardColouringTheorem`, defined in [`CI2ZF/Potts/Geometry/BoundedGraphClass.lean`](../CI2ZF/Potts/Geometry/BoundedGraphClass.lean), is the statement in the form the paper cites. It asserts that one real constant bounds the Hamming Wasserstein distance between the two normalized child Gibbs laws at activity zero, uniformly over all original finite simple graphs of maximum degree at most Δ, arbitrary partial colourings, free roots, and two root colours. The root is removed from the common configuration space, and constraints involving only pinned vertices are omitted. It is thus stated on original graphs with arbitrary pinning, rather than on an enlarged abstract class of boundary-count data.

The paper's cited route is kept for comparison. The declarations
`ExternalCriticalHardColouringTheorem.to_normalizedInput`,
`GraphClassCoupling`, and the `PinningLeaf*` modules formalize the
boundary-count conversion used by the comparison theorem. Their scope is the
Lean statements linked above; they should not be read as a theorem-by-theorem
reproduction of every construction in the cited proof. The comparison
theorems `critical_potts_zero_free_from_external` and
`potts_zero_free_from_external` retain the original-graph premise, while the
paper-facing entry points instantiate the proved premise
`external_critical_hard_colouring_theorem`.

The paper-facing `potts_main_theorem (q Δ : ℕ)` uses colours `Fin q`, assumes `Δ ≥ 2` and `11 * Δ ≤ 6 * q`, and has no further hypothesis. It specializes `potts_zero_free_of_vigoda_line`, the same statement for an arbitrary finite colour type. `strict_potts_zero_free` and `potts_main_strict` use only the Vigoda coupling. The standalone positive-temperature response theorem and the general CI-to-zero-free transfer are also proved; the latter retains exactly the CI hypotheses of the paper's conditional transfer theorem.

## CLMM Lemma 8.7: the tree influence identity

Source: [Chen–Liu–Mani–Moitra, *Strong spatial mixing for colorings on trees and its algorithmic applications*, arXiv:2304.01954v3](https://arxiv.org/html/2304.01954v3), Lemma 8.7. `CI2ZF.Appendix.Girth.CavityTree.CLMMInfluenceIdentity`, in [`Tree/TotalInfluence.lean`](../CI2ZF/Coupling/Girth/Tree/TotalInfluence.lean), states the exact tree influence–Jacobian factorization used by the `q ≥ Δ+3` large-girth route. `clmmInfluenceIdentity` in [`Tree/InfluenceIdentity.lean`](../CI2ZF/Coupling/Girth/Tree/InfluenceIdentity.lean) proves it from the actual finite-tree Gibbs law. The level influence is a difference of conditional expectations, and the CLMM level response is that difference times the scaled potential diagonal, by induction on the level.

The BBR route uses its own square-root influence–Jacobian identity, proved from actual finite Gibbs conditional expectations and the explicit projection/Jacobian algebra: [`BBR/InfluenceIdentity.lean`](../CI2ZF/Coupling/BBR/InfluenceIdentity.lean) proves `level_influence_factorization` and constructs `influenceIdentity`.

## CLMM Lemma 5.13: sphere decay implies coupling

Source: [CLMM2023, Condition 5.12 and Lemma 5.13](https://arxiv.org/html/2304.01954v3). `CI2ZF.Appendix.CLMM.Lemma513.sphere_to_coupling`, in [`CLMM/SphereCoupling.lean`](../CI2ZF/Coupling/CLMM/SphereCoupling.lean), proves that fixed-ambient sphere decay with error `ε ≤ 1/(8R log Δ)` bounds the Hamming transport between the two actual root-child Potts laws by `2Δ^R`. `CLMM.FixedAmbientSphereDecay` fixes the base graph, measures all spheres in that graph, and then quantifies over every complete further pinning. The Lean proposition uses the positive-activity branch (`x > 0`, `Δ ≥ 3`, `R ≥ 2`) and does not claim the paper's separate zero-temperature colouring endpoint.

The proof is a strong induction on the number of free vertices, tracking the number ℓ of free vertices on the sphere of radius R. If ℓ = 0, the two laws have a common marginal off the ball, so the transport cost is at most the ball size. If ℓ ≥ 1, the proof conditions on the sphere vertex of least total variation, using a maximal coupling. The conditioned laws are smaller instances, one with the same root and one rerooted at that vertex. The induction bound uses `1 + log ℓ` in place of the harmonic numbers of the written proof.

## CLMM Equation (10): the graph sphere estimate

Source: CLMM2023, Equation (10), derived there from Lemmas 5.19 and 5.20. `CI2ZF.Appendix.CLMM.Literature C` has the single field `sphere_estimate`. It derives fixed-ambient sphere decay, with error `2Bρ^K Δ^R + Aρ^R`, from tree total-influence decay (`TreeTID`) and ratio-form relative strong spatial mixing (`TreeRelative`) at the chosen cutting depth. `CI2ZF.Appendix.CLMM.Eq10.sphere_estimate_proof`, in [`CLMM/SphereEstimate.lean`](../CI2ZF/Coupling/CLMM/SphereEstimate.lean), proves it, and `CI2ZF.Appendix.CLMM.literature C` packages it as `CLMM.Literature C`.

The proof formalizes Lemma 5.19 as a finite-sum decomposition over sphere configurations, and Lemma 5.20 turns the ratio bound into a total-variation bound `2ε`. A ball–tree correspondence uses girth for exactly two facts: no edge joins two vertices of the same distance layer, and each vertex has a unique parent. The formalized Equation (10) interface is the relative-SSM estimate beyond the chosen cutting depth `K₀`; it is the form consumed by the transfer proof. `CLMM.eventual_transfer` still takes the bundle as its argument `clmm`, and the public large-girth and BBR theorems pass `CLMM.literature C`.

## BBR Theorem 2.5 and Proposition 2.6(i)

Source: [Bencs–Berrekkal–Regts, *Near optimal bounds for weak and strong spatial mixing for the anti-ferromagnetic Potts model on trees*, Electron. J. Probab. 30 (2025)](https://doi.org/10.1214/25-EJP1327), Theorem 2.5 and Proposition 2.6(i); Theorem 7 and Proposition 8(i) of [arXiv:2310.04338v2](https://arxiv.org/html/2310.04338v2). `CI2ZF.Appendix.BBR.Literature C`, in [`BBR/Certificate.lean`](../CI2ZF/Coupling/BBR/Certificate.lean), states both for the actual cavity messages, with their published hypotheses; the printed degree assumption of Proposition 2.6(i) is unchanged. The application handles separate degree-gap-two cases by its own arithmetic branch; it does not assert an extension of Proposition 2.6(i)'s published theorem statement.

- `theorem_2_5_holds`, in [`BBR/Theorem25.lean`](../CI2ZF/Coupling/BBR/Theorem25.lean), proves the squared-norm contraction of the square-root message recursion as in BBR Section 3: the mean value theorem along the segment `sR + (1−s)R'`, Cauchy–Schwarz, and the pointwise Jacobian bound `differential_contraction`.
- `proposition_2_6_i_holds`, in [`BBR/Proposition26.lean`](../CI2ZF/Coupling/BBR/Proposition26.lean), follows BBR Section 4, but replaces their Lemma 4.1 (smoothing) and Lemma 4.2(i) by two uses of the concavity of `log`: a chord bound and Jensen's inequality in AM–GM form. Lemma 4.3 is proved by a derivative argument.

`CI2ZF.Appendix.BBR.literature C` bundles the two proofs. The internal BBR lemmas still take `(bbr : Literature C)`; the public theorems `BBR.high_girth_coupling`, `BBR.high_girth_zero_free`, `BBR.high_girth_original_zero_free_and_responses` and `BBR.high_girth_residual_original_zero_free` pass `BBR.literature C` and take no literature parameter. The interval-wide contraction, tree influence and relative spatial decay, and uniform positive-temperature zero-free transfer are derived from these results.

## Where the cited results are used

The [Appendix status document](appendix/STATUS.md) records the exact
hypotheses of every region. Edge-Potts, general-graph high temperature,
and Carlson–Vigoda use none of the cited results. Near-Vigoda uses the
critical-line bound only at its twenty exceptional integer pairs
`(Δ,q) = (6j,11j)`, `1 ≤ j ≤ 20`. The `q ≥ Δ+3` large-girth route uses
CLMM Lemmas 8.7 and 5.13 and Equation (10). The BBR route uses both BBR
results with CLMM Lemma 5.13 and Equation (10). The girth-five route uses
CLMM Lemma 5.13; its spectral gap, insertion estimates, Doob conditioning,
finite response induction, weighted-source bound, endpoints, and complex
zero-free conclusions are proved directly.

`CI2ZF.LeeYang.uniform_curve_transfer` proves the complete
hard-colouring-CI-to-field induction. Uniform field directions, actual
separator identities, exterior analytic logarithms and the multivariable
polydisc conversion are discharged in Lean. The CV vertex-field and
`q ≥ 3Δ` edge-field endpoints use no cited result. Near-Vigoda uses the
critical-line bound at the same twenty integer pairs, and the `q ≥ Δ+3`
high-girth endpoint uses the proved Appendix CI theorem. None of these
endpoints takes a literature parameter, and no full-range CFFGZZ CI, CWZZ
edge CI or Lee–Yang transfer premise is introduced. See the
[Lee–Yang proof map](lee-yang.md).

## Meaning of the kernel audit

The transitive axiom dependencies of all imported theorems are limited to `propext`, `Classical.choice`, and `Quot.sound`. Passing the audit rules out hidden proof placeholders and added axioms. The audit does not inspect a theorem's explicit premises, which are part of its statement. With these six formalized ingredients proved, the premises of the paper-facing theorems are their parameter conditions, together with the coupling assumptions of the conditional transfer theorems.

The regional conclusions do not assert that every auxiliary lemma or
generalization in the paper has been formalized at its original scope.
The general pairwise-family transfer is implemented for positive-activity
Potts systems, and the edge-Potts proof uses finite slot approximations
instead of a standalone countable exact-slot representation theorem.
See the [Appendix scope limits](appendix/STATUS.md#scope-of-the-coverage).
