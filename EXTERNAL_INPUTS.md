# External input to the main-text Potts proof

The formalization leaves one explicitly identified result as an external input. This boundary is expressed as a theorem parameter, without introducing an `axiom`, using `sorry`, or bypassing the Lean kernel.

## Hard-colouring coupling independence at the critical threshold

Source: [Chen–Feng–Guo–Zhang–Zou, *Deterministic counting from coupling independence*, arXiv:2410.23225v2, Theorem 20](https://arxiv.org/html/2410.23225v2). The theorem's second parameter regime gives a finite Hamming coupling-independence constant depending only on `q, Δ` when `Δ ≥ 3` and `q ≥ (11/6 − ε₀)Δ`. This includes the critical equality needed here. Its proof explicitly permits partial colourings that are not proper and defines the conditional laws through the remaining list-colouring model.

The final public interface is `CI2ZF.Potts.ExternalCriticalHardColouringTheorem`, defined in [`CI2ZF/BoundedGraphClass.lean`](CI2ZF/BoundedGraphClass.lean). It asserts that one real constant bounds the Hamming Wasserstein distance between the two normalized child Gibbs laws at activity zero, uniformly over all original finite simple graphs of maximum degree at most Δ, arbitrary partial colourings, free roots, and two root colours. The root is removed from the common configuration space, and constraints involving only pinned vertices are omitted. In particular, the external input is stated on original graphs with arbitrary pinning, rather than on an enlarged abstract class of boundary-count data.

[`CI2ZF/PottsExternalTheorem.lean`](CI2ZF/PottsExternalTheorem.lean) proves `ExternalCriticalHardColouringTheorem.to_normalizedInput`, which supplies the internal `CriticalHardColouringInput` from this original-graph premise. `PinningLeafRealization` realizes each occurrence of a boundary colour count by a distinct, genuinely pinned leaf. The free degree becomes the original constraint degree, and each new leaf has degree one, so the maximum-degree bound is preserved. `GraphClassCoupling` proves the exact correspondence of the Gibbs laws and their transport bounds. The boundary-count formulation is therefore derived in Lean, not a second external assumption. `PinningLeafCycles` and `PinningLeafGirth` also prove that this realization preserves cycles and girth.

`critical_potts_zero_free_from_external` combines this premise with the internally proved positive-temperature CI bound, the complete positive-temperature and zero-temperature strong inductions, and neighborhood patching. `potts_zero_free_from_external` uses the premise only in the equality case. The paper-facing `potts_main_theorem (q Δ : ℕ)` uses colors `Fin q`, assumes `11 * Δ ≤ 6 * q`, and requests the external premise only when `6 * q = 11 * Δ`. `CriticalLineArithmetic` proves that integer equality forces Δ to be a positive multiple of six, hence Δ ≥ 6, within the degree regime of the cited external theorem.

`strict_potts_zero_free` and `potts_main_strict` require neither this input nor any unproved coupling, contraction, stationarity, or complex nonvanishing assumption. The standalone positive-temperature response theorem and the general CI-to-zero-free transfer are also proved internally; the latter retains exactly the CI hypotheses of the paper's conditional transfer theorem.

## Meaning of the kernel audit

An explicit mathematical hypothesis does not become an additional Lean axiom. The transitive axiom dependencies of all imported theorems remain limited to `propext`, `Classical.choice`, and `Quot.sound`. Passing the audit rules out hidden proof placeholders; it does not establish the external hard-CI hypothesis itself.
