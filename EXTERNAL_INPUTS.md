# External input to the main-text Potts proof

The formalization leaves one explicitly identified result as an external input. This boundary is expressed as a theorem parameter, without introducing an `axiom`, using `sorry`, or bypassing the Lean kernel.

## Hard-colouring coupling independence at the critical threshold

Source: [Chen–Feng–Guo–Zhang–Zou, *Deterministic counting from coupling independence*, arXiv:2410.23225v2, Theorem 20](https://arxiv.org/html/2410.23225v2). The theorem's second parameter regime gives a finite Hamming coupling-independence constant depending only on `q, Δ` when `Δ ≥ 3` and `q ≥ (11/6 − ε₀)Δ`. This includes the critical equality needed here. Its proof explicitly permits partial colourings that are not proper and defines the conditional laws through the remaining list-colouring model.

The exact interface is `CI2ZF.Potts.CriticalHardColouringInput`, defined in [`CI2ZF/TransferCouplingInputs.lean`](CI2ZF/TransferCouplingInputs.lean). It asserts the existence of a real constant `cost` such that, for every actual `PinningData (Option O) C` satisfying the degree bound, the two normalized child Gibbs laws corresponding to two root colours obey `W ham ≤ cost` at activity zero. The root is removed from the common configuration space, and constraints involving only pinned vertices are omitted. This is the normalized root-CI formulation used in the paper.

`critical_transfer_coupling_inputs` combines this parameter with the internally proved positive-temperature CI bound. `critical_potts_zero_free` then applies the complete positive-temperature and zero-temperature strong inductions and joins the resulting neighborhoods. `potts_zero_free` uses the external input only in the equality case.

`strict_potts_zero_free` requires neither this input nor any unproved coupling, contraction, stationarity, or complex nonvanishing assumption.

## Meaning of the kernel audit

An explicit mathematical hypothesis does not become an additional Lean axiom. The transitive axiom dependencies of all imported theorems remain limited to `propext`, `Classical.choice`, and `Quot.sound`. Passing the audit rules out hidden proof placeholders; it does not establish the external hard-CI hypothesis itself.
