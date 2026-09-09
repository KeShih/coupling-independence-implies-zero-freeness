# Potts appendix: module guide

[Regions.lean](../../CI2ZF/Potts/Regions.lean) imports all seven regions below. See [theorem status and external inputs](STATUS.md) for precise hypotheses and proof boundaries, and the [documentation index](../README.md) for the rest of the library.

| Region | Main entry point |
| --- | --- |
| Near-Vigoda | [NearVigoda/Theorem.lean](../../CI2ZF/Potts/Regions/NearVigoda/Theorem.lean) |
| Carlson–Vigoda, q ≥ 1.809Δ | [CV/ZeroFree.lean](../../CI2ZF/Potts/Regions/CV/ZeroFree.lean), with [CV.lean](../../CI2ZF/Potts/Regions/CV.lean) as the aggregate import |
| Edge-Potts | [Edge/ZeroFree.lean](../../CI2ZF/Potts/Regions/Edge/ZeroFree.lean) |
| Large girth, q ≥ Δ+3 | [Girth/High/Theorem.lean](../../CI2ZF/Potts/Regions/Girth/High/Theorem.lean) |
| High temperature | [HighTemperature/ZeroFree.lean](../../CI2ZF/Potts/Regions/HighTemperature/ZeroFree.lean) |
| BBR large-girth interval | [BBR/High.lean](../../CI2ZF/Potts/Regions/BBR/High.lean) |
| Girth five, q ≥ (1+δ)Δ | [Girth/Five/ZeroFree.lean](../../CI2ZF/Potts/Regions/Girth/Five/ZeroFree.lean) |

[Girth/Transfer/ResidualOriginal.lean](../../CI2ZF/Potts/Regions/Girth/Transfer/ResidualOriginal.lean) collects the original-graph conclusions for the three girth regions. They allow arbitrary pinning and require the girth condition only on the free residual graph. The girth-five and q ≥ Δ+3 results identify every forced zero of the full polynomial and its exact multiplicity. The BBR result proves that both normalized and full partition functions are nonzero in a positive-temperature neighbourhood excluding zero.

## Reading the girth-five proof

1. **Spectral gap.** [Five/Poincare.lean](../../CI2ZF/Coupling/Girth/Five/Poincare.lean) and [Five/ClosedPoincare.lean](../../CI2ZF/Coupling/Girth/Five/ClosedPoincare.lean) assemble the concrete heat-bath, star, and Schur-complement proofs in `CI2ZF/Coupling/Girth/Spectral/`.
2. **Insertion estimates.** [Covariance/Insertion/ActualEstimates.lean](../../CI2ZF/Coupling/Girth/Covariance/Insertion/ActualEstimates.lean) connects the actual insertion laws to the proved spectral gap.
3. **Successive conditioning.** [Covariance/Doob/PinningVertex.lean](../../CI2ZF/Coupling/Girth/Covariance/Doob/PinningVertex.lean) and [Doob/ResponseBounds.lean](../../CI2ZF/Coupling/Girth/Covariance/Doob/ResponseBounds.lean) retain the complete additive source under further pinnings.
4. **Response induction.** [Covariance/Response/Induction.lean](../../CI2ZF/Coupling/Girth/Covariance/Response/Induction.lean) yields the uniform weighted-source theorem in [Five/Response.lean](../../CI2ZF/Coupling/Girth/Five/Response.lean).
5. **Sphere decay and coupling.** [CLMM/Ambient.lean](../../CI2ZF/Coupling/CLMM/Ambient.lean) fixes one ambient graph for all spheres. [Transfer/SphereCoupling.lean](../../CI2ZF/Coupling/Girth/Transfer/SphereCoupling.lean) applies CLMM Lemma 5.13 under all further pinnings and handles the real-parameter endpoints.
6. **Uniform complex neighbourhood.** [Five/Transfer.lean](../../CI2ZF/Potts/Regions/Girth/Five/Transfer.lean), [Five/ZeroFree.lean](../../CI2ZF/Potts/Regions/Girth/Five/ZeroFree.lean), and [Transfer/ResidualOriginal.lean](../../CI2ZF/Potts/Regions/Girth/Transfer/ResidualOriginal.lean) give the zero-free and original-graph statements.

## Build and audit

From the repository root, run:

```sh
./scripts/check-appendix.sh
```

This builds all seven regions with warnings treated as errors and audits their transitive axiom dependencies. Run `./scripts/check-all.sh` for the whole library, or `./scripts/check.sh` for the main-text proofs. The appendix audit is [audit/Appendix.lean](../../audit/Appendix.lean); recorded scope and source hashes are in [verification record](../verification.json). The [module migration record](../module-moves.tsv) lists renamed source modules.

## Lee–Yang colour fields

The actual hard-colouring CI results also feed the independent-colour-field proof imported by [CI2ZF/LeeYang.lean](../../CI2ZF/LeeYang.lean). It covers the near-Vigoda, CV, and large-girth q ≥ Δ+3 vertex ranges, together with the q ≥ 3Δ edge-colouring range. See the [Lee–Yang proof guide](../lee-yang.md) for the field model and transfer argument.
