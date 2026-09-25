# Potts appendix: module guide

[Regions.lean](../../ZeroFreeness/Potts/Regions.lean) imports all seven regions below. See [theorem status and cited results](STATUS.md) for precise hypotheses and proof boundaries, and the [documentation index](../README.md) for the rest of the library.

| Region | Main entry point |
| --- | --- |
| Near-Vigoda | [NearVigoda/Theorem.lean](../../ZeroFreeness/Potts/Regions/NearVigoda/Theorem.lean) |
| Carlson–Vigoda, q ≥ 1.809Δ | [CV/ZeroFree.lean](../../ZeroFreeness/Potts/Regions/CV/ZeroFree.lean), with [CV.lean](../../ZeroFreeness/Potts/Regions/CV.lean) as the aggregate import |
| Edge-Potts | [Edge/ZeroFree.lean](../../ZeroFreeness/Potts/Regions/Edge/ZeroFree.lean) |
| Large girth, q ≥ Δ+3 | [Girth/High/Theorem.lean](../../ZeroFreeness/Potts/Regions/Girth/High/Theorem.lean) |
| High temperature | [HighTemperature/ZeroFree.lean](../../ZeroFreeness/Potts/Regions/HighTemperature/ZeroFree.lean) |
| BBR large-girth interval | [BBR/High.lean](../../ZeroFreeness/Potts/Regions/BBR/High.lean) |
| Girth five, q ≥ (1+δ)Δ | [Girth/Five/ZeroFree.lean](../../ZeroFreeness/Potts/Regions/Girth/Five/ZeroFree.lean) |

[Girth/Transfer/ResidualOriginal.lean](../../ZeroFreeness/Potts/Regions/Girth/Transfer/ResidualOriginal.lean) collects the original-graph conclusions for the three girth regions. They allow arbitrary pinning and require the girth condition only on the free residual graph. The girth-five and q ≥ Δ+3 results identify every forced zero of the full polynomial and its exact multiplicity. The BBR result proves that both normalized and full partition functions are nonzero in a positive-temperature neighbourhood excluding zero.

## Reading the girth-five proof

1. **Spectral gap.** [Five/Poincare.lean](../../ZeroFreeness/Coupling/Girth/Five/Poincare.lean) and [Five/ClosedPoincare.lean](../../ZeroFreeness/Coupling/Girth/Five/ClosedPoincare.lean) assemble the concrete heat-bath, star, and Schur-complement proofs in `ZeroFreeness/Coupling/Girth/Spectral/`.
2. **Insertion estimates.** [Covariance/Insertion/ActualEstimates.lean](../../ZeroFreeness/Coupling/Girth/Covariance/Insertion/ActualEstimates.lean) connects the actual insertion laws to the proved spectral gap.
3. **Successive conditioning.** [Covariance/Doob/PinningVertex.lean](../../ZeroFreeness/Coupling/Girth/Covariance/Doob/PinningVertex.lean) and [Doob/ResponseBounds.lean](../../ZeroFreeness/Coupling/Girth/Covariance/Doob/ResponseBounds.lean) retain the complete additive source under further pinnings.
4. **Response induction.** [Covariance/Response/Induction.lean](../../ZeroFreeness/Coupling/Girth/Covariance/Response/Induction.lean) yields the uniform weighted-source theorem in [Five/Response.lean](../../ZeroFreeness/Coupling/Girth/Five/Response.lean).
5. **Sphere decay and coupling.** [CLMM/Ambient.lean](../../ZeroFreeness/Coupling/CLMM/Ambient.lean) fixes one ambient graph for all spheres. [CLMM/SphereCoupling.lean](../../ZeroFreeness/Coupling/CLMM/SphereCoupling.lean) proves CLMM Lemma 5.13, the bound `2Δ^R` from sphere decay, by strong induction on the number of free vertices. [Transfer/SphereCoupling.lean](../../ZeroFreeness/Coupling/Girth/Transfer/SphereCoupling.lean) applies it under all further pinnings and handles the real-parameter endpoints.
6. **Uniform complex neighbourhood.** [Five/Transfer.lean](../../ZeroFreeness/Potts/Regions/Girth/Five/Transfer.lean), [Five/ZeroFree.lean](../../ZeroFreeness/Potts/Regions/Girth/Five/ZeroFree.lean), and [Transfer/ResidualOriginal.lean](../../ZeroFreeness/Potts/Regions/Girth/Transfer/ResidualOriginal.lean) give the zero-free and original-graph statements.

## Proofs of the cited results

The regions use the following cited ingredients. The Lean versions listed
here are proved in the library; their formalized scope and route differences
are recorded in [STATUS.md](STATUS.md):

| Cited result | Used by | Proof |
| --- | --- | --- |
| CFFGZZ Theorem 20 at `q = 11Δ/6` | near-Vigoda, main theorem | [CV/Scalar.lean](../../ZeroFreeness/Coupling/CV/Scalar.lean) extends the CV contraction to `Δ ≥ 6`, `q ≥ 11Δ/6`; [CV/RootCI.lean](../../ZeroFreeness/Coupling/CV/RootCI.lean) gives `option_root_ci_critical` |
| CLMM Lemma 8.7 | large girth | [Tree/InfluenceIdentity.lean](../../ZeroFreeness/Coupling/Girth/Tree/InfluenceIdentity.lean) |
| CLMM Lemma 5.13 | large girth, BBR, girth five | [CLMM/SphereCoupling.lean](../../ZeroFreeness/Coupling/CLMM/SphereCoupling.lean) |
| CLMM Equation (10) | large girth, BBR | [CLMM/SphereEstimate.lean](../../ZeroFreeness/Coupling/CLMM/SphereEstimate.lean) |
| BBR Theorem 2.5 | BBR | [BBR/Theorem25.lean](../../ZeroFreeness/Coupling/BBR/Theorem25.lean) |
| BBR Proposition 2.6(i) | BBR | [BBR/Proposition26.lean](../../ZeroFreeness/Coupling/BBR/Proposition26.lean) |

[STATUS.md](STATUS.md) and the [cited-results record](../external-inputs.md) describe each proof and where it differs from the cited one.

## Companion statements in dedicated modules

Every numbered theorem, lemma, proposition and corollary of the companion
has a Lean counterpart; the [coverage table](../coverage.json) lists all 75
numbered statements, definitions and remarks included, with their status
and Lean names. Most of them are proved in the modules of the regional proofs above.
The statements below, and a few unnumbered claims of the text, are stated in
dedicated modules, in the form the companion gives them. Names are relative
to `ZeroFreeness`, except those starting with `PottsCI`.

| Companion statement | Lean | Module |
| --- | --- | --- |
| 2.1 `lem:pinned-leaf-realization` | `Potts.pinned_leaf_realization`, `Potts.pinned_leaf_realization_girth_class` | [Geometry/PinningLeafTransfer.lean](../../ZeroFreeness/Potts/Geometry/PinningLeafTransfer.lean) |
| 2.5 `lem:potts-positive-response` | `Potts.lem_potts_positive_response`, `Potts.uniform_positive_response` | [Theorems/UniformClassConstants.lean](../../ZeroFreeness/Potts/Theorems/UniformClassConstants.lean) |
| 3.3 `cor:critical-line-input`, 4.4 `rem:critical-scope` | `Potts.critical_line_hard_endpoint`, `Potts.critical_line_pairs`, `Potts.hardList_slack_critical`, `Potts.gibbs_zero_uniform` | [Theorems/CriticalScope.lean](../../ZeroFreeness/Potts/Theorems/CriticalScope.lean) |
| 3.4 `lem:soft-stationary`, 3.6 `lem:boundary-sensitivity` | `Potts.lem_soft_stationary`, `Potts.softFlipKernel_cv`, `Potts.softCVKernel_reversible_irreducible`, `Potts.lem_boundary_sensitivity`, `Potts.rootChild_softCV_boundary_W_le` | [Vigoda/SoftFlipKernel.lean](../../ZeroFreeness/Coupling/Vigoda/SoftFlipKernel.lean) |
| 3.5 `lem:coupled-activation-root-local` | `coupled_activation_root_local`, `activationLaw_one` | [Vigoda/CoupledActivation.lean](../../ZeroFreeness/Coupling/Vigoda/CoupledActivation.lean) |
| 3.7 `lem:finite-endpoint-closure` | `PottsCI.finite_endpoint_closure`, `PottsCI.finite_endpoint_closure_dist` | [Model/Real/EndpointClosure.lean](../../ZeroFreeness/Potts/Model/Real/EndpointClosure.lean) |
| text after 4.6 `thm:intro-bbr-interval` | `Appendix.BBR.rounded_interval_subset`, `Appendix.BBR.rounded_interval_three_four_empty` | [BBR/RoundedInterval.lean](../../ZeroFreeness/Coupling/BBR/RoundedInterval.lean) |
| 4.8 `thm:unrestricted-girth5`; main-paper Table A.1 footnote | `Appendix.Girth.girth_five_common_threshold`, `Appendix.Girth.high_girth_common_threshold`, `Appendix.Girth.bbr_common_threshold` | [Girth/CommonThreshold.lean](../../ZeroFreeness/Potts/Regions/Girth/CommonThreshold.lean) |
| 5.2 `def:cv-kernel`, 5.3 `def:cv-metric`, 5.25 `thm:cv-contraction`, 5.26 `lem:cv-child-middle` | `Appendix.CV.cvKernel`, `Appendix.CV.hardMetric`, `Appendix.CV.geometricMetric_tendsto_hardMetric_cv`, `Appendix.CV.cv_contraction`, `Appendix.CV.cv_child_middle_ham` | [CV/ClosedKernel.lean](../../ZeroFreeness/Coupling/CV/ClosedKernel.lean) |
| 5.6 `lem:cv-root-local-structure` | `Appendix.CV.cv_root_local_structure` | [CV/RootLocalStructure.lean](../../ZeroFreeness/Coupling/CV/RootLocalStructure.lean) |
| 5.7 `lem:cv-move-partition` | `Appendix.CV.cv_move_partition` | [CV/MovePartition.lean](../../ZeroFreeness/Coupling/CV/MovePartition.lean) |
| 5.12 `lem:cv-fresh` | `Appendix.CV.cv_fresh` | [CV/FreshGain.lean](../../ZeroFreeness/Coupling/CV/FreshGain.lean) |
| 5.14 `lem:cv-expected` | `Appendix.CV.cv_expected` | [CV/ExpectedLoss.lean](../../ZeroFreeness/Coupling/CV/ExpectedLoss.lean) |
| 5.21 `lem:cv-high` | `Appendix.CV.cv_high_bulk`, `Appendix.CV.cv_high_missing` | [CV/HighColours.lean](../../ZeroFreeness/Coupling/CV/HighColours.lean) |
| 5.23 `lem:cv-assembly` | `Appendix.CV.cv_assembly_1809`, `Appendix.CV.cv_assembly` | [CV/Assembly.lean](../../ZeroFreeness/Coupling/CV/Assembly.lean) |
| 6.10 `lem:hg-eventual-transfer` | `Appendix.Girth.potts_eventual_transfer_uniform`, `Appendix.Girth.potts_eventual_transfer_source`, `Appendix.Girth.potts_eventual_transfer` | [Girth/Transfer/PottsTransfer.lean](../../ZeroFreeness/Potts/Regions/Girth/Transfer/PottsTransfer.lean) |
| text before 6.9 `lem:hg-eventual-relative-ssm` | `Appendix.Girth.no_uniform_distance_one` | [Tree/SingleEdge.lean](../../ZeroFreeness/Coupling/Girth/Tree/SingleEdge.lean) |
| 7.1 `lem:bbr-certificate`; BBR Proposition 2.6(i) at `Δ ≥ q + 2` | `Appendix.BBR.contraction_certificate_of_gap_two`, `Appendix.BBR.proposition_2_6_i_of_gap_two` | [BBR/GapTwo.lean](../../ZeroFreeness/Coupling/BBR/GapTwo.lean) |
| 8.3 `lem:slot-fact`, 8.4 `lem:edge-slot-lift` | `Appendix.Edge.slot_representation`, `Appendix.Edge.lem_edge_slot_lift` | [Edge/Slots/SlotLift.lean](../../ZeroFreeness/Coupling/Edge/Slots/SlotLift.lean) |
| 8.5 `lem:edge-one-label` | `Appendix.Edge.OneLabel.edge_one_label` | [Edge/Slots/OneLabel.lean](../../ZeroFreeness/Coupling/Edge/Slots/OneLabel.lean) |
| 9.1 `lem:girth5-disintegration` | `Appendix.Girth.second_layer_disintegration` | [Covariance/Graph/Disintegration.lean](../../ZeroFreeness/Coupling/Girth/Covariance/Graph/Disintegration.lean) |
| 9.2 `lem:girth5-one-edge` | `Appendix.Girth.girth5_one_edge` | [Covariance/Insertion/OneEdgeOperator.lean](../../ZeroFreeness/Coupling/Girth/Covariance/Insertion/OneEdgeOperator.lean) |
| 9.7 `thm:potts-gap-girth5` | `Appendix.Girth.OperatorGap.potts_gap_girth5` | [Spectral/OperatorGap.lean](../../ZeroFreeness/Coupling/Girth/Spectral/OperatorGap.lean) |

Lemma 6.10 and the `k`-fold clause of Lemma 3.6 are formalized in the
narrowed form the companion now states. What remains unformalized is
citation-level: that CFFGZZ Theorem 20 and Proposition 22 apply in
Remark 4.4, that `Appendix.CV.hardMetric` is literally Eq. (2) of Carlson
and Vigoda (2024), and the literature attributions of Remarks 4.2 and 4.9.
See [STATUS.md](STATUS.md#scope-of-the-coverage).

## Build and audit

From the repository root, run:

```sh
./scripts/check-appendix.sh
```

This builds all seven regions with warnings treated as errors and audits their transitive axiom dependencies. Run `./scripts/check-all.sh` for the whole library, or `./scripts/check.sh` for the main-text proofs. The appendix audit is [audit/Appendix.lean](../../audit/Appendix.lean); recorded scope and source hashes are in [verification record](../verification.json). The [module migration record](../module-moves.tsv) lists renamed source modules.

## Lee–Yang colour fields

The actual hard-colouring CI results also feed the independent-colour-field proof imported by [ZeroFreeness/LeeYang.lean](../../ZeroFreeness/LeeYang.lean). It covers the near-Vigoda, CV, and large-girth q ≥ Δ+3 vertex ranges, together with the q ≥ 3Δ edge-colouring range. See the [Lee–Yang proof guide](../lee-yang.md) for the field model and transfer argument.
