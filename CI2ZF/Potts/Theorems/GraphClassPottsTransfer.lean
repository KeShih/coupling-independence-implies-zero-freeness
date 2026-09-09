import CI2ZF.Potts.Geometry.GraphClassCoupling
import CI2ZF.Potts.Transfer.FamilyUniformTransfer
import CI2ZF.Potts.Transfer.UniformZeroFreePackaging

/-! The main-text transfer theorem for an arbitrary graph class closed
under induced subgraphs. The CI inputs use original graphs and arbitrary
partial colourings; the proof derives every smaller datum's membership. -/
namespace CI2ZF.Potts
open PottsCI Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem graph_class_potts_transfer (F : GraphClass.{u})
    (C : Type v) [Fintype C] [Nonempty C] (Δ : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C) (hCI : GraphClassTransferInputs F C) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
      (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C,
      (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
      (∀ z ∈ thickening eps pottsInterval,
        fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
      (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G := by
  obtain ⟨eps, heps, hn⟩ :=
    (F.pinningFamily C).uniform_transfer_zero_free Δ hq (hCI.to_pinningFamily hq)
  have hzero : (0 : ℂ) ∈ thickening eps pottsInterval := by
    apply mem_thickening_iff.mpr
    exact ⟨0, ⟨0, by simp, rfl⟩, by simpa using heps⟩
  refine ⟨eps, heps, ?_⟩
  intro V _ G hG hd tau
  have hnorm (z : ℂ) (hz : z ∈ thickening eps pottsInterval) :
      normalizedPartition tau G z ≠ 0 := by
    have h := hn (tau.toPinningData G) (F.original_pinning_mem C G hG tau)
      (tau.degreeBound_of_original G hd) z hz
    rwa [pinningProductPartition_toPinningData] at h
  refine ⟨hnorm, ?_, ?_⟩
  · intro z hz
    exact fullPartition_eq_zero_iff_of_normalized_ne_zero tau G z (hnorm z hz)
  · exact fullPolynomial_rootMultiplicity_zero_of_normalized_ne_zero tau G (hnorm 0 hzero)

/-- With the paper's class-wide degree premise, no degree premise is
left on the individual conclusions. This is `thm:potts-transfer`. -/
theorem graph_class_potts_transfer_of_bounded (F : GraphClass.{u})
    (C : Type v) [Fintype C] [Nonempty C] (Δ : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C)
    (hdegree : ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      F.contains G → ∀ w, G.degree w ≤ Δ)
    (hCI : GraphClassTransferInputs F C) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
      ∀ tau : PartialColouring V C,
      (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
      (∀ z ∈ thickening eps pottsInterval,
        fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
      (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G := by
  obtain ⟨eps, heps, h⟩ := graph_class_potts_transfer F C Δ hq hCI
  exact ⟨eps, heps, fun G hG tau => h G hG (hdegree G hG) tau⟩

end
end CI2ZF.Potts
