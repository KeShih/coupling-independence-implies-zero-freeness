import CI2ZF.Appendix.Girth.Transfer.Family
import CI2ZF.Appendix.Girth.Transfer.SphereCoupling
import CI2ZF.Appendix.Girth.Covariance.Response.Constants

/-! Family transfer for the fixed-girth theorem. All real endpoint and
complex-neighbourhood steps use the actual residual Potts family. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts CI2ZF.Potts.Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

theorem girthFiveCIThreshold_degree_three {δ : ℝ} {Δ : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveCIThreshold δ ≤ Δ) : 3 ≤ Δ := by
  obtain ⟨hD, _, _, _, hc, _⟩ := girthFiveThreshold_bounds hδ hδ1 (girthFiveCIThreshold_gap hΔ)
  have hh : 1 ≤ (1 / 8 : ℝ) * (δ * Δ) := (div_le_iff₀ (mul_pos hδ hD)).mp hc
  have hd : (3 : ℝ) ≤ Δ := by nlinarith [mul_le_mul_of_nonneg_right hδ1 hD.le]
  exact_mod_cast hd

theorem girthFiveCIThreshold_colour_slack {δ : ℝ} {Δ q : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hΔ : girthFiveCIThreshold δ ≤ Δ)
    (hq : (1 + δ) * Δ ≤ (q : ℝ)) : Δ + 2 ≤ q := by
  have hd := (girthFiveThreshold_bounds hδ hδ1 (girthFiveCIThreshold_gap hΔ)).2.1
  have hh : (Δ : ℝ) + 2 ≤ q := by nlinarith
  exact_mod_cast hh

theorem large_girth_transfer_inputs_of_weighted_source
    (external : SphereCouplingInput.{u,v} C) (Δ g : ℕ) (hΔ : 3 ≤ Δ)
    (hq : Δ + 1 ≤ Fintype.card C) {χ M : ℝ} (hχ : 1 < χ) (hM : 0 ≤ M)
    (hsource : ∀ (x : ℝ), 0 < x → x ≤ 1 → UniformWeightedSource.{u,v} C Δ g x χ M) :
    (largeGirthFamily.{u,v} C g).TransferCouplingInputs Δ hq := by
  obtain ⟨cost, _, hc⟩ := closed_coupling_from_weighted_source external Δ g hΔ hχ hM hsource
  have hroot : ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ≤ 1 →
      (largeGirthFamily.{u,v} C g).RootCouplingBound Δ hq x cost := by
    intro x hx O _ I hg hd a b
    exact hc x x.property hx I hd hg a b _ _
  constructor
  · exact ⟨cost, hroot PinningData.hardParameter (by norm_num)⟩
  · intro δ _ _
    exact ⟨cost, fun x hx => hroot x hx.2⟩

theorem large_girth_zero_free_of_weighted_source
    (external : SphereCouplingInput.{u,v} C) (Δ g : ℕ) (hΔ : 3 ≤ Δ)
    (hq : Δ + 1 ≤ Fintype.card C) {χ M : ℝ} (hχ : 1 < χ) (hM : 0 ≤ M)
    (hsource : ∀ (x : ℝ), 0 < x → x ≤ 1 → UniformWeightedSource.{u,v} C Δ g x χ M) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0 :=
  (largeGirthFamily.{u,v} C g).uniform_transfer_zero_free Δ hq
    (large_girth_transfer_inputs_of_weighted_source external Δ g hΔ hq hχ hM hsource)

/-- The standard original-graph Potts conclusion restricted to graphs
of the stated girth; the full polynomial keeps exactly its forced zero. -/
def UniformGirthPottsZeroFree (C : Type v) [Fintype C] (Δ g : ℕ) (eps : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    (g : ℕ∞) ≤ G.egirth → (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C,
    (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
    (∀ z ∈ thickening eps pottsInterval,
      fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
    (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G

theorem uniformGirthPottsZeroFree_of_residual {Δ g : ℕ} {eps : ℝ} (heps : 0 < eps)
    (hresidual : ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0) :
    UniformGirthPottsZeroFree.{u,v} C Δ g eps := by
  have hzero : (0 : ℂ) ∈ thickening eps pottsInterval := by
    apply mem_thickening_iff.mpr
    exact ⟨0, ⟨0, by simp, rfl⟩, by simpa using heps⟩
  intro V _ G hg hd tau
  have hfree : (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth :=
    hg.trans (SimpleGraph.Embedding.comap
      (⟨Subtype.val, Subtype.val_injective⟩ : tau.FreeVertex ↪ V) G).isContained.egirth_le
  have hnorm : ∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0 := by
    intro z hz
    have hh := hresidual (tau.toPinningData G) hfree (tau.degreeBound_of_original G hd) z hz
    rwa [pinningProductPartition_toPinningData] at hh
  exact ⟨hnorm, fun z hz => fullPartition_eq_zero_iff_of_normalized_ne_zero tau G z (hnorm z hz),
    fullPolynomial_rootMultiplicity_zero_of_normalized_ne_zero tau G (hnorm 0 hzero)⟩

theorem large_girth_original_zero_free_of_weighted_source
    (external : SphereCouplingInput.{u,v} C) (Δ g : ℕ) (hΔ : 3 ≤ Δ)
    (hq : Δ + 1 ≤ Fintype.card C) {χ M : ℝ} (hχ : 1 < χ) (hM : 0 ≤ M)
    (hsource : ∀ (x : ℝ), 0 < x → x ≤ 1 → UniformWeightedSource.{u,v} C Δ g x χ M) :
    ∃ eps > 0, UniformGirthPottsZeroFree.{u,v} C Δ g eps := by
  obtain ⟨eps, heps, hnz⟩ := large_girth_zero_free_of_weighted_source external Δ g hΔ hq hχ hM hsource
  exact ⟨eps, heps, uniformGirthPottsZeroFree_of_residual heps hnz⟩

end
end CI2ZF.Appendix.Girth
