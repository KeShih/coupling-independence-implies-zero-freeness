import ZeroFreeness.Potts.Regions.Girth.Five.ZeroFree
import ZeroFreeness.Potts.Regions.Girth.High.Theorem
import ZeroFreeness.Potts.Regions.BBR.High

/-! Paper-facing original-graph conclusions with a girth condition only
on the free residual graph. Pinned vertices may belong to shorter cycles. -/
namespace ZeroFreeness.Appendix
open PottsCI PottsCI.FinDist ZeroFreeness.Potts ZeroFreeness.Potts.Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

namespace Girth

/-- Uniform normalized nonvanishing and exact forced-zero semantics,
assuming girth only after the supplied original-graph pinning. -/
def UniformResidualGirthPottsZeroFree (C : Type v) [Fintype C]
    (Δ g : ℕ) (eps : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C,
    (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth →
    (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
    (∀ z ∈ thickening eps pottsInterval,
      fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
    (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G

omit [Nonempty C] in
theorem uniformResidualGirthPottsZeroFree_of_residual {Δ g : ℕ} {eps : ℝ}
    (heps : 0 < eps)
    (hresidual : ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0) :
    UniformResidualGirthPottsZeroFree.{u,v} C Δ g eps := by
  have hzero : (0 : ℂ) ∈ thickening eps pottsInterval := by
    apply mem_thickening_iff.mpr
    exact ⟨0, ⟨0, by simp, rfl⟩, by simpa using heps⟩
  intro V _ G hd tau hg
  have hn : ∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0 := by
    intro z hz
    have h := hresidual (tau.toPinningData G) hg (tau.degreeBound_of_original G hd) z hz
    rwa [pinningProductPartition_toPinningData] at h
  exact ⟨hn, fun z hz => fullPartition_eq_zero_iff_of_normalized_ne_zero tau G z (hn z hz),
    fullPolynomial_rootMultiplicity_zero_of_normalized_ne_zero tau G (hn 0 hzero)⟩

/-- The unrestricted girth-five theorem for the original pinned polynomial:
only the free residual graph must have girth at least five. -/
theorem girth_five_residual_original_zero_free
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hThreshold : girthFiveCIThreshold δ ≤ Δ)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    ∃ eps > 0, UniformResidualGirthPottsZeroFree.{u,v} C Δ 5 eps := by
  obtain ⟨eps, heps, hn⟩ := girth_five_zero_free hδ hδ1 hThreshold hq
  exact ⟨eps, heps, uniformResidualGirthPottsZeroFree_of_residual heps hn⟩

/-- The q ≥ Δ+3 theorem with the paper's residual-girth hypothesis. -/
theorem high_girth_residual_original_zero_free
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ g : ℕ, 3 ≤ g ∧ ∃ eps > 0, UniformResidualGirthPottsZeroFree.{u,v} C Δ g eps := by
  obtain ⟨g, hg, eps, heps, hn⟩ := high_girth_zero_free Δ hΔ hq
  exact ⟨g, hg, eps, heps, uniformResidualGirthPottsZeroFree_of_residual heps hn⟩

end Girth

namespace BBR

/-- On the BBR interval both original polynomials are nonzero, uniformly
over arbitrary pinnings whose free residual graph has the required girth. -/
theorem high_girth_residual_original_zero_free
    (Δ : ℕ) (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C) :
    ∃ g : ℕ, 3 ≤ g ∧ ∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C,
      (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth →
      ∀ z ∈ thickening eps (Complex.ofReal '' Icc (start (Fintype.card C) Δ) 1),
        normalizedPartition tau G z ≠ 0 ∧ fullPartition tau G z ≠ 0 := by
  obtain ⟨g, hg, r, hrpos, hn⟩ := high_girth_zero_free Δ hq hr
  let x₀ := start (Fintype.card C) Δ
  have hx₀ : 0 < x₀ := (start_mem hq hr).1
  refine ⟨g, hg, min r (x₀ / 2), lt_min hrpos (by positivity), ?_⟩
  intro V _ G hd tau hfree z hz
  obtain ⟨w, ⟨x, hx, rfl⟩, hdist⟩ := mem_thickening_iff.mp hz
  have hzr : z ∈ thickening r (Complex.ofReal '' Icc x₀ 1) :=
    mem_thickening_iff.mpr ⟨x, ⟨x, hx, rfl⟩, hdist.trans_le (min_le_left _ _)⟩
  have hnorm : normalizedPartition tau G z ≠ 0 := by
    have h := hn (tau.toPinningData G) hfree (tau.degreeBound_of_original G hd) z hzr
    rwa [pinningProductPartition_toPinningData] at h
  have hzero : z ≠ 0 := by
    intro hz0
    subst z
    have hxpos : 0 < x := hx₀.trans_le hx.1
    have he : dist (0 : ℂ) (x : ℂ) = x := by
      simp only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    rw [he] at hdist
    have hh := hdist.trans_le (min_le_right r (x₀ / 2))
    linarith [hx.1]
  exact ⟨hnorm, fullPartition_ne_zero_of_normalized tau G hzero hnorm⟩

end BBR
end
end ZeroFreeness.Appendix
