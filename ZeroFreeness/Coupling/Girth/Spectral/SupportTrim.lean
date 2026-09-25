import ZeroFreeness.Coupling.Girth.Spectral.SectorRepresentation

/-! Canonical zero extension outside a cavity support. This preserves
all actual star functions and their conditional means while making the
Bayes cancellation pointwise on the full colour set. -/

namespace ZeroFreeness.Appendix.Girth.ConditionalStar

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem joint_zero_of_cavity_zero (c : C) (σ : D → C) (i : D)
    (h : (S.cavity i).w (σ i) = 0) : S.jointLaw.w (c, σ) = 0 := by
  change S.centreLaw.w c * (∏ j, (S.cavity j).w (σ j) * edgeLikelihood S.s (S.cavity j) c (σ j)) = 0
  have he : (∏ j, (S.cavity j).w (σ j) * edgeLikelihood S.s (S.cavity j) c (σ j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, zero_mul])
  rw [he, mul_zero]

theorem joint_pos_cavity_pos (c : C) (σ : D → C) (i : D)
    (h : 0 < S.jointLaw.w (c, σ)) : 0 < (S.cavity i).w (σ i) := by
  by_contra! hi
  have hz : (S.cavity i).w (σ i) = 0 := le_antisymm hi ((S.cavity i).nonneg _)
  rw [S.joint_zero_of_cavity_zero c σ i hz] at h
  exact (lt_irrefl 0) h

def cavityTrim (i : D) (g : C → C → ℝ) (c t : C) : ℝ :=
  if 0 < (S.cavity i).w t then g c t else 0

theorem cavityTrim_zero (i : D) (g : C → C → ℝ) (c t : C) (ht : (S.cavity i).w t = 0) :
    S.cavityTrim i g c t = 0 := by simp [cavityTrim, ht]

theorem cavityTrim_mean (i : D) (g : C → C → ℝ) (c : C) :
    expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (S.cavityTrim i g c) =
      expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g c) := by
  unfold expectReal
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : 0 < (S.cavity i).w t
  · rw [cavityTrim, if_pos ht]
  · have hz : (S.cavity i).w t = 0 := le_antisymm (le_of_not_gt ht) ((S.cavity i).nonneg t)
    simp only [edgeChannel, hz, zero_mul]

theorem cavityTrim_embed (i : D) (g : C → C → ℝ) :
    supportedEmbed S.jointLaw (fun σ => S.cavityTrim i g σ.1 (σ.2 i)) =
      supportedEmbed S.jointLaw (fun σ => g σ.1 (σ.2 i)) := by
  apply (supportedEmbed_eq_iff S.jointLaw _ _).mpr
  intro σ hσ
  exact if_pos (S.joint_pos_cavity_pos σ.1 σ.2 i hσ)

/-- Actual singleton eigenvectors have representatives centred at every
centre colour and identically zero outside the cavity support. -/
theorem singleton_representation_supported (z : SupportedSpace S.jointLaw) (i : D)
    (hz : (S.leafHeatBath i).operator z = 0)
    (hfixed : ∀ j, j ≠ i → (S.leafHeatBath j).operator z = z) :
    ∃ g : C → C → ℝ,
      (∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c
        (S.edge_positive i c)) (g c) = 0) ∧
      (∀ c t, (S.cavity i).w t = 0 → g c t = 0) ∧
      supportedEmbed S.jointLaw (fun σ => g σ.1 (σ.2 i)) = z := by
  obtain ⟨g, hg, he⟩ := S.singleton_representation z i hz hfixed
  refine ⟨S.cavityTrim i g, ?_, S.cavityTrim_zero i g, ?_⟩
  · intro c
    rw [S.cavityTrim_mean, hg]
  · rw [S.cavityTrim_embed, he]

end
end ZeroFreeness.Appendix.Girth.ConditionalStar
