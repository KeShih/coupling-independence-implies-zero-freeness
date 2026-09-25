import ZeroFreeness.Coupling.Girth.Spectral.PartialAverage

/-! Actual supported function representations of the degree-zero and
singleton conditional Hoeffding sectors, with legitimate zero extensions
at zero-mass centre colours. -/

namespace ZeroFreeness.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

private theorem exists_positive_atom {Ω : Type*} [Fintype Ω] (μ : FinDist Ω) : ∃ ω, 0 < μ.w ω := by
  by_contra! h
  have hz : ∀ ω, μ.w ω = 0 := fun ω => le_antisymm (h ω) (μ.nonneg ω)
  have hs := μ.sum_one
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

namespace ConditionalStar

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

theorem joint_pos_centre_pos {c : C} {σ : D → C} (h : 0 < S.jointLaw.w (c, σ)) :
    0 < S.centreLaw.w c := by
  change 0 < S.centreLaw.w c * (S.leafChannel c).w σ at h
  by_contra! hc
  have hz : S.centreLaw.w c = 0 := le_antisymm hc (S.centreLaw.nonneg c)
  simp only [hz, zero_mul, lt_self_iff_false] at h

theorem supported_root_eq_zero_iff (h : C → ℝ) :
    supportedEmbed S.jointLaw (fun σ => h σ.1) = 0 ↔
      ∀ c, 0 < S.centreLaw.w c → h c = 0 := by
  rw [← map_zero (supportedEmbed S.jointLaw), supportedEmbed_eq_iff]
  constructor
  · intro he c hc
    obtain ⟨σ, hσ⟩ := exists_positive_atom (S.leafChannel c)
    exact he (c, σ) (mul_pos hc hσ)
  · intro he σ hσ
    exact he σ.1 (S.joint_pos_centre_pos hσ)

theorem singletonAverage_mean (f : C × (D → C) → ℝ) (i : D) (c : C) :
    expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c))
      (S.singletonAverage f i c) = S.rootAverage f c := by
  unfold singletonAverage rootAverage
  rw [expectReal_comm]
  exact productProjection_stationary _ i (fun τ => f (c, τ))

theorem rootAverage_zero_of_leaf_sector (z : SupportedSpace S.jointLaw) (i : D)
    (hz : (S.leafHeatBath i).operator z = 0)
    (hfixed : ∀ j, j ≠ i → (S.leafHeatBath j).operator z = z) :
    ∀ c, 0 < S.centreLaw.w c → S.rootAverage (supportedRepresent S.jointLaw z) c = 0 := by
  have h := congrArg (S.leafHeatBath i).operator
    (S.supported_partial_eq_self {i} z (fun j hj => hfixed j (by simpa using hj)))
  rw [SupportedOperator.intertwine, hz] at h
  change supportedEmbed S.jointLaw (S.leafProjection i
    (S.partialProjection {i} (supportedRepresent S.jointLaw z))) = 0 at h
  rw [S.leafProjection_partial {i} (Finset.mem_singleton_self i), Finset.erase_singleton,
    S.partialProjection_empty] at h
  exact (S.supported_root_eq_zero_iff _).mp h

def singletonRepresentative (z : SupportedSpace S.jointLaw) (i : D) (c t : C) : ℝ :=
  if 0 < S.centreLaw.w c then S.singletonAverage (supportedRepresent S.jointLaw z) i c t else 0

theorem singletonRepresentative_embed (z : SupportedSpace S.jointLaw) (i : D)
    (hfixed : ∀ j, j ≠ i → (S.leafHeatBath j).operator z = z) :
    supportedEmbed S.jointLaw (fun σ => S.singletonRepresentative z i σ.1 (σ.2 i)) = z := by
  calc
    _ = supportedEmbed S.jointLaw (fun σ => S.singletonAverage
        (supportedRepresent S.jointLaw z) i σ.1 (σ.2 i)) := by
      apply (supportedEmbed_eq_iff S.jointLaw _ _).mpr
      intro σ hσ
      exact if_pos (S.joint_pos_centre_pos hσ)
    _ = z := S.supported_singleton_of_fixed z i hfixed

theorem singletonRepresentative_mean (z : SupportedSpace S.jointLaw) (i : D)
    (hz : (S.leafHeatBath i).operator z = 0)
    (hfixed : ∀ j, j ≠ i → (S.leafHeatBath j).operator z = z) (c : C) :
    expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c))
      (S.singletonRepresentative z i c) = 0 := by
  by_cases hc : 0 < S.centreLaw.w c
  · have he : S.singletonRepresentative z i c =
        S.singletonAverage (supportedRepresent S.jointLaw z) i c := by
      funext t
      exact if_pos hc
    rw [he, S.singletonAverage_mean]
    exact S.rootAverage_zero_of_leaf_sector z i hz hfixed c hc
  · have he : S.singletonRepresentative z i c = fun _ => 0 := by
      funext t
      exact if_neg hc
    rw [he]
    exact expectReal_const _ 0

/-- The singleton-sector representation is proved from the actual
joint eigen-equations, including all probability-zero fibres. -/
theorem singleton_representation (z : SupportedSpace S.jointLaw) (i : D)
    (hz : (S.leafHeatBath i).operator z = 0)
    (hfixed : ∀ j, j ≠ i → (S.leafHeatBath j).operator z = z) :
    ∃ g : C → C → ℝ,
      (∀ c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c
        (S.edge_positive i c)) (g c) = 0) ∧
      supportedEmbed S.jointLaw (fun σ => g σ.1 (σ.2 i)) = z :=
  ⟨S.singletonRepresentative z i, S.singletonRepresentative_mean z i hz hfixed,
    S.singletonRepresentative_embed z i hfixed⟩

end ConditionalStar
end
end ZeroFreeness.Appendix.Girth
