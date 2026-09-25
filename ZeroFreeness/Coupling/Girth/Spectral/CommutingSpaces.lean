import ZeroFreeness.Coupling.Girth.Spectral.CommutingBounds

/-! Degree subspaces and their actual orthogonal projectors. These turn
the complete Boolean-sector decomposition into the degree-zero,
singleton and higher blocks used by the star argument. -/
namespace ZeroFreeness.Appendix.Girth.Schur
open scoped BigOperators InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]

namespace CommutingProjections
variable (P : CommutingProjections I E)

def degreeSpace (S : Set ℕ) : Submodule ℝ E where
  carrier := {f | ∀ χ, degree χ ∉ S → P.part χ f = 0}
  zero_mem' := by intro χ _; exact map_zero _
  add_mem' := by
    intro f g hf hg χ hχ
    rw [map_add, hf χ hχ, hg χ hχ, zero_add]
  smul_mem' := by
    intro a f hf χ hχ
    rw [map_smul, hf χ hχ, smul_zero]

def selectDegrees (S : Set ℕ) : E →ₗ[ℝ] E :=
  ∑ χ : I → Bool, if degree χ ∈ S then P.part χ else 0

theorem selectDegrees_apply (S : Set ℕ) (f : E) :
    P.selectDegrees S f = ∑ χ : I → Bool, if degree χ ∈ S then P.part χ f else 0 := by
  simp only [selectDegrees, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro χ _
  split_ifs <;> rfl

theorem part_selectDegrees (S : Set ℕ) (χ : I → Bool) (f : E) :
    P.part χ (P.selectDegrees S f) = if degree χ ∈ S then P.part χ f else 0 := by
  rw [P.selectDegrees_apply, map_sum]
  have he (ψ : I → Bool) : P.part χ (if degree ψ ∈ S then P.part ψ f else 0) =
      if χ = ψ then (if degree ψ ∈ S then P.part ψ f else 0) else 0 := by
    by_cases hψ : degree ψ ∈ S
    · rw [if_pos hψ, P.part_on_sector _ _ (P.part_mem ψ f)]
    · simp only [if_neg hψ, map_zero, ite_self]
  simp_rw [he]
  simp

theorem selectDegrees_mem (S : Set ℕ) (f : E) : P.selectDegrees S f ∈ P.degreeSpace S := by
  intro χ hχ
  rw [P.part_selectDegrees, if_neg hχ]

theorem selectDegrees_eq_self (S : Set ℕ) {f : E} (hf : f ∈ P.degreeSpace S) :
    P.selectDegrees S f = f := by
  rw [P.selectDegrees_apply]
  calc
    _ = ∑ χ : I → Bool, P.part χ f := by
      apply Finset.sum_congr rfl
      intro χ _
      by_cases hχ : degree χ ∈ S
      · exact if_pos hχ
      · rw [if_neg hχ, hf χ hχ]
    _ = f := P.sum_parts f

theorem selectDegrees_symmetric (S : Set ℕ) : Symmetric (P.selectDegrees S) := by
  intro f g
  rw [P.selectDegrees_apply, P.selectDegrees_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro χ _
  by_cases hχ : degree χ ∈ S
  · simp only [if_pos hχ]
    exact (P.part_projection χ).symmetric f g
  · simp only [if_neg hχ, inner_zero_left, inner_zero_right]

theorem selectDegrees_projection (S : Set ℕ) : Projection (P.selectDegrees S) :=
  ⟨P.selectDegrees_symmetric S, fun f => P.selectDegrees_eq_self S (P.selectDegrees_mem S f)⟩

theorem selectDegrees_eq_starProjection (S : Set ℕ) (f : E) :
    P.selectDegrees S f = (P.degreeSpace S).starProjection f := by
  apply Eq.symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (P.selectDegrees_mem S f)
  intro g hg
  rw [inner_sub_left, P.selectDegrees_symmetric, P.selectDegrees_eq_self S hg, sub_self]

theorem selectDegrees_add_compl (S : Set ℕ) (f : E) :
    P.selectDegrees S f + P.selectDegrees Sᶜ f = f := by
  rw [P.selectDegrees_apply, P.selectDegrees_apply, ← Finset.sum_add_distrib]
  calc
    _ = ∑ χ : I → Bool, P.part χ f := by
      apply Finset.sum_congr rfl
      intro χ _
      by_cases hχ : degree χ ∈ S <;> simp [hχ]
    _ = f := P.sum_parts f

theorem inner_eq_sum_parts (f g : E) :
    ⟪f, g⟫_ℝ = ∑ χ : I → Bool, ⟪P.part χ f, P.part χ g⟫_ℝ := by
  have h := P.sector_orthogonal.inner_sum
    (fun χ => (⟨P.part χ f, P.part_mem χ f⟩ : P.sector χ))
    (fun χ => (⟨P.part χ g, P.part_mem χ g⟩ : P.sector χ)) Finset.univ
  change ⟪∑ χ : I → Bool, P.part χ f, ∑ χ : I → Bool, P.part χ g⟫_ℝ =
    ∑ χ : I → Bool, ⟪P.part χ f, P.part χ g⟫_ℝ at h
  rwa [P.sum_parts, P.sum_parts] at h

theorem degreeSpace_orthogonal {S T : Set ℕ} (hST : Disjoint S T) {f g : E}
    (hf : f ∈ P.degreeSpace S) (hg : g ∈ P.degreeSpace T) : ⟪f, g⟫_ℝ = 0 := by
  rw [P.inner_eq_sum_parts]
  apply Finset.sum_eq_zero
  intro χ _
  by_cases hχ : degree χ ∈ S
  · have hn : degree χ ∉ T := fun ht => (Set.disjoint_left.mp hST) hχ ht
    rw [hg χ hn, inner_zero_right]
  · rw [hf χ hχ, inner_zero_left]

theorem degreeSpace_compl (S : Set ℕ) : P.degreeSpace Sᶜ = (P.degreeSpace S)ᗮ := by
  apply le_antisymm
  · intro f hf g hg
    exact P.degreeSpace_orthogonal disjoint_compl_right hg hf
  · intro f hf
    have hs : P.selectDegrees S f = 0 := by
      rw [P.selectDegrees_eq_starProjection]
      exact (P.degreeSpace S).starProjection_apply_eq_zero_iff.mpr hf
    have he : P.selectDegrees Sᶜ f = f := by
      have hh := P.selectDegrees_add_compl S f
      rwa [hs, zero_add] at hh
    exact he ▸ P.selectDegrees_mem Sᶜ f

theorem degree_zero_iff (χ : I → Bool) : degree χ = 0 ↔ χ = fun _ => false := by
  constructor
  · intro h
    have hz : active χ = ∅ := Finset.card_eq_zero.mp h
    funext i
    cases hc : χ i
    · rfl
    · have hm : i ∈ active χ := by simp [active, hc]
      rw [hz] at hm
      exact (Finset.notMem_empty i hm).elim
  · rintro rfl
    simp [degree, active]

theorem selectDegrees_zero (f : E) : P.selectDegrees {0} f = P.part (fun _ => false) f := by
  rw [P.selectDegrees_apply]
  simp only [Set.mem_singleton_iff, degree_zero_iff]
  simp

/-- Orthogonality to the common-kernel sector is exactly positive degree. -/
theorem positive_degree_space :
    P.degreeSpace (Set.Ici 1) = (P.sector (fun _ => false))ᗮ := by
  have hset : Set.Ici (1 : ℕ) = ({0} : Set ℕ)ᶜ := by ext n; simp; omega
  rw [hset, P.degreeSpace_compl]
  congr 1
  apply le_antisymm
  · intro f hf
    have he := P.selectDegrees_eq_self {0} hf
    rw [P.selectDegrees_zero] at he
    exact he ▸ P.part_mem (fun _ => false) f
  · intro f hf χ hχ
    rw [P.part_on_sector _ _ hf]
    apply if_neg
    intro h
    subst χ
    exact hχ (by simp [degree, active])

/-- Every positive-degree vector splits orthogonally into its singleton
and higher parts, with both components defined by actual projections. -/
theorem singleton_higher_decomposition {f : E} (hf : f ∈ P.degreeSpace (Set.Ici 1)) :
    ∃ b ∈ P.degreeSpace {1}, ∃ h ∈ P.degreeSpace (Set.Ici 2),
      f = b + h ∧ ⟪b, h⟫_ℝ = 0 := by
  refine ⟨P.selectDegrees {1} f, P.selectDegrees_mem {1} f,
    P.selectDegrees (Set.Ici 2) f, P.selectDegrees_mem (Set.Ici 2) f, ?_, ?_⟩
  · rw [P.selectDegrees_apply, P.selectDegrees_apply, ← Finset.sum_add_distrib]
    calc
      f = ∑ χ : I → Bool, P.part χ f := (P.sum_parts f).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro χ _
        by_cases h1 : degree χ = 1
        · simp [h1]
        · by_cases h2 : 2 ≤ degree χ
          · simp [h1, h2]
          · have hz : degree χ = 0 := by omega
            have hp : P.part χ f = 0 := hf χ (by simp [hz])
            simp [h1, h2, hp]
  · apply P.degreeSpace_orthogonal _ (P.selectDegrees_mem {1} f) (P.selectDegrees_mem (Set.Ici 2) f)
    rw [Set.disjoint_left]
    intro n hn hn2
    simp only [Set.mem_singleton_iff, Set.mem_Ici] at hn hn2
    omega

/-- The Boolean sector supported by exactly one incidence. -/
def singleSignature (i : I) : I → Bool := fun j => decide (j = i)

@[simp] theorem degree_singleSignature (i : I) : degree (singleSignature i) = 1 := by
  have h : active (singleSignature i) = {i} := by
    ext j
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and, singleSignature,
      decide_eq_true_eq, Finset.mem_singleton]
  rw [degree, h, Finset.card_singleton]

theorem singleSignature_injective : Function.Injective (singleSignature (I := I)) := by
  intro i j h
  have hh := congrFun h i
  simpa [singleSignature] using hh

theorem degree_one_iff (χ : I → Bool) : degree χ = 1 ↔ ∃! i, χ = singleSignature i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
    have he : χ = singleSignature i := by
      funext j
      have hm : j ∈ active χ ↔ j = i := by rw [hi]; exact Finset.mem_singleton
      apply Bool.eq_iff_iff.mpr
      simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and, singleSignature,
        decide_eq_true_eq] using hm
    refine ⟨i, he, ?_⟩
    intro j hj
    exact singleSignature_injective (hj.symm.trans he)
  · rintro ⟨i, rfl, _⟩
    exact degree_singleSignature i

/-- The singleton projection is the sum of its incidence sectors. -/
theorem sum_singleSignature (f : E) :
    (∑ i : I, P.part (singleSignature i) f) = P.selectDegrees {1} f := by
  rw [P.selectDegrees_apply]
  simp only [Set.mem_singleton_iff]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ => singleSignature i)
  · intro i _
    simp
  · intro i _ j _ h
    exact singleSignature_injective h
  · intro χ hχ
    have hd : degree χ = 1 := (Finset.mem_filter.mp hχ).2
    obtain ⟨i, hi, _⟩ := (degree_one_iff χ).mp hd
    exact ⟨i, Finset.mem_univ i, hi.symm⟩
  · intro i _
    rfl

theorem sum_singleSignature_eq_self {b : E} (hb : b ∈ P.degreeSpace {1}) :
    (∑ i : I, P.part (singleSignature i) b) = b := by
  rw [P.sum_singleSignature, P.selectDegrees_eq_self {1} hb]

end CommutingProjections
end
end ZeroFreeness.Appendix.Girth.Schur
