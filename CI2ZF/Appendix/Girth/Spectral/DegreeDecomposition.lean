import CI2ZF.Appendix.Girth.Spectral.CommutingSpaces

/-! Splitting the positive-degree space around an actual additive
subspace, with all orthogonality and invariance consequences. -/
namespace CI2ZF.Appendix.Girth.Schur
open scoped BigOperators InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]

theorem Symmetric.preserves_orthogonal {T : E →ₗ[ℝ] E} (hT : Symmetric T)
    (A : Submodule ℝ E) (hA : ∀ a ∈ A, T a ∈ A) {f : E} (hf : f ∈ Aᗮ) :
    T f ∈ Aᗮ := by
  intro a ha
  rw [← hT]
  exact hf (T a) (hA a ha)

namespace CommutingProjections
variable (P : CommutingProjections I E)

theorem sector_le_degreeSpace (χ : I → Bool) (S : Set ℕ) (hχ : degree χ ∈ S) :
    P.sector χ ≤ P.degreeSpace S := by
  intro f hf ψ hψ
  rw [P.part_on_sector _ _ hf]
  apply if_neg
  rintro rfl
  exact hψ hχ

theorem degreeSpace_mono {S T : Set ℕ} (h : S ⊆ T) : P.degreeSpace S ≤ P.degreeSpace T := by
  intro f hf χ hχ
  exact hf χ (fun hS => hχ (h hS))

/-- The singleton part splits into the additive range and its actual
orthogonal complement. The higher part is unchanged. -/
theorem additive_singleton_higher_decomposition (A : Submodule ℝ E)
    (hA : A ≤ P.degreeSpace {1}) {f : E} (hf : f ∈ P.degreeSpace (Set.Ici 1)) :
    ∃ a ∈ A, ∃ b ∈ P.degreeSpace {1} ⊓ Aᗮ, ∃ h ∈ P.degreeSpace (Set.Ici 2),
      f = a + (b + h) := by
  obtain ⟨b, hb, h, hh, hsum, _⟩ := P.singleton_higher_decomposition hf
  refine ⟨A.starProjection b, A.starProjection_apply_mem b,
    b - A.starProjection b, ⟨(P.degreeSpace {1}).sub_mem hb (hA (A.starProjection_apply_mem b)),
      A.sub_starProjection_mem_orthogonal b⟩, h, hh, ?_⟩
  rw [hsum]
  abel

theorem additive_singleton_orthogonal (A : Submodule ℝ E) {a b : E}
    (ha : a ∈ A) (hb : b ∈ P.degreeSpace {1} ⊓ Aᗮ) : ⟪a, b⟫_ℝ = 0 := hb.2 a ha

theorem singleton_higher_orthogonal {b h : E}
    (hb : b ∈ P.degreeSpace {1}) (hh : h ∈ P.degreeSpace (Set.Ici 2)) : ⟪b, h⟫_ℝ = 0 := by
  apply P.degreeSpace_orthogonal _ hb hh
  rw [Set.disjoint_left]
  intro n hn hn2
  simp only [Set.mem_singleton_iff, Set.mem_Ici] at hn hn2
  omega

theorem additive_higher_orthogonal (A : Submodule ℝ E) (hA : A ≤ P.degreeSpace {1})
    {a h : E} (ha : a ∈ A) (hh : h ∈ P.degreeSpace (Set.Ici 2)) : ⟪a, h⟫_ℝ = 0 :=
  P.singleton_higher_orthogonal (hA ha) hh

theorem weighted_preserves_singleton_complement (β : I → ℝ) (A : Submodule ℝ E)
    (hW : Symmetric (P.weighted β)) (hA : ∀ a ∈ A, P.weighted β a ∈ A)
    {b : E} (hb : b ∈ P.degreeSpace {1} ⊓ Aᗮ) :
    P.weighted β b ∈ P.degreeSpace {1} ⊓ Aᗮ :=
  ⟨P.weighted_preserves_degrees β {1} b hb.1, hW.preserves_orthogonal A hA hb.2⟩

theorem higher_zero_on_singleton {f : E} (hf : f ∈ P.degreeSpace {1}) : P.higher f = 0 := by
  conv_lhs => rw [← P.sum_parts f]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro χ _
  by_cases hχ : degree χ = 1
  · rw [P.higher_action χ (P.part_mem χ f)]
    simp [hχ]
  · rw [hf χ hχ, map_zero]

end CommutingProjections
end
end CI2ZF.Appendix.Girth.Schur
