import ZeroFreeness.Coupling.Girth.Spectral.SchurSector
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

/-! Complete conditional Hoeffding decomposition for a finite commuting
family of orthogonal projections. The spaces are the actual simultaneous
0/1 eigenspaces, and the components are their orthogonal projections. -/
namespace ZeroFreeness.Appendix.Girth.Schur
open scoped BigOperators InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]

structure CommutingProjections (I E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Q : I → E →ₗ[ℝ] E
  projection : ∀ i, Projection (Q i)
  commute : ∀ i j, Commute (Q i) (Q j)

namespace CommutingProjections
variable (P : CommutingProjections I E)

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def sector (χ : I → Bool) : Submodule ℝ E :=
  ⨅ i, Module.End.eigenspace (P.Q i) (bitValue (χ i))

theorem symmetric (i : I) : (P.Q i).IsSymmetric := (P.projection i).symmetric

theorem eigenvalue_binary (i : I) {lam : ℝ} {f : E} (hf : f ≠ 0)
    (he : P.Q i f = lam • f) : lam = 0 ∨ lam = 1 := by
  have hh := congrArg (P.Q i) he
  rw [(P.projection i).idem, map_smul, he, ← mul_smul] at hh
  have hz : (lam ^ 2 - lam) • f = 0 := by
    rw [sub_smul, pow_two, hh, sub_self]
  have hz' := (smul_eq_zero.mp hz).resolve_right hf
  have hm : lam * (lam - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hm with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem bitValue_injective : Function.Injective bitValue := by
  intro b c h
  cases b <;> cases c <;> simp_all [bitValue]

theorem sector_orthogonal : OrthogonalFamily ℝ (fun χ : I → Bool => P.sector χ)
    (fun χ => (P.sector χ).subtypeₗᵢ) := by
  have h := LinearMap.IsSymmetric.orthogonalFamily_iInf_eigenspaces P.symmetric
  have hi : Function.Injective (fun χ : I → Bool => fun i => bitValue (χ i)) := by
    intro χ ψ hχ
    funext i
    exact bitValue_injective (congrFun hχ i)
  exact h.comp hi

/-- No completeness of a proposed tensor basis is assumed: the joint
spectral theorem plus idempotence proves that the Boolean sectors span. -/
theorem sectors_span : (⨆ χ : I → Bool, P.sector χ) = ⊤ := by
  have htop := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute P.symmetric
    (fun i j _ => P.commute i j)
  apply top_unique
  rw [← htop]
  apply iSup_le
  intro γ f hf
  by_cases hzero : f = 0
  · rw [hzero]
    exact Submodule.zero_mem _
  let χ : I → Bool := fun i => decide (γ i = 1)
  apply (le_iSup (fun χ : I → Bool => P.sector χ) χ)
  apply (Submodule.mem_iInf _).mpr
  intro i
  have hi := (Submodule.mem_iInf _).mp hf i
  rw [Module.End.mem_eigenspace_iff] at hi ⊢
  have hbinary := P.eigenvalue_binary i hzero hi
  rcases hbinary with hz | ho
  · simpa [χ, bitValue, hz] using hi
  · simpa [χ, bitValue, ho] using hi

def part (χ : I → Bool) : E →ₗ[ℝ] E := (P.sector χ).starProjection.toLinearMap

theorem part_mem (χ : I → Bool) (f : E) : P.part χ f ∈ P.sector χ :=
  (P.sector χ).starProjection_apply_mem f

theorem part_projection (χ : I → Bool) : Projection (P.part χ) where
  symmetric x y := (P.sector χ).inner_starProjection_left_eq_right x y
  idem x := (P.sector χ).starProjection_eq_self_iff.mpr (P.part_mem χ x)

/-- The exact complete orthogonal sum, including degree zero. -/
theorem sum_parts (f : E) : (∑ χ : I → Bool, P.part χ f) = f :=
  P.sector_orthogonal.sum_projection_of_mem_iSup f (by rw [P.sectors_span]; trivial)

theorem sector_action (χ : I → Bool) {f : E} (hf : f ∈ P.sector χ) (i : I) :
    P.Q i f = bitValue (χ i) • f :=
  Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hf i)

theorem part_action (χ : I → Bool) (f : E) (i : I) :
    P.Q i (P.part χ f) = bitValue (χ i) • P.part χ f :=
  P.sector_action χ (P.part_mem χ f) i

theorem parts_inner_zero {χ ψ : I → Bool} (hχ : χ ≠ ψ) (f g : E) :
    ⟪P.part χ f, P.part ψ g⟫_ℝ = 0 :=
  P.sector_orthogonal hχ ⟨P.part χ f, P.part_mem χ f⟩ ⟨P.part ψ g, P.part_mem ψ g⟩

theorem norm_sq_sum_parts (f : E) : ‖f‖ ^ 2 = ∑ χ : I → Bool, ‖P.part χ f‖ ^ 2 := by
  have h := P.sector_orthogonal.norm_sum
    (fun χ => (⟨P.part χ f, P.part_mem χ f⟩ : P.sector χ)) Finset.univ
  change ‖∑ χ : I → Bool, P.part χ f‖ ^ 2 = ∑ χ : I → Bool, ‖P.part χ f‖ ^ 2 at h
  rwa [P.sum_parts] at h

end CommutingProjections
end
end ZeroFreeness.Appendix.Girth.Schur
