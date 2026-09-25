import ZeroFreeness.Holant.CoefficientBounds
import ZeroFreeness.Holant.Separator
import ZeroFreeness.Holant.PolynomialStability

/-!
# Bounded local polynomials in the Holant separator expansion

The inside coefficient is exactly the sum of ordinary Holant monomials
whose shell restriction equals the chosen shell assignment.  Consequently
its coefficients satisfy the same finite-family bound as the original
polynomial.  This supplies the uniform local perturbation constant without
an assumed enumeration of graph isomorphism classes.
-/
namespace ZeroFreeness.Holant
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E R : Type*} [Fintype V] [DecidableEq E]

/-- On every interior subset the removed exterior constants reproduce
exactly the original signature coefficient at the union with the shell. -/
theorem interior_signatureWeight_eq [Field R] (inc : E → V → Prop)
    (I O ξ A : Finset E) (f : V → ℕ → R) (hsep : EdgeSeparated inc I O)
    (hA : A ⊆ I) (hd : Disjoint ξ A) :
    signatureWeight inc (interiorSignature inc O ξ f) A =
      signatureWeight inc f (ξ ∪ A) := by
  unfold signatureWeight
  apply prod_congr rfl
  intro v _
  rw [selectedDegree_union inc ξ A hd]
  unfold interiorSignature
  split_ifs with hv
  · rw [inside_degree_zero inc I O A hsep hA v hv, add_zero]
  · rfl

/-- `D_ξ` is a sum of actual original monomials, with the shell held fixed. -/
theorem separatorCoefficient_eq_sum_weights [Field R] (inc : E → V → Prop)
    (I O ξ : Finset E) (f : V → ℕ → R) (z : E → R)
    (hsep : EdgeSeparated inc I O) (hd : Disjoint ξ I) :
    separatorCoefficient inc I O ξ f z =
      ∑ A ∈ I.powerset, weight inc f z (ξ ∪ A) := by
  unfold separatorCoefficient partition
  rw [mul_sum]
  apply sum_congr rfl
  intro A hA
  have hsub := mem_powerset.mp hA
  have hd' := hd.mono_right hsub
  unfold weight
  rw [interior_signatureWeight_eq inc I O ξ A f hsep hsub hd', prod_union hd']
  ring

/-- Ordinary coefficients retained only for subsets with a prescribed shell. -/
def shellCoefficient (inc : E → V → Prop) (S ξ : Finset E)
    (f : V → ℕ → ℂ) (T : Finset E) : ℂ :=
  if T ∩ S = ξ then signatureWeight inc f T else 0

private theorem union_inter_shell (S I ξ A : Finset E) (hSI : Disjoint S I)
    (hξ : ξ ⊆ S) (hA : A ⊆ I) : (ξ ∪ A) ∩ S = ξ := by
  ext e
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨he | he, heS⟩
    · exact he
    · exact (disjoint_left.mp hSI heS (hA he)).elim
  · intro he
    exact ⟨Or.inl he, hξ he⟩

/-- The coefficient is an actual multilinear polynomial on the local
inside-plus-shell edge set. -/
theorem separatorCoefficient_eq_multilinear (inc : E → V → Prop)
    (I S O ξ : Finset E) (f : V → ℕ → ℂ) (z : E → ℂ)
    (hsep : EdgeSeparated inc I O) (hSI : Disjoint S I) (hξ : ξ ⊆ S) :
    separatorCoefficient inc I O ξ f z =
      multilinear (S ∪ I) (shellCoefficient inc S ξ f) z := by
  rw [separatorCoefficient_eq_sum_weights inc I O ξ f z hsep (hSI.mono_left hξ)]
  unfold multilinear
  rw [sum_powerset_union S I hSI]
  symm
  rw [sum_eq_single ξ]
  · apply sum_congr rfl
    intro A hA
    simp only [shellCoefficient, union_inter_shell S I ξ A hSI hξ (mem_powerset.mp hA),
      if_true, weight]
  · intro η hη hne
    apply sum_eq_zero
    intro A hA
    simp only [shellCoefficient,
      union_inter_shell S I η A hSI (mem_powerset.mp hη) (mem_powerset.mp hA),
      if_neg hne, zero_mul]
  · intro hnot
    exact (hnot (mem_powerset.mpr hξ)).elim

/-- Complex signature coefficients are casts of their nonnegative real values. -/
theorem signatureWeight_complex_norm (inc : E → V → Prop)
    (g : V → Signature) (T : Finset E) :
    ‖signatureWeight inc (fun v k => ((g v).value k : ℂ)) T‖ =
      signatureWeight inc (fun v => (g v).value) T := by
  have heq : signatureWeight inc (fun v k => ((g v).value k : ℂ)) T =
      ((signatureWeight inc (fun v => (g v).value) T : ℝ) : ℂ) := by
    simp [signatureWeight, Complex.ofReal_prod]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact prod_nonneg (fun v _ => (g v).nonneg _)

/-- Uniform bounds for each actual local shell coefficient. -/
theorem shellCoefficient_norm_le (F : Finset Signature) (inc : E → V → Prop)
    (g : V → Signature) (hg : ∀ v, g v ∈ residualFamily F)
    (S I ξ T : Finset E) (hT : T ⊆ S ∪ I)
    (htwo : ∀ e ∈ S ∪ I, (univ.filter fun v => inc e v).card = 2)
    {N : ℕ} (hN : (S ∪ I).card ≤ N) :
    ‖shellCoefficient inc S ξ (fun v k => ((g v).value k : ℂ)) T‖ ≤
      residualGrowthBound F ^ (2 * N) := by
  unfold shellCoefficient
  split_ifs
  · rw [signatureWeight_complex_norm]
    exact signatureWeight_le_growthBound_of_card F inc g hg T
      (fun e he => htwo e (hT he)) ((card_le_card hT).trans hN)
  · simp only [norm_zero]
    exact pow_nonneg (residualGrowthBound_nonneg F) _

/-- This is the graph-independent additive perturbation bound for `D_ξ`.
Only the local edge count, residual family and activity box enter K. -/
theorem separatorCoefficient_lipschitz (F : Finset Signature) (inc : E → V → Prop)
    (g : V → Signature) (hg : ∀ v, g v ∈ residualFamily F)
    (I S O ξ : Finset E) (hsep : EdgeSeparated inc I O)
    (hSI : Disjoint S I) (hξ : ξ ⊆ S)
    (htwo : ∀ e ∈ S ∪ I, (univ.filter fun v => inc e v).card = 2)
    (z w : E → ℂ) {N : ℕ} {M δ : ℝ} (hN : (S ∪ I).card ≤ N)
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hz : ∀ e ∈ S ∪ I, ‖z e‖ ≤ M) (hw : ∀ e ∈ S ∪ I, ‖w e‖ ≤ M)
    (hd : ∀ e ∈ S ∪ I, ‖z e - w e‖ ≤ δ) :
    ‖separatorCoefficient inc I O ξ (fun v k => ((g v).value k : ℂ)) z -
      separatorCoefficient inc I O ξ (fun v k => ((g v).value k : ℂ)) w‖ ≤
      polynomialLipschitzConstant N (residualGrowthBound F ^ (2 * N)) M * δ := by
  rw [separatorCoefficient_eq_multilinear inc I S O ξ _ z hsep hSI hξ,
    separatorCoefficient_eq_multilinear inc I S O ξ _ w hsep hSI hξ]
  exact multilinear_lipschitz (S ∪ I) _ z w hN
    (pow_nonneg (residualGrowthBound_nonneg F) _) hM hδ
    (fun T hT => shellCoefficient_norm_le F inc g hg S I ξ T hT htwo hN) hz hw hd

end
end ZeroFreeness.Holant
