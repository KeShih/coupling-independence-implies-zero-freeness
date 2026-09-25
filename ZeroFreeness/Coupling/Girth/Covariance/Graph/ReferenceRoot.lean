import ZeroFreeness.Coupling.Girth.Covariance.Graph.ResponseRoot
import ZeroFreeness.Coupling.Girth.Covariance.Reference.Marginal

/-! The density comparison between the actual inserted root marginal
and its product reference, obtained from the insertion log quotient. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C]

theorem normalized_log_comparison (a T Q : C → ℝ) (ha : ∀ c, 0 ≤ a c)
    (hT : ∀ c, 0 < T c) (hQ : ∀ c, 0 < Q c) (hZQ : 0 < ∑ c, a c * Q c)
    {E : ℝ} (he : ∀ c, |Real.log (T c / Q c)| ≤ E) (c : C) :
    a c * T c / (∑ b, a b * T b) ≤ Real.exp (2 * E) * (a c * Q c / (∑ b, a b * Q b)) := by
  have hl (b : C) : Real.exp (-E) * Q b ≤ T b := by
    have hh := Real.exp_le_exp.mpr (abs_le.mp (he b)).1
    rw [Real.exp_log (div_pos (hT b) (hQ b))] at hh
    exact (le_div_iff₀ (hQ b)).mp hh
  have hu (b : C) : T b ≤ Real.exp E * Q b := by
    have hh := Real.exp_le_exp.mpr (abs_le.mp (he b)).2
    rw [Real.exp_log (div_pos (hT b) (hQ b))] at hh
    exact (div_le_iff₀ (hQ b)).mp hh
  have hZ : Real.exp (-E) * (∑ b, a b * Q b) ≤ ∑ b, a b * T b := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left (hl b) (ha b)
  have hZ0 := mul_pos (Real.exp_pos (-E)) hZQ
  have hn : a c * T c ≤ Real.exp E * (a c * Q c) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using mul_le_mul_of_nonneg_left (hu c) (ha c)
  calc
    _ ≤ (Real.exp E * (a c * Q c)) / (Real.exp (-E) * (∑ b, a b * Q b)) :=
      div_le_div₀ (mul_nonneg (Real.exp_pos _).le (mul_nonneg (ha c) (hQ c).le)) hn hZ0 hZ
    _ = Real.exp E * Real.exp E * (a c * Q c / (∑ b, a b * Q b)) := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

namespace GraphResponseRoot
variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] [Nonempty C]
variable (I : PinningData (Option V) C) (x : ℝ) (hx : 0 < x)

def unary (c : C) : ℝ := x ^ I.boundaryCount none c
def cavityMarginal (u : Neighbour I) : FinDist C := coordinateMarginal (deletedLaw I x hx) (coordinate I u)
def referenceProduct (c : C) : ℝ := ∏ u, (1 - (1-x) * (cavityMarginal I x hx u).w c)

theorem referenceProduct_pos (c : C) : 0 < referenceProduct I x hx c :=
  Finset.prod_pos fun u _ => deleted_denominator_pos I x hx u c

theorem root_normalization (c : C) :
    (rootLaw I x hx).w c =
      unary I x c * RootInsertion.normalizer (deletedLaw I x hx) (coordinate I) (1-x) c /
        (∑ b, unary I x b * RootInsertion.normalizer (deletedLaw I x hx) (coordinate I) (1-x) b) := by
  have hp : I.partition x = ∑ a, x ^ I.boundaryCount none a * (optionChildData I a).partition x := by
    have hp := option_parent_partition I x
    simpa only [← real_partition_eq_product] using hp
  simp_rw [child_normalizer]
  have he : (∑ b, unary I x b * ((optionChildData I b).partition x / (optionMiddleData I).partition x)) =
      I.partition x / (optionMiddleData I).partition x := by
    rw [hp, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    unfold unary
    ring
  rw [he]
  change x ^ I.boundaryCount none c * (optionChildData I c).partition x / I.partition x = _
  unfold unary
  field_simp [((optionMiddleData I).partition_pos_of_parameter_pos hx).ne']

theorem root_reference_bound {E : ℝ}
    (he : ∀ c, |Real.log (RootInsertion.normalizer (deletedLaw I x hx) (coordinate I) (1-x) c /
      referenceProduct I x hx c)| ≤ E) (c : C) :
    (rootLaw I x hx).w c ≤ Real.exp (2 * E) *
      messageMarginal (unary I x) (fun u c => (1-x) * (cavityMarginal I x hx u).w c) c := by
  rw [root_normalization]
  exact normalized_log_comparison (unary I x)
    (RootInsertion.normalizer (deletedLaw I x hx) (coordinate I) (1-x)) (referenceProduct I x hx)
    (fun c => (pow_pos hx _).le) (normalizer_pos I x hx) (referenceProduct_pos I x hx)
    (Finset.sum_pos (fun c _ => mul_pos (pow_pos hx _) (referenceProduct_pos I x hx c))
      Finset.univ_nonempty) he c

end GraphResponseRoot
end
end ZeroFreeness.Appendix.Girth
