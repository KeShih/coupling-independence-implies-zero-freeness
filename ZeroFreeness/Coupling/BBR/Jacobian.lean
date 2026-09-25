import ZeroFreeness.Coupling.BBR.Differential
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The displayed Jacobian blocks are actual derivatives of the
square-root recursion, including its orthogonal-projection factor. -/
namespace ZeroFreeness.Appendix.BBR
open scoped BigOperators
open Finset
noncomputable section
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [Nonempty C]

theorem hasDerivAt_squareMass {y : ℝ → C → ℝ} {z : C → ℝ} {a : ℝ}
    (hy : ∀ c, HasDerivAt (fun t => y t c) (z c) a) :
    HasDerivAt (fun t => squareMass (y t)) (2 * innerSum (y a) z) a := by
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset C)) (fun c _ => (hy c).pow 2)
  apply h.congr_deriv
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, innerSum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem hasDerivAt_localFactor {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {y : ℝ → C → ℝ} {z : C → ℝ} {a : ℝ}
    (hy : ∀ c, HasDerivAt (fun t => y t c) (z c) a) (hS : 0 < squareMass (y a)) (c : C) :
    HasDerivAt (fun t => localFactor x (y t) c)
      ((x - 1) * y a c / (localFactor x (y a) c * squareMass (y a)) * projection (y a) z c) a := by
  have hmass := hasDerivAt_squareMass hy
  have hi := hmass.sub (((hy c).pow 2).const_mul (1 - x))
  have hden := excludedMass_pos hx hx1 (y a) hS c
  have hratio : 0 < excludedMass x (y a) c / squareMass (y a) := div_pos hden hS
  have h := (hi.div hmass hS.ne').sqrt hratio.ne'
  change HasDerivAt (fun t => localFactor x (y t) c)
    (((2 * innerSum (y a) z - (1 - x) * (2 * y a c ^ (2 - 1) * z c)) * squareMass (y a) -
      excludedMass x (y a) c * (2 * innerSum (y a) z)) / squareMass (y a) ^ 2 /
      (2 * localFactor x (y a) c)) a at h
  have hF : 0 < localFactor x (y a) c := Real.sqrt_pos.2 hratio
  apply h.congr_deriv
  unfold projection excludedMass
  simp only [Nat.add_one_sub_one, pow_one]
  field_simp [hS.ne', hF.ne']
  ring

/-- Multiplying a child factor by all the fixed factors at the parent
gives exactly the Jacobian block used in `differential_contraction`. -/
theorem hasDerivAt_weighted_localFactor {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    {y : ℝ → C → ℝ} {z : C → ℝ} {a : ℝ}
    (hy : ∀ c, HasDerivAt (fun t => y t c) (z c) a) (hS : 0 < squareMass (y a))
    (K : ℝ) (c : C) :
    HasDerivAt (fun t => K * localFactor x (y t) c)
      (jacobianBlock x (fun j => K * localFactor x (y a) j) (y a) z c) a := by
  have h := (hasDerivAt_localFactor hx hx1 hy hS c).const_mul K
  have hden := excludedMass_pos hx hx1 (y a) hS c
  have hratio := div_pos hden hS
  have hF : 0 < localFactor x (y a) c := Real.sqrt_pos.2 hratio
  have hFsq : localFactor x (y a) c ^ 2 * squareMass (y a) = excludedMass x (y a) c := by
    unfold localFactor
    rw [Real.sq_sqrt hratio.le]
    field_simp [hS.ne']
  apply h.congr_deriv
  unfold jacobianBlock
  rw [← hFsq]
  field_simp [hF.ne', hS.ne']

end
end ZeroFreeness.Appendix.BBR
