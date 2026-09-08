import CI2ZF.HammingResponses
import CI2ZF.HardEndpointLocalError
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Relative additive errors in the hard separator expansion. The error
is the actual finite weighted sum of local polynomial defects. Its bound
uses a hard-feasible anchor, single-coordinate hard-weight comparisons,
and single-coordinate complex response estimates. -/
namespace CI2ZF
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

def hardEndpointError {S : Type*} [Fintype S] (D Dzero : S → ℂ)
    (w : S → ℝ) (h : S → ℂ) (Z : ℝ) : ℂ :=
  (∑ s, (D s - Dzero s) * (w s : ℂ) * Complex.exp (h s)) / (Z : ℂ)

theorem norm_exp_le_reference {S : Type*} (h : S → ℂ) (anchor s : S) {B : ℝ}
    (hh : ‖h s - h anchor‖ ≤ B) :
    ‖Complex.exp (h s)‖ ≤ Real.exp B * ‖Complex.exp (h anchor)‖ := by
  have he : Complex.exp (h s) = Complex.exp (h s - h anchor) * Complex.exp (h anchor) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [he, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hh)

/-- The weighted defect sum is small relative to the anchor exponential.
The parent hard partition dominates the feasible anchor's exterior weight. -/
theorem hardEndpointError_norm_le {S : Type*} [Fintype S]
    (D Dzero : S → ℂ) (w : S → ℝ) (h : S → ℂ) (anchor : S)
    {Z K r T B : ℝ} (hZ : 0 < Z) (hK : 0 ≤ K) (hr : 0 ≤ r) (hT : 0 ≤ T)
    (hw : ∀ s, 0 ≤ w s) (hparent : w anchor ≤ Z)
    (hweight : ∀ s, w s ≤ T * w anchor)
    (hlocal : ∀ s, ‖D s - Dzero s‖ ≤ K * r)
    (hresponse : ∀ s, ‖h s - h anchor‖ ≤ B) :
    ‖hardEndpointError D Dzero w h Z‖ ≤
      Fintype.card S * K * r * T * Real.exp B * ‖Complex.exp (h anchor)‖ := by
  have hterm (s : S) : ‖(D s - Dzero s) * (w s : ℂ) * Complex.exp (h s)‖ ≤
      (K * r) * (T * Z) * (Real.exp B * ‖Complex.exp (h anchor)‖) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw s)]
    have hwZ := (hweight s).trans (mul_le_mul_of_nonneg_left hparent hT)
    exact mul_le_mul
      (mul_le_mul (hlocal s) hwZ (hw s) (mul_nonneg hK hr))
      (norm_exp_le_reference h anchor s (hresponse s)) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hK hr) (mul_nonneg hT hZ.le))
  unfold hardEndpointError
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  calc
    ‖∑ s, (D s - Dzero s) * (w s : ℂ) * Complex.exp (h s)‖ / Z ≤
        (∑ _s : S, (K * r) * (T * Z) * (Real.exp B * ‖Complex.exp (h anchor)‖)) / Z :=
      div_le_div_of_nonneg_right ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun s _ => hterm s))) hZ.le
    _ = Fintype.card S * K * r * T * Real.exp B * ‖Complex.exp (h anchor)‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp

section Configurations
variable {V C P : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype P]

/-- The hard endpoint error bound with all shell ratios and response
differences obtained along true Hamming paths from coordinate estimates. -/
theorem hardEndpointError_norm_le_of_coordinates
    (D Dzero : (V → C) → ℂ) (w : (V → C) → ℝ) (h : (V → C) → ℂ)
    (anchor : V → C) {Z K r H alpha : ℝ}
    (hZ : 0 < Z) (hK : 0 ≤ K) (hr : 0 ≤ r) (hH : 1 ≤ H) (ha : 0 ≤ alpha)
    (hw : ∀ sigma, 0 ≤ w sigma) (hparent : w anchor ≤ Z)
    (hweight : ∀ sigma u c, w (Function.update sigma u c) ≤ H * w sigma)
    (hlocal : ∀ sigma, ‖D sigma - Dzero sigma‖ ≤ K * r)
    (hresponse : ∀ sigma u c, ‖h (Function.update sigma u c) - h sigma‖ ≤ alpha) :
    ‖hardEndpointError D Dzero w h Z‖ ≤
      (Fintype.card C : ℝ) ^ Fintype.card V * K * r * H ^ Fintype.card V *
        Real.exp (alpha * Fintype.card V) * ‖Complex.exp (h anchor)‖ := by
  have he := hardEndpointError_norm_le D Dzero w h anchor hZ hK hr
    (pow_nonneg (le_trans zero_le_one hH) _) hw hparent
    (fun sigma => le_pow_card_mul_of_coordinates w hH hw hweight sigma anchor) hlocal
    (fun sigma => norm_sub_le_card_of_coordinates h ha hresponse sigma anchor)
  simpa only [Fintype.card_fun, Nat.cast_pow] using he

/-- Every local defect is a genuine difference of finite monomial sums.
In particular the estimate includes hard-infeasible inside configurations. -/
theorem monomial_hardEndpointError_norm_le_of_coordinates
    (m : (V → C) → P → ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (w : (V → C) → ℝ) (h : (V → C) → ℂ) (anchor : V → C)
    {Z H alpha : ℝ} (hZ : 0 < Z) (hH : 1 ≤ H) (ha : 0 ≤ alpha)
    (hw : ∀ sigma, 0 ≤ w sigma) (hparent : w anchor ≤ Z)
    (hweight : ∀ sigma u c, w (Function.update sigma u c) ≤ H * w sigma)
    (hresponse : ∀ sigma u c, ‖h (Function.update sigma u c) - h sigma‖ ≤ alpha) :
    ‖hardEndpointError (fun sigma => ∑ p, z ^ m sigma p)
        (fun sigma => ∑ p, (0 : ℂ) ^ m sigma p) w h Z‖ ≤
      (Fintype.card C : ℝ) ^ Fintype.card V * Fintype.card P * ‖z‖ *
        H ^ Fintype.card V * Real.exp (alpha * Fintype.card V) *
          ‖Complex.exp (h anchor)‖ := by
  apply hardEndpointError_norm_le_of_coordinates _ _ w h anchor hZ
    (Nat.cast_nonneg _) (norm_nonneg z) hH ha hw hparent hweight
    (fun sigma => sum_monomials_error_zero (m sigma) z hz) hresponse

/-- Bounded inside and shell cardinalities give the paper's uniform
q^(N+s) H^s exponential coefficient, directly for the finite defect sum. -/
theorem bounded_monomial_hardEndpointError_norm_le [Nonempty C]
    (m : (V → C) → P → ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (w : (V → C) → ℝ) (h : (V → C) → ℂ) (anchor : V → C)
    {Z H alpha : ℝ} {N s : ℕ} (hZ : 0 < Z) (hH : 1 ≤ H) (ha : 0 ≤ alpha)
    (hinside : Fintype.card P ≤ (Fintype.card C) ^ N) (hshell : Fintype.card V ≤ s)
    (hw : ∀ sigma, 0 ≤ w sigma) (hparent : w anchor ≤ Z)
    (hweight : ∀ sigma u c, w (Function.update sigma u c) ≤ H * w sigma)
    (hresponse : ∀ sigma u c, ‖h (Function.update sigma u c) - h sigma‖ ≤ alpha) :
    ‖hardEndpointError (fun sigma => ∑ p, z ^ m sigma p)
        (fun sigma => ∑ p, (0 : ℂ) ^ m sigma p) w h Z‖ ≤
      (Fintype.card C : ℝ) ^ (N + s) * H ^ s * Real.exp (alpha * s) * ‖z‖ *
        ‖Complex.exp (h anchor)‖ := by
  have he := monomial_hardEndpointError_norm_le_of_coordinates m z hz w h anchor
    hZ hH ha hw hparent hweight hresponse
  have hq : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have hP : (Fintype.card P : ℝ) ≤ (Fintype.card C : ℝ) ^ N := by exact_mod_cast hinside
  have hcount : (Fintype.card C : ℝ) ^ Fintype.card V * Fintype.card P ≤
      (Fintype.card C : ℝ) ^ (N + s) := by
    calc
      _ ≤ (Fintype.card C : ℝ) ^ s * (Fintype.card C : ℝ) ^ N :=
        mul_le_mul (pow_le_pow_right₀ hq hshell) hP (Nat.cast_nonneg _)
          (pow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by rw [pow_add]; ring
  have hphase : H ^ Fintype.card V * Real.exp (alpha * Fintype.card V) ≤
      H ^ s * Real.exp (alpha * s) :=
    mul_le_mul (pow_le_pow_right₀ hH hshell)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hshell) ha))
      (Real.exp_pos _).le (pow_nonneg (le_trans zero_le_one hH) _)
  have hboth := mul_le_mul hcount hphase
    (mul_nonneg (pow_nonneg (le_trans zero_le_one hH) _) (Real.exp_pos _).le)
    (pow_nonneg (Nat.cast_nonneg _) _)
  have hfinal := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hboth (norm_nonneg z)) (norm_nonneg (Complex.exp (h anchor)))
  apply he.trans
  convert hfinal using 1 <;> ring

end Configurations
end
end CI2ZF
