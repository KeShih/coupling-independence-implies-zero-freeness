import CI2ZF.Appendix.GirthFiniteL2
import CI2ZF.Appendix.GirthScalarCalculus

namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω U : Type*} [Fintype Ω] [Fintype U]

/-- The raw bounded cavity probabilities under their actual exterior law. -/
structure ScalarInsertion (Ω U : Type*) [Fintype Ω] [Fintype U] where
  μ : FinDist Ω
  π : U → Ω → ℝ
  s : ℝ
  B : ℝ
  Δ : ℝ
  s_nonneg : 0 ≤ s
  s_le_one : s ≤ 1
  B_nonneg : 0 ≤ B
  B_lt_one : B < 1
  degree : (Fintype.card U : ℝ) ≤ Δ
  π_nonneg : ∀ u ω, 0 ≤ π u ω
  π_le : ∀ u ω, π u ω ≤ B

namespace ScalarInsertion
variable (I : ScalarInsertion Ω U)

def p (u : U) : ℝ := expectReal I.μ (I.π u)
def X (ω : Ω) : ℝ := ∑ u, I.π u ω
def M (ω : Ω) : ℝ := ∑ u, (I.π u ω - I.p u)
def Y (ω : Ω) : ℝ := ∏ u, (1 - I.s * I.π u ω)
def T : ℝ := expectReal I.μ I.Y
def Q : ℝ := ∏ u, (1 - I.s * I.p u)
def logError (ω : Ω) : ℝ := ∑ u, logRemainder (I.s * I.π u ω)
def meanLogError : ℝ := ∑ u, logRemainder (I.s * I.p u)
def amplitude : ℝ := I.Δ * I.B
def remainderBudget : ℝ := I.Δ * I.B ^ 2 / (2 * (1 - I.B))
def quotientError (V : ℝ) : ℝ := I.remainderBudget + Real.exp I.amplitude * V / 2

theorem Δ_nonneg : 0 ≤ I.Δ := (Nat.cast_nonneg _).trans I.degree
theorem amplitude_nonneg : 0 ≤ I.amplitude := mul_nonneg I.Δ_nonneg I.B_nonneg
theorem remainderBudget_nonneg : 0 ≤ I.remainderBudget :=
  div_nonneg (mul_nonneg I.Δ_nonneg (sq_nonneg _)) (by linarith [I.B_lt_one])

theorem p_bounds (u : U) : 0 ≤ I.p u ∧ I.p u ≤ I.B := by
  constructor
  · simpa only [expectReal_const, p] using expectReal_mono I.μ (fun ω => I.π_nonneg u ω)
  · exact (expectReal_mono I.μ (I.π_le u)).trans_eq (expectReal_const I.μ I.B)

theorem scaled_bounds {x : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ I.B) :
    0 ≤ I.s * x ∧ I.s * x ≤ I.B :=
  ⟨mul_nonneg I.s_nonneg hx0, (mul_le_mul_of_nonneg_right I.s_le_one hx0).trans (by simpa using hxB)⟩

theorem X_bounds (ω : Ω) : 0 ≤ I.X ω ∧ I.X ω ≤ I.amplitude := by
  constructor
  · exact Finset.sum_nonneg fun u _ => I.π_nonneg u ω
  · calc
      _ ≤ ∑ _u : U, I.B := Finset.sum_le_sum fun u _ => I.π_le u ω
      _ ≤ _ := by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, amplitude] using
        mul_le_mul_of_nonneg_right I.degree I.B_nonneg

theorem M_eq (ω : Ω) : I.M ω = I.X ω - expectReal I.μ I.X := by
  rw [M, X, Finset.sum_sub_distrib]
  change _ = _ - expectReal I.μ (fun ω => ∑ u, I.π u ω)
  rw [expectReal_sum]
  rfl

theorem M_mean : expectReal I.μ I.M = 0 := by
  change expectReal I.μ (fun ω => I.M ω) = 0
  simp_rw [I.M_eq]
  exact expectation_centered I.μ I.X

theorem M_abs (ω : Ω) : |I.M ω| ≤ I.amplitude := by
  rw [I.M_eq]
  have hμ0 : 0 ≤ expectReal I.μ I.X := by
    simpa only [expectReal_const] using expectReal_mono I.μ (fun ω => (I.X_bounds ω).1)
  have hμ1 : expectReal I.μ I.X ≤ I.amplitude :=
    (expectReal_mono I.μ fun ω => (I.X_bounds ω).2).trans_eq (expectReal_const I.μ I.amplitude)
  exact abs_le.mpr ⟨by linarith [(I.X_bounds ω).1], by linarith [(I.X_bounds ω).2]⟩

theorem Y_pos (ω : Ω) : 0 < I.Y ω := Finset.prod_pos fun u _ => by
  have hh := I.scaled_bounds (I.π_nonneg u ω) (I.π_le u ω)
  linarith [I.B_lt_one]

theorem Q_pos : 0 < I.Q := Finset.prod_pos fun u _ => by
  have hh := I.scaled_bounds (I.p_bounds u).1 (I.p_bounds u).2
  linarith [I.B_lt_one]

theorem remainder_sum_bounds (f : U → ℝ) (hf : ∀ u, 0 ≤ f u ∧ f u ≤ I.B) :
    0 ≤ ∑ u, logRemainder (f u) ∧ ∑ u, logRemainder (f u) ≤ I.remainderBudget := by
  constructor
  · exact Finset.sum_nonneg fun u _ => logRemainder_nonneg ((hf u).2.trans_lt I.B_lt_one)
  · calc
      _ ≤ ∑ u, f u ^ 2 / (2 * (1 - I.B)) :=
        Finset.sum_le_sum fun u _ => logRemainder_le I.B_lt_one (hf u).1 (hf u).2
      _ ≤ ∑ _u : U, I.B ^ 2 / (2 * (1 - I.B)) := Finset.sum_le_sum fun u _ =>
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (hf u).1 (hf u).2 2) (by linarith [I.B_lt_one])
      _ ≤ _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, remainderBudget]
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right I.degree
          (div_nonneg (sq_nonneg I.B) (by linarith [I.B_lt_one]))

theorem logError_bounds (ω : Ω) : 0 ≤ I.logError ω ∧ I.logError ω ≤ I.remainderBudget :=
  I.remainder_sum_bounds _ fun u => I.scaled_bounds (I.π_nonneg u ω) (I.π_le u ω)

theorem meanLogError_bounds : 0 ≤ I.meanLogError ∧ I.meanLogError ≤ I.remainderBudget :=
  I.remainder_sum_bounds _ fun u => I.scaled_bounds (I.p_bounds u).1 (I.p_bounds u).2

theorem log_Y (ω : Ω) : Real.log (I.Y ω) = -I.s * I.X ω - I.logError ω := by
  rw [Y, Real.log_prod (fun u _ => by
    have hh := I.scaled_bounds (I.π_nonneg u ω) (I.π_le u ω)
    linarith [I.B_lt_one] : ∀ u ∈ (Finset.univ : Finset U), 1 - I.s * I.π u ω ≠ 0)]
  simp only [X, logError, logRemainder, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem log_Q : Real.log I.Q = -I.s * expectReal I.μ I.X - I.meanLogError := by
  rw [Q, Real.log_prod (fun u _ => by
    have hh := I.scaled_bounds (I.p_bounds u).1 (I.p_bounds u).2
    linarith [I.B_lt_one] : ∀ u ∈ (Finset.univ : Finset U), 1 - I.s * I.p u ≠ 0)]
  change _ = -I.s * expectReal I.μ (fun ω => ∑ u, I.π u ω) - _
  rw [expectReal_sum]
  simp only [meanLogError, logRemainder, p, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem log_Y_div_Q (ω : Ω) : Real.log (I.Y ω / I.Q) =
    -I.s * I.M ω + (I.meanLogError - I.logError ω) := by
  rw [Real.log_div (I.Y_pos ω).ne' I.Q_pos.ne', I.log_Y, I.log_Q, I.M_eq]
  ring

theorem T_lower : Real.exp (-I.amplitude - I.remainderBudget) ≤ I.T := by
  have hh (ω : Ω) : Real.exp (-I.amplitude - I.remainderBudget) ≤ I.Y ω := by
    rw [← Real.exp_log (I.Y_pos ω), Real.exp_le_exp, I.log_Y]
    have hX := mul_le_mul_of_nonneg_right I.s_le_one (I.X_bounds ω).1
    linarith [(I.X_bounds ω).2, (I.logError_bounds ω).2]
  exact (expectReal_const I.μ _).symm.trans_le (expectReal_mono I.μ hh)

theorem T_pos : 0 < I.T := (Real.exp_pos _).trans_le I.T_lower

theorem exp_M_bounds {V : ℝ} (hV : variance I.μ I.M ≤ V) :
    1 ≤ expectReal I.μ (fun ω => Real.exp (-I.s * I.M ω)) ∧
    expectReal I.μ (fun ω => Real.exp (-I.s * I.M ω)) ≤
      1 + Real.exp I.amplitude * V / 2 := by
  have hmean : expectReal I.μ (fun ω => -I.s * I.M ω) = 0 := by
    rw [expectReal_const_mul, I.M_mean, mul_zero]
  have hsq : expectReal I.μ (fun ω => (-I.s * I.M ω) ^ 2) ≤ V := by
    have hs : I.s ^ 2 ≤ 1 := by nlinarith [I.s_nonneg, I.s_le_one]
    calc
      _ ≤ expectReal I.μ (fun ω => I.M ω ^ 2) := expectReal_mono I.μ fun ω => by
        simpa only [mul_pow, neg_sq, one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (I.M ω))
      _ = variance I.μ I.M := by simp only [variance, I.M_mean, sub_zero]
      _ ≤ _ := hV
  constructor
  · have hh := expectReal_mono I.μ (fun ω => Real.add_one_le_exp (-I.s * I.M ω))
    rw [expectReal_add, hmean, expectReal_const, zero_add] at hh
    exact hh
  · have hh := expectReal_mono I.μ (fun ω => exp_quadratic_upper (x := -I.s * I.M ω) I.amplitude_nonneg (by
        rw [abs_mul, abs_neg, abs_of_nonneg I.s_nonneg]
        exact (mul_le_mul_of_nonneg_right I.s_le_one (abs_nonneg (I.M ω))).trans
          (by simpa only [one_mul] using I.M_abs ω)))
    simp only [expectReal_add, expectReal_const, hmean, add_zero,
      div_eq_mul_inv, expectReal_mul_const, expectReal_const_mul] at hh
    apply hh.trans
    have hh2 := mul_le_mul_of_nonneg_left hsq (Real.exp_pos I.amplitude).le
    nlinarith

theorem quotient_bounds {V : ℝ} (hV : variance I.μ I.M ≤ V) :
    Real.exp (-I.quotientError V) ≤ I.T / I.Q ∧
      I.T / I.Q ≤ Real.exp (I.quotientError V) := by
  have hV0 : 0 ≤ V := (variance_nonneg I.μ I.M).trans hV
  have hκ : 0 ≤ Real.exp I.amplitude * V / 2 := by positivity
  have hlow (ω : Ω) : Real.exp (-I.remainderBudget) * Real.exp (-I.s * I.M ω) ≤ I.Y ω / I.Q := by
    rw [← Real.exp_add, ← Real.exp_log (div_pos (I.Y_pos ω) I.Q_pos), Real.exp_le_exp, I.log_Y_div_Q]
    linarith [(I.meanLogError_bounds).1, (I.logError_bounds ω).2]
  have hupp (ω : Ω) : I.Y ω / I.Q ≤ Real.exp I.remainderBudget * Real.exp (-I.s * I.M ω) := by
    rw [← Real.exp_add, ← Real.exp_log (div_pos (I.Y_pos ω) I.Q_pos), Real.exp_le_exp, I.log_Y_div_Q]
    linarith [(I.meanLogError_bounds).2, (I.logError_bounds ω).1]
  have hlo := expectReal_mono I.μ hlow
  have hup := expectReal_mono I.μ hupp
  simp only [div_eq_mul_inv, expectReal_const_mul, expectReal_mul_const] at hlo hup
  change Real.exp (-I.remainderBudget) * expectReal I.μ (fun ω => Real.exp (-I.s * I.M ω)) ≤ I.T / I.Q at hlo
  change I.T / I.Q ≤ Real.exp I.remainderBudget * expectReal I.μ (fun ω => Real.exp (-I.s * I.M ω)) at hup
  constructor
  · calc
      _ ≤ Real.exp (-I.remainderBudget) := Real.exp_le_exp.mpr (by dsimp [quotientError]; linarith)
      _ ≤ Real.exp (-I.remainderBudget) * expectReal I.μ (fun ω => Real.exp (-I.s * I.M ω)) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (I.exp_M_bounds hV).1
          (Real.exp_pos (-I.remainderBudget)).le
      _ ≤ _ := hlo
  · calc
      _ ≤ Real.exp I.remainderBudget * (1 + Real.exp I.amplitude * V / 2) :=
        hup.trans (mul_le_mul_of_nonneg_left (I.exp_M_bounds hV).2 (Real.exp_pos I.remainderBudget).le)
      _ ≤ Real.exp I.remainderBudget * Real.exp (Real.exp I.amplitude * V / 2) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (Real.exp I.amplitude * V / 2)])
          (Real.exp_pos I.remainderBudget).le
      _ = _ := by rw [← Real.exp_add]; rfl

theorem log_quotient_bound {V : ℝ} (hV : variance I.μ I.M ≤ V) :
    |Real.log (I.T / I.Q)| ≤ I.quotientError V := by
  have hh := I.quotient_bounds hV
  have hp := div_pos I.T_pos I.Q_pos
  apply abs_le.mpr
  constructor
  · exact (Real.exp_le_exp.mp (by simpa only [Real.exp_log hp] using hh.1))
  · exact (Real.exp_le_exp.mp (by simpa only [Real.exp_log hp] using hh.2))

end ScalarInsertion
end
end CI2ZF.Appendix.Girth
