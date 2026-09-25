import ZeroFreeness.Coupling.Girth.Covariance.Recursion
import ZeroFreeness.Coupling.Girth.Covariance.ScalarCalculus

/-! Uniform quantitative constants, retaining their actual q-dependence. -/
namespace ZeroFreeness.Appendix.Girth
noncomputable section

def covarianceGamma (δ : ℝ) : ℝ := δ / (4 * (2 + δ))
def covarianceL0 (δ : ℝ) : ℝ := (1 + Real.sqrt (1 + 1 / δ)) / δ
def covarianceP0 (δ : ℝ) : ℝ := covarianceL0 δ ^ 2 / (δ * covarianceGamma δ)
def covarianceE0 (δ : ℝ) : ℝ := 1 / δ ^ 2 + Real.exp (1 / δ) * covarianceP0 δ / 2
def covarianceb0 (δ : ℝ) : ℝ := 4 * Real.sqrt (covarianceP0 δ) +
  2 * Real.exp (2 / δ) * (Real.sqrt (covarianceP0 δ) + 1 / δ ^ 2)
def covarianceK0 (δ : ℝ) : ℝ := Real.sqrt (covarianceP0 δ) * covarianceb0 δ

structure CovarianceScale where
  δ : ℝ
  Δ : ℝ
  q : ℝ
  delta_pos : 0 < δ
  degree_one : 1 ≤ Δ
  degree_large : 2 ≤ δ * Δ
  colour_budget : δ * Δ ≤ q - Δ

namespace CovarianceScale
variable (p : CovarianceScale)

def m : ℝ := p.q - p.Δ
def B : ℝ := 1 / p.m
def a : ℝ := 1 / (1 - p.B)
def L : ℝ := (1 + Real.sqrt (p.q / (p.m + 1))) / p.m
def Vπ : ℝ := p.Δ * p.B * p.L ^ 2 / covarianceGamma p.δ
def VM : ℝ := p.Δ * p.Vπ
def D : ℝ := p.Δ * p.B ^ 2 * p.a / 2
def E : ℝ := p.D + Real.exp (p.Δ * p.B) * p.VM / 2
def b : ℝ := p.a ^ 2 * Real.sqrt p.Vπ +
  p.a * Real.exp (p.Δ * p.B + 2 * p.D) * (Real.sqrt p.VM + p.D)
def g : ℝ := Real.sqrt p.VM * p.b
def ell : ℝ := 2 * p.Δ * p.B * p.b
def K : ℝ := p.Δ * p.g
def epsilon : ℝ := Real.sqrt p.B * p.K

theorem Δ_pos : 0 < p.Δ := lt_of_lt_of_le zero_lt_one p.degree_one
theorem m_ge_two : 2 ≤ p.m := p.degree_large.trans p.colour_budget
theorem m_pos : 0 < p.m := by linarith [p.m_ge_two]
theorem q_pos : 0 < p.q := by have hh := p.m_pos; dsimp [m] at hh; linarith [p.Δ_pos]
theorem gamma_pos : 0 < covarianceGamma p.δ := by unfold covarianceGamma; positivity [p.delta_pos]
theorem B_pos : 0 < p.B := one_div_pos.mpr p.m_pos
theorem B_le_half : p.B ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) p.m_ge_two
theorem a_pos : 0 < p.a := one_div_pos.mpr (by linarith [p.B_le_half])
theorem a_le_two : p.a ≤ 2 := by
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
    (show 1 / 2 ≤ 1 - p.B by linarith [p.B_le_half])
  norm_num at hh
  simpa only [a, one_div] using hh
theorem B_le : p.B ≤ 1 / (p.δ * p.Δ) :=
  one_div_le_one_div_of_le (mul_pos p.delta_pos p.Δ_pos) p.colour_budget
theorem amplitude_le : p.Δ * p.B ≤ 1 / p.δ := by
  have hh := mul_le_mul_of_nonneg_left p.B_le p.Δ_pos.le
  calc
    _ ≤ p.Δ * (1 / (p.δ * p.Δ)) := hh
    _ = _ := by field_simp [p.delta_pos.ne', p.Δ_pos.ne']

theorem colours_times_B_le : p.q * p.B ≤ 1 + 1 / p.δ := by
  have he : p.q * p.B = 1 + p.Δ * p.B := by
    unfold B m
    field_simp [show p.q - p.Δ ≠ 0 from p.m_pos.ne']
    ring
  rw [he]
  exact add_le_add le_rfl p.amplitude_le

theorem L_nonneg : 0 ≤ p.L := div_nonneg (by positivity) p.m_pos.le
theorem L0_nonneg : 0 ≤ covarianceL0 p.δ := by unfold covarianceL0; positivity [p.delta_pos]
theorem P0_nonneg : 0 ≤ covarianceP0 p.δ := by
  unfold covarianceP0
  exact div_nonneg (sq_nonneg _) (mul_nonneg p.delta_pos.le p.gamma_pos.le)
theorem b0_nonneg : 0 ≤ covarianceb0 p.δ := by unfold covarianceb0; positivity

theorem root_ratio_le : p.q / (p.m + 1) ≤ 1 + 1 / p.δ := by
  have hm : 0 < p.m + 1 := by linarith [p.m_pos]
  apply (div_le_iff₀ hm).mpr
  apply (mul_le_mul_iff_right₀ p.delta_pos).mp
  have he : p.δ * ((1 + 1 / p.δ) * (p.m + 1)) = (p.δ + 1) * (p.m + 1) := by
    field_simp [p.delta_pos.ne']
  rw [he]
  have hb := p.colour_budget
  change p.δ * p.Δ ≤ p.m at hb
  have hq : p.q = p.m + p.Δ := by dsimp [m]; ring
  rw [hq]
  nlinarith [p.delta_pos, p.m_pos]

theorem L_le : p.L ≤ covarianceL0 p.δ / p.Δ := by
  calc
    _ ≤ (1 + Real.sqrt (1 + 1 / p.δ)) / (p.δ * p.Δ) :=
      div_le_div₀ (by positivity) (add_le_add le_rfl (Real.sqrt_le_sqrt p.root_ratio_le))
        (mul_pos p.delta_pos p.Δ_pos) p.colour_budget
    _ = _ := by unfold covarianceL0; field_simp

theorem Vπ_nonneg : 0 ≤ p.Vπ := by
  unfold Vπ
  exact div_nonneg (mul_nonneg (mul_nonneg p.Δ_pos.le p.B_pos.le) (sq_nonneg _)) p.gamma_pos.le
theorem VM_nonneg : 0 ≤ p.VM := mul_nonneg p.Δ_pos.le p.Vπ_nonneg
theorem D_nonneg : 0 ≤ p.D := by unfold D; positivity [p.Δ_pos, p.a_pos]
theorem E_nonneg : 0 ≤ p.E := by unfold E; positivity [p.D_nonneg, p.VM_nonneg]
theorem b_nonneg : 0 ≤ p.b := by unfold b; positivity [p.a_pos, p.D_nonneg]
theorem g_nonneg : 0 ≤ p.g := mul_nonneg (Real.sqrt_nonneg _) p.b_nonneg
theorem ell_nonneg : 0 ≤ p.ell := by unfold ell; positivity [p.Δ_pos, p.B_pos, p.b_nonneg]
theorem K_nonneg : 0 ≤ p.K := mul_nonneg p.Δ_pos.le p.g_nonneg
theorem epsilon_nonneg : 0 ≤ p.epsilon := mul_nonneg (Real.sqrt_nonneg _) p.K_nonneg

theorem Vπ_le : p.Vπ ≤ covarianceP0 p.δ / p.Δ ^ 2 := by
  calc
    _ ≤ (1 / p.δ) * (covarianceL0 p.δ / p.Δ) ^ 2 / covarianceGamma p.δ := by
      apply div_le_div_of_nonneg_right _ p.gamma_pos.le
      exact mul_le_mul p.amplitude_le (pow_le_pow_left₀ p.L_nonneg p.L_le 2)
        (sq_nonneg _) (one_div_nonneg.mpr p.delta_pos.le)
    _ = _ := by unfold covarianceP0; field_simp

theorem VM_le : p.VM ≤ covarianceP0 p.δ / p.Δ := by
  have hh := mul_le_mul_of_nonneg_left p.Vπ_le p.Δ_pos.le
  calc
    _ ≤ p.Δ * (covarianceP0 p.δ / p.Δ ^ 2) := hh
    _ = _ := by field_simp

theorem D_le : p.D ≤ 1 / (p.δ ^ 2 * p.Δ) := by
  calc
    _ ≤ p.Δ * (1 / (p.δ * p.Δ)) ^ 2 * 2 / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ p.B_pos.le p.B_le 2) p.Δ_pos.le)
        p.a_le_two p.a_pos.le (mul_nonneg p.Δ_pos.le (sq_nonneg _))
    _ = _ := by field_simp

theorem D_le_fixed : p.D ≤ 1 / (2 * p.δ) := by
  apply p.D_le.trans
  apply one_div_le_one_div_of_le (mul_pos (by norm_num) p.delta_pos)
  have hh := mul_le_mul_of_nonneg_left p.degree_large p.delta_pos.le
  nlinarith

theorem E_le : p.E ≤ covarianceE0 p.δ / p.Δ := by
  calc
    _ ≤ 1 / (p.δ ^ 2 * p.Δ) + Real.exp (1 / p.δ) * (covarianceP0 p.δ / p.Δ) / 2 := by
      exact add_le_add p.D_le (div_le_div_of_nonneg_right
        (mul_le_mul (Real.exp_le_exp.mpr p.amplitude_le) p.VM_le p.VM_nonneg (Real.exp_pos _).le)
        (by norm_num))
    _ = _ := by unfold covarianceE0; field_simp

theorem sqrt_Vπ_le : Real.sqrt p.Vπ ≤ Real.sqrt (covarianceP0 p.δ) / p.Δ := by
  have hh := Real.sqrt_le_sqrt p.Vπ_le
  rw [Real.sqrt_div p.P0_nonneg, Real.sqrt_sq p.Δ_pos.le] at hh
  exact hh

theorem sqrt_VM_le : Real.sqrt p.VM ≤ Real.sqrt (covarianceP0 p.δ) / Real.sqrt p.Δ := by
  have hh := Real.sqrt_le_sqrt p.VM_le
  rw [Real.sqrt_div p.P0_nonneg] at hh
  exact hh

theorem inv_degree_le_inv_sqrt : 1 / p.Δ ≤ 1 / Real.sqrt p.Δ := by
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr p.Δ_pos)
  nlinarith [Real.sq_sqrt p.Δ_pos.le, Real.sqrt_nonneg p.Δ, p.degree_one]

theorem b_le : p.b ≤ covarianceb0 p.δ / Real.sqrt p.Δ := by
  have he : Real.exp (p.Δ * p.B + 2 * p.D) ≤ Real.exp (2 / p.δ) := by
    apply Real.exp_le_exp.mpr
    have hd : 2 * p.D ≤ 1 / p.δ := by
      have hh := mul_le_mul_of_nonneg_left p.D_le_fixed (by norm_num : (0 : ℝ) ≤ 2)
      calc
        _ ≤ 2 * (1 / (2 * p.δ)) := hh
        _ = _ := by field_simp
    calc
      _ ≤ 1 / p.δ + 1 / p.δ := add_le_add p.amplitude_le hd
      _ = _ := by ring
  have hπ : Real.sqrt p.Vπ ≤ Real.sqrt (covarianceP0 p.δ) / Real.sqrt p.Δ :=
    p.sqrt_Vπ_le.trans (by simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left p.inv_degree_le_inv_sqrt (Real.sqrt_nonneg _))
  have hD : p.D ≤ (1 / p.δ ^ 2) / Real.sqrt p.Δ := by
    apply p.D_le.trans
    have hh := mul_le_mul_of_nonneg_left p.inv_degree_le_inv_sqrt (one_div_nonneg.mpr (sq_nonneg p.δ))
    convert hh using 1 <;> first | rfl | ring
  calc
    _ ≤ 4 * (Real.sqrt (covarianceP0 p.δ) / Real.sqrt p.Δ) +
        (2 * Real.exp (2 / p.δ)) * (Real.sqrt (covarianceP0 p.δ) / Real.sqrt p.Δ +
          (1 / p.δ ^ 2) / Real.sqrt p.Δ) := by
      exact add_le_add (mul_le_mul (by nlinarith [p.a_le_two, p.a_pos] : p.a ^ 2 ≤ 4)
        hπ (Real.sqrt_nonneg _) (by norm_num))
        (mul_le_mul (mul_le_mul p.a_le_two he (Real.exp_pos _).le (by norm_num))
          (add_le_add p.sqrt_VM_le hD) (add_nonneg (Real.sqrt_nonneg _) p.D_nonneg)
          (by positivity))
    _ = _ := by unfold covarianceb0; ring

theorem K_le : p.K ≤ covarianceK0 p.δ := by
  calc
    _ ≤ p.Δ * ((Real.sqrt (covarianceP0 p.δ) / Real.sqrt p.Δ) *
        (covarianceb0 p.δ / Real.sqrt p.Δ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul p.sqrt_VM_le p.b_le p.b_nonneg
        (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) p.Δ_pos.le
    _ = _ := by
      unfold covarianceK0
      have hs : Real.sqrt p.Δ ≠ 0 := (Real.sqrt_pos.mpr p.Δ_pos).ne'
      field_simp
      rw [Real.sq_sqrt p.Δ_pos.le]
      ring

theorem ell_le : p.ell ≤ (2 * covarianceb0 p.δ / p.δ) / Real.sqrt p.Δ := by
  have hA : 2 * p.Δ * p.B ≤ 2 / p.δ := by
    have hh := mul_le_mul_of_nonneg_left p.amplitude_le (by norm_num : (0 : ℝ) ≤ 2)
    convert hh using 1 <;> first | rfl | ring
  calc
    _ ≤ (2 / p.δ) * (covarianceb0 p.δ / Real.sqrt p.Δ) :=
      mul_le_mul hA
        p.b_le p.b_nonneg (by positivity [p.delta_pos])
    _ = _ := by ring

theorem g_le : p.g ≤ covarianceK0 p.δ / p.Δ := by
  apply (le_div_iff₀ p.Δ_pos).mpr
  have hh := p.K_le
  change p.Δ * p.g ≤ covarianceK0 p.δ at hh
  simpa only [mul_comm] using hh

theorem epsilon_le : p.epsilon ≤
    (Real.sqrt (1 / p.δ) * covarianceK0 p.δ) / Real.sqrt p.Δ := by
  have hB : Real.sqrt p.B ≤ Real.sqrt (1 / p.δ) / Real.sqrt p.Δ := by
    have hh := Real.sqrt_le_sqrt p.B_le
    rw [div_mul_eq_div_div, Real.sqrt_div (one_div_nonneg.mpr p.delta_pos.le)] at hh
    exact hh
  calc
    _ ≤ (Real.sqrt (1 / p.δ) / Real.sqrt p.Δ) * covarianceK0 p.δ :=
      mul_le_mul hB p.K_le p.K_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = _ := by ring

end CovarianceScale
end
end ZeroFreeness.Appendix.Girth
