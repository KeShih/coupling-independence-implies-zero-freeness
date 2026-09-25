import ZeroFreeness.Analysis.ComplexAverage
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-! Explicit uniform estimates for bounded multilinear local polynomials.
The constants depend on the number of variables and a coefficient bound,
and do not depend on the ambient graph or on positive lower activities. -/
namespace ZeroFreeness.Holant
open scoped BigOperators
noncomputable section
variable {E : Type*} [DecidableEq E]
set_option linter.unusedSectionVars false

theorem norm_monomial_le (s : Finset E) (z : E → ℂ) {M : ℝ} (_hM : 0 ≤ M)
    (hz : ∀ e ∈ s, ‖z e‖ ≤ M) : ‖∏ e ∈ s, z e‖ ≤ M ^ s.card := by
  rw [norm_prod]
  calc
    ∏ e ∈ s, ‖z e‖ ≤ ∏ _e ∈ s, M :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) hz
    _ = M ^ s.card := by simp

/-- Telescoping a product gives a bound valid even when some factors vanish. -/
theorem norm_monomial_sub_le (s : Finset E) (z w : E → ℂ) {M δ : ℝ}
    (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hz : ∀ e ∈ s, ‖z e‖ ≤ M) (hw : ∀ e ∈ s, ‖w e‖ ≤ M)
    (hd : ∀ e ∈ s, ‖z e - w e‖ ≤ δ) :
    ‖(∏ e ∈ s, z e) - ∏ e ∈ s, w e‖ ≤ s.card * δ * M ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
    have hz' := hz e (Finset.mem_insert_self e s)
    have hd' := hd e (Finset.mem_insert_self e s)
    have ih' := ih (fun a ha => hz a (Finset.mem_insert_of_mem ha))
      (fun a ha => hw a (Finset.mem_insert_of_mem ha))
      (fun a ha => hd a (Finset.mem_insert_of_mem ha))
    have hpw := norm_monomial_le s w (by linarith : 0 ≤ M)
      (fun a ha => hw a (Finset.mem_insert_of_mem ha))
    rw [Finset.prod_insert he, Finset.prod_insert he, Finset.card_insert_of_notMem he]
    have hid : z e * (∏ a ∈ s, z a) - w e * (∏ a ∈ s, w a) =
        z e * ((∏ a ∈ s, z a) - ∏ a ∈ s, w a) +
          (z e - w e) * (∏ a ∈ s, w a) := by ring
    rw [hid]
    have ht := norm_add_le
      (z e * ((∏ a ∈ s, z a) - ∏ a ∈ s, w a))
      ((z e - w e) * (∏ a ∈ s, w a))
    simp only [norm_mul] at ht
    have ht1 := mul_le_mul hz' ih' (norm_nonneg _) (by linarith : 0 ≤ M)
    have ht2 := mul_le_mul hd' hpw (norm_nonneg _) hδ
    have hp : 0 ≤ δ * M ^ s.card := mul_nonneg hδ (pow_nonneg (by linarith) _)
    have hm := mul_le_mul_of_nonneg_right hM hp
    push_cast
    rw [pow_succ]
    nlinarith

def multilinear (edges : Finset E) (c : Finset E → ℂ) (z : E → ℂ) : ℂ :=
  ∑ s ∈ edges.powerset, c s * ∏ e ∈ s, z e

/-- A common bound for every local polynomial with at most `N` variables. -/
def polynomialLipschitzConstant (N : ℕ) (B M : ℝ) : ℝ :=
  1 + 2 ^ N * B * N * M ^ N

theorem polynomialLipschitzConstant_pos (N : ℕ) {B M : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) : 0 < polynomialLipschitzConstant N B M := by
  unfold polynomialLipschitzConstant
  positivity

theorem multilinear_lipschitz (edges : Finset E) (c : Finset E → ℂ)
    (z w : E → ℂ) {N : ℕ} {B M δ : ℝ}
    (hN : edges.card ≤ N) (hB : 0 ≤ B) (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hc : ∀ s ⊆ edges, ‖c s‖ ≤ B)
    (hz : ∀ e ∈ edges, ‖z e‖ ≤ M) (hw : ∀ e ∈ edges, ‖w e‖ ≤ M)
    (hd : ∀ e ∈ edges, ‖z e - w e‖ ≤ δ) :
    ‖multilinear edges c z - multilinear edges c w‖ ≤
      polynomialLipschitzConstant N B M * δ := by
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hterm : ∀ s ∈ edges.powerset,
      ‖c s * ((∏ e ∈ s, z e) - ∏ e ∈ s, w e)‖ ≤ B * N * δ * M ^ N := by
    intro s hs
    have hse := Finset.mem_powerset.mp hs
    have hsN := (Finset.card_le_card hse).trans hN
    have hm := norm_monomial_sub_le s z w hM hδ
      (fun e he => hz e (hse he)) (fun e he => hw e (hse he)) (fun e he => hd e (hse he))
    have hp := pow_le_pow_right₀ hM hsN
    have hsN' : (s.card : ℝ) ≤ N := by exact_mod_cast hsN
    have hc' := mul_le_mul (hc s hse) hm (norm_nonneg _) hB
    rw [norm_mul]
    calc
      ‖c s‖ * ‖(∏ e ∈ s, z e) - ∏ e ∈ s, w e‖
          ≤ B * (s.card * δ * M ^ s.card) := hc'
      _ ≤ B * (N * δ * M ^ N) := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact mul_le_mul (mul_le_mul_of_nonneg_right hsN' hδ) hp
          (pow_nonneg hM0 _) (mul_nonneg (Nat.cast_nonneg _) hδ)
      _ = _ := by ring
  have heq : multilinear edges c z - multilinear edges c w =
      ∑ s ∈ edges.powerset, c s * ((∏ e ∈ s, z e) - ∏ e ∈ s, w e) := by
    simp [multilinear, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ s ∈ edges.powerset, ‖c s * ((∏ e ∈ s, z e) - ∏ e ∈ s, w e)‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ edges.powerset, B * N * δ * M ^ N := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ edges.card * (B * N * δ * M ^ N) := by simp
    _ ≤ (2 : ℝ) ^ N * (B * N * δ * M ^ N) := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hN)
      positivity
    _ ≤ polynomialLipschitzConstant N B M * δ := by
      unfold polynomialLipschitzConstant
      nlinarith

/-- Relative control needs only a lower bound at the real base, not positive
individual monomials. The all-zero monomial supplies that lower bound. -/
theorem multilinear_relative_stability (edges : Finset E) (c : Finset E → ℂ)
    (z w : E → ℂ) {N : ℕ} {B M δ η : ℝ}
    (hN : edges.card ≤ N) (hB : 0 ≤ B) (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (hc : ∀ s ⊆ edges, ‖c s‖ ≤ B)
    (hz : ∀ e ∈ edges, ‖z e‖ ≤ M) (hw : ∀ e ∈ edges, ‖w e‖ ≤ M)
    (hd : ∀ e ∈ edges, ‖z e - w e‖ ≤ δ)
    (hbase : 1 ≤ ‖multilinear edges c w‖)
    (hbudget : polynomialLipschitzConstant N B M * δ < η) :
    ‖multilinear edges c z / multilinear edges c w - 1‖ < η := by
  have hp : 0 < ‖multilinear edges c w‖ := lt_of_lt_of_le zero_lt_one hbase
  rw [div_sub_one (norm_pos_iff.mp hp), norm_div]
  have hbound := multilinear_lipschitz edges c z w hN hB hM hδ hc hz hw hd
  exact (div_le_self (norm_nonneg _) hbase).trans_lt (hbound.trans_lt hbudget)

end
end ZeroFreeness.Holant
