import ZeroFreeness.Holant.PolynomialStability

/-! One choice of numerical budgets for the entire graph family. Looser
ball bounds and smaller radii simplify bookkeeping without changing the
nonnegative-polytube theorem. -/
namespace ZeroFreeness.Holant
noncomputable section

structure TransferParameters (D : ℕ) (A R C : ℝ) where
  layers : ℕ
  layers_pos : 0 < layers
  coupling_small : C / layers ≤ 1 / 64
  localSize : ℕ
  ball_bound : (D + 1) ^ layers ≤ localSize
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_small : alpha ≤ 1 / 4
  oscillation_small : localSize * alpha ≤ 1 / 8
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_le_one : epsilon ≤ 1
  error_small : (2 : ℝ) ^ localSize *
    (polynomialLipschitzConstant localSize (A ^ (2 * localSize)) (R + 1) * epsilon) * (4 / 3) ≤ alpha / 16
  parent_small : A ^ 2 * epsilon * (4 / 3) < 1

theorem exists_transferParameters (D : ℕ) {A R C : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    Nonempty (TransferParameters D A R C) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (64 * C) 0)
  have hL0 : 0 < L := by
    have : (0 : ℝ) < L := (le_max_right _ _).trans_lt hL
    exact_mod_cast this
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL0
  have hCL : C / L ≤ 1 / 64 := by
    apply (div_le_iff₀ hLreal).mpr
    have := (le_max_left _ _).trans_lt hL
    linarith
  let N := (D + 1) ^ L
  let α : ℝ := 1 / (16 * ((N : ℝ) + 1))
  have hNp : 0 < (N : ℝ) + 1 := by positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hαeq : α * (16 * ((N : ℝ) + 1)) = 1 := by
    dsimp [α]
    exact div_mul_cancel₀ _ (by positivity)
  have hαsmall : α ≤ 1 / 4 := by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  have hosc : (N : ℝ) * α ≤ 1 / 8 := by nlinarith
  let K := polynomialLipschitzConstant N (A ^ (2 * N)) (R + 1)
  have hK : 0 < K := polynomialLipschitzConstant_pos N (pow_nonneg hA _) (by linarith)
  let T : ℝ := 2 ^ N * K * (4 / 3)
  have hT : 0 < T := by dsimp [T]; positivity
  let ε := min 1 (min (α / (32 * T)) (1 / (4 * (A ^ 2 + 1))))
  have hε : 0 < ε := by
    apply lt_min zero_lt_one
    apply lt_min (div_pos hα (by positivity))
    positivity
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεT : ε ≤ α / (32 * T) := (min_le_right _ _).trans (min_le_left _ _)
  have hεA : ε ≤ 1 / (4 * (A ^ 2 + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have herror : T * ε ≤ α / 16 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 32 * T)).mp hεT
    linarith
  have hparent : A ^ 2 * ε * (4 / 3) < 1 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 4 * (A ^ 2 + 1))).mp hεA
    nlinarith
  refine ⟨⟨L, hL0, hCL, N, le_rfl, α, hα, hαsmall, hosc, ε, hε, hε1, ?_, hparent⟩⟩
  change 2 ^ N * (K * ε) * (4 / 3) ≤ α / 16
  have heq : 2 ^ N * (K * ε) * (4 / 3) = T * ε := by dsimp [T]; ring
  rw [heq]
  exact herror

namespace TransferParameters
variable {D : ℕ} {A R C : ℝ}

def localErrorBound (p : TransferParameters D A R C) : ℝ :=
  polynomialLipschitzConstant p.localSize (A ^ (2 * p.localSize)) (R + 1) * p.epsilon

def totalErrorBound (p : TransferParameters D A R C) : ℝ :=
  (2 : ℝ) ^ p.localSize * p.localErrorBound * (4 / 3)

theorem localErrorBound_nonneg (p : TransferParameters D A R C)
    (hA : 0 ≤ A) (hR : 0 ≤ R) : 0 ≤ p.localErrorBound := by
  exact mul_nonneg (polynomialLipschitzConstant_pos p.localSize (pow_nonneg hA _)
    (by linarith)).le p.epsilon_pos.le

theorem totalErrorBound_nonneg (p : TransferParameters D A R C)
    (hA : 0 ≤ A) (hR : 0 ≤ R) : 0 ≤ p.totalErrorBound := by
  have := p.localErrorBound_nonneg hA hR
  unfold totalErrorBound
  positivity

theorem totalErrorBound_small (p : TransferParameters D A R C) : p.totalErrorBound ≤ 2 / 9 := by
  have h := p.error_small
  have ha := p.alpha_small
  change p.totalErrorBound ≤ p.alpha / 16 at h
  linarith

end TransferParameters
end
end ZeroFreeness.Holant
