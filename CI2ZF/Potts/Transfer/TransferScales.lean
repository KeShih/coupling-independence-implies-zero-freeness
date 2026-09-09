import CI2ZF.Potts.Transfer.HardSeparatorLog
import Mathlib.Algebra.Order.Archimedean.Basic

/-! Uniform scalar choices for the shell induction. The choices depend
on the degree, colour count and real coupling bound, never on graph size. -/
namespace CI2ZF.Potts
noncomputable section

/-- Coarse BFS volume bounds suffice to select a strictly positive
logarithmic budget uniformly over every graph. -/
theorem exists_transfer_scales (Delta : ℕ) (cost : ℝ) :
    ∃ L : ℕ, 0 < L ∧ 64 * max cost 1 ≤ (L : ℝ) ∧
      ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ (1 / 16 : ℝ) ∧
        alpha * ((Delta + 1 : ℕ) ^ (L + 1) : ℝ) ≤ 1 / 16 := by
  obtain ⟨L, hL⟩ := exists_nat_gt (64 * max cost 1)
  have hmax : (1 : ℝ) ≤ max cost 1 := le_max_right _ _
  have hLpos : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  let B : ℝ := ((Delta + 1 : ℕ) ^ (L + 1) : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let alpha : ℝ := 1 / (32 * (B + 1))
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have he : alpha * (32 * (B + 1)) = 1 := by
    dsimp [alpha]
    exact div_mul_cancel₀ 1 (by positivity)
  refine ⟨L, hLpos, hL.le, alpha, ha, ?_, ?_⟩
  · nlinarith [mul_nonneg ha.le hB]
  · change alpha * B ≤ _
    nlinarith

/-- The exact geometric-volume cutoff used by the actual BFS split can
also be chosen before the instance. -/
theorem exists_geometric_transfer_scales (Delta : ℕ) (cost : ℝ) :
    ∃ L B : ℕ, 0 < L ∧ 64 * cost ≤ (L : ℝ) ∧
      (∑ j ∈ Finset.range (L + 2), Delta ^ j) ≤ B ∧
      ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ (1 / 16 : ℝ) ∧
        alpha * (B : ℝ) ≤ 1 / 16 := by
  obtain ⟨L, hL⟩ := exists_nat_gt (64 * max cost 1)
  have hmax : (1 : ℝ) ≤ max cost 1 := le_max_right _ _
  have hLpos : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  let B : ℕ := ∑ j ∈ Finset.range (L + 2), Delta ^ j
  let alpha : ℝ := 1 / (32 * ((B : ℝ) + 1))
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have he : alpha * (32 * ((B : ℝ) + 1)) = 1 := by
    dsimp [alpha]
    exact div_mul_cancel₀ 1 (by positivity)
  refine ⟨L, B, hLpos, ?_, le_rfl, alpha, ha, ?_, ?_⟩
  · have hc := le_max_left cost 1
    linarith
  · nlinarith [mul_nonneg ha.le hB]
  · nlinarith

/-- The positive-base average estimate closes under the uniform shell
and local logarithm budgets. -/
theorem positive_shell_budget_closes {L : ℕ} {cost alpha W delta : ℝ}
    (hL : 0 < L) (hcost : 64 * cost ≤ (L : ℝ)) (ha : 0 ≤ alpha)
    (hW : W ≤ cost / L) (hd : delta ≤ alpha / 8) :
    2 * alpha * W + 4 * delta ≤ alpha := by
  have hp : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : cost / L ≤ (1 / 64 : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    linarith
  have hbound := mul_le_mul_of_nonneg_left (hW.trans hc) (show 0 ≤ 2 * alpha by positivity)
  linarith

/-- The hard-base average estimate closes with the same choices. -/
theorem hard_shell_budget_closes {L : ℕ} {cost alpha W delta : ℝ}
    (hL : 0 < L) (hcost : 64 * cost ≤ (L : ℝ)) (ha : 0 ≤ alpha)
    (hW : W ≤ cost / L) (hd : delta ≤ alpha / 8) :
    2 * alpha * W + 3 * delta ≤ alpha := by
  have hp : (0 : ℝ) < L := by exact_mod_cast hL
  have hc : cost / L ≤ (1 / 64 : ℝ) := by
    apply (div_le_iff₀ hp).mpr
    linarith
  have hbound := mul_le_mul_of_nonneg_left (hW.trans hc) (show 0 ≤ 2 * alpha by positivity)
  linarith

/-- One strictly positive hard radius meets the local-component radius,
the separator defect budget, and the parent defective-colour budget. -/
theorem exists_hard_transfer_radius (q Delta B : ℕ) {alpha eps : ℝ}
    (ha : 0 < alpha) (heps : 0 < eps) :
    ∃ r : ℝ, 0 < r ∧ r ≤ eps ∧ r ≤ 1 ∧
      (3 / 2 : ℝ) * Separator.hardErrorCoefficient q Delta B B alpha * r ≤ alpha / 8 ∧
      (4 / 3 : ℝ) * q * (q : ℝ) ^ Delta * r < 1 := by
  let K := Separator.hardErrorCoefficient q Delta B B alpha
  let P := (4 / 3 : ℝ) * q * (q : ℝ) ^ Delta
  have hK : 0 ≤ K := Separator.hardErrorCoefficient_nonneg _ _ _ _ _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let r := min eps (min 1 (min (alpha / (12 * (K + 1))) (1 / (2 * (P + 1)))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hre : r ≤ eps := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrK : r ≤ alpha / (12 * (K + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrP : r ≤ 1 / (2 * (P + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨r, hr, hre, hr1, ?_, ?_⟩
  · have hk := (le_div_iff₀ (show 0 < 12 * (K + 1) by positivity)).mp hrK
    change (3 / 2 : ℝ) * K * r ≤ alpha / 8
    nlinarith
  · have hp := (le_div_iff₀ (show 0 < 2 * (P + 1) by positivity)).mp hrP
    change P * r < 1
    nlinarith

end
end CI2ZF.Potts
