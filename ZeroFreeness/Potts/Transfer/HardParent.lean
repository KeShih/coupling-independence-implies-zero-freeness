import ZeroFreeness.Potts.Transfer.HardCountComparison
import ZeroFreeness.Potts.Transfer.HardEndpointLocalError
import ZeroFreeness.Analysis.ComplexAverage

/-! The hard-endpoint parent recursion is nonzero when the normalized
child logarithms are small. Zero-exponent terms form a positive main part;
all positive-exponent terms are controlled by a uniform additive error.
The actual Potts instance supplies both the hard-allowed anchor and the
q^Delta comparison of its child hard weights. -/
namespace ZeroFreeness
open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

def hardParentSum {S : Type*} [Fintype S] (w : S → ℝ) (m : S → ℕ)
    (L : S → ℂ) (z : ℂ) : ℂ :=
  ∑ s, z ^ m s * (w s : ℂ) * Complex.exp (L s)

theorem hardParentSum_zero_re_ge {S : Type*} [Fintype S]
    (w : S → ℝ) (hw : ∀ s, 0 < w s) (m : S → ℕ) (L : S → ℂ) (anchor : S)
    (hm : m anchor = 0) (hanchor : L anchor = 0)
    (hL : ∀ s, ‖L s‖ ≤ (1 / 4 : ℝ)) :
    w anchor ≤ (hardParentSum w m L 0).re := by
  have hRe (s : S) : 0 ≤ (Complex.exp (L s)).re := by
    have he := norm_exp_sub_one_le_third (L s) (hL s)
    have hr := Complex.re_le_norm (1 - Complex.exp (L s))
    rw [norm_sub_rev] at hr
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith
  have hn (s : S) : 0 ≤ ((0 : ℂ) ^ m s * (w s : ℂ) * Complex.exp (L s)).re := by
    cases he : m s with
    | zero => simpa using mul_nonneg (hw s).le (hRe s)
    | succ k => simp
  have ha : ((0 : ℂ) ^ m anchor * (w anchor : ℂ) * Complex.exp (L anchor)).re = w anchor := by
    simp [hm, hanchor]
  unfold hardParentSum
  rw [Complex.re_sum]
  rw [← ha]
  exact Finset.single_le_sum (fun s _ => hn s) (Finset.mem_univ anchor)

theorem hardParentSum_error_le {S : Type*} [Fintype S]
    (w : S → ℝ) (hw : ∀ s, 0 < w s) (m : S → ℕ) (L : S → ℂ) (anchor : S)
    {H : ℝ} (hH : 0 ≤ H) (hweight : ∀ s, w s ≤ H * w anchor)
    (hL : ∀ s, ‖L s‖ ≤ (1 / 4 : ℝ)) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖hardParentSum w m L z - hardParentSum w m L 0‖ ≤
      (4 / 3 : ℝ) * Fintype.card S * H * ‖z‖ * w anchor := by
  have hexp (s : S) : ‖Complex.exp (L s)‖ ≤ (4 / 3 : ℝ) := by
    rw [Complex.norm_exp]
    exact (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hL s))).trans
      exp_quarter_le_four_thirds
  have heq : hardParentSum w m L z - hardParentSum w m L 0 =
      ∑ s, (z ^ m s - (0 : ℂ) ^ m s) * (w s : ℂ) * Complex.exp (L s) := by
    simp only [hardParentSum, sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  calc
    ‖∑ s, (z ^ m s - (0 : ℂ) ^ m s) * (w s : ℂ) * Complex.exp (L s)‖ ≤
        ∑ s, ‖(z ^ m s - (0 : ℂ) ^ m s) * (w s : ℂ) * Complex.exp (L s)‖ := norm_sum_le _ _
    _ ≤ ∑ _s : S, ‖z‖ * (H * w anchor) * (4 / 3 : ℝ) := by
      apply Finset.sum_le_sum
      intro s _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hw s)]
      exact mul_le_mul
        (mul_le_mul (monomial_error_zero z hz (m s)) (hweight s) (hw s).le (norm_nonneg z))
        (hexp s) (norm_nonneg _) (mul_nonneg (norm_nonneg z) (mul_nonneg hH (hw anchor).le))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- A positive hard main part cannot be cancelled by the defective terms
under the explicit radius budget. -/
theorem hardParentSum_ne_zero {S : Type*} [Fintype S]
    (w : S → ℝ) (hw : ∀ s, 0 < w s) (m : S → ℕ) (L : S → ℂ) (anchor : S)
    (hm : m anchor = 0) (hanchor : L anchor = 0)
    {H : ℝ} (hH : 0 ≤ H) (hweight : ∀ s, w s ≤ H * w anchor)
    (hL : ∀ s, ‖L s‖ ≤ (1 / 4 : ℝ)) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (hsmall : (4 / 3 : ℝ) * Fintype.card S * H * ‖z‖ < 1) :
    hardParentSum w m L z ≠ 0 := by
  have hmain := (hardParentSum_zero_re_ge w hw m L anchor hm hanchor hL).trans
    (Complex.re_le_norm (hardParentSum w m L 0))
  have herr := hardParentSum_error_le w hw m L anchor hH hweight hL z hz
  have hstrict := mul_lt_mul_of_pos_right hsmall (hw anchor)
  intro hzero
  rw [hzero, zero_sub, norm_neg] at herr
  linarith

namespace Potts
variable {V C : Type*} [Fintype V] [Fintype C]

/-- The degree/colour threshold supplies an actual root colour that is
absent from every old pinned neighbour. -/
theorem exists_zero_root_boundary (tau : PartialColouring V C) (G : SimpleGraph V)
    (v : tau.FreeVertex) {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    ∃ a : C, tau.boundaryCount G v a = 0 := by
  have hc := card_hardList_of_succ_le (tau.toPinningData G)
    (tau.degreeBound_of_original G hdegree) hcolours v
  have hn : ((tau.toPinningData G).hardList v).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨a, ha⟩ := hn
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

/-- Actual normalized Potts parent nonvanishing from its child response
logs around a hard-allowed root colour. The q^Delta weight comparison is
proved by local recolouring, rather than supplied as an assumption. -/
theorem hard_parent_nonzero_of_child_logs
    (tau : PartialColouring V C) (G : SimpleGraph V) (v : tau.FreeVertex)
    {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C)
    (anchor : C) (hm : tau.boundaryCount G v anchor = 0) (z : ℂ)
    (hchild : normalizedPartition (pinVertex tau v anchor) G z ≠ 0)
    (L : C → ℂ) (hanchor : L anchor = 0)
    (hexp : ∀ c, Complex.exp (L c) =
      (normalizedPartition (pinVertex tau v c) G z /
        normalizedPartition (pinVertex tau v c) G 0) /
      (normalizedPartition (pinVertex tau v anchor) G z /
        normalizedPartition (pinVertex tau v anchor) G 0))
    (hL : ∀ c, ‖L c‖ ≤ (1 / 4 : ℝ)) (hz : ‖z‖ ≤ 1)
    (hsmall : (4 / 3 : ℝ) * Fintype.card C * (Fintype.card C : ℝ) ^ Δ * ‖z‖ < 1) :
    normalizedPartition tau G z ≠ 0 := by
  let : Nonempty C := ⟨anchor⟩
  let w (c : C) : ℝ := ((pinVertex tau v c).toPinningData G).partition 0
  have hw (c : C) : 0 < w c := partition_zero_pos_of_succ_le
    ((pinVertex tau v c).toPinningData G)
    ((pinVertex tau v c).degreeBound_of_original G hdegree) hcolours
  have hbase (c : C) : normalizedPartition (pinVertex tau v c) G 0 = (w c : ℂ) :=
    normalizedPartition_ofReal _ _ 0
  have hwne (c : C) : (w c : ℂ) ≠ 0 := by exact_mod_cast (hw c).ne'
  have hweight (c : C) : w c ≤ (Fintype.card C : ℝ) ^ Δ * w anchor := by
    have hc := normalizedPartition_pinVertex_zero_comparison tau G v c anchor hdegree hcolours
    rw [hbase c, hbase anchor] at hc
    simpa only [Complex.ofReal_re] using hc
  have hsum := hardParentSum_ne_zero w hw (tau.boundaryCount G v) L anchor hm hanchor
    (pow_nonneg (Nat.cast_nonneg _) _) hweight hL z hz hsmall
  let A := normalizedPartition (pinVertex tau v anchor) G z / (w anchor : ℂ)
  have hA : A ≠ 0 := div_ne_zero hchild (hwne anchor)
  have heq : normalizedPartition tau G z = A * hardParentSum w (tau.boundaryCount G v) L z := by
    rw [normalizedPartition_pinVertex_recursion, hardParentSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [hexp c, hbase c, hbase anchor]
    dsimp only [A]
    field_simp [hwne c, hwne anchor, hchild]
  rw [heq]
  exact mul_ne_zero hA hsum

/-- An anchor-free version suited to induction: every child is nonzero
and every ordered pair has its normalized small response logarithm. The
root's hard-allowed anchor is obtained from the actual graph. -/
theorem hard_parent_nonzero_of_pairwise_child_logs
    (tau : PartialColouring V C) (G : SimpleGraph V) (v : tau.FreeVertex)
    {Δ : ℕ} (hdegree : ∀ u, G.degree u ≤ Δ) (hcolours : Δ + 1 ≤ Fintype.card C)
    (z : ℂ) (hchild : ∀ c, normalizedPartition (pinVertex tau v c) G z ≠ 0)
    (L : C → C → ℂ) (hdiag : ∀ a, L a a = 0)
    (hexp : ∀ a c, Complex.exp (L a c) =
      (normalizedPartition (pinVertex tau v c) G z /
        normalizedPartition (pinVertex tau v c) G 0) /
      (normalizedPartition (pinVertex tau v a) G z /
        normalizedPartition (pinVertex tau v a) G 0))
    (hL : ∀ a c, ‖L a c‖ ≤ (1 / 4 : ℝ)) (hz : ‖z‖ ≤ 1)
    (hsmall : (4 / 3 : ℝ) * Fintype.card C * (Fintype.card C : ℝ) ^ Δ * ‖z‖ < 1) :
    normalizedPartition tau G z ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_zero_root_boundary tau G v hdegree hcolours
  exact hard_parent_nonzero_of_child_logs tau G v hdegree hcolours a ha z
    (hchild a) (L a) (hdiag a) (hexp a) (hL a) hz hsmall

end Potts
end
end ZeroFreeness
