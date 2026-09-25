import ZeroFreeness.Potts.Transfer.PositiveParent
import ZeroFreeness.Potts.Transfer.HardParent
import ZeroFreeness.Potts.Model.OptionPartition
import ZeroFreeness.Potts.Transfer.ExteriorHardComparison

/-! The parent nonvanishing step for arbitrary actual pinning data with
a distinguished root. Every recursion and hard weight comparison is
derived from the model. -/
namespace ZeroFreeness.Potts
open PottsCI Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {O C : Type*} [Fintype O] [Fintype C]

theorem option_child_partition_ofReal (I : PinningData (Option O) C) (a : C) (x : ℝ) :
    pinningProductPartition (optionChildData I a) (x : ℂ) =
      (((optionChildData I a).partition x : ℝ) : ℂ) := by
  rw [← pinningPolynomial_eval, pinningPolynomial_ofReal]

theorem option_positive_parent_nonzero_of_child_logs [Nonempty C]
    (I : PinningData (Option O) C) (anchor : C) {x : ℝ} (hx : 0 < x) (z : ℂ)
    (hchild : pinningProductPartition (optionChildData I anchor) z ≠ 0)
    (g L : C → ℂ)
    (hg : ∀ c, Complex.exp (g c) =
      z ^ I.boundaryCount none c / (x : ℂ) ^ I.boundaryCount none c)
    (hL : ∀ c, Complex.exp (L c) =
      (pinningProductPartition (optionChildData I c) z /
        pinningProductPartition (optionChildData I c) (x : ℂ)) /
      (pinningProductPartition (optionChildData I anchor) z /
        pinningProductPartition (optionChildData I anchor) (x : ℂ)))
    (hbound : ∀ c, ‖g c + L c‖ ≤ (1 / 4 : ℝ)) :
    pinningProductPartition I z ≠ 0 := by
  let Z (c : C) : ℝ := (optionChildData I c).partition x
  have hZ (c : C) : 0 < Z c := PinningData.partition_pos_of_parameter_pos _ hx
  have hbase (c : C) : pinningProductPartition (optionChildData I c) (x : ℂ) =
      (Z c : ℂ) := option_child_partition_ofReal I c x
  have hZne (c : C) : (Z c : ℂ) ≠ 0 := by exact_mod_cast (hZ c).ne'
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  let A := pinningProductPartition (optionChildData I anchor) z / (Z anchor : ℂ)
  let R (c : C) := (z ^ I.boundaryCount none c / (x : ℂ) ^ I.boundaryCount none c) *
    (pinningProductPartition (optionChildData I c) z / (Z c : ℂ))
  let w (c : C) : ℝ := x ^ I.boundaryCount none c * Z c
  have hexp (c : C) : Complex.exp (g c + L c) = R c / A := by
    rw [Complex.exp_add, hg c, hL c, hbase c, hbase anchor]
    dsimp [R, A]
    ring
  have hn := weighted_response_sum_ne_zero w (fun c => mul_pos (pow_pos hx _) (hZ c)) R A
    (div_ne_zero hchild (hZne anchor)) (fun c => g c + L c) hexp hbound
  rw [option_parent_partition]
  convert hn using 1
  apply Finset.sum_congr rfl
  intro c _
  dsimp [w, R]
  push_cast
  field_simp [hZne c]

/-- The budgets supplied by the uniform boundary logarithm and the
child-response induction fit the actual positive parent step. -/
theorem option_positive_parent_nonzero_of_pairwise_child_logs [Nonempty C]
    (I : PinningData (Option O) C) {x : ℝ} (hx : 0 < x) (z : ℂ)
    {alpha : ℝ} (ha : alpha ≤ (1 / 8 : ℝ))
    (hchild : ∀ a, pinningProductPartition (optionChildData I a) z ≠ 0)
    (g : C → ℂ)
    (hg : ∀ c, Complex.exp (g c) =
      z ^ I.boundaryCount none c / (x : ℂ) ^ I.boundaryCount none c)
    (hgbound : ∀ c, ‖g c‖ ≤ alpha / 8)
    (hlogs : ∀ a b, ∃ L : ℂ,
      Complex.exp L =
        (pinningProductPartition (optionChildData I a) z /
          pinningProductPartition (optionChildData I a) (x : ℂ)) /
        (pinningProductPartition (optionChildData I b) z /
          pinningProductPartition (optionChildData I b) (x : ℂ)) ∧ ‖L‖ ≤ alpha) :
    pinningProductPartition I z ≠ 0 := by
  let anchor : C := Classical.arbitrary C
  choose L hexp hnorm using fun a => hlogs a anchor
  apply option_positive_parent_nonzero_of_child_logs I anchor hx z (hchild anchor) g L hg hexp
  intro c
  exact (norm_add_le _ _).trans (by linarith [hgbound c, hnorm c])

theorem option_exists_zero_root_boundary (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) :
    ∃ a : C, I.boundaryCount none a = 0 := by
  have hc := card_hardList_of_succ_le I hd hq none
  have hn : (I.hardList none).Nonempty := by
    rw [← Finset.card_pos]
    omega
  obtain ⟨a, ha⟩ := hn
  exact ⟨a, (Finset.mem_filter.mp ha).2⟩

theorem option_hard_parent_nonzero_of_child_logs
    (I : PinningData (Option O) C) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (anchor : C)
    (hm : I.boundaryCount none anchor = 0) (z : ℂ)
    (hchild : pinningProductPartition (optionChildData I anchor) z ≠ 0)
    (L : C → ℂ) (hanchor : L anchor = 0)
    (hexp : ∀ c, Complex.exp (L c) =
      (pinningProductPartition (optionChildData I c) z /
        pinningProductPartition (optionChildData I c) (0 : ℂ)) /
      (pinningProductPartition (optionChildData I anchor) z /
        pinningProductPartition (optionChildData I anchor) (0 : ℂ)))
    (hL : ∀ c, ‖L c‖ ≤ (1 / 4 : ℝ)) (hz : ‖z‖ ≤ 1)
    (hsmall : (4 / 3 : ℝ) * Fintype.card C * (Fintype.card C : ℝ) ^ Δ * ‖z‖ < 1) :
    pinningProductPartition I z ≠ 0 := by
  let : Nonempty C := ⟨anchor⟩
  let w (c : C) : ℝ := (optionChildData I c).partition 0
  have hw (c : C) : 0 < w c := partition_zero_pos_of_succ_le
    (optionChildData I c) (optionChildData_degreeBound I hd c) hq
  have hbase (c : C) : pinningProductPartition (optionChildData I c) (0 : ℂ) =
      (w c : ℂ) := option_child_partition_ofReal I c 0
  have hwne (c : C) : (w c : ℂ) ≠ 0 := by exact_mod_cast (hw c).ne'
  have hweight (c : C) : w c ≤ (Fintype.card C : ℝ) ^ Δ * w anchor :=
    optionChildData_zero_comparison I hd hq c anchor
  have hsum := hardParentSum_ne_zero w hw (I.boundaryCount none) L anchor hm hanchor
    (pow_nonneg (Nat.cast_nonneg _) _) hweight hL z hz hsmall
  let A := pinningProductPartition (optionChildData I anchor) z / (w anchor : ℂ)
  have hA : A ≠ 0 := div_ne_zero hchild (hwne anchor)
  have heq : pinningProductPartition I z =
      A * hardParentSum w (I.boundaryCount none) L z := by
    rw [option_parent_partition, hardParentSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [hexp c, hbase c, hbase anchor]
    dsimp only [A]
    field_simp [hwne c, hwne anchor, hchild]
  rw [heq]
  exact mul_ne_zero hA hsum

/-- Pairwise child logs need no prescribed diagonal: the actual
hard-allowed anchor is selected from the root list and its log is zero. -/
theorem option_hard_parent_nonzero_of_pairwise_child_logs
    (I : PinningData (Option O) C) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (z : ℂ) {alpha : ℝ}
    (ha : alpha ≤ (1 / 8 : ℝ))
    (hchild : ∀ c, pinningProductPartition (optionChildData I c) z ≠ 0)
    (hlogs : ∀ a b, ∃ L : ℂ,
      Complex.exp L =
        (pinningProductPartition (optionChildData I a) z /
          pinningProductPartition (optionChildData I a) (0 : ℂ)) /
        (pinningProductPartition (optionChildData I b) z /
          pinningProductPartition (optionChildData I b) (0 : ℂ)) ∧ ‖L‖ ≤ alpha)
    (hz : ‖z‖ ≤ 1)
    (hsmall : (4 / 3 : ℝ) * Fintype.card C * (Fintype.card C : ℝ) ^ Δ * ‖z‖ < 1) :
    pinningProductPartition I z ≠ 0 := by
  obtain ⟨anchor, hm⟩ := option_exists_zero_root_boundary I hd hq
  let : Nonempty C := ⟨anchor⟩
  choose L hexp hnorm using fun c => hlogs c anchor
  let L' (c : C) : ℂ := if c = anchor then 0 else L c
  have hbase : pinningProductPartition (optionChildData I anchor) (0 : ℂ) ≠ 0 := by
    have he := option_child_partition_ofReal I anchor 0
    simp only [Complex.ofReal_zero] at he
    rw [he]
    exact_mod_cast (partition_zero_pos_of_succ_le (optionChildData I anchor)
      (optionChildData_degreeBound I hd anchor) hq).ne'
  apply option_hard_parent_nonzero_of_child_logs I hd hq anchor hm z
    (hchild anchor) L' (by simp [L']) _ _ hz hsmall
  · intro c
    by_cases hc : c = anchor
    · subst c
      simp [L', div_ne_zero (hchild anchor) hbase]
    · simpa only [L', hc, if_false] using hexp c
  · intro c
    by_cases hc : c = anchor
    · simp [L', hc]
    · simp only [L', hc, if_false]
      linarith [hnorm c]

end
end ZeroFreeness.Potts
