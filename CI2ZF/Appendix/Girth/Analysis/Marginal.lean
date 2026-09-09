import CI2ZF.Appendix.Girth.Analysis.Product
import CI2ZF.Appendix.Girth.Analysis.Parameters

/-!
# The sharp local marginal estimate

This proves `hg-continuous-marginal` from the actual finite tree recursion.
The deleted-colour normalizer is bounded by weighted Jensen, so the odds
bound is derived from the weight sum rather than assumed.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset

noncomputable section

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

theorem sum_excluding_eq (f : C → ℝ) (c : C) :
    (∑ b : {b : C // b ≠ c}, f b.1) = (∑ b, f b) - f c := by
  have h := Fintype.sum_eq_add_sum_subtype_ne f c
  linarith

theorem quarter_log_loss : -Real.log (1 - (1 / 4 : ℝ)) / (1 / 4 : ℝ) =
    4 * Real.log (4 / 3) := by
  have h := Real.log_inv (4 / 3 : ℝ)
  norm_num at h ⊢
  rw [h]
  ring

/-- The full pointwise marginal lemma for weighted subdistribution inputs. -/
theorem sharp_message_marginal (a : C → ℝ) (m : D → C → ℝ) {A : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA : A ≤ ∑ c, a c)
    (hslack : (Fintype.card D : ℝ) + 4 ≤ A)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ 1 / 4)
    (hmass : ∀ i, ∑ c, m i c ≤ 1) (c : C) :
    0 ≤ messageMarginal a m c ∧ messageMarginal a m c < 1 ∧
      messageMarginal a m c / (1 - messageMarginal a m c) ≤
        messageOddsBound (Fintype.card D) A ∧
      messageMarginal a m c ≤ messageCap (Fintype.card D) A := by
  let offA : {b : C // b ≠ c} → ℝ := fun b => a b.1
  let offM : D → {b : C // b ≠ c} → ℝ := fun i b => m i b.1
  let offZ : ℝ := messagePartition offA offM
  have hd : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  have hA1 : 0 < A - 1 := by linarith
  have hmass' (i : D) : ∑ b : {b : C // b ≠ c}, offM i b ≤ 1 := by
    rw [show (∑ b : {b : C // b ≠ c}, offM i b) =
      (∑ b : {b : C // b ≠ c}, m i b.1) from rfl, sum_excluding_eq]
    linarith [(hm i c).1, hmass i]
  have hpalette : A - 1 ≤ ∑ b : {b : C // b ≠ c}, offA b := by
    rw [show (∑ b : {b : C // b ≠ c}, offA b) =
      (∑ b : {b : C // b ≠ c}, a b.1) from rfl, sum_excluding_eq]
    linarith [(ha c).2]
  have hlow := weighted_messagePartition_lower_of_palette_bound offA offM
    (fun _ : D => (1 / 4 : ℝ)) (fun b => ha b.1) hA1 hpalette
    (fun _ => by norm_num) (fun i b => hm i b.1) hmass'
  have hsum : (∑ _i : D, -Real.log (1 - (1 / 4 : ℝ)) / (1 / 4 : ℝ)) =
      4 * (Fintype.card D : ℝ) * Real.log (4 / 3) := by
    rw [quarter_log_loss]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hsum] at hlow
  have hlow' : (A - 1) * Real.exp (-(4 * (Fintype.card D : ℝ) * Real.log (4 / 3)) / (A - 1)) ≤
      offZ := hlow
  have hlowpos : 0 < (A - 1) *
      Real.exp (-(4 * (Fintype.card D : ℝ) * Real.log (4 / 3)) / (A - 1)) :=
    mul_pos hA1 (Real.exp_pos _)
  have hoffpos : 0 < offZ := hlowpos.trans_le hlow'
  have hoff : offZ = messagePartition a m - messageWeight a m c := by
    change (∑ b : {b : C // b ≠ c}, messageWeight a m b.1) = _
    exact sum_excluding_eq (messageWeight a m) c
  have hw0 : 0 ≤ messageWeight a m c := messageWeight_nonneg (fun b => (ha b).1)
    (fun i b => by linarith [(hm i b).2]) c
  have hw1 : messageWeight a m c ≤ 1 := messageWeight_le_one ha
    (fun i b => ⟨(hm i b).1, by linarith [(hm i b).2]⟩) c
  have hZ : 0 < messagePartition a m := by linarith
  have hp0 : 0 ≤ messageMarginal a m c := div_nonneg hw0 hZ.le
  have hp1 : messageMarginal a m c < 1 := by
    apply (div_lt_one hZ).mpr
    linarith
  have hidentity : messageMarginal a m c / (1 - messageMarginal a m c) =
      messageWeight a m c / offZ := by
    unfold messageMarginal
    rw [hoff]
    field_simp
  have hrecip : 1 / ((A - 1) *
      Real.exp (-(4 * (Fintype.card D : ℝ) * Real.log (4 / 3)) / (A - 1))) =
      messageOddsBound (Fintype.card D) A := by
    have he : 1 / Real.exp (-(4 * (Fintype.card D : ℝ) * Real.log (4 / 3)) / (A - 1)) =
        messageXi (Fintype.card D) A := by
      rw [one_div, ← Real.exp_neg]
      unfold messageXi
      congr 1
      ring
    calc
      _ = (1 / Real.exp (-(4 * (Fintype.card D : ℝ) * Real.log (4 / 3)) / (A - 1))) /
          (A - 1) := by rw [one_div, mul_inv_rev]; ring
      _ = _ := by rw [he]; rfl
  have hodds : messageMarginal a m c / (1 - messageMarginal a m c) ≤
      messageOddsBound (Fintype.card D) A := by
    rw [hidentity]
    calc
      _ ≤ 1 / offZ := div_le_div_of_nonneg_right hw1 hoffpos.le
      _ ≤ 1 / ((A - 1) *
          Real.exp (-(4 * (Fintype.card D : ℝ) * Real.log (4 / 3)) / (A - 1))) :=
        div_le_div_of_nonneg_left zero_le_one hlowpos hlow'
      _ = _ := hrecip
  have hy0 := messageOddsBound_pos hslack
  refine ⟨hp0, hp1, hodds, ?_⟩
  unfold messageCap
  apply (le_div_iff₀ (show 0 < 1 + messageOddsBound (Fintype.card D) A by linarith)).mpr
  have hh := (div_le_iff₀ (sub_pos.mpr hp1)).mp hodds
  nlinarith

end

end CI2ZF.Appendix.Girth
