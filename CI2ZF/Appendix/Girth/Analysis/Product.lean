import CI2ZF.Appendix.Girth.Analysis.Messages
import Mathlib.Analysis.MeanInequalities

/-!
# Product and occupancy estimates for the weighted tree recursion

The product lower bound follows from concavity of log; the numerator bound
follows from the tangent inequality for exp. Weighted Jensen then gives the
actual normalizing denominator bound used in the amortized estimate.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset

noncomputable section

variable {C D : Type*} [Fintype C] [Fintype D]

theorem log_one_sub_chord {B y : ℝ} (hB0 : 0 < B) (hB1 : B < 1)
    (hy0 : 0 ≤ y) (hyB : y ≤ B) :
    (Real.log (1 - B) / B) * y ≤ Real.log (1 - y) := by
  have ht0 : 0 ≤ y / B := div_nonneg hy0 hB0.le
  have ht1 : y / B ≤ 1 := (div_le_one hB0).mpr hyB
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show 1 - B ∈ Set.Ioi 0 by simpa only [Set.mem_Ioi] using sub_pos.mpr hB1)
    (show 0 ≤ 1 - y / B by linarith) ht0 (by ring : 1 - y / B + y / B = 1)
  have hid : (1 - y / B) * 1 + (y / B) * (1 - B) = 1 - y := by
    field_simp
    ring
  simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add, hid] at h
  calc
    (Real.log (1 - B) / B) * y = (y / B) * Real.log (1 - B) := by ring
    _ ≤ Real.log (1 - y) := h

/-- The product inequality `hg-product-lemma`, with no positivity requirement
on individual occupancies and including an empty index type. -/
theorem product_lower_bound {B : ℝ} (hB0 : 0 < B) (hB1 : B < 1)
    (y : C → ℝ) (hy0 : ∀ c, 0 ≤ y c) (hyB : ∀ c, y c ≤ B)
    (hmass : ∑ c, y c ≤ 1) :
    (1 - B) ^ (1 / B) ≤ ∏ c, (1 - y c) := by
  have hpos (c : C) : 0 < 1 - y c := by linarith [hyB c]
  have hcoef : Real.log (1 - B) / B ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (by linarith) (by linarith)) hB0.le
  have hlog : Real.log (1 - B) / B ≤ ∑ c, Real.log (1 - y c) := by
    calc
      _ ≤ (Real.log (1 - B) / B) * ∑ c, y c := by nlinarith
      _ = ∑ c, (Real.log (1 - B) / B) * y c := Finset.mul_sum ..
      _ ≤ _ := Finset.sum_le_sum fun c _ => log_one_sub_chord hB0 hB1 (hy0 c) (hyB c)
  rw [Real.rpow_def_of_pos (sub_pos.mpr hB1)]
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sum] at he
  simp_rw [Real.exp_log (hpos _)] at he
  simpa only [mul_one_div] using he

theorem weighted_log_lower {B : ℝ} (hB0 : 0 < B) (hB1 : B < 1)
    (a y : C → ℝ) (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1)
    (hy0 : ∀ c, 0 ≤ y c) (hyB : ∀ c, y c ≤ B)
    (hmass : ∑ c, y c ≤ 1) :
    Real.log (1 - B) / B ≤ ∑ c, a c * Real.log (1 - y c) := by
  have hcoef : Real.log (1 - B) / B ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (Real.log_nonpos (by linarith) (by linarith)) hB0.le
  have hmass' : ∑ c, a c * y c ≤ 1 := by
    exact (Finset.sum_le_sum fun c _ =>
      (mul_le_mul_of_nonneg_right (ha c).2 (hy0 c)).trans_eq (one_mul _)).trans hmass
  calc
    _ ≤ (Real.log (1 - B) / B) * ∑ c, a c * y c := by nlinarith
    _ = ∑ c, a c * ((Real.log (1 - B) / B) * y c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ _ := Finset.sum_le_sum fun c _ =>
      mul_le_mul_of_nonneg_left (log_one_sub_chord hB0 hB1 (hy0 c) (hyB c)) (ha c).1

/-- Occupancy times exclusion probability has the universal `e⁻¹` bound. -/
theorem occupancy_numerator_le (y : D → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    (∑ i, y i) * (∏ i, (1 - y i)) ≤ Real.exp (-1) := by
  have hs : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ => (hy i).1
  have hp : (∏ i, (1 - y i)) ≤ Real.exp (-(∑ i, y i)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro i _
      exact sub_nonneg.mpr (hy i).2
    · intro i _
      have h := Real.add_one_le_exp (-(y i))
      linarith
  have he : (∑ i, y i) ≤ Real.exp ((∑ i, y i) - 1) := by
    have h := Real.add_one_le_exp ((∑ i, y i) - 1)
    linarith
  calc
    _ ≤ (∑ i, y i) * Real.exp (-(∑ i, y i)) := mul_le_mul_of_nonneg_left hp hs
    _ ≤ Real.exp ((∑ i, y i) - 1) * Real.exp (-(∑ i, y i)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = Real.exp (-1) := by rw [← Real.exp_add]; congr 1; ring

/-- Jensen's inequality gives a quantitative lower bound for the actual
weighted Potts recursion denominator with nonidentical child caps. -/
theorem weighted_messagePartition_lower (a : C → ℝ) (m : D → C → ℝ) (B : D → ℝ)
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA : 0 < ∑ c, a c)
    (hB : ∀ i, 0 < B i ∧ B i < 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ B i)
    (hmass : ∀ i, ∑ c, m i c ≤ 1) :
    (∑ c, a c) * Real.exp ((∑ i, Real.log (1 - B i) / B i) / (∑ c, a c)) ≤
      messagePartition a m := by
  let A : ℝ := ∑ c, a c
  let z : C → ℝ := fun c => ∏ i, (1 - m i c)
  have hz (c : C) : 0 < z c := Finset.prod_pos fun i _ => by
    have hb := (hB i).2
    have hmi := (hm i c).2
    linarith
  have hw : ∀ c ∈ (Finset.univ : Finset C), 0 ≤ a c / A :=
    fun c _ => div_nonneg (ha c).1 hA.le
  have hw1 : ∑ c, a c / A = 1 := by rw [← Finset.sum_div]; exact div_self hA.ne'
  have hj := convexOn_exp.map_sum_le hw hw1
    (fun c _ => show Real.log (z c) ∈ Set.univ from Set.mem_univ _)
  simp only [smul_eq_mul] at hj
  simp_rw [Real.exp_log (hz _)] at hj
  have hl : (∑ i, Real.log (1 - B i) / B i) / A ≤ ∑ c, (a c / A) * Real.log (z c) := by
    have hinner (i : D) := weighted_log_lower (hB i).1 (hB i).2 a (m i) ha
      (fun c => (hm i c).1) (fun c => (hm i c).2) (hmass i)
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun i _ => hinner i)
    have hdiv := div_le_div_of_nonneg_right hsum hA.le
    have hid : (∑ i, ∑ c, a c * Real.log (1 - m i c)) / A =
        ∑ c, (a c / A) * Real.log (z c) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      dsimp [z]
      rw [Real.log_prod (fun i _ => (show 0 < 1 - m i c by linarith [(hm i c).2, (hB i).2]).ne'),
        ← Finset.mul_sum]
      ring
    exact hdiv.trans_eq hid
  have he := (Real.exp_le_exp.mpr hl).trans hj
  have hmul := mul_le_mul_of_nonneg_left he hA.le
  calc
    _ ≤ A * ∑ c, (a c / A) * z c := hmul
    _ = messagePartition a m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      change A * (a c / A * z c) = a c * z c
      field_simp [show A ≠ 0 from hA.ne']

/-- Replacing the actual palette mass by a positive certified lower bound
preserves the exponential lower bound. -/
theorem weighted_messagePartition_lower_of_palette_bound
    (a : C → ℝ) (m : D → C → ℝ) (B : D → ℝ) {A : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA0 : 0 < A) (hA : A ≤ ∑ c, a c)
    (hB : ∀ i, 0 < B i ∧ B i < 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ B i)
    (hmass : ∀ i, ∑ c, m i c ≤ 1) :
    A * Real.exp (-(∑ i, -Real.log (1 - B i) / B i) / A) ≤
      messagePartition a m := by
  let H : ℝ := ∑ i, -Real.log (1 - B i) / B i
  have hH : 0 ≤ H := Finset.sum_nonneg fun i _ =>
    div_nonneg (neg_nonneg.mpr (Real.log_nonpos (by linarith [(hB i).2])
      (by linarith [(hB i).1]))) (hB i).1.le
  have hsum : (∑ i, Real.log (1 - B i) / B i) = -H := by
    simp only [H, neg_div, Finset.sum_neg_distrib, neg_neg]
  have hden := weighted_messagePartition_lower a m B ha (hA0.trans_le hA) hB hm hmass
  rw [hsum] at hden
  have hratio := div_le_div_of_nonneg_left hH hA0 hA
  have he : Real.exp (-H / A) ≤ Real.exp (-H / (∑ c, a c)) :=
    Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hratio)
  exact (mul_le_mul hA he (Real.exp_pos _).le (hA0.trans_le hA).le).trans hden

/-- The complete occupancy-factor bound, expressed directly in the child
coordinate caps. Substitution of `ζ_i + 1 = -log(1-B_i)/B_i` gives the
displayed amortized estimate of the large-girth appendix. -/
theorem message_occupancy_bound
    (a : C → ℝ) (m : D → C → ℝ) (B : D → ℝ) {A : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA0 : 0 < A) (hA : A ≤ ∑ c, a c)
    (hB : ∀ i, 0 < B i ∧ B i < 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ B i)
    (hmass : ∀ i, ∑ c, m i c ≤ 1) (c : C) :
    messageMarginal a m c * (∑ i, m i c) ≤
      Real.exp (-1 + (∑ i, -Real.log (1 - B i) / B i) / A) / A := by
  let H : ℝ := ∑ i, -Real.log (1 - B i) / B i
  have hlow := weighted_messagePartition_lower_of_palette_bound a m B ha hA0 hA hB hm hmass
  have hlpos : 0 < A * Real.exp (-H / A) := mul_pos hA0 (Real.exp_pos _)
  have hZ : 0 < messagePartition a m := hlpos.trans_le hlow
  have hm1 : ∀ i, 0 ≤ m i c ∧ m i c ≤ 1 :=
    fun i => ⟨(hm i c).1, (hm i c).2.trans (hB i).2.le⟩
  have hnum := occupancy_numerator_le (fun i => m i c) hm1
  have hn0 : 0 ≤ (∑ i, m i c) * ∏ i, (1 - m i c) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => (hm i c).1)
      (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hm1 i).2)
  have hnum' : messageWeight a m c * (∑ i, m i c) ≤ Real.exp (-1) := by
    have hmul := mul_le_mul_of_nonneg_right (ha c).2 hn0
    calc
      _ = a c * ((∑ i, m i c) * ∏ i, (1 - m i c)) := by unfold messageWeight; ring
      _ ≤ 1 * ((∑ i, m i c) * ∏ i, (1 - m i c)) := hmul
      _ ≤ Real.exp (-1) := by simpa using hnum
  have he : 1 / Real.exp (-H / A) = Real.exp (H / A) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  calc
    messageMarginal a m c * (∑ i, m i c) =
        (messageWeight a m c * (∑ i, m i c)) / messagePartition a m := by
      unfold messageMarginal
      ring
    _ ≤ Real.exp (-1) / messagePartition a m := div_le_div_of_nonneg_right hnum' hZ.le
    _ ≤ Real.exp (-1) / (A * Real.exp (-H / A)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hlpos hlow
    _ = (Real.exp (-1) / A) * (1 / Real.exp (-H / A)) := by ring
    _ = Real.exp (-1 + H / A) / A := by rw [he, Real.exp_add]; ring

end

end CI2ZF.Appendix.Girth
