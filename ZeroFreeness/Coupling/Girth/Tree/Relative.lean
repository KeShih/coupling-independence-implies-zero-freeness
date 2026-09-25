import ZeroFreeness.Coupling.Girth.Tree.Decay

/-!
# Relative error at the root

The root unary weight cancels inside the logarithmic ratio. The resulting
`5/3` Lipschitz coefficient needs only cavity coordinates at most `1/4`
and the root denominator at least three.
-/

namespace ZeroFreeness.Appendix.Girth

open scoped BigOperators
open Finset Set PottsCI

set_option linter.unusedSectionVars false

noncomputable section

private theorem log_lipschitz_ordered {a u v : ℝ} (ha : 0 < a)
    (hu : a ≤ u) (huv : u < v) :
    Real.log v - Real.log u ≤ (v - u) / a := by
  have hu0 : 0 < u := ha.trans_le hu
  obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_slope Real.log (fun t => t⁻¹) huv
    (fun t ht => (Real.continuousAt_log (by linarith [ht.1])).continuousWithinAt)
    (fun t ht => Real.hasDerivAt_log (by linarith [ht.1]))
  have hc0 : 0 < c := hu0.trans hc.1
  have hinv : c⁻¹ ≤ a⁻¹ := inv_anti₀ ha (hu.trans hc.1.le)
  have he := (eq_div_iff (sub_pos.mpr huv).ne').mp hd
  calc
    _ = c⁻¹ * (v - u) := he.symm
    _ ≤ a⁻¹ * (v - u) := mul_le_mul_of_nonneg_right hinv (sub_nonneg.mpr huv.le)
    _ = _ := by ring

theorem log_lipschitz_lower {a u v : ℝ} (ha : 0 < a) (hu : a ≤ u) (hv : a ≤ v) :
    |Real.log u - Real.log v| ≤ |u - v| / a := by
  rcases lt_trichotomy u v with huv | huv | huv
  · have hlog := Real.log_le_log (ha.trans_le hu) huv.le
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), abs_of_nonpos (sub_nonpos.mpr huv.le)]
    simpa only [neg_sub] using log_lipschitz_ordered ha hu huv
  · simp only [huv, sub_self, abs_zero, zero_div, le_refl]
  · have hlog := Real.log_le_log (ha.trans_le hv) huv.le
    rw [abs_of_nonneg (sub_nonneg.mpr hlog), abs_of_nonneg (sub_nonneg.mpr huv.le)]
    exact log_lipschitz_ordered ha hv huv

theorem product_lipschitz {E : Type*} (s : Finset E) (f g : E → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) (hg : ∀ i ∈ s, 0 ≤ g i ∧ g i ≤ 1) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤ ∑ i ∈ s, |f i - g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hgi := hg i (Finset.mem_insert_self _ _)
    have hfs := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hgs := fun j hj => hg j (Finset.mem_insert_of_mem hj)
    have hpg0 : 0 ≤ ∏ j ∈ s, g j := Finset.prod_nonneg fun j hj => (hgs j hj).1
    have hpg1 : (∏ j ∈ s, g j) ≤ 1 := Finset.prod_le_one
      (fun j hj => (hgs j hj).1) (fun j hj => (hgs j hj).2)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    calc
      _ = |f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) +
          (f i - g i) * ∏ j ∈ s, g j| := by congr 1; ring
      _ ≤ |f i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j)| +
          |(f i - g i) * ∏ j ∈ s, g j| := abs_add_le _ _
      _ = f i * |(∏ j ∈ s, f j) - ∏ j ∈ s, g j| +
          |f i - g i| * ∏ j ∈ s, g j := by rw [abs_mul, abs_mul, abs_of_nonneg hfi.1, abs_of_nonneg hpg0]
      _ ≤ (∑ j ∈ s, |f j - g j|) + |f i - g i| := add_le_add
        ((mul_le_of_le_one_left (abs_nonneg _) hfi.2).trans (ih hfs hgs))
        (mul_le_of_le_one_right (abs_nonneg _) hpg1)
      _ = _ := add_comm _ _

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

theorem messagePartition_lipschitz (a : C → ℝ) (m n : D → C → ℝ)
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ 1)
    (hn : ∀ i c, 0 ≤ n i c ∧ n i c ≤ 1) :
    |messagePartition a m - messagePartition a n| ≤ ∑ i, ∑ c, |m i c - n i c| := by
  have hpoint (c : C) : |messageWeight a m c - messageWeight a n c| ≤
      ∑ i, |m i c - n i c| := by
    have hp := product_lipschitz (Finset.univ : Finset D)
      (fun i => 1 - m i c) (fun i => 1 - n i c)
      (fun i _ => ⟨by linarith [(hm i c).2], by linarith [(hm i c).1]⟩)
      (fun i _ => ⟨by linarith [(hn i c).2], by linarith [(hn i c).1]⟩)
    have he (i : D) : |(1 - m i c) - (1 - n i c)| = |m i c - n i c| := by
      rw [show (1 - m i c) - (1 - n i c) = -(m i c - n i c) by ring, abs_neg]
    simp_rw [he] at hp
    unfold messageWeight
    rw [← mul_sub, abs_mul, abs_of_nonneg (ha c).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (ha c).2).trans hp
  unfold messagePartition
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, |messageWeight a m c - messageWeight a n c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, ∑ i, |m i c - n i c| := Finset.sum_le_sum fun c _ => hpoint c
    _ = _ := Finset.sum_comm

theorem log_messageMarginal (a : C → ℝ) (m : D → C → ℝ)
    (ha : ∀ c, 0 < a c) (hm : ∀ i c, m i c < 1)
    (hZ : 0 < messagePartition a m) (c : C) :
    Real.log (messageMarginal a m c) = Real.log (a c) +
      (∑ i, Real.log (1 - m i c)) - Real.log (messagePartition a m) := by
  have hp : 0 < ∏ i, (1 - m i c) := Finset.prod_pos fun i _ => sub_pos.mpr (hm i c)
  rw [messageMarginal, messageWeight, Real.log_div (mul_pos (ha c) hp).ne' hZ.ne',
    Real.log_mul (ha c).ne' hp.ne',
    Real.log_prod (fun i _ => (sub_pos.mpr (hm i c)).ne')]

/-- Relative root control with no lower bound on any unary colour weight. -/
theorem relative_root_bound (a : C → ℝ) (m n : D → C → ℝ)
    (ha : ∀ c, 0 < a c ∧ a c ≤ 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ 1 / 4)
    (hn : ∀ i c, 0 ≤ n i c ∧ n i c ≤ 1 / 4)
    (hZm : 3 ≤ messagePartition a m) (hZn : 3 ≤ messagePartition a n) (c : C) :
    |Real.log (messageMarginal a m c / messageMarginal a n c)| ≤
      (5 / 3 : ℝ) * ∑ i, ∑ b, |m i b - n i b| := by
  let H : ℝ := ∑ i, ∑ b, |m i b - n i b|
  have hm1 := fun i b => show m i b < 1 by linarith [(hm i b).2]
  have hn1 := fun i b => show n i b < 1 by linarith [(hn i b).2]
  have hmpos := messageMarginal_pos (fun b => (ha b).1) hm1 (by linarith : 0 < messagePartition a m) c
  have hnpos := messageMarginal_pos (fun b => (ha b).1) hn1 (by linarith : 0 < messagePartition a n) c
  have hlog (i : D) : |Real.log (1 - m i c) - Real.log (1 - n i c)| ≤
      (4 / 3 : ℝ) * |m i c - n i c| := by
    have h := log_lipschitz_lower (by norm_num : (0 : ℝ) < 3 / 4)
      (show 3 / 4 ≤ 1 - m i c by linarith [(hm i c).2])
      (show 3 / 4 ≤ 1 - n i c by linarith [(hn i c).2])
    have he : |(1 - m i c) - (1 - n i c)| = |m i c - n i c| := by
      rw [show (1 - m i c) - (1 - n i c) = -(m i c - n i c) by ring, abs_neg]
    rw [he] at h
    convert h using 1
    ring
  have hsum : (∑ i, |m i c - n i c|) ≤ H := Finset.sum_le_sum fun i _ =>
    Finset.single_le_sum (fun b _ => abs_nonneg (m i b - n i b)) (Finset.mem_univ c)
  have hlogsum : |(∑ i, Real.log (1 - m i c)) - ∑ i, Real.log (1 - n i c)| ≤
      (4 / 3 : ℝ) * H := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i, |Real.log (1 - m i c) - Real.log (1 - n i c)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (4 / 3 : ℝ) * |m i c - n i c| := Finset.sum_le_sum fun i _ => hlog i
      _ ≤ (4 / 3 : ℝ) * H := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsum (by norm_num)
  have hZlog : |Real.log (messagePartition a n) - Real.log (messagePartition a m)| ≤ H / 3 := by
    have h := log_lipschitz_lower (by norm_num : (0 : ℝ) < 3) hZn hZm
    have hp := messagePartition_lipschitz a m n (fun b => ⟨(ha b).1.le, (ha b).2⟩)
      (fun i b => ⟨(hm i b).1, (hm1 i b).le⟩) (fun i b => ⟨(hn i b).1, (hn1 i b).le⟩)
    rw [abs_sub_comm (messagePartition a n)] at h
    exact h.trans (div_le_div_of_nonneg_right hp (by norm_num))
  rw [Real.log_div hmpos.ne' hnpos.ne',
    log_messageMarginal a m (fun b => (ha b).1) hm1 (by linarith),
    log_messageMarginal a n (fun b => (ha b).1) hn1 (by linarith)]
  have he : (Real.log (a c) + (∑ i, Real.log (1 - m i c)) - Real.log (messagePartition a m)) -
      (Real.log (a c) + (∑ i, Real.log (1 - n i c)) - Real.log (messagePartition a n)) =
      ((∑ i, Real.log (1 - m i c)) - ∑ i, Real.log (1 - n i c)) +
        (Real.log (messagePartition a n) - Real.log (messagePartition a m)) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith [hlogsum, hZlog])

end

end ZeroFreeness.Appendix.Girth
