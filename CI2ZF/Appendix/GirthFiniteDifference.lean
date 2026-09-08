import CI2ZF.Appendix.GirthScaled

/-!
# Finite differences for the actual soft tree recursion

The argument uses a scalar mean-value theorem and Cauchy--Schwarz, after
proving that the entire potential-coordinate segment stays admissible.
There is no assumed Jacobian estimate or finite-difference premise.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset Set PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

/-- A finite-dimensional mean-value energy estimate without a loss in the
number of coordinates. -/
theorem finite_curve_energy (f df : ℝ → C → ℝ) {W K : ℝ}
    (hW : 0 ≤ W) (hK : 0 ≤ K)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, ∀ c, HasDerivAt (fun u => f u c) (df t c) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, W * (∑ c, df t c ^ 2) ≤ K) :
    W * (∑ c, (f 1 c - f 0 c) ^ 2) ≤ K := by
  let v : C → ℝ := fun c => f 1 c - f 0 c
  let E : ℝ := ∑ c, v c ^ 2
  let g : ℝ → ℝ := fun t => ∑ c, v c * f t c
  let dg : ℝ → ℝ := fun t => ∑ c, v c * df t c
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (dg t) t :=
    HasDerivAt.fun_sum fun c _ => (hd t ht c).const_mul (v c)
  obtain ⟨t, ht, hmean⟩ := exists_hasDerivAt_eq_slope g dg (by norm_num : (0 : ℝ) < 1)
    (fun z hz => (hg z hz).continuousAt.continuousWithinAt)
    (fun z hz => hg z (Ioo_subset_Icc_self hz))
  have hgdiff : g 1 - g 0 = E := by
    change (∑ c, v c * f 1 c) - (∑ c, v c * f 0 c) = ∑ c, v c ^ 2
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    dsimp [v]
    ring
  have hmean' : dg t = E := by simpa only [hgdiff, sub_zero, div_one] using hmean
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C) v (df t)
  change dg t ^ 2 ≤ E * ∑ c, df t c ^ 2 at hcs
  rw [hmean'] at hcs
  have hE : 0 ≤ E := Finset.sum_nonneg fun c _ => sq_nonneg _
  change W * E ≤ K
  by_cases he : E = 0
  · simpa only [he, mul_zero] using hK
  · have hep : 0 < E := lt_of_le_of_ne hE (Ne.symm he)
    have h1 := mul_le_mul_of_nonneg_left hcs hW
    have h2 := mul_le_mul_of_nonneg_left (hb t (Ioo_subset_Icc_self ht)) hE
    have hh : E * (W * E) ≤ E * K := by nlinarith
    exact (mul_le_mul_iff_right₀ hep).mp (by simpa only [mul_comm E] using hh)

def potentialSegment (m n : D → C → ℝ) (z : ℝ) (i : D) (c : C) : ℝ :=
  inversePotential ((1 - z) * messagePotential (m i c) + z * messagePotential (n i c))

theorem potentialSegment_zero (m n : D → C → ℝ)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c < 1) : potentialSegment m n 0 = m := by
  funext i c
  simp only [potentialSegment, sub_zero, one_mul, zero_mul, add_zero,
    inversePotential_messagePotential (hm i c).1 (hm i c).2]

theorem potentialSegment_one (m n : D → C → ℝ)
    (hn : ∀ i c, 0 ≤ n i c ∧ n i c < 1) : potentialSegment m n 1 = n := by
  funext i c
  simp only [potentialSegment, sub_self, zero_mul, one_mul, zero_add,
    inversePotential_messagePotential (hn i c).1 (hn i c).2]

theorem hasDerivAt_potentialSegment (m n : D → C → ℝ)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c < 1)
    (hn : ∀ i c, 0 ≤ n i c ∧ n i c < 1)
    {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1) (i : D) (c : C) :
    HasDerivAt (fun u => potentialSegment m n u i c)
      ((1 - potentialSegment m n z i c) *
        (Real.sqrt (potentialSegment m n z i c) *
          (messagePotential (n i c) - messagePotential (m i c)))) z := by
  let a := messagePotential (m i c)
  let b := messagePotential (n i c)
  have ha : 0 ≤ a := messagePotential_nonneg (hm i c).1 (hm i c).2
  have hb : 0 ≤ b := messagePotential_nonneg (hn i c).1 (hn i c).2
  have hu : 0 ≤ (1 - z) * a + z * b :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hz.2) ha) (mul_nonneg hz.1 hb)
  have hdinner := (((hasDerivAt_id z).const_sub 1).mul_const a).add
    ((hasDerivAt_id z).mul_const b)
  have hd := (hasDerivAt_inversePotential ((1 - z) * a + z * b)).comp z hdinner
  change HasDerivAt (fun u => potentialSegment m n u i c) _ z at hd
  apply hd.congr_deriv
  rw [inversePotential_deriv_formula hu]
  change (1 - potentialSegment m n z i c) * Real.sqrt (potentialSegment m n z i c) *
    (-1 * a + 1 * b) = _
  ring

namespace LocalRecursion

variable (I : LocalRecursion C D) (n : D → C → ℝ)
  (hn0 : ∀ i c, 0 ≤ n i c)
  (hncap : ∀ i c, n i c ≤ messageCap (I.childDegree i) (I.childPalette i))
  (hnmass : ∀ i, ∑ c, n i c ≤ 1)

def interpolate (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : LocalRecursion C D where
  unary := I.unary
  unary_pos := I.unary_pos
  unary_le_one := I.unary_le_one
  input := potentialSegment I.input n z
  childDegree := I.childDegree
  childPalette := I.childPalette
  child_slack := I.child_slack
  input_nonneg := fun _ _ => inversePotential_nonneg _
  input_cap := fun i c =>
    ((potential_interpolation_domain (I.input i) (n i)
      (fun c => ⟨I.input_nonneg i c, I.input_cap i c⟩)
      (fun c => ⟨hn0 i c, hncap i c⟩) (messageCap_bounds (I.child_slack i)).2
      (I.input_mass i) (hnmass i) hz).1 c).2
  input_mass := fun i =>
    (potential_interpolation_domain (I.input i) (n i)
      (fun c => ⟨I.input_nonneg i c, I.input_cap i c⟩)
      (fun c => ⟨hn0 i c, hncap i c⟩) (messageCap_bounds (I.child_slack i)).2
      (I.input_mass i) (hnmass i) hz).2
  palette := I.palette
  palette_lower := I.palette_lower
  parent_slack := I.parent_slack

include hn0 hncap hnmass in
/-- The appendix's finite-difference bound, stated in squared weighted
energy form with a simultaneous child energy budget `T`. -/
theorem weighted_finite_difference {s q T : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hq : I.palette ≤ q) (hT : 0 ≤ T)
    (hh : ∀ i, (∑ c, (messagePotential (n i c) - messagePotential (I.input i c)) ^ 2) ≤
      T * (1 - I.childEntropy i)) :
    (1 / (1 - I.parentEntropy)) *
      (∑ c, (messagePotential (s * messageMarginal I.unary n c) -
        messagePotential (s * I.law.w c)) ^ 2) ≤ Real.exp (-8 / (81 * q)) * T := by
  let h : D → C → ℝ := fun i c => messagePotential (n i c) - messagePotential (I.input i c)
  let m : ℝ → D → C → ℝ := potentialSegment I.input n
  let f : ℝ → C → ℝ := fun z c => messagePotential (s * messageMarginal I.unary (m z) c)
  have hmr : ∀ i c, 0 ≤ I.input i c ∧ I.input i c < 1 :=
    fun i c => ⟨I.input_nonneg i c, by linarith [I.input_quarter i c]⟩
  have hnr : ∀ i c, 0 ≤ n i c ∧ n i c < 1 := fun i c =>
    ⟨hn0 i c, (hncap i c).trans_lt ((messageCap_bounds (I.child_slack i)).2.trans_lt (by norm_num))⟩
  have hmder (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (i : D) (c : C) :
      HasDerivAt (fun u => m u i c)
        ((1 - m z i c) * (Real.sqrt (m z i c) * h i c)) z :=
    hasDerivAt_potentialSegment I.input n hmr hnr hz i c
  let df : ℝ → C → ℝ := fun z c => deriv (fun u => f u c) z
  have hd (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) (c : C) :
      HasDerivAt (fun u => f u c) (df z c) z := by
    let J := I.interpolate n hn0 hncap hnmass z hz
    have hw : ∀ c, 0 ≤ messageWeight I.unary (m z) c := fun c =>
      messageWeight_nonneg (fun b => (I.unary_pos b).le)
        (fun i b => by change J.input i b ≤ 1; linarith [J.input_quarter i b]) c
    have hdz := hasDerivAt_scaled_transformed_message I.unary m h z hs hs1 (hmder z hz)
      hw J.partition_pos (fun c => ⟨J.law_pos c, J.law_lt_one c⟩) c
    exact hdz.differentiableAt.hasDerivAt
  have hb (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      (1 / (1 - I.parentEntropy)) * (∑ c, df z c ^ 2) ≤
        Real.exp (-8 / (81 * q)) * T := by
    let J := I.interpolate n hn0 hncap hnmass z hz
    have hw : ∀ c, 0 ≤ messageWeight I.unary (m z) c := fun c =>
      messageWeight_nonneg (fun b => (I.unary_pos b).le)
        (fun i b => by change J.input i b ≤ 1; linarith [J.input_quarter i b]) c
    have hid (c : C) : df z c = scaledRowFactor s (J.law.w c) * blockAction J.law J.input h c :=
      (hasDerivAt_scaled_transformed_message I.unary m h z hs hs1 (hmder z hz)
        hw J.partition_pos (fun c => ⟨J.law_pos c, J.law_lt_one c⟩) c).deriv
    simp_rw [hid]
    exact J.weighted_scaled_matrix_contraction h hs.le hs1 hq hT hh
  have hcurve := finite_curve_energy f df I.parent_weight_nonneg
    (mul_nonneg (Real.exp_pos _).le hT) hd hb
  simpa only [f, m, potentialSegment_zero I.input n hmr, potentialSegment_one I.input n hnr,
    law, messageLaw_apply] using hcurve

end LocalRecursion

end

end CI2ZF.Appendix.Girth
