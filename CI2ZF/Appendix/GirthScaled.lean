import CI2ZF.Appendix.GirthPotential

/-!
# Scaling the output message

The chain-rule row factor for `m = s p` lies in `[0,1]`; consequently
the actual soft-message differential retains the uniform weighted bound.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

noncomputable section

def scaledRowFactor (s p : ℝ) : ℝ := Real.sqrt s * (1 - p) / (1 - s * p)

theorem scaledRowFactor_mem {s p : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hp : 0 ≤ p) (hp1 : p < 1) : scaledRowFactor s p ∈ Set.Icc (0 : ℝ) 1 := by
  have hsp : s * p < 1 := (mul_le_of_le_one_left hp hs1).trans_lt hp1
  have hsq : Real.sqrt s ≤ 1 := by nlinarith [Real.sq_sqrt hs, Real.sqrt_nonneg s]
  constructor
  · exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) (by linarith)
  · apply (div_le_one (show 0 < 1 - s * p by linarith)).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hsq)
      (show 0 ≤ 1 + Real.sqrt s * p by positivity)
    nlinarith [Real.sq_sqrt hs]

theorem scaled_potential_derivative {s p : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hp : 0 < p) (hp1 : p < 1) :
    (1 / (Real.sqrt (s * p) * (1 - s * p))) * s =
      scaledRowFactor s p * (1 / (Real.sqrt p * (1 - p))) := by
  have hsp : s * p < 1 := (mul_le_of_le_one_left hp.le hs1).trans_lt hp1
  have hrs : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hrp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  unfold scaledRowFactor
  rw [Real.sqrt_mul hs.le]
  field_simp [hrs.ne', hrp.ne', show 1 - p ≠ 0 by linarith,
    show 1 - s * p ≠ 0 by linarith]
  nlinarith [Real.sq_sqrt hs.le]

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

theorem hasDerivAt_scaled_transformed_message (a : C → ℝ) (m : ℝ → D → C → ℝ)
    (h : D → C → ℝ) (t : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hm : ∀ i c, HasDerivAt (fun u => m u i c)
      ((1 - m t i c) * (Real.sqrt (m t i c) * h i c)) t)
    (hw : ∀ c, 0 ≤ messageWeight a (m t) c)
    (hZ : 0 < messagePartition a (m t))
    (hp : ∀ c, 0 < messageMarginal a (m t) c ∧ messageMarginal a (m t) c < 1)
    (c : C) :
    HasDerivAt (fun u => messagePotential (s * messageMarginal a (m u) c))
      (scaledRowFactor s (messageMarginal a (m t) c) *
        blockAction (messageLaw a (m t) hw hZ) (m t) h c) t := by
  have hd := hasDerivAt_messageMarginal a m h t hm hZ.ne' c
  have hds := (hasDerivAt_messagePotential (mul_pos hs (hp c).1)
    ((mul_le_of_le_one_left (hp c).1.le hs1).trans_lt (hp c).2)).comp t (hd.const_mul s)
  have hdu := hasDerivAt_transformed_message a m h t hm hw hZ hp c
  have hbase := (hasDerivAt_messagePotential (hp c).1 (hp c).2).comp t hd
  change HasDerivAt (fun u => messagePotential (messageMarginal a (m u) c)) _ t at hbase
  have he := hbase.unique hdu
  apply hds.congr_deriv
  rw [← he, ← mul_assoc,
    scaled_potential_derivative hs hs1 (hp c).1 (hp c).2, mul_assoc]

/-- Scaling never increases the weighted squared differential energy. -/
theorem LocalRecursion.weighted_scaled_matrix_contraction (I : LocalRecursion C D)
    (h : D → C → ℝ) {s q T : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hq : I.palette ≤ q) (hT : 0 ≤ T)
    (hh : ∀ i, (∑ c, h i c ^ 2) ≤ T * (1 - I.childEntropy i)) :
    (1 / (1 - I.parentEntropy)) *
      (∑ c, (scaledRowFactor s (I.law.w c) * blockAction I.law I.input h c) ^ 2) ≤
      Real.exp (-8 / (81 * q)) * T := by
  apply le_trans _ (I.weighted_matrix_contraction h hq hT hh)
  apply mul_le_mul_of_nonneg_left _ I.parent_weight_nonneg
  apply Finset.sum_le_sum
  intro c _
  rw [mul_pow]
  apply mul_le_of_le_one_left (sq_nonneg _)
  have hf := scaledRowFactor_mem hs hs1 (I.law.nonneg c) (I.law_lt_one c)
  nlinarith [hf.1, hf.2]

end

end CI2ZF.Appendix.Girth
