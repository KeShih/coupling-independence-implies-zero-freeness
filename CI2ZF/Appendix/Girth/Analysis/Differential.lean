import CI2ZF.Appendix.Girth.Analysis.Contraction
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Differentiating the actual tree recursion

The potential is the logarithmic expression for `2 artanh √t`. The
directional derivative below is obtained from the normalized product
recursion, and is identified with `blockAction`.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

set_option linter.unusedSectionVars false

noncomputable section

def messagePotential (t : ℝ) : ℝ :=
  Real.log (1 + Real.sqrt t) - Real.log (1 - Real.sqrt t)

theorem messagePotential_eq_artanh {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    messagePotential t = 2 * Real.artanh (Real.sqrt t) := by
  have hs0 := Real.sqrt_nonneg t
  have hs1 : Real.sqrt t < 1 := by
    nlinarith [Real.sq_sqrt ht]
  rw [Real.artanh_eq_half_log (by constructor <;> linarith),
    Real.log_div (by linarith) (by linarith)]
  unfold messagePotential
  ring

theorem hasDerivAt_messagePotential {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt messagePotential (1 / (Real.sqrt t * (1 - t))) t := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs1 : Real.sqrt t < 1 := by
    nlinarith [Real.sq_sqrt ht.le]
  have hd := (((Real.hasDerivAt_sqrt ht.ne').const_add 1).log
      (show 1 + Real.sqrt t ≠ 0 by linarith)).sub
    (((Real.hasDerivAt_sqrt ht.ne').const_sub 1).log
      (show 1 - Real.sqrt t ≠ 0 by linarith))
  change HasDerivAt messagePotential _ t at hd
  apply hd.congr_deriv
  field_simp [hs0.ne', show 1 + Real.sqrt t ≠ 0 by linarith,
    show 1 - Real.sqrt t ≠ 0 by linarith, show 1 - t ≠ 0 by linarith]
  nlinarith [Real.sq_sqrt ht.le]

/-- Product differentiation in multiplicative logarithmic-derivative form. -/
theorem hasDerivAt_product_logarithmic {E : Type*} (s : Finset E)
    (f : E → ℝ → ℝ) (v : E → ℝ) (t : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (f i) (f i t * v i) t) :
    HasDerivAt (fun u => ∏ i ∈ s, f i u)
      ((∏ i ∈ s, f i t) * ∑ i ∈ s, v i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const t (1 : ℝ)
  | @insert i s hi ih =>
    have hi' := h i (Finset.mem_insert_self _ _)
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have hd := hi'.mul hs
    change HasDerivAt (fun u => f i u * ∏ j ∈ s, f j u) _ t at hd
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact hd.congr_deriv (by ring)

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

theorem hasDerivAt_messageWeight (a : C → ℝ) (m : ℝ → D → C → ℝ)
    (h : D → C → ℝ) (t : ℝ)
    (hm : ∀ i c, HasDerivAt (fun u => m u i c)
      ((1 - m t i c) * (Real.sqrt (m t i c) * h i c)) t) (c : C) :
    HasDerivAt (fun u => messageWeight a (m u) c)
      (messageWeight a (m t) c * (-∑ i, Real.sqrt (m t i c) * h i c)) t := by
  have hd := hasDerivAt_product_logarithmic (Finset.univ : Finset D)
    (fun i u => 1 - m u i c) (fun i => -(Real.sqrt (m t i c) * h i c)) t
    (fun i _ => (hm i c).const_sub 1 |>.congr_deriv (by ring))
  simpa [messageWeight, Finset.sum_neg_distrib, mul_assoc] using hd.const_mul (a c)

theorem hasDerivAt_messageMarginal (a : C → ℝ) (m : ℝ → D → C → ℝ)
    (h : D → C → ℝ) (t : ℝ)
    (hm : ∀ i c, HasDerivAt (fun u => m u i c)
      ((1 - m t i c) * (Real.sqrt (m t i c) * h i c)) t)
    (hZ : messagePartition a (m t) ≠ 0) (c : C) :
    HasDerivAt (fun u => messageMarginal a (m u) c)
      (messageMarginal a (m t) c *
        ((∑ b, messageMarginal a (m t) b * ∑ i, Real.sqrt (m t i b) * h i b) -
          ∑ i, Real.sqrt (m t i c) * h i c)) t := by
  have hdw := hasDerivAt_messageWeight a m h t hm
  have hdZ := HasDerivAt.fun_sum (u := (Finset.univ : Finset C)) (fun b _ => hdw b)
  have hd := (hdw c).div hdZ hZ
  change HasDerivAt (fun u => messageMarginal a (m u) c) _ t at hd
  apply hd.congr_deriv
  simp only [messageMarginal, mul_neg, Finset.sum_neg_distrib]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  unfold messagePartition at hZ ⊢
  field_simp
  ring

theorem hasDerivAt_transformed_message (a : C → ℝ) (m : ℝ → D → C → ℝ)
    (h : D → C → ℝ) (t : ℝ)
    (hm : ∀ i c, HasDerivAt (fun u => m u i c)
      ((1 - m t i c) * (Real.sqrt (m t i c) * h i c)) t)
    (hw : ∀ c, 0 ≤ messageWeight a (m t) c)
    (hZ : 0 < messagePartition a (m t))
    (hp : ∀ c, 0 < messageMarginal a (m t) c ∧ messageMarginal a (m t) c < 1)
    (c : C) :
    HasDerivAt (fun u => messagePotential (messageMarginal a (m u) c))
      (blockAction (messageLaw a (m t) hw hZ) (m t) h c) t := by
  let p := messageLaw a (m t) hw hZ
  have hd := (hasDerivAt_messagePotential (hp c).1 (hp c).2).comp t
    (hasDerivAt_messageMarginal a m h t hm hZ.ne' c)
  have hs : 0 < Real.sqrt (p.w c) := Real.sqrt_pos.mpr (hp c).1
  have hs2 : Real.sqrt (p.w c) ^ 2 = p.w c := Real.sq_sqrt (hp c).1.le
  have hb : blockAction p (m t) h c =
      (Real.sqrt (p.w c) / (1 - p.w c)) *
        ((∑ b, p.w b * ∑ i, Real.sqrt (m t i b) * h i b) -
          ∑ i, Real.sqrt (m t i c) * h i c) := by
    unfold blockAction transformedBlock potentialDiagonal
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 2
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
  apply hd.congr_deriv
  change 1 / (Real.sqrt (p.w c) * (1 - p.w c)) *
    (p.w c * ((∑ b, p.w b * ∑ i, Real.sqrt (m t i b) * h i b) -
      ∑ i, Real.sqrt (m t i c) * h i c)) =
    blockAction p (m t) h c
  rw [hb]
  field_simp [hs.ne', show 1 - p.w c ≠ 0 from (sub_pos.mpr (hp c).2).ne']
  rw [hs2]

end

end CI2ZF.Appendix.Girth
