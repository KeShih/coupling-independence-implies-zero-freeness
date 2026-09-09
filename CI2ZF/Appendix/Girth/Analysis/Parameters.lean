import CI2ZF.Appendix.Girth.Analysis.Entropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Uniform local parameters for the large-girth proof

The parameter inequalities below retain the strict `8/(81 A)` margin.
The child count is a natural number; the palette mass is real, as required
for soft activities and interpolation messages.
-/

namespace CI2ZF.Appendix.Girth

open Set

noncomputable section

def messageXi (d : ℕ) (A : ℝ) : ℝ :=
  Real.exp ((4 * d / (A - 1)) * Real.log (4 / 3))

def messageOddsBound (d : ℕ) (A : ℝ) : ℝ := messageXi d A / (A - 1)

def messageCap (d : ℕ) (A : ℝ) : ℝ :=
  messageOddsBound d A / (1 + messageOddsBound d A)

theorem log_four_thirds_bounds : (1 / 4 : ℝ) ≤ Real.log (4 / 3) ∧
    Real.log (4 / 3) ≤ 1 / 3 := by
  constructor
  · have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at h ⊢
    exact h
  · have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at h ⊢
    exact h

private def capCertificate (t : ℝ) : ℝ :=
  Real.log ((t + 3) / 3) - (4 * t / (t + 3)) * Real.log (4 / 3)

private theorem capCertificate_derivative {t : ℝ} (ht : 1 ≤ t) :
    HasDerivAt capCertificate
      ((t + 3 - 12 * Real.log (4 / 3)) / (t + 3) ^ 2) t := by
  have hden : t + 3 ≠ 0 := by linarith
  have hlog := (((hasDerivAt_id t).add_const 3).div_const 3).log
    (by positivity : (t + 3) / 3 ≠ 0)
  have hrat := (((hasDerivAt_id t).const_mul 4).div ((hasDerivAt_id t).add_const 3) hden).mul_const
    (Real.log (4 / 3))
  have hd := hlog.sub hrat
  change HasDerivAt capCertificate
    ((1 / 3) / ((t + 3) / 3) -
      ((4 * 1 * (t + 3) - (4 * t) * 1) / (t + 3) ^ 2) * Real.log (4 / 3)) t at hd
  apply hd.congr_deriv
  field_simp
  ring

private theorem capCertificate_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ capCertificate t := by
  have hmon := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (1 : ℝ))
    (fun x hx => (capCertificate_derivative hx).continuousAt.continuousWithinAt)
    (fun x hx => (capCertificate_derivative (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => show 0 ≤ (x + 3 - 12 * Real.log (4 / 3)) / (x + 3) ^ 2 from
      div_nonneg (by have h := log_four_thirds_bounds.2; have hx' : (1 : ℝ) ≤ x := interior_subset hx; linarith)
        (sq_nonneg _))
  have hz : capCertificate 1 = 0 := by norm_num [capCertificate]
  have h := hmon (show (1 : ℝ) ∈ Ici 1 by norm_num) ht ht
  simpa only [hz] using h

theorem messageOddsBound_pos {d : ℕ} {A : ℝ} (hA : (d : ℝ) + 4 ≤ A) :
    0 < messageOddsBound d A := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  exact div_pos (Real.exp_pos _) (by linarith)

/-- The quarter-cap proof uses the actual integer child count, including
the exceptional zero-child case. -/
theorem messageOddsBound_le_third {d : ℕ} {A : ℝ} (hA : (d : ℝ) + 4 ≤ A) :
    messageOddsBound d A ≤ 1 / 3 := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hA1 : 0 < A - 1 := by linarith
  by_cases hd0 : d = 0
  · subst d
    unfold messageOddsBound messageXi
    simp only [Nat.cast_zero, mul_zero, zero_div, zero_mul, Real.exp_zero]
    apply (div_le_iff₀ hA1).mpr
    norm_num at hA
    linarith
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd0
    have hcap := capCertificate_nonneg hd1
    unfold capCertificate at hcap
    have hc : Real.exp ((4 * (d : ℝ) / (d + 3)) * Real.log (4 / 3)) ≤ (d + 3) / 3 := by
      have h := Real.exp_le_exp.mpr (show (4 * (d : ℝ) / (d + 3)) * Real.log (4 / 3) ≤
        Real.log ((d + 3) / 3) by linarith)
      rw [Real.exp_log (by positivity)] at h
      exact h
    have hL : 0 ≤ Real.log (4 / 3) := le_trans (by norm_num) log_four_thirds_bounds.1
    have hdiv := div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hd) hL)
      (show (0 : ℝ) < d + 3 by positivity) (show (d : ℝ) + 3 ≤ A - 1 by linarith)
    have he : messageXi d A ≤ Real.exp ((4 * (d : ℝ) / (d + 3)) * Real.log (4 / 3)) := by
      apply Real.exp_le_exp.mpr
      simpa only [div_mul_eq_mul_div] using hdiv
    unfold messageOddsBound
    apply (div_le_iff₀ hA1).mpr
    have hh := he.trans hc
    linarith

theorem messageCap_bounds {d : ℕ} {A : ℝ} (hA : (d : ℝ) + 4 ≤ A) :
    0 < messageCap d A ∧ messageCap d A ≤ 1 / 4 := by
  have hy0 := messageOddsBound_pos hA
  have hy1 := messageOddsBound_le_third hA
  unfold messageCap
  constructor
  · exact div_pos hy0 (by linarith)
  · apply (div_le_iff₀ (show 0 < 1 + messageOddsBound d A by linarith)).mpr
    linarith

theorem messageCap_eq_paper_formula {d : ℕ} {A : ℝ} (hA : (d : ℝ) + 4 ≤ A) :
    messageCap d A = messageXi d A / (A - 1 + messageXi d A) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hA1 : A - 1 ≠ 0 := by linarith
  unfold messageCap messageOddsBound
  field_simp

theorem cap_log_eq_entropy {d : ℕ} {A : ℝ} (hA : (d : ℝ) + 4 ≤ A) :
    -Real.log (1 - messageCap d A) / messageCap d A =
      entropyCorrection (messageOddsBound d A) + 1 := by
  let y := messageOddsBound d A
  have hy : 0 < y := messageOddsBound_pos hA
  have hid : 1 - y / (1 + y) = (1 + y)⁻¹ := by field_simp; ring
  change -Real.log (1 - y / (1 + y)) / (y / (1 + y)) = entropyCorrection y + 1
  rw [hid, Real.log_inv]
  unfold entropyCorrection
  field_simp
  ring

/-- This is the bound responsible for the strict contraction margin. -/
theorem messageXi_palette_ratio_le {d : ℕ} {A : ℝ} (hA : (d : ℝ) + 4 ≤ A) :
    messageXi d A * (A / (A - 1)) ≤ 256 / 81 := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hA1 : 0 < A - 1 := by linarith
  have hL : 0 ≤ Real.log (4 / 3) := le_trans (by norm_num) log_four_thirds_bounds.1
  have hexponent : (4 * (d : ℝ) / (A - 1)) * Real.log (4 / 3) ≤
      4 * Real.log (4 / 3) - 12 * Real.log (4 / 3) / (A - 1) := by
    calc
      _ = (d : ℝ) * (4 * Real.log (4 / 3) / (A - 1)) := by ring
      _ ≤ (A - 4) * (4 * Real.log (4 / 3) / (A - 1)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  have hratio : A / (A - 1) ≤ Real.exp (12 * Real.log (4 / 3) / (A - 1)) := by
    calc
      A / (A - 1) = 1 / (A - 1) + 1 := by field_simp; ring
      _ ≤ Real.exp (1 / (A - 1)) := Real.add_one_le_exp _
      _ ≤ Real.exp (12 * Real.log (4 / 3) / (A - 1)) := by
        apply Real.exp_le_exp.mpr
        apply div_le_div_of_nonneg_right _ hA1.le
        have h := log_four_thirds_bounds.1
        linarith
  have hpow : Real.exp (4 * Real.log (4 / 3)) = (256 / 81 : ℝ) := by
    have h := Real.exp_nat_mul (Real.log (4 / 3)) 4
    norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)] at h
    exact h
  calc
    _ ≤ Real.exp (4 * Real.log (4 / 3) - 12 * Real.log (4 / 3) / (A - 1)) *
        Real.exp (12 * Real.log (4 / 3) / (A - 1)) :=
      mul_le_mul (Real.exp_le_exp.mpr hexponent) hratio
        (div_nonneg (by linarith) hA1.le) (Real.exp_pos _).le
    _ = Real.exp (4 * Real.log (4 / 3)) := by rw [← Real.exp_add]; congr 1; ring
    _ = 256 / 81 := hpow

theorem contraction_exponent_margin {d : ℕ} {A q : ℝ}
    (hA : (d : ℝ) + 4 ≤ A) (hAq : A ≤ q) :
    (5 / 2 : ℝ) * messageOddsBound d A - 8 / A ≤ -8 / (81 * q) := by
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hA0 : 0 < A := by linarith
  have hq0 : 0 < q := hA0.trans_le hAq
  have hratio := messageXi_palette_ratio_le hA
  have hyA : messageOddsBound d A * A ≤ 256 / 81 := by
    simpa only [messageOddsBound, div_mul_eq_mul_div, mul_div_assoc] using hratio
  have hy := (le_div_iff₀ hA0).mpr hyA
  have hfirst : (5 / 2 : ℝ) * messageOddsBound d A - 8 / A ≤ -8 / (81 * A) := by
    have hid : ((5 / 2 : ℝ) * messageOddsBound d A - 8 / A) * A =
        (5 / 2 : ℝ) * (messageOddsBound d A * A) - 8 := by
      field_simp
    calc
      _ ≤ (-8 / 81) / A := by
        apply (le_div_iff₀ hA0).mpr
        rw [hid]
        nlinarith [hyA]
      _ = _ := by ring
  have hmono : -8 / (81 * A) ≤ -8 / (81 * q) := by
    have hh := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 8)
      (show 0 < 81 * A by positivity) (show 81 * A ≤ 81 * q by nlinarith)
    simpa only [neg_div] using neg_le_neg hh
  exact hfirst.trans hmono

/-- The exponential amortization, retaining both copies of the four-unit
slack. The identity is valid for every real `S`; applications use the sum
of the children's entropy corrections. -/
theorem weighted_amortization {A d S y T : ℝ} (hA : 0 < A) (hd : d + 4 ≤ A)
    (hT : 0 ≤ T) :
    Real.exp (y / 2) * Real.exp (2 * y) *
      (Real.exp (-1 + (S + d) / A) / A) * (T * (d - S)) ≤
      Real.exp ((5 / 2 : ℝ) * y - 8 / A) * T := by
  have hlin : (d - S) / A ≤ 1 - (4 + S) / A := by
    apply (div_le_iff₀ hA).mpr
    have hid : (1 - (4 + S) / A) * A = A - (4 + S) := by field_simp
    rw [hid]
    linarith
  have hfactor : (d - S) / A ≤ Real.exp (-(4 + S) / A) := by
    have h := Real.add_one_le_exp (-(4 + S) / A)
    have hlin' : 1 - (4 + S) / A ≤ Real.exp (-(4 + S) / A) := by
      simpa only [neg_div, sub_eq_add_neg, add_comm] using h
    exact hlin.trans hlin'
  have hbase : -1 + d / A ≤ -(4 / A) := by
    have hd' : d / A ≤ (A - 4) / A := div_le_div_of_nonneg_right (by linarith) hA.le
    have hid : (A - 4) / A = 1 - 4 / A := by field_simp
    rw [hid] at hd'
    linarith
  calc
    _ = T * Real.exp ((5 / 2 : ℝ) * y - 1 + (S + d) / A) * ((d - S) / A) := by
      have he : Real.exp (y / 2) * Real.exp (2 * y) * Real.exp (-1 + (S + d) / A) =
          Real.exp ((5 / 2 : ℝ) * y - 1 + (S + d) / A) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = T * (Real.exp (y / 2) * Real.exp (2 * y) * Real.exp (-1 + (S + d) / A)) *
            ((d - S) / A) := by ring
        _ = _ := by rw [he]
    _ ≤ T * Real.exp ((5 / 2 : ℝ) * y - 1 + (S + d) / A) * Real.exp (-(4 + S) / A) :=
      mul_le_mul_of_nonneg_left hfactor (mul_nonneg hT (Real.exp_pos _).le)
    _ = T * Real.exp ((5 / 2 : ℝ) * y - 1 + d / A - 4 / A) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring
    _ ≤ T * Real.exp ((5 / 2 : ℝ) * y - 8 / A) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        rw [show 8 / A = 4 / A + 4 / A by ring]
        linarith)) hT
    _ = _ := mul_comm _ _

end

end CI2ZF.Appendix.Girth
