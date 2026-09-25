import ZeroFreeness.Coupling.Girth.Analysis.Differential
import Mathlib.Analysis.Convex.Deriv

/-!
# Convex interpolation in potential coordinates

The inverse potential is explicitly `(exp u - 1)^2 / (exp u + 1)^2`.
Its convexity on `[0, log 3]` proves that the full interpolation preserves
both the coordinate caps and the subdistribution mass bound.
-/

namespace ZeroFreeness.Appendix.Girth

open scoped BigOperators
open Finset Set

noncomputable section

def inversePotential (u : ℝ) : ℝ := ((Real.exp u - 1) / (Real.exp u + 1)) ^ 2

theorem inversePotential_nonneg (u : ℝ) : 0 ≤ inversePotential u := sq_nonneg _

theorem sqrt_inversePotential {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt (inversePotential u) = (Real.exp u - 1) / (Real.exp u + 1) := by
  unfold inversePotential
  rw [Real.sqrt_sq (div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu))
    (by positivity))]

theorem inversePotential_lt_one (u : ℝ) : inversePotential u < 1 := by
  unfold inversePotential
  rw [div_pow]
  apply (div_lt_one (sq_pos_of_pos (by positivity))).mpr
  nlinarith [Real.exp_pos u]

theorem inversePotential_messagePotential {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    inversePotential (messagePotential t) = t := by
  have hs1 : Real.sqrt t < 1 := by nlinarith [Real.sqrt_nonneg t, Real.sq_sqrt ht]
  have he : Real.exp (messagePotential t) = (1 + Real.sqrt t) / (1 - Real.sqrt t) := by
    rw [messagePotential, Real.exp_sub, Real.exp_log (by positivity),
      Real.exp_log (by linarith)]
  unfold inversePotential
  rw [he]
  have hratio : (((1 + Real.sqrt t) / (1 - Real.sqrt t) - 1) /
      ((1 + Real.sqrt t) / (1 - Real.sqrt t) + 1)) = Real.sqrt t := by
    field_simp [show 1 - Real.sqrt t ≠ 0 by linarith,
      show (1 + Real.sqrt t) / (1 - Real.sqrt t) + 1 ≠ 0 by positivity]
    ring
  rw [hratio, Real.sq_sqrt ht]

theorem messagePotential_inversePotential {u : ℝ} (hu : 0 ≤ u) :
    messagePotential (inversePotential u) = u := by
  have hp : 0 < Real.exp u + 1 := by positivity
  have hr : 1 - (Real.exp u - 1) / (Real.exp u + 1) = 2 / (Real.exp u + 1) := by
    field_simp
    ring
  have hs : 1 + (Real.exp u - 1) / (Real.exp u + 1) =
      2 * Real.exp u / (Real.exp u + 1) := by field_simp; ring
  rw [messagePotential, sqrt_inversePotential hu, hr, hs, ← Real.log_div
    (by positivity) (by positivity)]
  convert Real.log_exp u using 2
  field_simp

theorem messagePotential_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ messagePotential t := by
  rw [messagePotential_eq_artanh ht ht1]
  exact mul_nonneg (by norm_num) (Real.artanh_nonneg (Real.sqrt_nonneg _))

theorem messagePotential_quarter : messagePotential (1 / 4) = Real.log 3 := by
  have hs : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by norm_num
  rw [messagePotential, hs, ← Real.log_div (by norm_num) (by norm_num)]
  norm_num

theorem messagePotential_mono {t r : ℝ} (ht : 0 ≤ t) (htr : t ≤ r) (hr : r < 1) :
    messagePotential t ≤ messagePotential r := by
  rw [messagePotential_eq_artanh ht (htr.trans_lt hr),
    messagePotential_eq_artanh (ht.trans htr) hr]
  have hs1 : Real.sqrt r < 1 := by nlinarith [Real.sqrt_nonneg r, Real.sq_sqrt (ht.trans htr)]
  exact mul_le_mul_of_nonneg_left
    (Real.artanh_le_artanh (by linarith [Real.sqrt_nonneg t]) hs1 (Real.sqrt_le_sqrt htr))
    (by norm_num)

theorem messagePotential_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / 4)) :
    messagePotential t ∈ Icc (0 : ℝ) (Real.log 3) := by
  refine ⟨messagePotential_nonneg ht.1 (by linarith [ht.2]), ?_⟩
  rw [← messagePotential_quarter]
  exact messagePotential_mono ht.1 ht.2 (by norm_num)

def inversePotentialDeriv (u : ℝ) : ℝ :=
  4 * Real.exp u * (Real.exp u - 1) / (Real.exp u + 1) ^ 3

theorem hasDerivAt_inversePotential (u : ℝ) :
    HasDerivAt inversePotential (inversePotentialDeriv u) u := by
  have he := Real.hasDerivAt_exp u
  have hd := ((he.sub_const 1).div (he.add_const 1) (by positivity)).pow 2
  change HasDerivAt inversePotential _ u at hd
  apply hd.congr_deriv
  simp only [Pi.div_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  unfold inversePotentialDeriv
  field_simp [show Real.exp u + 1 ≠ 0 by positivity]
  ring

theorem hasDerivAt_inversePotentialDeriv (u : ℝ) :
    HasDerivAt inversePotentialDeriv
      (4 * Real.exp u * (-(Real.exp u) ^ 2 + 4 * Real.exp u - 1) /
        (Real.exp u + 1) ^ 4) u := by
  have he := Real.hasDerivAt_exp u
  have hd := (((he.const_mul 4).mul (he.sub_const 1)).div
    ((he.add_const 1).pow 3) (by change (Real.exp u + 1) ^ 3 ≠ 0; positivity))
  change HasDerivAt inversePotentialDeriv _ u at hd
  apply hd.congr_deriv
  simp only [Pi.pow_apply, Pi.mul_apply]
  field_simp
  ring

theorem inversePotential_deriv_formula {u : ℝ} (hu : 0 ≤ u) :
    inversePotentialDeriv u =
      (1 - inversePotential u) * Real.sqrt (inversePotential u) := by
  rw [sqrt_inversePotential hu]
  unfold inversePotentialDeriv inversePotential
  field_simp
  ring

theorem convexOn_inversePotential : ConvexOn ℝ (Icc 0 (Real.log 3)) inversePotential := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
    (fun u _ => (hasDerivAt_inversePotential u).continuousAt.continuousWithinAt)
    (fun u _ => (hasDerivAt_inversePotential u).hasDerivWithinAt)
    (fun u _ => (hasDerivAt_inversePotentialDeriv u).hasDerivWithinAt)
  intro u hu
  have hu' : u ∈ Icc 0 (Real.log 3) := interior_subset hu
  have hlo : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu'.1
  have hhi : Real.exp u ≤ 3 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3)] using Real.exp_le_exp.mpr hu'.2
  apply div_nonneg
  · apply mul_nonneg (by positivity)
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
  · positivity

theorem potential_interpolation_le {t r z : ℝ}
    (ht : t ∈ Icc (0 : ℝ) (1 / 4)) (hr : r ∈ Icc (0 : ℝ) (1 / 4))
    (hz : z ∈ Icc (0 : ℝ) 1) :
    inversePotential ((1 - z) * messagePotential t + z * messagePotential r) ≤
      (1 - z) * t + z * r := by
  have h := convexOn_inversePotential.2 (messagePotential_mem ht) (messagePotential_mem hr)
    (sub_nonneg.mpr hz.2) hz.1 (by ring : (1 - z) + z = 1)
  simpa only [smul_eq_mul, inversePotential_messagePotential ht.1 (by linarith [ht.2]),
    inversePotential_messagePotential hr.1 (by linarith [hr.2])] using h

variable {C : Type*} [Fintype C]

/-- The actual potential-coordinate segment stays in the sharp message
domain, including the closed faces where some input coordinates vanish. -/
theorem potential_interpolation_domain (m n : C → ℝ) {B s z : ℝ}
    (hm : ∀ c, 0 ≤ m c ∧ m c ≤ B) (hn : ∀ c, 0 ≤ n c ∧ n c ≤ B)
    (hB : B ≤ 1 / 4) (hms : ∑ c, m c ≤ s) (hns : ∑ c, n c ≤ s)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    (∀ c, 0 ≤ inversePotential ((1 - z) * messagePotential (m c) + z * messagePotential (n c)) ∧
      inversePotential ((1 - z) * messagePotential (m c) + z * messagePotential (n c)) ≤ B) ∧
    (∑ c, inversePotential ((1 - z) * messagePotential (m c) + z * messagePotential (n c))) ≤ s := by
  have hinterp (c : C) := potential_interpolation_le
    ⟨(hm c).1, (hm c).2.trans hB⟩ ⟨(hn c).1, (hn c).2.trans hB⟩ hz
  refine ⟨fun c => ⟨inversePotential_nonneg _, (hinterp c).trans ?_⟩, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left (hm c).2 (sub_nonneg.mpr hz.2),
      mul_le_mul_of_nonneg_left (hn c).2 hz.1]
  · have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hinterp c)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    nlinarith [mul_le_mul_of_nonneg_left hms (sub_nonneg.mpr hz.2),
      mul_le_mul_of_nonneg_left hns hz.1]

end

end ZeroFreeness.Appendix.Girth
