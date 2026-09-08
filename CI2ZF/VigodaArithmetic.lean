import PottsCI.Vigoda.ComponentCoupling
import Mathlib.Tactic

/-!
# Exact local arithmetic for the strict Vigoda coupling

This module proves local profile and charge inequalities from the actual
Vigoda profile. The two-neighbour certificate is checked by Lean's kernel
after a proved size truncation; it does not trust a Python run or add an axiom.
The graph-to-charge coupling construction is a separate theorem.
-/

namespace CI2ZF.VigodaArithmetic

open PottsCI.Vigoda

noncomputable section

lemma profile_zero_of_seven_le (r : ℕ) (hr : 7 ≤ r) : vigodaMass r = 0 := by
  match r with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | 4 => omega
  | 5 => omega
  | 6 => omega
  | _ + 7 => simp [vigodaMass]

lemma profile_nonsingleton_bound (r : ℕ) (hr : 2 ≤ r) :
    (r : ℝ) * vigodaMass r ≤ 13 / 21 := by
  by_cases hsmall : r ≤ 6
  · interval_cases r <;> norm_num [vigodaMass] at *
  · rw [profile_zero_of_seven_le r (by omega)]
    norm_num

lemma profile_large_component_bound (r : ℕ) (hr : 3 ≤ r) :
    (r : ℝ) * vigodaMass r ≤ 1 / 2 := by
  by_cases hsmall : r ≤ 6
  · interval_cases r <;> norm_num [vigodaMass] at *
  · rw [profile_zero_of_seven_le r (by omega)]
    norm_num

/-- The residual rate after matching a singleton-root extension. -/
def profileDiff (r : ℕ) : ℝ := vigodaMass r - vigodaMass (r + 1)

lemma profileDiff_nonneg (r : ℕ) (hr : 1 ≤ r) : 0 ≤ profileDiff r := by
  by_cases hsmall : r ≤ 6
  · interval_cases r <;> norm_num [profileDiff, vigodaMass] at *
  · have hlarge : 7 ≤ r := by omega
    simp [profileDiff, profile_zero_of_seven_le r hlarge,
      profile_zero_of_seven_le (r + 1) (by omega)]

lemma size_mul_profileDiff_le (r : ℕ) (hr : 1 ≤ r) :
    (r : ℝ) * profileDiff r ≤ 29 / 42 := by
  by_cases hsmall : r ≤ 6
  · interval_cases r <;> norm_num [profileDiff, vigodaMass] at *
  · have hlarge : 7 ≤ r := by omega
    norm_num [profileDiff, profile_zero_of_seven_le r hlarge,
      profile_zero_of_seven_le (r + 1) (by omega)]

lemma sub_one_mul_profileDiff_le (r : ℕ) (hr : 1 ≤ r) :
    ((r : ℝ) - 1) * profileDiff r ≤ 1 / 7 := by
  by_cases hsmall : r ≤ 6
  · interval_cases r <;> norm_num [profileDiff, vigodaMass] at *
  · have hlarge : 7 ≤ r := by omega
    simp [profileDiff, profile_zero_of_seven_le r hlarge,
      profile_zero_of_seven_le (r + 1) (by omega)]

/-- Size charges minus the guaranteed common-neighbour matching saving. -/
def pairCharge (r s : ℕ) (u w : ℝ) : ℝ := r * u + s * w - min u w

/-- The one-neighbour estimate holds throughout the residual-mass rectangle,
including blocked off-root moves. -/
theorem one_neighbour_box (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (u w : ℝ) (_hu0 : 0 ≤ u) (hur : u ≤ profileDiff r)
    (_hw0 : 0 ≤ w) (hws : w ≤ profileDiff s) : pairCharge r s u w ≤ 5 / 6 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hru : (r : ℝ) * u ≤ 29 / 42 :=
    (mul_le_mul_of_nonneg_left hur (by positivity)).trans (size_mul_profileDiff_le r hr)
  have hsw : (s : ℝ) * w ≤ 29 / 42 :=
    (mul_le_mul_of_nonneg_left hws (by positivity)).trans (size_mul_profileDiff_le s hs)
  have hrmu : ((r : ℝ) - 1) * u ≤ 1 / 7 :=
    (mul_le_mul_of_nonneg_left hur (by linarith)).trans (sub_one_mul_profileDiff_le r hr)
  have hsmw : ((s : ℝ) - 1) * w ≤ 1 / 7 :=
    (mul_le_mul_of_nonneg_left hws (by linarith)).trans (sub_one_mul_profileDiff_le s hs)
  unfold pairCharge
  rcases le_total u w with huw | hwu
  · rw [min_eq_left huw]
    nlinarith
  · rw [min_eq_right hwu]
    nlinarith

theorem root_colour_one_neighbour_bound (s : ℕ) :
    (s : ℝ) * vigodaMass s - ((s + 1 : ℕ) : ℝ) * vigodaMass (s + 1) ≤ 8 / 21 := by
  by_cases hsmall : s ≤ 6
  · interval_cases s <;> norm_num [vigodaMass]
  · have hlarge : 7 ≤ s := by omega
    norm_num [profile_zero_of_seven_le s hlarge,
      profile_zero_of_seven_le (s + 1) (by omega)]

/-! ## Kernel-checked two-neighbour arithmetic at scale 84 -/

/-- The exact profile in integer units of `1 / 84`. -/
def scaledP : ℕ → ℤ
  | 1 => 84
  | 2 => 26
  | 3 => 14
  | 4 => 8
  | 5 => 4
  | 6 => 1
  | _ => 0

lemma scaledP_zero_of_seven_le (r : ℕ) (hr : 7 ≤ r) : scaledP r = 0 := by
  match r with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | 3 => omega
  | 4 => omega
  | 5 => omega
  | 6 => omega
  | _ + 7 => simp [scaledP]

lemma scaledP_eq_profile (r : ℕ) : (scaledP r : ℝ) = 84 * vigodaMass r := by
  by_cases hsmall : r ≤ 6
  · interval_cases r <;> norm_num [scaledP, vigodaMass]
  · rw [scaledP_zero_of_seven_le r (by omega), profile_zero_of_seven_le r (by omega)]
    norm_num

/-- One two-component family, after its root-to-largest-component match.
The root move is feasible iff both off-root moves are feasible; the new root
colour is assumed available, as in the exceptional regular-colour case. -/
structure FamilyCharge where
  rootCost : ℤ
  firstResidual : ℤ
  secondResidual : ℤ
  firstCost : ℤ
  secondCost : ℤ
  deriving DecidableEq

def familyCharge (r s : ℕ) (f g : Bool) : FamilyCharge :=
  let P := if f && g then scaledP (1 + r + s) else 0
  let u := (if f then scaledP r else 0) - (if s ≤ r then P else 0)
  let w := (if g then scaledP s else 0) - (if r < s then P else 0)
  { rootCost := (min r s : ℕ) * P
    firstResidual := u
    secondResidual := w
    firstCost := (r : ℤ) * u
    secondCost := (s : ℤ) * w }

/-- The exact regular-colour charge for two distinct off-root components on
each side, including both root matches and the two residual matches. -/
def twoNeighbourScaledCharge (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : ℤ :=
  let a := familyCharge r₁ r₂ f₁ f₂
  let b := familyCharge s₁ s₂ g₁ g₂
  a.rootCost + b.rootCost + a.firstCost + a.secondCost + b.firstCost + b.secondCost -
    min a.firstResidual b.firstResidual - min a.secondResidual b.secondResidual

/-- Capping a zero-rate component at seven preserves its whole charge
record. In particular, a new tie caused by capping has zero root mass. -/
theorem familyCharge_cap (r s : ℕ) (f g : Bool) :
    familyCharge (min r 7) (min s 7) f g = familyCharge r s f g := by
  by_cases hr : r ≤ 7 <;> by_cases hs : s ≤ 7
  · rw [Nat.min_eq_left hr, Nat.min_eq_left hs]
  · have hs7 : 7 ≤ s := by omega
    have hroot : scaledP (1 + r + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    have hroot' : scaledP (1 + r + 7) = 0 := scaledP_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_left hr, Nat.min_eq_right hs7, familyCharge,
      hroot, hroot', scaledP_zero_of_seven_le s hs7, show scaledP 7 = 0 from rfl]
    simp
  · have hr7 : 7 ≤ r := by omega
    have hroot : scaledP (1 + r + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    have hroot' : scaledP (1 + 7 + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_left hs, Nat.min_eq_right hr7, familyCharge,
      hroot, hroot', scaledP_zero_of_seven_le r hr7, show scaledP 7 = 0 from rfl]
    simp
  · have hr7 : 7 ≤ r := by omega
    have hs7 : 7 ≤ s := by omega
    have hroot : scaledP (1 + r + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_right hr7, Nat.min_eq_right hs7, familyCharge, hroot,
      scaledP_zero_of_seven_le r hr7, scaledP_zero_of_seven_le s hs7,
      show scaledP 7 = 0 from rfl, show scaledP (1 + 7 + 7) = 0 from rfl]
    simp

theorem twoNeighbourScaledCharge_cap (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) :
    twoNeighbourScaledCharge (min r₁ 7) (min r₂ 7) (min s₁ 7) (min s₂ 7) f₁ f₂ g₁ g₂ =
      twoNeighbourScaledCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  simp only [twoNeighbourScaledCharge, familyCharge_cap]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exhaust the 7^4 size records and 2^4 feasibility patterns. `decide`
produces a proof checked by Lean's kernel; no native evaluator is trusted. -/
theorem twoNeighbourScaledCharge_small
    (r₁ r₂ s₁ s₂ : Fin 7) (f₁ f₂ g₁ g₂ : Bool) :
    twoNeighbourScaledCharge (r₁.val + 1) (r₂.val + 1) (s₁.val + 1) (s₂.val + 1)
      f₁ f₂ g₁ g₂ ≤ 224 := by
  fin_cases r₁ <;> revert r₂ s₁ s₂ f₁ f₂ g₁ g₂ <;> decide

theorem twoNeighbourScaledCharge_le (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ : Bool) :
    twoNeighbourScaledCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 224 := by
  have h (r : ℕ) (hr : 1 ≤ r) : min r 7 - 1 + 1 = min r 7 := by omega
  let R₁ : Fin 7 := ⟨min r₁ 7 - 1, by omega⟩
  let R₂ : Fin 7 := ⟨min r₂ 7 - 1, by omega⟩
  let S₁ : Fin 7 := ⟨min s₁ 7 - 1, by omega⟩
  let S₂ : Fin 7 := ⟨min s₂ 7 - 1, by omega⟩
  have hc := twoNeighbourScaledCharge_small R₁ R₂ S₁ S₂ f₁ f₂ g₁ g₂
  dsimp [R₁, R₂, S₁, S₂] at hc
  rw [h r₁ hr₁, h r₂ hr₂, h s₁ hs₁, h s₂ hs₂, twoNeighbourScaledCharge_cap] at hc
  exact hc

/-- The real charge in the probability scale used by the paper. -/
def twoNeighbourCharge (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : ℝ :=
  (twoNeighbourScaledCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) / 84

theorem two_neighbour_distinct_bound (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ : Bool) :
    twoNeighbourCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 8 / 3 := by
  have hc : (twoNeighbourScaledCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) ≤ 224 := by
    exact_mod_cast twoNeighbourScaledCharge_le r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂
  unfold twoNeighbourCharge
  linarith

end

end CI2ZF.VigodaArithmetic
