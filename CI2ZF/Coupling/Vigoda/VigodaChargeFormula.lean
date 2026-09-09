import CI2ZF.Coupling.Vigoda.VigodaArithmetic

/-!
# Real-valued form of the Vigoda local charge certificate

This file identifies the integer certificate with the literal root and
residual-mass formulas in the main text. It also supplies the analytic bound
when two root neighbours share an off-root component.
-/

namespace CI2ZF.VigodaArithmetic

open PottsCI.Vigoda

noncomputable section

lemma profile_antitone (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) :
    vigodaMass s ≤ vigodaMass r := by
  by_cases hs : 7 ≤ s
  · rw [profile_zero_of_seven_le s hs]
    exact vigodaMass_nonneg r
  · have hs6 : s ≤ 6 := by omega
    have hr6 : r ≤ 6 := by omega
    interval_cases r <;> interval_cases s <;> norm_num [vigodaMass] at *

def familyRootRate (r s : ℕ) (f g : Bool) : ℝ :=
  if f && g then vigodaMass (1 + r + s) else 0

def familyFirstResidual (r s : ℕ) (f g : Bool) : ℝ :=
  (if f then vigodaMass r else 0) -
    (if s ≤ r then familyRootRate r s f g else 0)

def familySecondResidual (r s : ℕ) (f g : Bool) : ℝ :=
  (if g then vigodaMass s else 0) -
    (if r < s then familyRootRate r s f g else 0)

lemma familyRootRate_nonneg (r s : ℕ) (f g : Bool) :
    0 ≤ familyRootRate r s f g := by
  unfold familyRootRate
  split_ifs
  · exact vigodaMass_nonneg _
  · exact le_rfl

lemma familyRootRate_le_first (r s : ℕ) (hr : 1 ≤ r) (f g : Bool) :
    familyRootRate r s f g ≤ if f then vigodaMass r else 0 := by
  cases f <;> cases g <;> simp [familyRootRate]
  · exact vigodaMass_nonneg r
  · exact profile_antitone r (1 + r + s) hr (by omega)

lemma familyRootRate_le_second (r s : ℕ) (hs : 1 ≤ s) (f g : Bool) :
    familyRootRate r s f g ≤ if g then vigodaMass s else 0 := by
  cases f <;> cases g <;> simp [familyRootRate]
  · exact vigodaMass_nonneg s
  · exact profile_antitone s (1 + r + s) hs (by omega)

lemma familyFirstResidual_nonneg (r s : ℕ) (hr : 1 ≤ r) (f g : Bool) :
    0 ≤ familyFirstResidual r s f g := by
  have hrate := familyRootRate_nonneg r s f g
  have hle := familyRootRate_le_first r s hr f g
  unfold familyFirstResidual
  by_cases h : s ≤ r
  · rw [if_pos h]
    exact sub_nonneg.mpr hle
  · rw [if_neg h, sub_zero]
    exact hrate.trans hle

lemma familySecondResidual_nonneg (r s : ℕ) (hs : 1 ≤ s) (f g : Bool) :
    0 ≤ familySecondResidual r s f g := by
  have hrate := familyRootRate_nonneg r s f g
  have hle := familyRootRate_le_second r s hs f g
  unfold familySecondResidual
  by_cases h : r < s
  · rw [if_pos h]
    exact sub_nonneg.mpr hle
  · rw [if_neg h, sub_zero]
    exact hrate.trans hle

lemma familyFirstResidual_le_profile (r s : ℕ) (f g : Bool) :
    familyFirstResidual r s f g ≤ vigodaMass r := by
  have hrate := familyRootRate_nonneg r s f g
  have hp := vigodaMass_nonneg r
  unfold familyFirstResidual
  split_ifs <;> linarith

lemma familySecondResidual_le_profile (r s : ℕ) (f g : Bool) :
    familySecondResidual r s f g ≤ vigodaMass s := by
  have hrate := familyRootRate_nonneg r s f g
  have hp := vigodaMass_nonneg s
  unfold familySecondResidual
  split_ifs <;> linarith

lemma family_rootCost_cast (r s : ℕ) (f g : Bool) :
    ((familyCharge r s f g).rootCost : ℝ) =
      84 * ((min r s : ℕ) : ℝ) * familyRootRate r s f g := by
  simp only [familyCharge, familyRootRate]
  push_cast
  simp only [scaledP_eq_profile]
  split_ifs <;> ring

lemma family_firstResidual_cast (r s : ℕ) (f g : Bool) :
    ((familyCharge r s f g).firstResidual : ℝ) =
      84 * familyFirstResidual r s f g := by
  simp only [familyCharge, familyFirstResidual, familyRootRate]
  push_cast
  simp only [scaledP_eq_profile]
  split_ifs <;> ring

lemma family_secondResidual_cast (r s : ℕ) (f g : Bool) :
    ((familyCharge r s f g).secondResidual : ℝ) =
      84 * familySecondResidual r s f g := by
  simp only [familyCharge, familySecondResidual, familyRootRate]
  push_cast
  simp only [scaledP_eq_profile]
  split_ifs <;> ring

lemma family_firstCost_cast (r s : ℕ) (f g : Bool) :
    ((familyCharge r s f g).firstCost : ℝ) =
      84 * (r : ℝ) * familyFirstResidual r s f g := by
  change (((r : ℤ) * (familyCharge r s f g).firstResidual : ℤ) : ℝ) = _
  rw [Int.cast_mul, Int.cast_natCast, family_firstResidual_cast]
  ring

lemma family_secondCost_cast (r s : ℕ) (f g : Bool) :
    ((familyCharge r s f g).secondCost : ℝ) =
      84 * (s : ℝ) * familySecondResidual r s f g := by
  change (((s : ℤ) * (familyCharge r s f g).secondResidual : ℤ) : ℝ) = _
  rw [Int.cast_mul, Int.cast_natCast, family_secondResidual_cast]
  ring

/-- The two root costs plus both off-root paired residual charges. -/
def twoNeighbourFormula (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : ℝ :=
  (min r₁ r₂ : ℕ) * familyRootRate r₁ r₂ f₁ f₂ +
  (min s₁ s₂ : ℕ) * familyRootRate s₁ s₂ g₁ g₂ +
  pairCharge r₁ s₁ (familyFirstResidual r₁ r₂ f₁ f₂) (familyFirstResidual s₁ s₂ g₁ g₂) +
  pairCharge r₂ s₂ (familySecondResidual r₁ r₂ f₁ f₂) (familySecondResidual s₁ s₂ g₁ g₂)

theorem twoNeighbourCharge_eq_formula (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) :
    twoNeighbourCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ =
      twoNeighbourFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  have hscale : (twoNeighbourScaledCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) =
      84 * twoNeighbourFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
    simp only [twoNeighbourScaledCharge, Int.cast_add, Int.cast_sub, Int.cast_min]
    rw [family_rootCost_cast, family_rootCost_cast,
      family_firstCost_cast, family_secondCost_cast,
      family_firstCost_cast, family_secondCost_cast,
      family_firstResidual_cast, family_firstResidual_cast,
      family_secondResidual_cast, family_secondResidual_cast]
    rw [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 84),
      ← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 84)]
    unfold twoNeighbourFormula pairCharge
    ring
  unfold twoNeighbourCharge
  rw [hscale]
  ring

/-- The literal real residual-charge formula has the required `8 / 3`
bound for all positive component sizes and all feasibility patterns. -/
theorem two_neighbour_formula_bound (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ : Bool) :
    twoNeighbourFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 8 / 3 := by
  rw [← twoNeighbourCharge_eq_formula]
  exact two_neighbour_distinct_bound r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂

lemma min_size_root_bound (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ((min r s : ℕ) : ℝ) * vigodaMass (1 + r + s) ≤ 1 / 6 := by
  by_cases hlarge : 7 ≤ 1 + r + s
  · rw [profile_zero_of_seven_le _ hlarge]
    norm_num
  · have hrsmall : r ≤ 5 := by omega
    have hssmall : s ≤ 5 := by omega
    interval_cases r <;> interval_cases s <;> norm_num [vigodaMass] at *

/-- If a component contains both neighbours, its size is at least three.
Charging the other side by two full branches and its root correction gives
the paper's analytic `1/2 + 2 + 1/6 = 8/3` bound. -/
theorem two_neighbour_shared_component_bound (r s t : ℕ)
    (hr : 3 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t) :
    (r : ℝ) * vigodaMass r + (s : ℝ) * vigodaMass s + (t : ℝ) * vigodaMass t +
      ((min s t : ℕ) : ℝ) * vigodaMass (1 + s + t) ≤ 8 / 3 := by
  have hshared := profile_large_component_bound r hr
  have hleft := vigoda_branch_bound s
  have hright := vigoda_branch_bound t
  have hroot := min_size_root_bound s t hs ht
  linarith

theorem regular_high_multiplicity_arithmetic (m : ℕ) (hm : 3 ≤ m) :
    8 / 21 + 4 * (m : ℝ) / 3 ≤ 11 * (m : ℝ) / 6 - 1 := by
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

theorem root_colour_high_multiplicity_arithmetic (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) + 4 / 21 ≤ 11 * (m : ℝ) / 6 - 1 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

end

end CI2ZF.VigodaArithmetic
