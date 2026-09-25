import ZeroFreeness.Coupling.Vigoda.VigodaFlexibleCharge

namespace ZeroFreeness.VigodaArithmetic
noncomputable section

def flexibleFirstResidual (r s : ℕ) (f g pick : Bool) : ℝ :=
  (if f then PottsCI.Vigoda.vigodaMass r else 0) - if pick then familyRootRate r s f g else 0

def flexibleSecondResidual (r s : ℕ) (f g pick : Bool) : ℝ :=
  (if g then PottsCI.Vigoda.vigodaMass s else 0) - if pick then 0 else familyRootRate r s f g

def flexibleRootCost (r s : ℕ) (f g pick : Bool) : ℝ :=
  (if pick then (s : ℝ) else r) * familyRootRate r s f g

def flexibleFormula (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ pickA pickB : Bool) : ℝ :=
  flexibleRootCost r₁ r₂ f₁ f₂ pickA + flexibleRootCost s₁ s₂ g₁ g₂ pickB +
  pairCharge r₁ s₁ (flexibleFirstResidual r₁ r₂ f₁ f₂ pickA)
    (flexibleFirstResidual s₁ s₂ g₁ g₂ pickB) +
  pairCharge r₂ s₂ (flexibleSecondResidual r₁ r₂ f₁ f₂ pickA)
    (flexibleSecondResidual s₁ s₂ g₁ g₂ pickB)

lemma flexibleFamily_root_cast (r s : ℕ) (f g pick : Bool) :
    ((flexibleFamily r s f g pick).rootCost : ℝ) = 84 * flexibleRootCost r s f g pick := by
  simp only [flexibleFamily, flexibleRootCost, familyRootRate]
  push_cast
  simp only [scaledP_eq_profile]
  split_ifs <;> ring

lemma flexibleFamily_first_cast (r s : ℕ) (f g pick : Bool) :
    ((flexibleFamily r s f g pick).firstResidual : ℝ) =
      84 * flexibleFirstResidual r s f g pick := by
  simp only [flexibleFamily, flexibleFirstResidual, familyRootRate]
  push_cast
  simp only [scaledP_eq_profile]
  split_ifs <;> ring

lemma flexibleFamily_second_cast (r s : ℕ) (f g pick : Bool) :
    ((flexibleFamily r s f g pick).secondResidual : ℝ) =
      84 * flexibleSecondResidual r s f g pick := by
  simp only [flexibleFamily, flexibleSecondResidual, familyRootRate]
  push_cast
  simp only [scaledP_eq_profile]
  split_ifs <;> ring

lemma flexibleFamily_firstCost_cast (r s : ℕ) (f g pick : Bool) :
    ((flexibleFamily r s f g pick).firstCost : ℝ) =
      84 * (r : ℝ) * flexibleFirstResidual r s f g pick := by
  change (((r : ℤ) * (flexibleFamily r s f g pick).firstResidual : ℤ) : ℝ) = _
  rw [Int.cast_mul, Int.cast_natCast, flexibleFamily_first_cast]
  ring

lemma flexibleFamily_secondCost_cast (r s : ℕ) (f g pick : Bool) :
    ((flexibleFamily r s f g pick).secondCost : ℝ) =
      84 * (s : ℝ) * flexibleSecondResidual r s f g pick := by
  change (((s : ℤ) * (flexibleFamily r s f g pick).secondResidual : ℤ) : ℝ) = _
  rw [Int.cast_mul, Int.cast_natCast, flexibleFamily_second_cast]
  ring

lemma flexibleCharge_eq_formula (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ pickA pickB : Bool) :
    (flexibleCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB : ℝ) =
      84 * flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB := by
  simp only [flexibleCharge, Int.cast_add, Int.cast_sub, Int.cast_min]
  rw [flexibleFamily_root_cast, flexibleFamily_root_cast,
    flexibleFamily_firstCost_cast, flexibleFamily_secondCost_cast,
    flexibleFamily_firstCost_cast, flexibleFamily_secondCost_cast,
    flexibleFamily_first_cast, flexibleFamily_first_cast,
    flexibleFamily_second_cast, flexibleFamily_second_cast]
  rw [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 84),
    ← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 84)]
  unfold flexibleFormula pairCharge
  ring

theorem flexibleFormula_le (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ pickA pickB : Bool)
    (hA : if pickA then r₂ ≤ r₁ else r₁ ≤ r₂)
    (hB : if pickB then s₂ ≤ s₁ else s₁ ≤ s₂) :
    flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 8 / 3 := by
  have hb : (flexibleCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB : ℝ) ≤ 224 := by
    exact_mod_cast flexibleCharge_le r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂
      f₁ f₂ g₁ g₂ pickA pickB hA hB
  rw [flexibleCharge_eq_formula] at hb
  linarith

end
end ZeroFreeness.VigodaArithmetic
