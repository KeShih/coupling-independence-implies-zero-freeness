import CI2ZF.Appendix.CV.Certificate

/-! Identification of the integer certificate with the appendix's real CV
record formula, including root masses and global residuals. -/
namespace CI2ZF.Appendix.CV
noncomputable section

def realAtom (b : Branch) : ℝ := if feasible b then mass (branchSize b) else 0

def oneResidual (b : Branch) : ℝ :=
  realAtom b - if feasible b then mass (1 + branchSize b) else 0

/-- The one-incidence formula in unscaled transition-mass units. -/
def recordOne (a b : Branch) : ℝ :=
  branchSize a * oneResidual a + branchSize b * oneResidual b - min (oneResidual a) (oneResidual b)

lemma realAtom_scaled (b : Branch) : (atomMass b : ℝ) = 1000 * realAtom b := by
  unfold atomMass realAtom
  split <;> simp [scaledMass_eq]

lemma oneResidual_scaled (b : Branch) :
    (atomMass b : ℝ) - (if feasible b then (scaledMass (1 + branchSize b) : ℝ) else 0) =
      1000 * oneResidual b := by
  unfold oneResidual
  rw [realAtom_scaled]
  split <;> simp [scaledMass_eq, mul_sub]

lemma one_record_scaled (a b : Branch) : (oneCharge a b : ℝ) = 1000 * recordOne a b := by
  unfold oneCharge recordOne
  push_cast
  rw [oneResidual_scaled, oneResidual_scaled]
  rw [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1000)]
  ring

structure RealFamily where
  rootCost : ℝ
  residual₀ : ℝ
  residual₁ : ℝ

def realFamily (a₀ a₁ : Branch) (i : Bool) : RealFamily :=
  let r := 1 + branchSize a₀ + branchSize a₁
  let p := if rootOK a₀ && rootOK a₁ then mass r else 0
  { rootCost := (if i then branchSize a₀ else branchSize a₁) * p
    residual₀ := realAtom a₀ - if i then 0 else p
    residual₁ := realAtom a₁ - if i then p else 0 }

lemma family_scaled (a₀ a₁ : Branch) (i : Bool) :
    ((family a₀ a₁ i).rootCost : ℝ) = 1000 * (realFamily a₀ a₁ i).rootCost ∧
    ((family a₀ a₁ i).residual₀ : ℝ) = 1000 * (realFamily a₀ a₁ i).residual₀ ∧
    ((family a₀ a₁ i).residual₁ : ℝ) = 1000 * (realFamily a₀ a₁ i).residual₁ := by
  cases i <;> by_cases h : (rootOK a₀ && rootOK a₁) = true <;>
    simp [family, realFamily, h, realAtom_scaled, scaledMass_eq] <;> ring_nf <;> simp


/-- The exact real root/off-root and residual-match charge in equation cv-charge. -/
def recordTwo (a₀ a₁ b₀ b₁ : Branch) (i j : Bool) : ℝ :=
  let a := realFamily a₀ a₁ i
  let b := realFamily b₀ b₁ j
  a.rootCost + b.rootCost + branchSize a₀ * a.residual₀ + branchSize a₁ * a.residual₁ +
    branchSize b₀ * b.residual₀ + branchSize b₁ * b.residual₁ -
    min a.residual₀ b.residual₀ - min a.residual₁ b.residual₁

lemma two_record_scaled (a₀ a₁ b₀ b₁ : Branch) (i j : Bool) :
    (twoCharge a₀ a₁ b₀ b₁ i j : ℝ) = 1000 * recordTwo a₀ a₁ b₀ b₁ i j := by
  obtain ⟨ha, ha₀, ha₁⟩ := family_scaled a₀ a₁ i
  obtain ⟨hb, hb₀, hb₁⟩ := family_scaled b₀ b₁ j
  unfold twoCharge recordTwo
  push_cast
  rw [ha, hb, ha₀, ha₁, hb₀, hb₁]
  rw [← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1000),
    ← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1000)]
  ring

/-- The low-multiplicity inequality for the actual unscaled one-index formula. -/
theorem recordOne_corrected (a b : Branch) (ha : 0 < branchSize a) (hb : 0 < branchSize b)
    (gain loss : ℝ) : recordOne a b + loss * safe11 a b - gain * safe12 a b ≤
      -1 + low gain loss := by
  have h := one_corrected a b ha hb gain loss
  rw [one_record_scaled] at h
  linarith

/-- The low-multiplicity inequality for the actual unscaled two-index formula,
with no gain/loss assumptions and every permitted maximum-component tie. -/
theorem recordTwo_corrected (a₀ a₁ b₀ b₁ : Branch) (i j : Bool)
    (ha : 0 < branchSize a₀ + branchSize a₁)
    (hb : 0 < branchSize b₀ + branchSize b₁)
    (hp : permitted a₀ a₁ b₀ b₁ i j = true) (gain loss : ℝ) :
    recordTwo a₀ a₁ b₀ b₁ i j +
      loss * (safe11 a₀ b₀ + safe11 a₁ b₁) -
      gain * (safe12 a₀ b₀ + safe12 a₁ b₁) ≤ -1 + 2 * low gain loss := by
  have h := two_corrected a₀ a₁ b₀ b₁ i j ha hb hp gain loss
  rw [two_record_scaled] at h
  linarith

end
end CI2ZF.Appendix.CV
