import CI2ZF.Appendix.CV.Arithmetic

/-! The unbounded-to-finite reduction of CV record charges. Zero-rate branches
retain their size-charge and residual matching data after capping at seven. -/
namespace CI2ZF.Appendix.CV
noncomputable section

lemma mass_cap (r : ℕ) : mass (min r 7) = mass r := by
  by_cases hr : r ≤ 7
  · rw [Nat.min_eq_left hr]
  · rw [Nat.min_eq_right (by omega), mass_zero_of_seven_le r (by omega)]
    norm_num [mass]

lemma size_mass_cap (r : ℕ) : (min r 7 : ℕ) * mass (min r 7) = (r : ℝ) * mass r := by
  by_cases hr : r ≤ 7
  · rw [Nat.min_eq_left hr]
  · rw [Nat.min_eq_right (by omega), mass_zero_of_seven_le r (by omega)]
    norm_num [mass]

/-- A whole family record includes costs as well as residual rates; preserving
only transition masses would not by itself preserve the coupling charge. -/
structure UnboundedFamily where
  rootCost : ℝ
  residual₀ : ℝ
  residual₁ : ℝ
  cost₀ : ℝ
  cost₁ : ℝ

def unboundedFamily (r s : ℕ) (f g i : Bool) : UnboundedFamily :=
  let p := if (r == 0 || f) && (s == 0 || g) then mass (1 + r + s) else 0
  let u := (if f then mass r else 0) - if i then 0 else p
  let w := (if g then mass s else 0) - if i then p else 0
  { rootCost := (if i then r else s) * p
    residual₀ := u
    residual₁ := w
    cost₀ := r * u
    cost₁ := s * w }

/-- For any root-match index, capping at seven preserves the entire family. -/
theorem unboundedFamily_cap (r s : ℕ) (f g i : Bool) :
    unboundedFamily (min r 7) (min s 7) f g i = unboundedFamily r s f g i := by
  by_cases hr : r ≤ 7 <;> by_cases hs : s ≤ 7
  · rw [Nat.min_eq_left hr, Nat.min_eq_left hs]
  · have hs7 : 7 ≤ s := by omega
    have hp : mass (1 + r + s) = 0 := mass_zero_of_seven_le _ (by omega)
    have hp' : mass (1 + r + 7) = 0 := mass_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_left hr, Nat.min_eq_right hs7, unboundedFamily,
      hp, hp', mass_zero_of_seven_le s hs7, show mass 7 = 0 from rfl]
    simp
  · have hr7 : 7 ≤ r := by omega
    have hp : mass (1 + r + s) = 0 := mass_zero_of_seven_le _ (by omega)
    have hp' : mass (1 + 7 + s) = 0 := mass_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_right hr7, Nat.min_eq_left hs, unboundedFamily,
      hp, hp', mass_zero_of_seven_le r hr7, show mass 7 = 0 from rfl]
    simp
  · have hr7 : 7 ≤ r := by omega
    have hs7 : 7 ≤ s := by omega
    have hp : mass (1 + r + s) = 0 := mass_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_right hr7, Nat.min_eq_right hs7, unboundedFamily,
      hp, mass_zero_of_seven_le r hr7, mass_zero_of_seven_le s hs7,
      show mass 7 = 0 from rfl, show mass (1 + 7 + 7) = 0 from rfl]
    simp

/-- The full two-incidence charge before truncation. Zero markers may occur. -/
def unboundedTwoCharge (r₀ r₁ s₀ s₁ : ℕ) (f₀ f₁ g₀ g₁ i j : Bool) : ℝ :=
  let a := unboundedFamily r₀ r₁ f₀ f₁ i
  let b := unboundedFamily s₀ s₁ g₀ g₁ j
  a.rootCost + b.rootCost + a.cost₀ + a.cost₁ + b.cost₀ + b.cost₁ -
    min a.residual₀ b.residual₀ - min a.residual₁ b.residual₁

theorem unboundedTwoCharge_cap (r₀ r₁ s₀ s₁ : ℕ) (f₀ f₁ g₀ g₁ i j : Bool) :
    unboundedTwoCharge (min r₀ 7) (min r₁ 7) (min s₀ 7) (min s₁ 7) f₀ f₁ g₀ g₁ i j =
      unboundedTwoCharge r₀ r₁ s₀ s₁ f₀ f₁ g₀ g₁ i j := by
  simp only [unboundedTwoCharge, unboundedFamily_cap]

end
end CI2ZF.Appendix.CV
