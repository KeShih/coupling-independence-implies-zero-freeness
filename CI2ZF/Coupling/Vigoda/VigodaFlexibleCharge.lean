import CI2ZF.Coupling.Vigoda.VigodaChargeFormula

/-! The exceptional two-neighbour certificate permits either maximizing
component when component sizes tie. -/
namespace CI2ZF.VigodaArithmetic
noncomputable section

def flexibleFamily (r s : ℕ) (f g pick : Bool) : FamilyCharge :=
  let P := if f && g then scaledP (1 + r + s) else 0
  let u := (if f then scaledP r else 0) - if pick then P else 0
  let w := (if g then scaledP s else 0) - if pick then 0 else P
  { rootCost := (if pick then (s : ℤ) else r) * P
    firstResidual := u
    secondResidual := w
    firstCost := (r : ℤ) * u
    secondCost := (s : ℤ) * w }

def flexibleCharge (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ pickA pickB : Bool) : ℤ :=
  let a := flexibleFamily r₁ r₂ f₁ f₂ pickA
  let b := flexibleFamily s₁ s₂ g₁ g₂ pickB
  a.rootCost + b.rootCost + a.firstCost + a.secondCost + b.firstCost + b.secondCost -
    min a.firstResidual b.firstResidual - min a.secondResidual b.secondResidual

lemma flexibleFamily_cap (r s : ℕ) (f g pick : Bool) :
    flexibleFamily (min r 7) (min s 7) f g pick = flexibleFamily r s f g pick := by
  by_cases hr : r ≤ 7 <;> by_cases hs : s ≤ 7
  · rw [Nat.min_eq_left hr, Nat.min_eq_left hs]
  · have hs7 : 7 ≤ s := by omega
    have hroot : scaledP (1 + r + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    have hroot' : scaledP (1 + r + 7) = 0 := scaledP_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_left hr, Nat.min_eq_right hs7, flexibleFamily,
      hroot, hroot', scaledP_zero_of_seven_le s hs7, show scaledP 7 = 0 from rfl]
    cases pick <;> simp
  · have hr7 : 7 ≤ r := by omega
    have hroot : scaledP (1 + r + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    have hroot' : scaledP (1 + 7 + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_left hs, Nat.min_eq_right hr7, flexibleFamily,
      hroot, hroot', scaledP_zero_of_seven_le r hr7, show scaledP 7 = 0 from rfl]
    cases pick <;> simp
  · have hr7 : 7 ≤ r := by omega
    have hs7 : 7 ≤ s := by omega
    have hroot : scaledP (1 + r + s) = 0 := scaledP_zero_of_seven_le _ (by omega)
    simp only [Nat.min_eq_right hr7, Nat.min_eq_right hs7, flexibleFamily, hroot,
      scaledP_zero_of_seven_le r hr7, scaledP_zero_of_seven_le s hs7,
      show scaledP 7 = 0 from rfl, show scaledP (1 + 7 + 7) = 0 from rfl]
    cases pick <;> simp

lemma flexibleCharge_cap (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ pickA pickB : Bool) :
    flexibleCharge (min r₁ 7) (min r₂ 7) (min s₁ 7) (min s₂ 7) f₁ f₂ g₁ g₂ pickA pickB =
      flexibleCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB := by
  simp only [flexibleCharge, flexibleFamily_cap]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem flexibleCharge_small (r₁ r₂ s₁ s₂ : Fin 7) (f₁ f₂ g₁ g₂ pickA pickB : Bool) :
    (if pickA then r₂.val ≤ r₁.val else r₁.val ≤ r₂.val) →
    (if pickB then s₂.val ≤ s₁.val else s₁.val ≤ s₂.val) →
    flexibleCharge (r₁.val + 1) (r₂.val + 1) (s₁.val + 1) (s₂.val + 1)
      f₁ f₂ g₁ g₂ pickA pickB ≤ 224 := by
  fin_cases r₁ <;> revert r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB <;> decide

theorem flexibleCharge_le (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ pickA pickB : Bool)
    (hA : if pickA then r₂ ≤ r₁ else r₁ ≤ r₂)
    (hB : if pickB then s₂ ≤ s₁ else s₁ ≤ s₂) :
    flexibleCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 224 := by
  have h (r : ℕ) (hr : 1 ≤ r) : min r 7 - 1 + 1 = min r 7 := by omega
  let R₁ : Fin 7 := ⟨min r₁ 7 - 1, by omega⟩
  let R₂ : Fin 7 := ⟨min r₂ 7 - 1, by omega⟩
  let S₁ : Fin 7 := ⟨min s₁ 7 - 1, by omega⟩
  let S₂ : Fin 7 := ⟨min s₂ 7 - 1, by omega⟩
  have hA' : if pickA then R₂.val ≤ R₁.val else R₁.val ≤ R₂.val := by
    dsimp [R₁, R₂]
    cases pickA <;> simp at hA ⊢ <;> omega
  have hB' : if pickB then S₂.val ≤ S₁.val else S₁.val ≤ S₂.val := by
    dsimp [S₁, S₂]
    cases pickB <;> simp at hB ⊢ <;> omega
  have hc := flexibleCharge_small R₁ R₂ S₁ S₂ f₁ f₂ g₁ g₂ pickA pickB hA' hB'
  dsimp [R₁, R₂, S₁, S₂] at hc
  rw [h r₁ hr₁, h r₂ hr₂, h s₁ hs₁, h s₂ hs₂, flexibleCharge_cap] at hc
  exact hc

end
end CI2ZF.VigodaArithmetic
