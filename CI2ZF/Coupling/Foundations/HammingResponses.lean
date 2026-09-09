import CI2ZF.Coupling.Foundations.PathCoupling
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

/-! Single-coordinate response bounds accumulate along actual Hamming
geodesics. These results include the empty vertex set and require neither
a supplied global Lipschitz bound nor a supplied multi-coordinate ratio. -/
namespace CI2ZF
open PottsCI
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

theorem exists_update_of_hamCard_eq_one {sigma eta : V → C}
    (h : hamCard sigma eta = 1) :
    ∃ u, eta = Function.update sigma u (eta u) := by
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h
  refine ⟨u, ?_⟩
  funext w
  by_cases hw : w = u
  · subst w
    simp
  · have he : sigma w = eta w := by
      by_contra hn
      have hm : w ∈ Finset.univ.filter (fun t => sigma t ≠ eta t) := by simp [hn]
      rw [hu] at hm
      exact hw (Finset.mem_singleton.mp hm)
    simp [hw, he]

section Additive
variable {E : Type*} [SeminormedAddCommGroup E]

theorem norm_sub_le_ham_of_adjacent (f : (V → C) → E) {alpha : ℝ}
    (hstep : ∀ sigma eta, hamCard sigma eta = 1 → ‖f sigma - f eta‖ ≤ alpha)
    (sigma eta : V → C) : ‖f sigma - f eta‖ ≤ alpha * ham sigma eta := by
  have main : ∀ k : ℕ, ∀ sigma eta, hamCard sigma eta = k →
      ‖f sigma - f eta‖ ≤ alpha * k := by
    intro k
    induction k with
    | zero =>
      intro sigma eta he
      have heq := hamCard_eq_zero he
      simp [heq]
    | succ k ih =>
      intro sigma eta he
      obtain ⟨mid, hfirst, hrest⟩ := exists_intermediate he
      calc
        ‖f sigma - f eta‖ = ‖(f sigma - f mid) + (f mid - f eta)‖ := by
          congr 1
          abel
        _ ≤ ‖f sigma - f mid‖ + ‖f mid - f eta‖ := norm_add_le _ _
        _ ≤ alpha + alpha * k := add_le_add (hstep sigma mid hfirst) (ih mid eta hrest)
        _ = alpha * (k + 1 : ℕ) := by push_cast; ring
  exact main (hamCard sigma eta) sigma eta rfl

theorem norm_sub_le_ham_of_coordinates (f : (V → C) → E) {alpha : ℝ}
    (hstep : ∀ sigma u c, ‖f (Function.update sigma u c) - f sigma‖ ≤ alpha)
    (sigma eta : V → C) : ‖f sigma - f eta‖ ≤ alpha * ham sigma eta := by
  apply norm_sub_le_ham_of_adjacent f _ sigma eta
  intro x y hxy
  obtain ⟨u, he⟩ := exists_update_of_hamCard_eq_one hxy
  rw [he, norm_sub_rev]
  exact hstep x u _

theorem norm_sub_le_card_of_coordinates (f : (V → C) → E) {alpha : ℝ}
    (ha : 0 ≤ alpha)
    (hstep : ∀ sigma u c, ‖f (Function.update sigma u c) - f sigma‖ ≤ alpha)
    (sigma eta : V → C) : ‖f sigma - f eta‖ ≤ alpha * Fintype.card V :=
  (norm_sub_le_ham_of_coordinates f hstep sigma eta).trans
    (mul_le_mul_of_nonneg_left (ham_le_card sigma eta) ha)

end Additive

theorem le_pow_hamCard_mul_of_adjacent (f : (V → C) → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hstep : ∀ sigma eta, hamCard sigma eta = 1 → f sigma ≤ H * f eta)
    (sigma eta : V → C) : f sigma ≤ H ^ hamCard sigma eta * f eta := by
  have main : ∀ k : ℕ, ∀ sigma eta, hamCard sigma eta = k → f sigma ≤ H ^ k * f eta := by
    intro k
    induction k with
    | zero =>
      intro sigma eta he
      have heq := hamCard_eq_zero he
      simp [heq]
    | succ k ih =>
      intro sigma eta he
      obtain ⟨mid, hfirst, hrest⟩ := exists_intermediate he
      calc
        f sigma ≤ H * f mid := hstep sigma mid hfirst
        _ ≤ H * (H ^ k * f eta) := mul_le_mul_of_nonneg_left (ih mid eta hrest) hH
        _ = H ^ (k + 1) * f eta := by rw [pow_succ]; ring
  exact main (hamCard sigma eta) sigma eta rfl

theorem le_pow_hamCard_mul_of_coordinates (f : (V → C) → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hstep : ∀ sigma u c, f (Function.update sigma u c) ≤ H * f sigma)
    (sigma eta : V → C) : f sigma ≤ H ^ hamCard sigma eta * f eta := by
  apply le_pow_hamCard_mul_of_adjacent f hH _ sigma eta
  intro x y hxy
  have hyx : hamCard y x = 1 := by rw [hamCard_comm, hxy]
  obtain ⟨u, he⟩ := exists_update_of_hamCard_eq_one hyx
  rw [he]
  exact hstep y u _

theorem le_pow_card_mul_of_coordinates (f : (V → C) → ℝ) {H : ℝ} (hH : 1 ≤ H)
    (hf : ∀ sigma, 0 ≤ f sigma)
    (hstep : ∀ sigma u c, f (Function.update sigma u c) ≤ H * f sigma)
    (sigma eta : V → C) : f sigma ≤ H ^ Fintype.card V * f eta := by
  apply (le_pow_hamCard_mul_of_coordinates f (le_trans zero_le_one hH) hstep sigma eta).trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (hamCard_le_card sigma eta)) (hf eta)

theorem ratio_le_pow_card_of_coordinates (f : (V → C) → ℝ) {H : ℝ} (hH : 1 ≤ H)
    (hf : ∀ sigma, 0 < f sigma)
    (hstep : ∀ sigma u c, f (Function.update sigma u c) ≤ H * f sigma)
    (sigma eta : V → C) : f sigma / f eta ≤ H ^ Fintype.card V :=
  (div_le_iff₀ (hf eta)).mpr
    (le_pow_card_mul_of_coordinates f hH (fun x => (hf x).le) hstep sigma eta)

omit [DecidableEq C] in
theorem shell_configuration_count [Fintype C] :
    Fintype.card (V → C) = (Fintype.card C) ^ Fintype.card V := Fintype.card_fun

end
end CI2ZF
