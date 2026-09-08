import CI2ZF.HardMoveMass

/-! Hamming costs of the actual prescribed component matches. -/

namespace PottsCI.Vigoda
open Finset
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V]

/-- Common off-root moves leave exactly the original root disagreement. -/
theorem common_offRoot_match_ham {X Y : V → C} {v : V} {S : Finset V} {a c : C}
    (hroot : X v ≠ Y v) (hagree : ∀ w, w ≠ v → X w = Y w) (hv : v ∉ S) :
    ham (flipConfiguration X S a c) (flipConfiguration Y S a c) = 1 := by
  have heq : (univ.filter fun w => flipConfiguration X S a c w ≠
      flipConfiguration Y S a c w) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hw : w = v
    · subst w
      simp [flipConfiguration, hv, hroot]
    · have ha := hagree w hw
      simp [flipConfiguration, ha, hw]
  simp [ham, hamCard, heq]

/-- A root component matched with one of its off-root pieces disagrees
exactly on the other pieces and on the root itself. -/
theorem root_offRoot_match_ham {X Y : V → C} {v : V} {R S : Finset V} {a b c : C}
    (hXa : X v = a) (hYb : Y v = b) (hac : a ≠ c) (hbc : b ≠ c)
    (hagree : ∀ w, w ≠ v → X w = Y w) (hvR : v ∈ R) (hvS : v ∉ S)
    (hsub : S ⊆ R) (hcol : ∀ w ∈ R, X w = a ∨ X w = c) :
    ham (flipConfiguration X R a c) (flipConfiguration Y S a c) =
      (R.card : ℝ) - S.card := by
  have heq : (univ.filter fun w => flipConfiguration X R a c w ≠
      flipConfiguration Y S a c w) = R \ S := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    by_cases hwv : w = v
    · subst w
      simp [flipConfiguration, hvR, hvS, hXa, hYb, hbc.symm]
    · have ha := hagree w hwv
      by_cases hwS : w ∈ S
      · have hwR := hsub hwS
        simp [flipConfiguration, hwR, hwS, ha]
      · by_cases hwR : w ∈ R
        · rcases hcol w hwR with hwa | hwc
          · have hy : Y w = a := ha.symm.trans hwa
            simp [flipConfiguration, hwR, hwS, hwa, hy, hac.symm]
          · have hy : Y w = c := ha.symm.trans hwc
            simp [flipConfiguration, hwR, hwS, hwc, hy, hac.symm, hac]
        · simp [flipConfiguration, hwR, hwS, ha]
  unfold ham hamCard
  rw [heq, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]

omit [Fintype V] in
/-- In the one-neighbour root-colour case, matching the root move to the
whole off-root component coalesces the two configurations. -/
theorem root_offRoot_match_coalesces {X Y : V → C} {v : V} {S : Finset V} {a b : C}
    (hXa : X v = a) (hYb : Y v = b) (hagree : ∀ w, w ≠ v → X w = Y w)
    (hv : v ∉ S) :
    flipConfiguration X (insert v S) a b = flipConfiguration Y S a b := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [flipConfiguration, hv, hXa, hYb]
  · simp [flipConfiguration, hw, hagree w hw]

/-- A root-colour move paired with holding removes the root disagreement
and can create disagreements only on the other vertices of its component. -/
theorem root_holding_match_ham {X Y : V → C} {v : V} {S : Finset V} {a b : C}
    (hXa : X v = a) (hYb : Y v = b) (hab : a ≠ b)
    (hagree : ∀ w, w ≠ v → X w = Y w) (hv : v ∈ S)
    (hcol : ∀ w ∈ S, X w = a ∨ X w = b) :
    ham (flipConfiguration X S a b) Y = (S.card : ℝ) - 1 := by
  have heq : (univ.filter fun w => flipConfiguration X S a b w ≠ Y w) = S.erase v := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hwv : w = v
    · subst w
      simp [flipConfiguration, hv, hXa, hYb]
    · have ha := hagree w hwv
      by_cases hw : w ∈ S
      · rcases hcol w hw with hwa | hwb
        · simp [flipConfiguration, hw, hwv, ← ha, hwa, hab.symm]
        · simp [flipConfiguration, hw, hwv, ← ha, hwb, hab, hab.symm]
      · simp [flipConfiguration, hw, hwv, ha]
  unfold ham hamCard
  rw [heq, Finset.card_erase_of_mem hv,
    Nat.cast_sub (Finset.one_le_card.mpr ⟨v, hv⟩), Nat.cast_one]

/-- When two residual moves share an incidence, the union-support bound
saves at least one unit over their separate size charges. -/
theorem intersecting_moves_ham_drift_le {X Y X' Y' : V → C} {v : V} {S T : Finset V}
    (hagree : ∀ w, w ≠ v → X w = Y w)
    (hX : ∀ w, w ∉ S → X' w = X w) (hY : ∀ w, w ∉ T → Y' w = Y w)
    (hne : (S ∩ T).Nonempty) :
    ham X' Y' - 1 ≤ (S.card : ℝ) + T.card - 1 := by
  have hsub : (univ.filter fun w => X' w ≠ Y' w) ⊆ insert v (S ∪ T) := by
    intro w hw
    by_contra hn
    have hn' : w ≠ v ∧ w ∉ S ∧ w ∉ T := by simpa using hn
    have hdis := (Finset.mem_filter.mp hw).2
    rw [hX w hn'.2.1, hY w hn'.2.2, hagree w hn'.1] at hdis
    exact hdis rfl
  have hc : hamCard X' Y' ≤ S.card + T.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_insert_le v (S ∪ T)
    have h3 := Finset.card_union_add_card_inter S T
    have h4 := Finset.card_pos.mpr hne
    unfold hamCard
    omega
  have hreal : ham X' Y' ≤ (S.card : ℝ) + T.card := by
    unfold ham
    exact_mod_cast hc
  linarith

end
end PottsCI.Vigoda
