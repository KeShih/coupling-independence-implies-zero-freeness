import CI2ZF.Coupling.CV.ColourActivation
import CI2ZF.Coupling.CV.CorrectedCharge

/-! Concrete per-colour activation averages of the corrected CV charge.
Physical low multiplicities retain their availability weight; high
multiplicities are bounded by the bulk budget using the exact coin law. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K]

def coinColourEnvelope (A D : Finset K) (rate : ℝ) (ω : K → Bool) : ℝ :=
  if (∀ k ∈ D, ω k = false) then
    -1 + (if coinCount A ω ≤ 2 then rate else bulk) * coinCount A ω
  else (743 / 500) * coinCount A ω

lemma coinColourEnvelope_low_eq (A D : Finset K) (hA : A.card ≤ 2) (rate : ℝ) (ω : K → Bool) :
    coinColourEnvelope A D rate ω =
      -(if (∀ k ∈ D, ω k = false) then (1 : ℝ) else 0) +
        rate * (if (∀ k ∈ D, ω k = false) then (coinCount A ω : ℝ) else 0) +
        (743 / 500) * (if ¬(∀ k ∈ D, ω k = false) then (coinCount A ω : ℝ) else 0) := by
  have hk : coinCount A ω ≤ 2 := (Finset.card_le_card (Finset.filter_subset _ _)).trans hA
  unfold coinColourEnvelope
  rw [if_pos hk]
  have he (P : Prop) [Decidable P] (n : ℝ) :
      (if P then -1 + rate * n else (743 / 500) * n) =
        -(if P then (1 : ℝ) else 0) + rate * (if P then n else 0) +
          (743 / 500) * (if ¬P then n else 0) := by
    by_cases hp : P <;> simp [hp]
  exact he (∀ k ∈ D, ω k = false) _

theorem coinColourEnvelope_low_expect (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (A D : Finset K) (hAD : Disjoint A D) (hA : A.card ≤ 2) (rate : ℝ) :
    expectReal (commonCoinLaw (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (coinColourEnvelope A D rate) ≤
      -x ^ D.card + (1 - x) * rate * A.card * x ^ D.card +
        bulk * ((A.card : ℝ) - A.card * x ^ D.card) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  change expectReal (commonCoinLaw (1 - x) ht) (fun ω => coinColourEnvelope A D rate ω) ≤ _
  have he (ω : K → Bool) := coinColourEnvelope_low_eq A D hA rate ω
  simp_rw [he]
  rw [expectReal_add, expectReal_add]
  have hneg : expectReal (commonCoinLaw (1 - x) ht)
      (fun ω => -(if ∀ k ∈ D, ω k = false then (1 : ℝ) else 0)) = -x ^ D.card := by
    have hn : expectReal (commonCoinLaw (1 - x) ht)
        (fun ω => -(if ∀ k ∈ D, ω k = false then (1 : ℝ) else 0)) =
        -expectReal (commonCoinLaw (1 - x) ht)
          (fun ω => if ∀ k ∈ D, ω k = false then (1 : ℝ) else 0) := by
      simp only [expectReal, mul_neg, Finset.sum_neg_distrib]
    rw [hn, coin_all_false_probability]
    simp only [sub_sub_cancel]
  rw [hneg, expectReal_mul_const, expectReal_mul_const,
    coinCount_joint_mean (1 - x) ht A D hAD,
    coinCount_not_false_joint_mean (1 - x) ht A D hAD]
  simp only [sub_sub_cancel]
  have hp0 : 0 ≤ x ^ D.card := pow_nonneg hx.1 _
  have hp1 : x ^ D.card ≤ 1 := pow_le_one₀ hx.1 hx.2
  have hm0 : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hh : (743 / 500 : ℝ) * (1 - x) ≤ bulk := by
    norm_num [bulk]
    linarith [hx.1]
  have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hm0 (sub_nonneg.mpr hp1))
  nlinarith

lemma coinColourEnvelope_high_le (A D : Finset K) {rate : ℝ}
    (hrate : rate ≤ 919 / 500) (ω : K → Bool) :
    coinColourEnvelope A D rate ω ≤
      -(if (∀ k ∈ D, ω k = false) then (1 : ℝ) else 0) +
        bulk * coinCount A ω + ((919 / 500) - bulk) *
          (if coinCount A ω ≤ 2 then (coinCount A ω : ℝ) else 0) := by
  have hm : 0 ≤ (coinCount A ω : ℝ) := Nat.cast_nonneg _
  have he (P : Prop) [Decidable P] (n : ℕ) :
      (if P then -1 + (if n ≤ 2 then rate else bulk) * n else (743 / 500) * n) ≤
        -(if P then (1 : ℝ) else 0) + bulk * n +
          ((919 / 500) - bulk) * (if n ≤ 2 then (n : ℝ) else 0) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_right hrate hn
    by_cases hp : P <;> by_cases hlow : n ≤ 2 <;>
      simp only [hp, hlow, if_true, if_false, neg_zero, zero_add, mul_zero, add_zero] <;>
      unfold bulk at * <;> nlinarith
  exact he (∀ k ∈ D, ω k = false) (coinCount A ω)

/-- Every physical multiplicity at least three has the bulk expected
positive charge after its actual availability baseline is separated. -/
theorem coinColourEnvelope_high_expect (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (A D : Finset K) (hA : 3 ≤ A.card) {rate : ℝ} (hrate : rate ≤ 919 / 500) :
    expectReal (commonCoinLaw (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (coinColourEnvelope A D rate) ≤ -x ^ D.card + bulk * A.card := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  change expectReal (commonCoinLaw (1 - x) ht) _ ≤ _
  have he := expectReal_mono (commonCoinLaw (1 - x) ht) (coinColourEnvelope_high_le A D hrate)
  rw [expectReal_add, expectReal_add] at he
  have hneg : expectReal (commonCoinLaw (1 - x) ht)
      (fun ω => -(if ∀ k ∈ D, ω k = false then (1 : ℝ) else 0)) = -x ^ D.card := by
    have hn : expectReal (commonCoinLaw (1 - x) ht)
        (fun ω => -(if ∀ k ∈ D, ω k = false then (1 : ℝ) else 0)) =
        -expectReal (commonCoinLaw (1 - x) ht)
          (fun ω => if ∀ k ∈ D, ω k = false then (1 : ℝ) else 0) := by
      simp only [expectReal, mul_neg, Finset.sum_neg_distrib]
    rw [hn, coin_all_false_probability]
    simp only [sub_sub_cancel]
  rw [hneg, expectReal_mul_const, expectReal_mul_const, coinCount_mean,
    coinCount_low_mean_inactive x hx A (by omega)] at he
  have hh := mul_le_mul_of_nonneg_left (averaged_high_rate hx hA) (Nat.cast_nonneg A.card : (0 : ℝ) ≤ _)
  nlinarith

variable {V C : Type*} [Fintype V] [Fintype C]

def activeRegularCharge (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (c : C) (hca : c ≠ X v) (hcb : c ≠ Y v) (gain loss : ℝ) (ω : I.Constraint → Bool) : ℝ :=
  let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
  correctedRegularCharge h (optimizedChoice h) c hca hcb gain loss

theorem activeRegularCharge_le_coinEnvelope (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (c : C) (hca : c ≠ X v) (hcb : c ≠ Y v)
    {gain loss : ℝ} (hgain : 0 ≤ gain) (hloss : loss ≤ 81 / 500) (ω : I.Constraint → Bool) :
    activeRegularCharge I X Y v hroot hagree c hca hcb gain loss ω ≤
      coinColourEnvelope (rootColourEdges I X v c) (rootColourBoundarySet I v c) (low gain loss) ω := by
  let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
  change correctedRegularCharge h (optimizedChoice h) c hca hcb gain loss ≤ _
  unfold coinColourEnvelope
  simp only [← root_available_iff_boundary_false I X v c hca ω,
    ← activeRootNeighbours_card_eq_coinCount I X v c hca ω]
  by_cases hav : c ∈ (activeHardListInstance I (activatedSet I X ω)).list v
  · rw [if_pos hav]
    by_cases hk : (rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v c).card ≤ 2
    · rw [if_pos hk]
      exact correctedRegularCharge_available_low_le h hca hcb hav hk gain loss
    · rw [if_neg hk]
      exact correctedRegularCharge_available_high_le h (optimizedChoice h) hca hcb hav
        (by omega) hgain (by linarith)
  · rw [if_neg hav]
    exact correctedRegularCharge_unavailable_le h (optimizedChoice h) hca hcb hav gain hloss

theorem expected_activeRegularCharge_low (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (c : C) (hca : c ≠ X v) (hcb : c ≠ Y v)
    (hm : (physicalColourIncidences I X v c).card ≤ 2)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {gain loss : ℝ} (hgain : 0 ≤ gain) (hloss : loss ≤ 81 / 500) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (activeRegularCharge I X Y v hroot hagree c hca hcb gain loss) ≤
      -x ^ I.boundaryCount v c +
        (1 - x) * low gain loss * (physicalColourIncidences I X v c).card * x ^ I.boundaryCount v c +
        bulk * ((physicalColourIncidences I X v c).card -
          (physicalColourIncidences I X v c).card * x ^ I.boundaryCount v c) := by
  have hp := expectReal_mono
    (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    (activeRegularCharge_le_coinEnvelope I X Y v hroot hagree c hca hcb hgain hloss)
  have he := coinColourEnvelope_low_expect x hx (rootColourEdges I X v c) (rootColourBoundarySet I v c)
    (rootColourEdges_boundary_disjoint I X v c c) (by simpa only [rootColourEdges_card] using hm) (low gain loss)
  exact hp.trans (by simpa only [rootColourEdges_card, rootColourBoundarySet_card] using he)

theorem expected_activeRegularCharge_high (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (c : C) (hca : c ≠ X v) (hcb : c ≠ Y v)
    (hm : 3 ≤ (physicalColourIncidences I X v c).card)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {gain loss : ℝ} (hgain : 51 / 2200 ≤ gain) (hloss : loss ≤ 81 / 500) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (activeRegularCharge I X Y v hroot hagree c hca hcb gain loss) ≤
      -x ^ I.boundaryCount v c + bulk * (physicalColourIncidences I X v c).card := by
  have hp := expectReal_mono
    (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    (activeRegularCharge_le_coinEnvelope I X Y v hroot hagree c hca hcb (by linarith : 0 ≤ gain) hloss)
  have he := coinColourEnvelope_high_expect x hx (rootColourEdges I X v c) (rootColourBoundarySet I v c)
    (by simpa only [rootColourEdges_card] using hm) (low_le_uniform hgain hloss)
  exact hp.trans (by simpa only [rootColourEdges_card, rootColourBoundarySet_card] using he)

lemma physicalColourIncidences_eq_of_agree (I : PinningData V C) (X Y : V → C) (v : V)
    (hagree : ∀ u, u ≠ v → X u = Y u) (c : C) :
    physicalColourIncidences I X v c = physicalColourIncidences I Y v c := by
  ext u
  simp only [physicalColourIncidences, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hagree u.val u.property.ne.symm]

theorem expected_activeRootColourCharge [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => rootColourCharge (activeHardListInstance I (activatedSet I X ω))
        (activeHardListInstance I (activatedSet I Y ω)) X Y v) ≤
      -x ^ I.boundaryCount v (X v) + bulk * (physicalColourIncidences I X v (X v)).card := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hp := expectReal_mono (commonCoinLaw (K := I.Constraint) (1 - x) ht)
    (fun ω => rootColourCharge_le (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree))
  rw [expectReal_sub, expectReal_mul_const, expected_rootMultiplicity I Y v (X v) hroot x hx,
    expected_root_available I Y v (X v) hroot x hx,
    ← physicalColourIncidences_eq_of_agree I X Y v hagree] at hp
  have hm : (0 : ℝ) ≤ (physicalColourIncidences I X v (X v)).card := Nat.cast_nonneg _
  have hb : 0 ≤ bulk := by norm_num [bulk]
  have hh := mul_nonneg (mul_nonneg hb hm) hx.1
  nlinarith

end
end CI2ZF.Appendix.CV
