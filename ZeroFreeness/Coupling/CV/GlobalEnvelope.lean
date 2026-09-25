import ZeroFreeness.Coupling.CV.ActivationEnvelope

/-! Summing the actual corrected colour charges and paying for missing
baselines with the physical boundary-degree budget. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def colourLossCount {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (_h : RootLocalPair FX FY X Y v a b) (c : C) : ℝ :=
  if c ≠ a ∧ c ≠ b then
    if c ∈ FX.list v then (safety11Count FX FY X Y v c : ℝ)
    else ((rootNeighbours FX X v c).card : ℝ) else 0

def colourGainCount {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b : C} (_h : RootLocalPair FX FY X Y v a b) (c : C) : ℝ :=
  if c ≠ a ∧ c ≠ b ∧ c ∈ FX.list v then (safety12Count FX FY X Y v c : ℝ) else 0

def correctedHardColourCharge [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (gain loss : ℝ) (c : C) : ℝ :=
  hardColourCharge h choice c + loss * colourLossCount h c - gain * colourGainCount h c

lemma correctedHardColourCharge_regular [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (gain loss : ℝ) :
    correctedHardColourCharge h choice gain loss c = correctedRegularCharge h choice c hca hcb gain loss := by
  unfold correctedHardColourCharge hardColourCharge correctedRegularCharge colourLossCount colourGainCount
  by_cases hav : c ∈ FX.list v <;> simp [hca, hcb, hav]

lemma correctedHardColourCharge_root_left [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (gain loss : ℝ) :
    correctedHardColourCharge h choice gain loss a = rootColourCharge FX FY X Y v := by
  simp [correctedHardColourCharge, hardColourCharge, colourLossCount, colourGainCount]

lemma correctedHardColourCharge_root_right [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (gain loss : ℝ) :
    correctedHardColourCharge h choice gain loss b = rootColourCharge FY FX Y X v := by
  simp [correctedHardColourCharge, hardColourCharge, colourLossCount, colourGainCount, h.colours_ne.symm]

lemma sum_correctedHardColourCharge [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h) (gain loss : ℝ) :
    (∑ c, correctedHardColourCharge h choice gain loss c) =
      (∑ c, hardColourCharge h choice c) + loss * (∑ c, colourLossCount h c) -
        gain * (∑ c, colourGainCount h c) := by
  simp only [correctedHardColourCharge, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]

def physicalLowColours (I : PinningData V C) (X Y : V → C) (v : V) : Finset C :=
  Finset.univ.filter fun c => c ≠ X v ∧ c ≠ Y v ∧ (physicalColourIncidences I X v c).card ≤ 2

def lowAvailabilityMass (I : PinningData V C) (X Y : V → C) (v : V) (x : ℝ) : ℝ :=
  ∑ c ∈ physicalLowColours I X Y v,
    (physicalColourIncidences I X v c).card * x ^ I.boundaryCount v c

lemma sum_physicalColourIncidences (I : PinningData V C) (X : V → C) (v : V) :
    (∑ c : C, ((physicalColourIncidences I X v c).card : ℝ)) = I.graph.degree v := by
  simp only [physicalColourIncidences, Finset.natCast_card_filter]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, SimpleGraph.card_neighborSet_eq_degree]

lemma lowAvailabilityMass_nonneg (I : PinningData V C) (X Y : V → C) (v : V)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ lowAvailabilityMass I X Y v x := by
  apply Finset.sum_nonneg
  intro c _
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)

lemma lowAvailabilityMass_le_degree (I : PinningData V C) (X Y : V → C) (v : V)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : lowAvailabilityMass I X Y v x ≤ I.graph.degree v := by
  calc
    _ ≤ ∑ c ∈ physicalLowColours I X Y v, ((physicalColourIncidences I X v c).card : ℝ) := by
      apply Finset.sum_le_sum
      intro c _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hx.1 hx.2)
        (Nat.cast_nonneg (physicalColourIncidences I X v c).card : (0 : ℝ) ≤ _)
    _ ≤ ∑ c : C, ((physicalColourIncidences I X v c).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun c _ _ => Nat.cast_nonneg _)
    _ = _ := sum_physicalColourIncidences I X v

lemma availability_baseline_budget (I : PinningData V C) (v : V)
    {x : ℝ} (hx : 0 ≤ x) :
    (Fintype.card C : ℝ) - ∑ c : C, (I.boundaryCount v c : ℝ) ≤
      ∑ c : C, x ^ I.boundaryCount v c := by
  have he (c : C) : 1 - (I.boundaryCount v c : ℝ) ≤ x ^ I.boundaryCount v c := by
    by_cases hc : I.boundaryCount v c = 0
    · simp [hc]
    · have hb : (1 : ℝ) ≤ I.boundaryCount v c := by exact_mod_cast (show 1 ≤ I.boundaryCount v c by omega)
      have hp := pow_nonneg hx (I.boundaryCount v c)
      linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => he c)
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hs

theorem expected_correctedHardColourCharge_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (c : C) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {gain loss : ℝ} (hgain : 51 / 2200 ≤ gain) (hloss : loss ≤ 81 / 500) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
        correctedHardColourCharge h (optimizedChoice h) gain loss c) ≤
      -x ^ I.boundaryCount v c + bulk * (physicalColourIncidences I X v c).card +
        ((1 - x) * low gain loss - bulk) *
          (if c ∈ physicalLowColours I X Y v then
            (physicalColourIncidences I X v c).card * x ^ I.boundaryCount v c else 0) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  change expectReal (commonCoinLaw (1 - x) ht) _ ≤ _
  by_cases hca : c = X v
  · subst c
    simp only [correctedHardColourCharge_root_left]
    have hn : X v ∉ physicalLowColours I X Y v := by simp [physicalLowColours]
    rw [if_neg hn, mul_zero, add_zero]
    exact expected_activeRootColourCharge I X Y v hroot hagree x hx
  by_cases hcb : c = Y v
  · subst c
    simp only [correctedHardColourCharge_root_right]
    have hn : Y v ∉ physicalLowColours I X Y v := by simp [physicalLowColours]
    rw [if_neg hn, mul_zero, add_zero]
    have hp := expected_activeRootColourCharge I Y X v hroot.symm (fun u hu => (hagree u hu).symm) x hx
    simpa only [← physicalColourIncidences_eq_of_agree I X Y v hagree] using hp
  simp only [correctedHardColourCharge_regular _ _ hca hcb]
  change expectReal (commonCoinLaw (1 - x) ht)
    (activeRegularCharge I X Y v hroot hagree c hca hcb gain loss) ≤ _
  by_cases hm : (physicalColourIncidences I X v c).card ≤ 2
  · have hc : c ∈ physicalLowColours I X Y v := by simp [physicalLowColours, hca, hcb, hm]
    rw [if_pos hc]
    have hp := expected_activeRegularCharge_low I X Y v hroot hagree c hca hcb hm x hx (by linarith : 0 ≤ gain) hloss
    nlinarith
  · have hc : c ∉ physicalLowColours I X Y v := by simp [physicalLowColours, hm]
    rw [if_neg hc, mul_zero, add_zero]
    exact expected_activeRegularCharge_high I X Y v hroot hagree c hca hcb (by omega) x hx hgain hloss

/-- The full corrected colour sum of the actual activated CV coupling
satisfies the appendix's degree envelope, with no assumed drift bound. -/
theorem expected_correctedHardCharge_envelope [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    {gain loss : ℝ} (hgain : 51 / 2200 ≤ gain) (hloss : loss ≤ 81 / 500) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
        ∑ c, correctedHardColourCharge h (optimizedChoice h) gain loss c) ≤
      -(Fintype.card C : ℝ) + (1 - x) * low gain loss * lowAvailabilityMass I X Y v x +
        bulk * ((Δ : ℝ) - lowAvailabilityMass I X Y v x) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun c _ => expected_correctedHardColourCharge_le I X Y v hroot hagree c x hx hgain hloss)
  rw [← expectReal_sum] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum,
    sum_physicalColourIncidences] at hs
  have hlo : (∑ c, if c ∈ physicalLowColours I X Y v then
      (physicalColourIncidences I X v c).card * x ^ I.boundaryCount v c else 0) =
      lowAvailabilityMass I X Y v x := by simp [lowAvailabilityMass]
  rw [hlo] at hs
  have hb := availability_baseline_budget I v hx.1
  have hd : (I.graph.degree v : ℝ) + ∑ c : C, (I.boundaryCount v c : ℝ) ≤ Δ := by
    exact_mod_cast hdegree v
  have hB : 0 ≤ ∑ c : C, (I.boundaryCount v c : ℝ) := by positivity
  have hb1 : 1 ≤ bulk := by norm_num [bulk]
  have hb0 : 0 ≤ bulk := by norm_num [bulk]
  have hh := mul_le_mul_of_nonneg_left hd hb0
  have hh' := mul_le_mul_of_nonneg_right hb1 hB
  nlinarith

end
end ZeroFreeness.Appendix.CV
