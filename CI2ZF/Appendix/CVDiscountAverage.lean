import CI2ZF.Appendix.CVDiscountActivation
import CI2ZF.Appendix.CVDiscountCredit

/-! Actual activation averages for the ordered-incidence balance. The
safe event alone certifies a singleton cross pair, giving a stronger
credit than the additional-inactivity event in the printed argument. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

abbrev AdjacentChoices (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ w, w ≠ v → X w = Y w) :=
  ∀ ω : I.Constraint → Bool,
    GlobalChoice (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree)

def activityCoins (I : PinningData V C) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    FinDist (I.Constraint → Bool) :=
  commonCoinLaw (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩

def allTargetsInactive (I : PinningData V C) (X Y : V → C) (v u : V)
    (ω : I.Constraint → Bool) : Prop := ∀ k ∈ targetConstraints I X Y v u, ω k = false

def adjacentHardCoupling [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (ω : I.Constraint → Bool) :
    Coupling (hardStep (activeHardListInstance I (activatedSet I X ω)) X)
      (hardStep (activeHardListInstance I (activatedSet I Y ω)) Y) :=
  fullHardCoupling (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) (choice ω)

def averagedCost [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (f : (V → C) → (V → C) → ℝ) : ℝ :=
  expectReal (activityCoins I x hx) fun ω => (adjacentHardCoupling I X Y v hroot hagree choice ω).cost f

lemma allTargetsInactive_probability (I : PinningData V C) (X Y : V → C) (v u : V)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx) (fun ω => if allTargetsInactive I X Y v u ω then 1 else 0) =
      x^(targetConstraints I X Y v u).card := by
  have hh := coinPatternProbability_eq_inactive x hx (∅ : Finset I.Constraint)
    (targetConstraints I X Y v u) (by simp)
  simpa [activityCoins, coinPatternProbability, coinPattern, allTargetsInactive] using hh

/-- The averaged target-loss rate includes exactly the probability that
all physical target blockers are inactive. -/
theorem adjacentHard_badMass_average [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (u : V) (hu : regularAt X Y v u) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx) (fun ω =>
      rootFixedBadMass (adjacentHardCoupling I X Y v hroot hagree choice ω) v u (X v) (Y v)) ≤
    (1 + 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) +
      ((1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C)) *
        x^(targetConstraints I X Y v u).card := by
  have huv : u ≠ v := by intro hh; subst u; exact hu.2.1 rfl
  have hpoint (ω : I.Constraint → Bool) :
      rootFixedBadMass (adjacentHardCoupling I X Y v hroot hagree choice ω) v u (X v) (Y v) ≤
      (1 + 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) +
        ((1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C)) *
          (if allTargetsInactive I X Y v u ω then 1 else 0) := by
    let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
    by_cases hinactive : allTargetsInactive I X Y v u ω
    · have hh := fullHardCoupling_root_fixed_badAt_le h (choice ω) u huv hu.2.1 hu.2.2
      change rootFixedBadMass (adjacentHardCoupling I X Y v hroot hagree choice ω) v u (X v) (Y v) ≤ _ at hh
      rw [if_pos hinactive]
      exact hh.trans_eq (by ring)
    · have he : ∃ k ∈ targetConstraints I X Y v u, ω k = true := by
        unfold allTargetsInactive at hinactive
        push Not at hinactive
        obtain ⟨k, hk, hn⟩ := hinactive
        exact ⟨k, hk, by simpa using hn⟩
      obtain ⟨k, hk, hcoin⟩ := he
      have hh := fullHardCoupling_active_blocker_badMass_le h (choice ω) huv hu.2.1 hu.2.2
        (active_targetConstraint_is_blocker I X Y ω v u hu hagree k hk hcoin)
      rw [if_neg hinactive, mul_zero, add_zero]
      exact hh
  have hh := expectReal_mono (activityCoins I x hx) hpoint
  rw [expectReal_add, expectReal_const, expectReal_mul_const, allTargetsInactive_probability] at hh
  exact hh

/-- The safe event alone supplies the cross-pair mass, without requiring
any extra inactivity at the neighbour receiving the output credit. -/
theorem adjacentHard_cross_average_lower [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (u : I.graph.neighborSet v) (hu : regularAt X Y v u.val)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C)) *
      ((1 - x) * x^(blockerCount I X Y v u.val)) ≤
    expectReal (activityCoins I x hx) (fun ω =>
      (adjacentHardCoupling I X Y v hroot hagree choice ω).w
        (Function.update X u.val (Y v)) (Function.update Y u.val (X v))) := by
  have hpoint (ω : I.Constraint → Bool) :
      ((1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C)) *
        (if safeActivation I X Y v u ω then (1 : ℝ) else 0) ≤
      (adjacentHardCoupling I X Y v hroot hagree choice ω).w
        (Function.update X u.val (Y v)) (Function.update Y u.val (X v)) := by
    by_cases hs : safeActivation I X Y v u ω
    · rw [if_pos hs, mul_one]
      exact fullHardCoupling_safe_cross_lower I X Y v u ω hroot hu hagree (choice ω) hs
    · rw [if_neg hs, mul_zero]
      exact (adjacentHardCoupling I X Y v hroot hagree choice ω).nonneg _ _
  have hh := expectReal_mono (activityCoins I x hx) hpoint
  rw [expectReal_mul_const] at hh
  have hp := safeActivation_probability I X Y v u x hx
  change expectReal (activityCoins I x hx) _ = _ at hp
  rw [hp] at hh
  exact hh

/-- Ordered-incidence input loss minus its actual output credit is bounded
by `(1+P₂)s_u/(nq)`. The stronger safe-only credit cancels the entire extra
inactivity term in the target-loss rate. -/
theorem ordered_incidence_average_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (u : I.graph.neighborSet v) (hu : regularAt X Y v u.val)
    (w : V) (hw : regularAt X Y v w) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx) (fun ω =>
      ((1 - x) * x^(blockerCount I X Y v u.val)) * (1 - x) *
        rootFixedBadMass (adjacentHardCoupling I X Y v hroot hagree choice ω) v w (X v) (Y v) -
      ((1 - x) * x^(targetConstraints I X Y v w).card) *
        (adjacentHardCoupling I X Y v hroot hagree choice ω).w
          (Function.update X u.val (Y v)) (Function.update Y u.val (X v))) ≤
      (1 + 81 / 250) * ((1 - x) * x^(blockerCount I X Y v u.val)) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  have ht : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hs : 0 ≤ (1 - x) * x^(blockerCount I X Y v u.val) := mul_nonneg ht (pow_nonneg hx.1 _)
  have hwgt : 0 ≤ (1 - x) * x^(targetConstraints I X Y v w).card := mul_nonneg ht (pow_nonneg hx.1 _)
  have hl := mul_le_mul_of_nonneg_left (adjacentHard_badMass_average I X Y v hroot hagree choice w hw x hx)
    (mul_nonneg hs ht)
  have hr := mul_le_mul_of_nonneg_left (adjacentHard_cross_average_lower I X Y v hroot hagree choice u hu x hx) hwgt
  rw [expectReal_sub, expectReal_mul_const, expectReal_mul_const]
  have heq :
      (((1 - x) * x^(blockerCount I X Y v u.val)) * (1 - x)) *
        ((1 + 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C) +
          ((1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C)) * x^(targetConstraints I X Y v w).card) -
      ((1 - x) * x^(targetConstraints I X Y v w).card) *
        (((1 - 81 / 250) / ((Fintype.card V : ℝ) * Fintype.card C)) *
          ((1 - x) * x^(blockerCount I X Y v u.val))) =
      ((1 + 81 / 250) * ((1 - x) * x^(blockerCount I X Y v u.val)) /
        ((Fintype.card V : ℝ) * Fintype.card C)) * (1 - x) := by ring
  exact ((sub_le_sub hl hr).trans_eq heq).trans
    (mul_le_of_le_one_right (by positivity) (by linarith [hx.1]))

end
end CI2ZF.Appendix.CV
