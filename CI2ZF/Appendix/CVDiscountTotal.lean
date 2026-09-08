import CI2ZF.Appendix.CVDiscountFreshAccount
import CI2ZF.Appendix.CVColourActivation

/-! Summation of the actual geometric discount accounting. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvDiscountTotalConfigDecEq : DecidableEq (V → C) := Classical.decEq _

lemma coupling_cost_add {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (f g : S → T → ℝ) :
    γ.cost (fun s t => f s t + g s t) = γ.cost f + γ.cost g := by
  simp only [Coupling.cost, mul_add, Finset.sum_add_distrib]

lemma coupling_cost_sub {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (f g : S → T → ℝ) :
    γ.cost (fun s t => f s t - g s t) = γ.cost f - γ.cost g := by
  simp only [Coupling.cost, mul_sub, Finset.sum_sub_distrib]

lemma coupling_cost_const {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (c : ℝ) :
    γ.cost (fun _ _ => c) = c := by
  simp only [Coupling.cost, ← Finset.sum_mul, γ.total_mass, one_mul]

lemma coupling_cost_indicator {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (P : S → T → Prop)
    [∀ s t, Decidable (P s t)] (c : ℝ) :
    γ.cost (fun s t => if P s t then c else 0) =
      c * ∑ s, ∑ t, if P s t then γ.w s t else 0 := by
  simp only [Coupling.cost, Finset.mul_sum, mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> ring

lemma newTargetCount_sum (I : PinningData V C) (X Y U Z : V → C) (v u : V) :
    (newTargetCount I X Y U Z v u : ℝ) =
      ∑ w ∈ regularOtherNeighbours I X Y v u, if badAt X Y U Z v w then 1 else 0 := by
  classical
  simp only [newTargetCount, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

lemma discountLoss_cost [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V)
    {FX FY : HardListInstance V C} (γ : Coupling (hardStep FX X) (hardStep FY Y)) :
    γ.cost (fun U Z => discountLoss I x X Y U Z v u) =
      incidenceDiscount I x X Y v u * rootEventMass γ X Y v +
      incidenceDiscount I x X Y v u * rootFixedBadMass γ v u (X v) (Y v) +
      ∑ w ∈ regularOtherNeighbours I X Y v u,
        (incidenceDiscount I x X Y v u * (1 - x)) * rootFixedBadMass γ v w (X v) (Y v) := by
  have he (U Z : V → C) : discountLoss I x X Y U Z v u =
      (if U v ≠ X v ∨ Z v ≠ Y v then incidenceDiscount I x X Y v u else 0) +
      (if rootFixed X Y U Z v ∧ badAt X Y U Z v u then incidenceDiscount I x X Y v u else 0) +
      ∑ w ∈ regularOtherNeighbours I X Y v u,
        if rootFixed X Y U Z v ∧ badAt X Y U Z v w then
          incidenceDiscount I x X Y v u * (1 - x) else 0 := by
    rw [discountLoss, newTargetCount_sum]
    by_cases hf : rootFixed X Y U Z v
    · have hn : ¬ (U v ≠ X v ∨ Z v ≠ Y v) := by simp only [rootFixed] at hf; tauto
      simp only [hf, hn, if_true, if_false, true_and, Finset.mul_sum, mul_ite, mul_one, mul_zero]
    · have hn : U v ≠ X v ∨ Z v ≠ Y v := by simp only [rootFixed] at hf; tauto
      simp only [hf, hn, if_true, if_false, false_and, Finset.sum_const_zero]
  simp_rw [he]
  rw [coupling_cost_add, coupling_cost_add, coupling_cost_finset_sum,
    coupling_cost_indicator, coupling_cost_indicator]
  congr 1
  · simp only [rootEventMass, rootFixedBadMass, rootFixed, badAt, and_assoc]
  · apply Finset.sum_congr rfl
    intro w _
    rw [coupling_cost_indicator]
    simp only [rootFixedBadMass, rootFixed, badAt, and_assoc]

lemma crossCreditAt_cost [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V)
    {FX FY : HardListInstance V C} (γ : Coupling (hardStep FX X) (hardStep FY Y))
    (hu : regularAt X Y v u) (hadj : I.graph.Adj v u) :
    γ.cost (crossCreditAt I x X Y v u) =
      ∑ w ∈ regularOtherNeighbours I X Y v u,
        ((1 - x) * x^(targetConstraints I X Y v w).card) *
          γ.w (Function.update X u (Y v)) (Function.update Y u (X v)) := by
  change γ.cost (fun U Z => crossCreditAt I x X Y v u U Z) = _
  simp only [crossCreditAt, hu, hadj, true_and]
  rw [coupling_cost_point, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

lemma crossCredit_eq_neighbor_sum (I : PinningData V C) (x : ℝ)
    (X Y U Z : V → C) (v : V) :
    crossCredit I x X Y v U Z =
      ∑ u ∈ I.graph.neighborFinset v, crossCreditAt I x X Y v u U Z := by
  classical
  unfold crossCredit
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro u _ hu
  have hn : ¬ I.graph.Adj v u := by simpa using hu
  simp only [crossCreditAt, hn, false_and, and_false, if_false]

lemma total_discount_pointwise (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y U Z : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ w, w ≠ v → X w = Y w) :
    vertexScore I x X Y v -
      (∑ u ∈ I.graph.neighborFinset v,
        (discountLoss I x X Y U Z v u - crossCreditAt I x X Y v u U Z)) +
      freshGainCost I x X Y v U Z ≤ outputScore I x U Z := by
  have h₁ := root_loss_add_freshGain_le I hx X Y U Z v hagree
  have h₂ := retained_root_add_crossCredit_le_outputScore I hx X Y U Z v hroot
  rw [crossCredit_eq_neighbor_sum I x X Y U Z v] at h₂
  rw [Finset.sum_sub_distrib]
  linarith

lemma net_cost_average_eq [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (u : I.graph.neighborSet v) (hu : regularAt X Y v u.val)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    averagedCost I X Y v hroot hagree choice x hx (fun U Z =>
      discountLoss I x X Y U Z v u.val - crossCreditAt I x X Y v u.val U Z) =
      incidenceDiscount I x X Y v u.val *
        expectReal (activityCoins I x hx) (fun ω =>
          rootEventMass (adjacentHardCoupling I X Y v hroot hagree choice ω) X Y v) +
      incidenceDiscount I x X Y v u.val *
        expectReal (activityCoins I x hx) (fun ω =>
          rootFixedBadMass (adjacentHardCoupling I X Y v hroot hagree choice ω) v u.val (X v) (Y v)) +
      ∑ w ∈ regularOtherNeighbours I X Y v u.val,
        expectReal (activityCoins I x hx) (fun ω =>
          (incidenceDiscount I x X Y v u.val * (1 - x)) *
            rootFixedBadMass (adjacentHardCoupling I X Y v hroot hagree choice ω) v w (X v) (Y v) -
          ((1 - x) * x^(targetConstraints I X Y v w).card) *
            (adjacentHardCoupling I X Y v hroot hagree choice ω).w
              (Function.update X u.val (Y v)) (Function.update Y u.val (X v))) := by
  have hadj : I.graph.Adj v u.val := u.property
  unfold averagedCost
  simp only [coupling_cost_sub, discountLoss_cost, crossCreditAt_cost I x X Y v u.val _ hu hadj,
    expectReal_sub, expectReal_add, expectReal_mul_const, expectReal_finset_sum,
    Finset.sum_sub_distrib]
  ring

lemma adjacentHard_badMass_average_two [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (u : V) (hu : regularAt X Y v u) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx) (fun ω =>
      rootFixedBadMass (adjacentHardCoupling I X Y v hroot hagree choice ω) v u (X v) (Y v)) ≤
      2 / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have huv : u ≠ v := by intro hh; subst u; exact hu.2.1 rfl
  have hp := expectReal_mono (activityCoins I x hx) (fun ω =>
    fullHardCoupling_root_fixed_badAt_le
      (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree)
      (choice ω) u huv hu.2.1 hu.2.2)
  simpa only [expectReal_const, rootFixedBadMass, adjacentHardCoupling] using hp

/-- The true per-incidence net loss, with every neighbour credit already
subtracted, has the claimed geometric coefficient. -/
theorem net_cost_average_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (u : I.graph.neighborSet v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (Δ : ℕ) (hdegree : I.graph.degree u.val ≤ Δ) (R : ℝ)
    (hR : expectReal (activityCoins I x hx) (fun ω =>
      rootEventMass (adjacentHardCoupling I X Y v hroot hagree choice ω) X Y v) ≤
        R / ((Fintype.card V : ℝ) * Fintype.card C)) :
    averagedCost I X Y v hroot hagree choice x hx (fun U Z =>
      discountLoss I x X Y U Z v u.val - crossCreditAt I x X Y v u.val U Z) ≤
      (R + 2 + (1 + 81 / 250) * Δ) * incidenceDiscount I x X Y v u.val /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  by_cases hu : regularAt X Y v u.val
  · rw [net_cost_average_eq I X Y v hroot hagree choice u hu x hx]
    have hs := incidenceDiscount_nonneg I hx X Y v u.val
    have hr := mul_le_mul_of_nonneg_left hR hs
    have hb := mul_le_mul_of_nonneg_left
      (adjacentHard_badMass_average_two I X Y v hroot hagree choice u.val hu x hx) hs
    have he := Finset.sum_le_sum (s := regularOtherNeighbours I X Y v u.val) (fun w hw =>
      ordered_incidence_average_le I X Y v hroot hagree choice u hu w
        ((Finset.mem_filter.mp hw).2.2) x hx)
    change (∑ w ∈ regularOtherNeighbours I X Y v u.val, _) ≤ _ at he
    have hid : incidenceDiscount I x X Y v u.val = (1 - x) * x^(blockerCount I X Y v u.val) :=
      if_pos hu
    rw [← hid] at he
    have hc : (regularOtherNeighbours I X Y v u.val).card ≤ Δ :=
      (Finset.card_filter_le _ _).trans (by simpa using hdegree)
    have hcR : ((regularOtherNeighbours I X Y v u.val).card : ℝ) ≤ Δ := by exact_mod_cast hc
    simp only [Finset.sum_const, nsmul_eq_mul] at he
    have he' := he.trans (mul_le_mul_of_nonneg_right hcR
      (by have := hs; positivity))
    calc
      _ ≤ incidenceDiscount I x X Y v u.val *
            (R / ((Fintype.card V : ℝ) * Fintype.card C)) +
          incidenceDiscount I x X Y v u.val *
            (2 / ((Fintype.card V : ℝ) * Fintype.card C)) +
          (Δ : ℝ) * ((1 + 81 / 250) * incidenceDiscount I x X Y v u.val /
            ((Fintype.card V : ℝ) * Fintype.card C)) := add_le_add (add_le_add hr hb) he'
      _ = _ := by ring
  · have hz : incidenceDiscount I x X Y v u.val = 0 := if_neg hu
    have hn (U Z : V → C) : crossCreditAt I x X Y v u.val U Z = 0 := by
      simp only [crossCreditAt, hu, false_and, if_false]
    simp only [averagedCost, discountLoss, hz, hn, zero_mul, ite_self, add_zero, sub_zero,
      coupling_cost_const, expectReal_const, mul_zero, zero_div, le_refl]

theorem expected_discount_decrease_of_root_bound [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (Δ : ℕ)
    (hdegree : ∀ u, I.graph.degree u + ∑ c, I.boundaryCount u c ≤ Δ) (R : ℝ)
    (hR : expectReal (activityCoins I x hx) (fun ω =>
      rootEventMass (adjacentHardCoupling I X Y v hroot hagree choice ω) X Y v) ≤
        R / ((Fintype.card V : ℝ) * Fintype.card C)) :
    vertexScore I x X Y v - averagedCost I X Y v hroot hagree choice x hx (outputScore I x) ≤
      ((R + 2 + (1 + 81 / 250) * Δ) * vertexScore I x X Y v -
        ((Fintype.card C : ℝ) - Δ - 2) * singleBlockerTotal I x X Y v) /
          ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hp := expectReal_mono (activityCoins I x hx) (fun ω =>
    cost_le_cost (adjacentHardCoupling I X Y v hroot hagree choice ω)
      (fun U Z => total_discount_pointwise I hx X Y U Z v hroot hagree))
  simp only [coupling_cost_add, coupling_cost_sub, coupling_cost_const, coupling_cost_finset_sum,
    expectReal_add, expectReal_sub, expectReal_const, expectReal_finset_sum] at hp
  have hn : (∑ u ∈ I.graph.neighborFinset v,
      averagedCost I X Y v hroot hagree choice x hx (fun U Z =>
        discountLoss I x X Y U Z v u - crossCreditAt I x X Y v u U Z)) ≤
      ∑ u ∈ I.graph.neighborFinset v,
        (R + 2 + (1 + 81 / 250) * Δ) * incidenceDiscount I x X Y v u /
          ((Fintype.card V : ℝ) * Fintype.card C) := by
    apply Finset.sum_le_sum
    intro u hu
    exact net_cost_average_le I X Y v hroot hagree choice ⟨u, by simpa using hu⟩ x hx Δ
      (by change I.graph.degree u ≤ Δ; exact (Nat.le_add_right _ _).trans (hdegree u)) R hR
  have he : (∑ u ∈ I.graph.neighborFinset v,
      (R + 2 + (1 + 81 / 250) * Δ) * incidenceDiscount I x X Y v u /
        ((Fintype.card V : ℝ) * Fintype.card C)) =
      (R + 2 + (1 + 81 / 250) * Δ) * vertexScore I x X Y v /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    rfl
  rw [he] at hn
  simp only [averagedCost, coupling_cost_sub, expectReal_sub] at hn
  have hf := expectReal_mono (activityCoins I x hx) (fun ω =>
    adjacentHard_freshGain_lower I X Y v hroot hagree choice ω x hx Δ hdegree)
  rw [expectReal_const] at hf
  change (((Fintype.card C : ℝ) - Δ - 2) * singleBlockerTotal I x X Y v) /
      ((Fintype.card V : ℝ) * Fintype.card C) ≤
    averagedCost I X Y v hroot hagree choice x hx (freshGainCost I x X Y v) at hf
  rw [sub_div]
  simp only [averagedCost] at hf ⊢
  linarith

/-- Full geometric discount drift of the actual completed coupling,
averaged over the actual common activation law. Every coefficient is
derived from the graph, colours and physical boundary occurrences. -/
theorem expected_discount_decrease_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (L : Finset C)
    (hL : ∀ c ∈ L, c ≠ X v ∧ c ≠ Y v ∧ (physicalColourIncidences I X v c).card ≤ 2)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (Δ : ℕ)
    (hdegree : ∀ u, I.graph.degree u + ∑ c, I.boundaryCount u c ≤ Δ) :
    vertexScore I x X Y v - averagedCost I X Y v hroot hagree choice x hx (outputScore I x) ≤
      (((Fintype.card C : ℝ) - (81 / 250) * (1 - x) *
          (∑ c ∈ L, (physicalColourIncidences I X v c).card * x ^ I.boundaryCount v c) +
          2 + (1 + 81 / 250) * Δ) * vertexScore I x X Y v -
        ((Fintype.card C : ℝ) - Δ - 2) * singleBlockerTotal I x X Y v) /
          ((Fintype.card V : ℝ) * Fintype.card C) := by
  apply expected_discount_decrease_of_root_bound I X Y v hroot hagree choice x hx Δ hdegree
  have hp := expected_active_rootEvent_le I X Y v hroot hagree choice L hL x hx
  apply (le_div_iff₀ (by positivity : 0 < (Fintype.card V : ℝ) * Fintype.card C)).mpr
  simpa only [mul_comm, activityCoins, adjacentHardCoupling] using hp

end
end CI2ZF.Appendix.CV
