import CI2ZF.ActivationLaw

/-! Expected active degrees and the passage from the conditional hard
estimate to the concrete soft-row contraction. -/

namespace CI2ZF
open PottsCI PottsCI.FinDist PottsCI.Vigoda
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section

theorem expectReal_sum {S J : Type*} [Fintype S] [Fintype J]
    (p : FinDist S) (f : J → S → ℝ) :
    expectReal p (fun s => ∑ j, f j s) = ∑ j, expectReal p (f j) := by
  simp only [expectReal, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem expectReal_sub {S : Type*} [Fintype S] (p : FinDist S) (f g : S → ℝ) :
    expectReal p (fun s => f s - g s) = expectReal p f - expectReal p g := by
  simp only [expectReal, mul_sub, Finset.sum_sub_distrib]

theorem expectReal_add {S : Type*} [Fintype S] (p : FinDist S) (f g : S → ℝ) :
    expectReal p (fun s => f s + g s) = expectReal p f + expectReal p g := by
  simp only [expectReal, mul_add, Finset.sum_add_distrib]

theorem expectReal_mul_const {S : Type*} [Fintype S] (p : FinDist S)
    (f : S → ℝ) (c : ℝ) : expectReal p (fun s => c * f s) = c * expectReal p f := by
  unfold expectReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem expected_coin {K : Type*} [Fintype K] [DecidableEq K]
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) (k : K) :
    expectReal (commonCoinLaw t ht) (fun ω => if ω k then (1 : ℝ) else 0) = t := by
  simpa [commonCoinLaw, expectReal, bernoulliLaw] using
    expectReal_product_coordinate (fun _ : K => bernoulliLaw t ht) k
      (fun b : Bool => if b then (1 : ℝ) else 0)

variable {V C : Type*} [Fintype V] [Fintype C]

/-- The physical free-edge constraint corresponding to a root neighbour. -/
def rootFreeConstraint (I : PinningData V C) (v : V) (u : I.graph.neighborSet v) :
    I.Constraint := Sum.inl ⟨s(v, u.1), by
      rw [SimpleGraph.mem_edgeFinset]
      exact u.2⟩

def rootFreeCoinCount (I : PinningData V C) (v : V) (ω : I.Constraint → Bool) : ℝ :=
  ∑ u : I.graph.neighborSet v, if ω (rootFreeConstraint I v u) then 1 else 0

def rootBoundaryCoinCount (I : PinningData V C) (v : V) (ω : I.Constraint → Bool) : ℝ :=
  ∑ c : C, ∑ i : Fin (I.boundaryCount v c), if ω (Sum.inr ⟨v, c, i⟩) then 1 else 0

def rootCommonListCount (I : PinningData V C) (X Y : V → C)
    (v : V) (ω : I.Constraint → Bool) : ℝ :=
  ∑ c : C, if c ∈ activeList I (activatedSet I X ω) v ∧
      c ∈ activeList I (activatedSet I Y ω) v then 1 else 0

theorem rootCommonListCount_eq_card (I : PinningData V C) (X Y : V → C)
    (v : V) (ω : I.Constraint → Bool) :
    rootCommonListCount I X Y v ω =
      ((activeList I (activatedSet I X ω) v ∩
        activeList I (activatedSet I Y ω) v).card : ℝ) := by
  rw [rootCommonListCount, ← Finset.natCast_card_filter]
  congr 2
  ext c
  simp

theorem expected_rootFreeCoinCount (I : PinningData V C) (v : V)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    expectReal (commonCoinLaw t ht) (rootFreeCoinCount I v) = I.graph.degree v * t := by
  unfold rootFreeCoinCount
  rw [expectReal_sum]
  simp only [expected_coin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    SimpleGraph.card_neighborSet_eq_degree]

theorem expected_rootBoundaryCoinCount (I : PinningData V C) (v : V)
    (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    expectReal (commonCoinLaw t ht) (rootBoundaryCoinCount I v) =
      (∑ c, (I.boundaryCount v c : ℝ)) * t := by
  unfold rootBoundaryCoinCount
  simp_rw [expectReal_sum, expected_coin]
  simp [← Finset.sum_mul]

/-- Every excluded colour consumes at least one successful labelled
boundary coin. Coin multiplicities can only increase this upper bound. -/
theorem root_common_list_budget (I : PinningData V C) (X Y : V → C)
    (v : V) (ω : I.Constraint → Bool) :
    (Fintype.card C : ℝ) ≤ rootCommonListCount I X Y v ω + rootBoundaryCoinCount I v ω := by
  unfold rootCommonListCount rootBoundaryCoinCount
  rw [← Finset.sum_add_distrib]
  have hsingle (c : C) : (1 : ℝ) ≤
      (if c ∈ activeList I (activatedSet I X ω) v ∧
        c ∈ activeList I (activatedSet I Y ω) v then 1 else 0) +
      ∑ i : Fin (I.boundaryCount v c), if ω (Sum.inr ⟨v, c, i⟩) then 1 else 0 := by
    have hallowed (h : ∀ i : Fin (I.boundaryCount v c), ω (Sum.inr ⟨v, c, i⟩) ≠ true)
        (Z : V → C) : c ∈ activeList I (activatedSet I Z ω) v := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rintro ⟨i, hi⟩
      exact h i ((mem_activatedSet I Z ω _).mp hi).1
    by_cases h : c ∈ activeList I (activatedSet I X ω) v ∧
        c ∈ activeList I (activatedSet I Y ω) v
    · simp only [if_pos h]
      have hn : 0 ≤ ∑ i : Fin (I.boundaryCount v c),
          (if ω (Sum.inr ⟨v, c, i⟩) then (1 : ℝ) else 0) :=
        Finset.sum_nonneg fun i _ => by split <;> norm_num
      linarith
    · have he : ∃ i : Fin (I.boundaryCount v c), ω (Sum.inr ⟨v, c, i⟩) = true := by
        by_contra hn
        have hall : ∀ i : Fin (I.boundaryCount v c), ω (Sum.inr ⟨v, c, i⟩) ≠ true :=
          fun i hi => hn ⟨i, hi⟩
        exact h ⟨hallowed hall X, hallowed hall Y⟩
      obtain ⟨i, hi⟩ := he
      simp only [if_neg h, zero_add]
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (I.boundaryCount v c) =>
          if ω (Sum.inr ⟨v, c, j⟩) then (1 : ℝ) else 0)
        (fun j _ => by split <;> norm_num) (Finset.mem_univ i)
      simpa [hi] using hle
  simpa using Finset.sum_le_sum (s := Finset.univ) (fun c _ => hsingle c)

theorem expected_rootCommonListCount_lower (I : PinningData V C)
    (X Y : V → C) (v : V) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    (Fintype.card C : ℝ) - (∑ c, (I.boundaryCount v c : ℝ)) * t ≤
      expectReal (commonCoinLaw t ht) (rootCommonListCount I X Y v) := by
  have h := expectReal_mono (commonCoinLaw t ht) (fun ω => root_common_list_budget I X Y v ω)
  rw [expectReal_const, expectReal_add, expected_rootBoundaryCoinCount] at h
  linarith

/-- Averaging the conditional hard estimate gives the exact soft contraction
coefficient. The only remaining dynamical premise is the hard estimate;
activation marginals, degree averaging and list budgets are all proved. -/
theorem softVigoda_contraction_of_hard_estimate [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (hconditional : ∀ ω : I.Constraint → Bool,
      ((Fintype.card V : ℝ) * Fintype.card C) *
        (W ham (hardStep (activeHardListInstance I (activatedSet I X ω)) X)
          (hardStep (activeHardListInstance I (activatedSet I Y ω)) Y) - 1) ≤
      (11 / 6 : ℝ) * rootFreeCoinCount I v ω - rootCommonListCount I X Y v ω) :
    W ham (softVigodaKernel I x hx0 hx1 X) (softVigodaKernel I x hx0 hx1 Y) ≤
      1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  let p := commonCoinLaw (K := I.Constraint) (1 - x) ht
  let w (ω : I.Constraint → Bool) := W ham
    (hardStep (activeHardListInstance I (activatedSet I X ω)) X)
    (hardStep (activeHardListInstance I (activatedSet I Y ω)) Y)
  have havg := expectReal_mono p hconditional
  change expectReal p (fun ω => ((Fintype.card V : ℝ) * Fintype.card C) * (w ω - 1)) ≤ _ at havg
  rw [expectReal_mul_const, expectReal_sub, expectReal_const,
    expectReal_sub, expectReal_mul_const] at havg
  have hf : expectReal p (rootFreeCoinCount I v) = I.graph.degree v * (1 - x) :=
    expected_rootFreeCoinCount I v (1 - x) ht
  rw [hf] at havg
  have hl : (Fintype.card C : ℝ) - (∑ c, (I.boundaryCount v c : ℝ)) * (1 - x) ≤
      expectReal p (rootCommonListCount I X Y v) :=
    expected_rootCommonListCount_lower I X Y v (1 - x) ht
  have hd : (I.graph.degree v : ℝ) + (∑ c, (I.boundaryCount v c : ℝ)) ≤ Δ := by
    exact_mod_cast hdegree v
  have hb : 0 ≤ ∑ c, (I.boundaryCount v c : ℝ) := by positivity
  have hdeg : 0 ≤ (I.graph.degree v : ℝ) := by positivity
  have ht0 : 0 ≤ 1 - x := ht.1
  have hsum : (I.graph.degree v : ℝ) * (1 - x) +
      (∑ c, (I.boundaryCount v c : ℝ)) * (1 - x) ≤ (Δ : ℝ) * (1 - x) := by
    nlinarith [mul_le_mul_of_nonneg_right hd ht0]
  have hnq : 0 < (Fintype.card V : ℝ) * (Fintype.card C : ℝ) := by
    exact mul_pos (by exact_mod_cast Fintype.card_pos (α := V))
      (by exact_mod_cast Fintype.card_pos (α := C))
  have htarget : expectReal p w ≤
      1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
    have hcancel : ((Fintype.card V : ℝ) * Fintype.card C) *
        (1 - ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) /
          ((Fintype.card V : ℝ) * Fintype.card C)) =
        ((Fintype.card V : ℝ) * Fintype.card C) -
          ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x) * Δ) := by
      field_simp
    nlinarith [mul_nonneg hb ht0]
  exact (softVigoda_W_le_average I X Y x hx0 hx1).trans htarget

end
end CI2ZF
