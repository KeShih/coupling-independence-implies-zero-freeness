import ZeroFreeness.Coupling.Vigoda.ActivationLaw

/-!
# Coupled activation is root-local (main text and companion, `lem:coupled-activation-root-local`)

`lem:coupled-activation-root-local` (main.tex Lemma 4.8 = companion Lemma 3.5)
on the paper's full range `x ∈ (0,1]`, as one declaration.

The paper's statement: for adjacent colourings `X, Y` differing at `v`, with
`X_v = a ≠ b = Y_v`, draw one independent Bernoulli(`1-x`) coin per labelled
constraint and activate that constraint on either side exactly when the coin
is one and the inequality is satisfied there.  This common-coin construction
has the correct activation marginals.  The two hard instances have the same
induced graph and lists off `v`; their edge sets at `v` can differ only at
neighbours of colour `a` or `b`, and their lists at `v` only in those two
colours.

Formalization.
* `activationLaw I x hx0 hx1 σ` (for `0 < x ≤ 1`) is the conditional law of
  the active set given the colouring `σ` in the joint spin/active-set
  representation, `A ↦ jointActiveWeight x A σ / weight x σ`.  It agrees with
  the library's `PinningData.activeLawGivenSpin` for `x < 1`
  (`activationLaw_eq_activeLawGivenSpin`), is the product law "activate every
  satisfied constraint independently with probability `1-x`"
  (`activationLaw_w_eq_prod`), and at `x = 1` is the point mass at `∅`
  (`activationLaw_one`: no constraint is activated).
* The common-coin construction is `activatedSet I X ω`, `ω` distributed as
  `commonCoinLaw (1-x)` (independent Bernoulli(`1-x`) coins on
  `I.Constraint` = free edges ⊕ labelled free–pinned occurrences).
* `RootLocalPair` (library) records exactly the four locality claims.

Main declaration: `coupled_activation_root_local`.
-/

namespace ZeroFreeness

open PottsCI PottsCI.FinDist PottsCI.Vigoda ZeroFreeness
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C]

lemma coinParam {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : 1 - x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith, by linarith⟩

/-- The activation law given the colouring `σ`, on the full range `0 < x ≤ 1`. -/
def activationLaw (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (σ : V → C) : FinDist (Finset I.Constraint) where
  w A := I.jointActiveWeight x A σ / I.weight x σ
  nonneg A := div_nonneg (I.jointActiveWeight_nonneg hx0.le hx1 A σ) (I.weight_pos hx0 σ).le
  sum_one := by
    rw [← Finset.sum_div, I.sum_jointActiveWeight_eq_weight]
    exact div_self (I.weight_pos hx0 σ).ne'

/-- For `x < 1` this is the library's conditional active-set law, used by the
soft kernels. -/
theorem activationLaw_eq_activeLawGivenSpin (I : PinningData V C) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (σ : V → C) :
    activationLaw I x hx0 hx1.le σ = I.activeLawGivenSpin x hx0 hx1 σ := by
  ext A
  rfl

/-- Probability that the constraint `k` is activated at `σ`: `1-x` if it is
satisfied, `0` otherwise. -/
def activationProb (I : PinningData V C) (x : ℝ) (σ : V → C) (k : I.Constraint) : ℝ :=
  if I.constraintSatisfied σ k then 1 - x else 0

omit [Fintype C] in
lemma coin_coordinate_weight (I : PinningData V C) (X : V → C) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (A : Finset I.Constraint) (k : I.Constraint) :
    (mapLaw (bernoulliLaw (1 - x) (coinParam hx0 hx1))
      (fun b => b && decide (I.constraintSatisfied X k))).w (decide (k ∈ A)) =
      if k ∈ A then activationProb I x X k else 1 - activationProb I x X k := by
  by_cases hs : I.constraintSatisfied X k <;> by_cases ha : k ∈ A <;>
    simp [mapLaw, FinDist.bind_w, FinDist.pure, bernoulliLaw, activationProb, hs, ha]

omit [Fintype C] in
lemma coin_coordinate_weight' (I : PinningData V C) (X : V → C) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (A : Finset I.Constraint) (k : I.Constraint) :
    (mapLaw (bernoulliLaw (1 - x) (coinParam hx0 hx1))
      (fun b => b && decide (I.constraintSatisfied X k))).w (decide (k ∈ A)) =
      (if k ∈ A then I.activationFactor x X k else x) / I.constraintFactor x X k := by
  by_cases hs : I.constraintSatisfied X k <;> by_cases ha : k ∈ A <;>
    simp [mapLaw, FinDist.bind_w, FinDist.pure, bernoulliLaw,
      PinningData.activationFactor, PinningData.constraintFactor, hs, ha, hx0.ne']

/-- The law of the common-coin active set at `X` is a product over the
constraints: each constraint is in the active set with probability
`activationProb`, independently. -/
theorem coinActivation_w_eq_prod (I : PinningData V C) (X : V → C) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (A : Finset I.Constraint) :
    (mapLaw (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
      (activatedSet I X)).w A =
      ∏ k : I.Constraint, (if k ∈ A then activationProb I x X k
        else 1 - activationProb I x X k) := by
  let ht := coinParam hx0 hx1
  let p := commonCoinLaw (K := I.Constraint) (1 - x) ht
  let f : I.Constraint → Bool → Bool :=
    fun k b => b && decide (I.constraintSatisfied X k)
  have hm : mapLaw p (fun ω k => f k (ω k)) =
      productLaw (fun k => mapLaw (bernoulliLaw (1 - x) ht) (f k)) :=
    map_productLaw (fun _ : I.Constraint => bernoulliLaw (1 - x) ht) f
  have hcomp : mapLaw p (activatedSet I X) =
      mapLaw (productLaw (fun k => mapLaw (bernoulliLaw (1 - x) ht) (f k)))
        bitsEquivFinset := by
    calc
      _ = mapLaw (mapLaw p (fun ω k => f k (ω k))) bitsEquivFinset :=
        (mapLaw_comp p (fun ω k => f k (ω k)) bitsEquivFinset).symm
      _ = _ := congrArg (fun law : FinDist (I.Constraint → Bool) =>
          mapLaw law bitsEquivFinset) hm
  change (mapLaw p (activatedSet I X)).w A = _
  rw [hcomp, mapLaw_equiv_w]
  change (∏ k : I.Constraint,
    (mapLaw (bernoulliLaw (1 - x) ht)
      (fun b => b && decide (I.constraintSatisfied X k))).w (decide (k ∈ A))) = _
  simp_rw [coin_coordinate_weight I X hx0 hx1 A]

/-- **Correct activation marginals, `0 < x ≤ 1`.**  The common-coin active set
at `X` has exactly the conditional activation law. -/
theorem coinActivation_law (I : PinningData V C) (X : V → C) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    mapLaw (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
      (activatedSet I X) = activationLaw I x hx0 hx1 X := by
  let ht := coinParam hx0 hx1
  let p := commonCoinLaw (K := I.Constraint) (1 - x) ht
  let f : I.Constraint → Bool → Bool :=
    fun k b => b && decide (I.constraintSatisfied X k)
  have hm : mapLaw p (fun ω k => f k (ω k)) =
      productLaw (fun k => mapLaw (bernoulliLaw (1 - x) ht) (f k)) :=
    map_productLaw (fun _ : I.Constraint => bernoulliLaw (1 - x) ht) f
  have hcomp : mapLaw p (activatedSet I X) =
      mapLaw (productLaw (fun k => mapLaw (bernoulliLaw (1 - x) ht) (f k)))
        bitsEquivFinset := by
    calc
      _ = mapLaw (mapLaw p (fun ω k => f k (ω k))) bitsEquivFinset :=
        (mapLaw_comp p (fun ω k => f k (ω k)) bitsEquivFinset).symm
      _ = _ := congrArg (fun law : FinDist (I.Constraint → Bool) =>
          mapLaw law bitsEquivFinset) hm
  change mapLaw p (activatedSet I X) = _
  rw [hcomp]
  apply FinDist.ext
  funext A
  rw [mapLaw_equiv_w]
  change (∏ k : I.Constraint,
    (mapLaw (bernoulliLaw (1 - x) ht)
      (fun b => b && decide (I.constraintSatisfied X k))).w (decide (k ∈ A))) = _
  simp_rw [coin_coordinate_weight' I X hx0 hx1 A]
  rw [Finset.prod_div_distrib, ← I.weight_eq_constraintProduct]
  have hn : (∏ k : I.Constraint, if k ∈ A then I.activationFactor x X k else x) =
      I.activeSetWeight x X A := by
    simp [PinningData.activeSetWeight, Finset.prod_ite, Finset.filter_not]
  rw [hn, I.activeSetWeight_eq_jointActiveWeight]
  rfl

/-- The activation law is the product law of independent activations of the
satisfied constraints with probability `1-x`. -/
theorem activationLaw_w_eq_prod (I : PinningData V C) (X : V → C) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (A : Finset I.Constraint) :
    (activationLaw I x hx0 hx1 X).w A =
      ∏ k : I.Constraint, (if k ∈ A then activationProb I x X k
        else 1 - activationProb I x X k) := by
  rw [← coinActivation_law I X hx0 hx1, coinActivation_w_eq_prod I X hx0 hx1]

/-- At `x = 1` no constraint is activated. -/
theorem activationLaw_one (I : PinningData V C) (X : V → C) :
    activationLaw I 1 one_pos le_rfl X = FinDist.pure ∅ := by
  ext A
  rw [activationLaw_w_eq_prod]
  by_cases hA : A = ∅
  · subst hA
    simp [FinDist.pure, activationProb]
  · obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.2 hA
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk, activationProb])]
    simp [FinDist.pure, hA]

/-- Support of a common-noise coupling. -/
lemma commonNoiseCoupling_support {S T U : Type*} [Fintype S] [Fintype T] [Fintype U]
    (p : FinDist S) (f : S → T) (g : S → U) (A : T) (B : U)
    (h : (commonNoiseCoupling p f g).w A B ≠ 0) : ∃ ω, f ω = A ∧ g ω = B := by
  by_contra hne
  push Not at hne
  apply h
  change (∑ ω, ∑ ω', (Coupling.diag p).w ω ω' *
    ((FinDist.pure (f ω)).w A * (FinDist.pure (g ω')).w B)) = 0
  refine Finset.sum_eq_zero fun ω _ => Finset.sum_eq_zero fun ω' _ => ?_
  by_cases hω : ω' = ω
  · subst hω
    by_cases hA : f ω' = A
    · have hB : g ω' ≠ B := hne ω' hA
      simp [FinDist.pure, Ne.symm hB]
    · simp [FinDist.pure, Ne.symm hA]
  · simp [Coupling.diag, hω]

/-- The common-coin coupling of the two activation laws, `0 < x ≤ 1`. -/
def coinActivationCoupling (I : PinningData V C) (X Y : V → C) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Coupling (activationLaw I x hx0 hx1 X) (activationLaw I x hx0 hx1 Y) where
  w := (commonNoiseCoupling (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
    (activatedSet I X) (activatedSet I Y)).w
  nonneg := (commonNoiseCoupling _ _ _).nonneg
  sum_row A := by
    rw [(commonNoiseCoupling _ _ _).sum_row A]
    exact congrArg (fun μ : FinDist (Finset I.Constraint) => μ.w A)
      (coinActivation_law I X hx0 hx1)
  sum_col B := by
    rw [(commonNoiseCoupling _ _ _).sum_col B]
    exact congrArg (fun μ : FinDist (Finset I.Constraint) => μ.w B)
      (coinActivation_law I Y hx0 hx1)

/-- **`lem:coupled-activation-root-local` (main.tex Lemma 4.8, companion
Lemma 3.5), for every `x ∈ (0,1]`.**  Let `X, Y` differ exactly at `v`, with
`X v = a ≠ b = Y v`.  Under the common-coin construction (one Bernoulli(`1-x`)
coin per labelled constraint; activate on a side iff the coin is one and the
constraint is satisfied there):
1. the active set at `X` has the activation law at `X`;
2. the active set at `Y` has the activation law at `Y`;
3. for every coin outcome the two hard instances form a `RootLocalPair`: the
   same induced graph and the same lists off `v`, the same edges from `v` to
   every neighbour whose colour is neither `a` nor `b`, and root lists that
   agree on every colour other than `a, b` (both colourings are proper for
   their instance);
4. consequently the joint law of the two active sets is a coupling of the two
   activation laws supported on root-local pairs. -/
theorem coupled_activation_root_local (I : PinningData V C) (X Y : V → C)
    (v : V) (a b : C) (hXa : X v = a) (hYb : Y v = b) (hab : a ≠ b)
    (hagree : ∀ u, u ≠ v → X u = Y u) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    mapLaw (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
        (activatedSet I X) = activationLaw I x hx0 hx1 X ∧
    mapLaw (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
        (activatedSet I Y) = activationLaw I x hx0 hx1 Y ∧
    (∀ ω : I.Constraint → Bool,
      RootLocalPair (activeHardListInstance I (activatedSet I X ω))
        (activeHardListInstance I (activatedSet I Y ω)) X Y v a b) ∧
    ∃ γ : Coupling (activationLaw I x hx0 hx1 X) (activationLaw I x hx0 hx1 Y),
      γ.w = (commonNoiseCoupling
        (commonCoinLaw (K := I.Constraint) (1 - x) (coinParam hx0 hx1))
        (activatedSet I X) (activatedSet I Y)).w ∧
      ∀ A B, γ.w A B ≠ 0 →
        RootLocalPair (activeHardListInstance I A) (activeHardListInstance I B) X Y v a b := by
  refine ⟨coinActivation_law I X hx0 hx1, coinActivation_law I Y hx0 hx1,
    fun ω => activatedSet_rootLocal I X Y ω v a b hXa hYb hab hagree,
    coinActivationCoupling I X Y hx0 hx1, rfl, ?_⟩
  intro A B hAB
  obtain ⟨ω, rfl, rfl⟩ := commonNoiseCoupling_support _ _ _ A B hAB
  exact activatedSet_rootLocal I X Y ω v a b hXa hYb hab hagree

end

end ZeroFreeness
