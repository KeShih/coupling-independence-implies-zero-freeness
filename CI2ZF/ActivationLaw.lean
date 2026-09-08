import CI2ZF.CommonCoins
import PottsCI.Vigoda.ComponentCoupling

/-! The common independent coins have exactly the soft kernel's activation
marginals; root-local compatibility is inherited from the concrete model. -/

namespace CI2ZF

open PottsCI PottsCI.FinDist PottsCI.Vigoda
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option maxHeartbeats 1200000

variable {V C : Type*} [Fintype V] [Fintype C]

def activatedBits (I : PinningData V C) (X : V → C)
    (ω : I.Constraint → Bool) (k : I.Constraint) : Bool :=
  ω k && decide (I.constraintSatisfied X k)

def activatedSet (I : PinningData V C) (X : V → C)
    (ω : I.Constraint → Bool) : Finset I.Constraint :=
  bitsEquivFinset (activatedBits I X ω)

@[simp] theorem mem_activatedSet (I : PinningData V C) (X : V → C)
    (ω : I.Constraint → Bool) (k : I.Constraint) :
    k ∈ activatedSet I X ω ↔ ω k = true ∧ I.constraintSatisfied X k := by
  simp [activatedSet, bitsEquivFinset, activatedBits]

theorem activatedSet_eq_fromBits (I : PinningData V C) (X : V → C)
    (ω : I.Constraint → Bool) :
    activatedSet I X ω = activeSetFromBits I (bitsEquivFinset ω) X := by
  ext k
  simp [bitsEquivFinset]

omit [Fintype C] in
/-- Each coordinate's acceptance law is its joint constraint factor divided
by the original spin factor. Unsatisfied constraints are never activated. -/
theorem activation_coordinate_weight (I : PinningData V C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (A : Finset I.Constraint) (k : I.Constraint) :
    (mapLaw (bernoulliLaw (1 - x) ⟨by linarith, by linarith⟩)
      (fun b => b && decide (I.constraintSatisfied X k))).w (decide (k ∈ A)) =
      (if k ∈ A then I.activationFactor x X k else x) / I.constraintFactor x X k := by
  by_cases hs : I.constraintSatisfied X k <;> by_cases ha : k ∈ A <;>
    simp [mapLaw, FinDist.bind_w, FinDist.pure, bernoulliLaw,
      PinningData.activationFactor, PinningData.constraintFactor, hs, ha, hx0.ne']

/-- The deterministic active-set map of independent common coins has the
exact conditional law used in the concrete soft Vigoda transition. -/
theorem activatedSet_law (I : PinningData V C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    mapLaw (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith, by linarith⟩)
      (activatedSet I X) = I.activeLawGivenSpin x hx0 hx1 X := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
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
  simp_rw [activation_coordinate_weight I X x hx0 hx1 A]
  rw [Finset.prod_div_distrib, ← I.weight_eq_constraintProduct]
  have hn : (∏ k : I.Constraint, if k ∈ A then I.activationFactor x X k else x) =
      I.activeSetWeight x X A := by
    simp [PinningData.activeSetWeight, Finset.prod_ite, Finset.filter_not]
  rw [hn, I.activeSetWeight_eq_jointActiveWeight]
  rfl

/-- Both activation marginals are exact, with a shared coin at every
labelled constraint. -/
def commonActivationCoupling (I : PinningData V C) (X Y : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Coupling (I.activeLawGivenSpin x hx0 hx1 X) (I.activeLawGivenSpin x hx0 hx1 Y) := by
  rw [← activatedSet_law I X x hx0 hx1, ← activatedSet_law I Y x hx0 hx1]
  exact commonNoiseCoupling _ (activatedSet I X) (activatedSet I Y)

/-- The concrete soft kernel is the mixture of the concrete hard steps under
the independent common coins. -/
theorem softVigodaKernel_eq_coin_mixture [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X : V → C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softVigodaKernel I x hx0 hx1 X =
      (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith, by linarith⟩).bind
        (fun ω => hardStep (activeHardListInstance I (activatedSet I X ω)) X) := by
  change (I.activeLawGivenSpin x hx0 hx1 X).bind
    (fun A => hardStep (activeHardListInstance I A) X) = _
  rw [← activatedSet_law I X x hx0 hx1]
  exact mapLaw_bind _ _ _

/-- Transportation of the two soft rows is bounded by the average of the
hard-row transportation costs under common activations. -/
theorem softVigoda_W_le_average [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softVigodaKernel I x hx0 hx1 X) (softVigodaKernel I x hx0 hx1 Y) ≤
      expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith, by linarith⟩)
        (fun ω => W ham (hardStep (activeHardListInstance I (activatedSet I X ω)) X)
          (hardStep (activeHardListInstance I (activatedSet I Y ω)) Y)) := by
  rw [softVigodaKernel_eq_coin_mixture, softVigodaKernel_eq_coin_mixture]
  exact W_bind_diag ham_nonneg _ _ _

theorem activatedSet_rootLocal (I : PinningData V C) (X Y : V → C)
    (ω : I.Constraint → Bool) (v : V) (a b : C)
    (hXa : X v = a) (hYb : Y v = b) (hab : a ≠ b)
    (hagree : ∀ u, u ≠ v → X u = Y u) :
    RootLocalPair (activeHardListInstance I (activatedSet I X ω))
      (activeHardListInstance I (activatedSet I Y ω)) X Y v a b := by
  rw [activatedSet_eq_fromBits, activatedSet_eq_fromBits]
  exact rootLocalPair_activeSetFromBits I _ X Y v a b hXa hYb hab hagree

end
end CI2ZF
