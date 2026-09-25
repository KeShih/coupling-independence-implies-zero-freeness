import ZeroFreeness.Coupling.Girth.Covariance.Response.Score
import ZeroFreeness.Potts.Geometry.SeparatorRelabel
import ZeroFreeness.Potts.Model.OptionPinning
import Mathlib.Combinatorics.SimpleGraph.Girth

/-! Actual residual instances and admissible additive sources for the
girth-five response induction. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {V W C : Type*} [Fintype V] [Fintype W] [Fintype C]

structure WeightedSource (I : PinningData V C) (χ : ℝ) where
  weight : V → ℝ
  positive : ∀ v, 0 < weight v
  edge_le : ∀ u v, I.graph.Adj u v → weight u ≤ χ * weight v
  term : V → C → ℝ
  term_bound : ∀ v c, |term v c| ≤ weight v

namespace WeightedSource
variable {I : PinningData V C} {χ : ℝ} (F : WeightedSource I χ)

def observable (σ : V → C) : ℝ := ∑ v, F.term v (σ v)

def pull (J : PinningData W C) (j : W → V)
    (hj : ∀ u v, J.graph.Adj u v → I.graph.Adj (j u) (j v)) : WeightedSource J χ where
  weight w := F.weight (j w)
  positive w := F.positive (j w)
  edge_le u v h := F.edge_le (j u) (j v) (hj u v h)
  term w := F.term (j w)
  term_bound w c := F.term_bound (j w) c

def relabel (e : V ≃ W) : WeightedSource (relabelData I e) χ :=
  F.pull _ e.symm (fun _ _ h => h)

theorem observable_relabel (e : V ≃ W) (σ : W → C) :
    (F.relabel e).observable σ = F.observable (σ ∘ e) := by
  unfold observable
  exact Fintype.sum_equiv e.symm _ _ (fun w => by simp [relabel, pull])

def deleted {I : PinningData (Option V) C} (F : WeightedSource I χ) :
    WeightedSource (optionMiddleData I) χ := F.pull _ Option.some (fun _ _ h => h)

def pinned {I : PinningData (Option V) C} (F : WeightedSource I χ) (a : C) :
    WeightedSource (optionChildData I a) χ := F.pull _ Option.some (fun _ _ h => h)

theorem observable_option {I : PinningData (Option V) C} (F : WeightedSource I χ)
    (σ : Option V → C) :
    F.observable σ = F.term none (σ none) + F.deleted.observable (σ ∘ Option.some) := by
  unfold observable
  rw [Fintype.sum_option]
  rfl

theorem neighbour_bound (v u : V) (h : I.graph.Adj v u) : F.weight u ≤ χ * F.weight v :=
  F.edge_le u v h.symm

theorem second_bound (v u w : V) (hvu : I.graph.Adj v u) (huw : I.graph.Adj u w)
    (hχ : 0 ≤ χ) : F.weight w ≤ χ ^ 2 * F.weight v := by
  calc
    _ ≤ χ * F.weight u := F.neighbour_bound u w huw
    _ ≤ χ * (χ * F.weight v) := mul_le_mul_of_nonneg_left (F.neighbour_bound v u hvu) hχ
    _ = _ := by ring

end WeightedSource

variable [DecidableEq V] [DecidableEq C] [Nonempty C]

def positiveLaw (I : PinningData V C) (x : ℝ) (hx : 0 < x) : FinDist (V → C) :=
  I.gibbs x hx.le (I.partition_pos_of_parameter_pos hx)

def instanceScore (I : PinningData V C) (x : ℝ) (hx : 0 < x) {χ : ℝ}
    (F : WeightedSource I χ) (v : V) : C → ℝ :=
  responseScore (1 - x) (positiveLaw I x hx) (fun σ => σ v) F.observable

def InstanceResponseBound (I : PinningData V C) (x : ℝ) (hx : 0 < x)
    (χ B U R : ℝ) : Prop :=
  ∀ (F : WeightedSource I χ) v,
    colourNorm (instanceScore I x hx F v) ≤ U * F.weight v ∧
    ∀ c, |instanceScore I x hx F v c| ≤ Real.sqrt B * R * F.weight v

def ResponseBoundsUpTo (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C]
    (Δ : ℕ) (χ B U R : ℝ) (n : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (I : PinningData V C),
    Fintype.card V ≤ n → I.DegreeBound Δ → 5 ≤ I.graph.egirth →
    ∀ (x : ℝ) (hx : 0 < x), x < 1 → InstanceResponseBound I x hx χ B U R

theorem responseBoundsUpTo_zero (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C]
    (Δ : ℕ) (χ B U R : ℝ) : ResponseBoundsUpTo.{u,v} C Δ χ B U R 0 := by
  intro V _ _ I hn _ _ x hx _ F v
  have hcard : Fintype.card V = 0 := Nat.eq_zero_of_le_zero hn
  have : IsEmpty V := Fintype.card_eq_zero_iff.mp hcard
  exact isEmptyElim v

theorem responseBoundsUpTo_mono (C : Type v) [Fintype C] [DecidableEq C] [Nonempty C]
    (Δ : ℕ) (χ B U R : ℝ) {n m : ℕ} (hn : n ≤ m)
    (h : ResponseBoundsUpTo.{u,v} C Δ χ B U R m) : ResponseBoundsUpTo.{u,v} C Δ χ B U R n := by
  intro V _ _ I hv
  exact h V I (hv.trans hn)

end
end ZeroFreeness.Appendix.Girth
