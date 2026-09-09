import CI2ZF.Appendix.Girth.Covariance.Doob.PinningTransport
import CI2ZF.Appendix.Girth.Covariance.Graph.ResponseRoot
import Mathlib.Combinatorics.SimpleGraph.Girth

/-! Successive colour observations are actual further pinnings. The
remaining source retains every unpinned summand and loses only a constant. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

def additiveObservable (f : V → C → ℝ) (σ : V → C) : ℝ := ∑ v, f v (σ v)

namespace GraphResponseRoot
variable (I : PinningData (Option V) C) (x : ℝ) (hx : 0 < x)

theorem given_parent_eq (a : C) :
    Doob.given (parentLaw I x hx) rootCoordinate a = mapLaw (childLaw I x hx a) (join a) := by
  have hp : 0 < (Doob.observed (parentLaw I x hx) rootCoordinate).w a := by
    rw [Doob.observed_eq_coordinateMarginal, rootMarginal_eq]
    exact rootLaw_pos I x hx a
  have he (f : (Option V → C) → ℝ) :
      expectReal (Doob.given (parentLaw I x hx) rootCoordinate a) f =
        expectReal (mapLaw (childLaw I x hx a) (join a)) f := by
    rw [expectReal_mapLaw]
    exact (Doob.observedMean_eq_coordinateMean (parentLaw I x hx) rootCoordinate f a hp).trans
      (root_mean I x hx f a)
  apply FinDist.ext
  funext σ
  simpa only [expect_colourIndicator] using he (colourIndicator σ)

theorem additiveObservable_join (f : Option V → C → ℝ) (a : C) (σ : V → C) :
    additiveObservable f (join a σ) = additiveObservable (fun v => f (some v)) σ + f none a := by
  unfold additiveObservable
  rw [Fintype.sum_option]
  change f none a + ∑ v : V, f (some v) (σ v) = _
  ring

theorem pinned_responseScore (f : Option V → C → ℝ) (a c : C) (s : ℝ) (v : V) :
    responseScore s (Doob.given (parentLaw I x hx) rootCoordinate a)
      (fun σ => σ (some v)) (additiveObservable f) c =
    responseScore s (childLaw I x hx a) (fun σ => σ v)
      (additiveObservable (fun v => f (some v))) c := by
  rw [given_parent_eq, responseScore_map]
  have he : (fun σ : V → C => additiveObservable f (join a σ)) =
      fun σ => additiveObservable (fun v => f (some v)) σ + f none a :=
    funext (additiveObservable_join f a)
  rw [he, responseScore_add_const]
  rfl

theorem boundedScores_pinned (f : Option V → C → ℝ) (a : C) (s K : ℝ)
    (ks : List (((Option V → C) → C) × ℝ)) :
    Doob.BoundedScores s K (additiveObservable f) ks (Doob.given (parentLaw I x hx) rootCoordinate a) ↔
      Doob.BoundedScores s K (additiveObservable (fun v => f (some v)))
        (Doob.pullScores (join a) ks) (childLaw I x hx a) := by
  rw [given_parent_eq]
  exact Doob.boundedScores_map_add_const (join a) ks s K (additiveObservable f)
    (additiveObservable (fun v => f (some v))) (f none a) (additiveObservable_join f a) _

theorem child_girth (a : C) (hg : 5 ≤ I.graph.egirth) :
    5 ≤ (optionChildData I a).graph.egirth := by
  exact hg.trans (SimpleGraph.Embedding.comap
    (⟨Option.some, Option.some_injective V⟩ : V ↪ Option V) I.graph).isContained.egirth_le

theorem child_card_lt : Fintype.card V < Fintype.card (Option V) := by simp

theorem child_weight_ratios (a : C) (w : Option V → ℝ) (χ : ℝ)
    (hw : ∀ u v, I.graph.Adj u v → w v ≤ χ * w u) :
    ∀ u v, (optionChildData I a).graph.Adj u v → w (some v) ≤ χ * w (some u) := by
  intro u v huv
  exact hw (some u) (some v) huv

theorem child_source_caps (f : Option V → C → ℝ) (w : Option V → ℝ)
    (hf : ∀ v c, |f v c| ≤ w v) : ∀ v c, |f (some v) c| ≤ w (some v) := fun v c => hf (some v) c

end GraphResponseRoot
end
end CI2ZF.Appendix.Girth
