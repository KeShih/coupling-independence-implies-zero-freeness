import ZeroFreeness.Coupling.Girth.Covariance.Doob.Pinning

/-! Vertex-independent pinning and its exact finite-law and source transport. -/
namespace ZeroFreeness.Appendix.Girth.DoobPinning
open scoped BigOperators
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

abbrev Remaining (v : V) := {u : V // u ≠ v}
def rootIndex (v : V) : V ≃ Option (Remaining v) := (Equiv.optionSubtypeNe v).symm
def rootData (I : PinningData V C) (v : V) : PinningData (Option (Remaining v)) C := relabelData I (rootIndex v)
def childData (I : PinningData V C) (v : V) (c : C) : PinningData (Remaining v) C := optionChildData (rootData I v) c

def extendColouring (v : V) (c : C) (σ : Remaining v → C) : V → C :=
  (relabelColouring (rootIndex v)).symm (GraphResponseRoot.join c σ)

theorem extendColouring_root (v : V) (c : C) (σ : Remaining v → C) : extendColouring v c σ v = c := by
  simp only [extendColouring, relabelColouring, Equiv.coe_fn_symm_mk, Function.comp_apply,
    rootIndex, Equiv.optionSubtypeNe_symm_self, GraphResponseRoot.join, Option.elim'_none]

theorem extendColouring_remaining (v : V) (c : C) (σ : Remaining v → C) (u : Remaining v) :
    extendColouring v c σ u.val = σ u := by
  simp only [extendColouring, relabelColouring, Equiv.coe_fn_symm_mk, Function.comp_apply,
    rootIndex, Equiv.optionSubtypeNe_symm_of_ne u.property, GraphResponseRoot.join, Option.elim'_some]

def law (I : PinningData V C) (x : ℝ) (hx : 0 < x) : FinDist (V → C) :=
  I.gibbs x hx.le (I.partition_pos_of_parameter_pos hx)

theorem rootLaw_back (I : PinningData V C) (v : V) (x : ℝ) (hx : 0 < x) :
    mapLaw (GraphResponseRoot.parentLaw (rootData I v) x hx) (relabelColouring (rootIndex v)).symm = law I x hx := by
  apply FinDist.ext
  funext σ
  rw [mapLaw_equiv_w]
  change (rootData I v).weight x (relabelColouring (rootIndex v) σ) / (rootData I v).partition x =
    I.weight x σ / I.partition x
  rw [rootData, weight_relabel, partition_relabel, Equiv.symm_apply_apply]

theorem given_eq_child (I : PinningData V C) (v : V) (c : C) (x : ℝ) (hx : 0 < x) :
    Doob.given (law I x hx) (fun σ => σ v) c =
      mapLaw (law (childData I v c) x hx) (extendColouring v c) := by
  rw [← rootLaw_back I v x hx, Doob.given_map]
  have hk : (fun σ : Option (Remaining v) → C => (relabelColouring (rootIndex v)).symm σ v) =
      GraphResponseRoot.rootCoordinate := by
    funext σ
    simp only [relabelColouring, Equiv.coe_fn_symm_mk, Function.comp_apply,
      rootIndex, Equiv.optionSubtypeNe_symm_self, GraphResponseRoot.rootCoordinate]
  rw [hk, GraphResponseRoot.given_parent_eq, mapLaw_comp]
  rfl

theorem child_degreeBound (I : PinningData V C) {Δ : ℕ} (hd : I.DegreeBound Δ) (v : V) (c : C) :
    (childData I v c).DegreeBound Δ :=
  optionChildData_degreeBound (rootData I v) (relabelData_degreeBound I (rootIndex v) hd) c

theorem root_girth (I : PinningData V C) (hg : 5 ≤ I.graph.egirth) (v : V) :
    5 ≤ (rootData I v).graph.egirth :=
  hg.trans (SimpleGraph.Embedding.comap (rootIndex v).symm.toEmbedding I.graph).isContained.egirth_le

theorem child_girth (I : PinningData V C) (hg : 5 ≤ I.graph.egirth) (v : V) (c : C) :
    5 ≤ (childData I v c).graph.egirth :=
  GraphResponseRoot.child_girth (rootData I v) c (root_girth I hg v)

theorem remaining_card_lt (v : V) : Fintype.card (Remaining v) < Fintype.card V :=
  Fintype.card_subtype_lt (x := v) (by simp)

theorem child_adj (I : PinningData V C) (v : V) (c : C) (u w : Remaining v) :
    (childData I v c).graph.Adj u w ↔ I.graph.Adj u.val w.val := Iff.rfl

theorem child_weight_ratios (I : PinningData V C) (v : V) (c : C) (a : V → ℝ) (χ : ℝ)
    (ha : ∀ u w, I.graph.Adj u w → a u ≤ χ * a w) :
    ∀ u w, (childData I v c).graph.Adj u w → a u.val ≤ χ * a w.val := by
  intro u w huw
  exact ha u.val w.val huw

theorem additiveObservable_extend (f : V → C → ℝ) (v : V) (c : C) (σ : Remaining v → C) :
    additiveObservable f (extendColouring v c σ) = additiveObservable (fun u : Remaining v => f u.val) σ + f v c := by
  unfold additiveObservable
  rw [Fintype.sum_eq_add_sum_subtype_ne _ v]
  simp only [extendColouring_root, extendColouring_remaining]
  ring

theorem responseScore_given (I : PinningData V C) (x : ℝ) (hx : 0 < x) (v : V) (c d : C)
    (u : Remaining v) (s : ℝ) (f : V → C → ℝ) :
    responseScore s (Doob.given (law I x hx) (fun σ => σ v) c) (fun σ => σ u.val) (additiveObservable f) d =
      responseScore s (law (childData I v c) x hx) (fun σ => σ u)
        (additiveObservable (fun w : Remaining v => f w.val)) d := by
  rw [given_eq_child, responseScore_map]
  have hk : (fun σ : Remaining v → C => extendColouring v c σ u.val) = fun σ => σ u :=
    funext (fun σ => extendColouring_remaining v c σ u)
  rw [hk]
  have hf : (fun σ : Remaining v → C => additiveObservable f (extendColouring v c σ)) =
      fun σ => additiveObservable (fun w : Remaining v => f w.val) σ + f v c :=
    funext (additiveObservable_extend f v c)
  rw [hf, responseScore_add_const]

theorem boundedScores_given (I : PinningData V C) (x : ℝ) (hx : 0 < x) (v : V) (c : C)
    (s K : ℝ) (f : V → C → ℝ) (ks : List (((V → C) → C) × ℝ)) :
    Doob.BoundedScores s K (additiveObservable f) ks (Doob.given (law I x hx) (fun σ => σ v) c) ↔
      Doob.BoundedScores s K (additiveObservable (fun w : Remaining v => f w.val))
        (Doob.pullScores (extendColouring v c) ks) (law (childData I v c) x hx) := by
  rw [given_eq_child]
  exact Doob.boundedScores_map_add_const (extendColouring v c) ks s K (additiveObservable f)
    (additiveObservable (fun w : Remaining v => f w.val)) (f v c) (additiveObservable_extend f v c) _

end
end ZeroFreeness.Appendix.Girth.DoobPinning
