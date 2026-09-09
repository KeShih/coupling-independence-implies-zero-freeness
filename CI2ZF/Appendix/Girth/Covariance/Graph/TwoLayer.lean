import CI2ZF.Appendix.Girth.Covariance.Graph.ResponseRoot
import CI2ZF.Appendix.Girth.Geometry
import CI2ZF.Appendix.Girth.Covariance.Insertion.Graph
import CI2ZF.BFSShells

/-! The actual two-layer separator of a root-deleted graph. The first
layer consists of root neighbours, the second of their other neighbours,
and every remaining vertex is retained in the exterior. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphTwoLayer
variable (I : PinningData (Option V) C)

abbrev First := GraphResponseRoot.Neighbour I
def HasPredecessor (v : V) : Prop := ∃ u : First I, I.graph.Adj (some u.val) (some v)
abbrev Second := {v : V // v ∉ optionRootNeighbours I ∧ HasPredecessor I v}
abbrev Outside := {v : V // v ∉ optionRootNeighbours I ∧ ¬ HasPredecessor I v}
abbrev Vertex := Separator.Vertex (First I) (Second I) (Outside I)

def value : Vertex I → V := Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)

def splitEquiv : V ≃ Vertex I where
  toFun v := if h : v ∈ optionRootNeighbours I then Sum.inl ⟨v,h⟩
    else if h' : HasPredecessor I v then Sum.inr (Sum.inl ⟨v,h,h'⟩)
    else Sum.inr (Sum.inr ⟨v,h,h'⟩)
  invFun := value I
  left_inv v := by dsimp only [value]; split_ifs <;> rfl
  right_inv v := by
    rcases v with u | w | o
    · simp [value, u.property]
    · simp [value, w.property.1, w.property.2]
    · simp [value, o.property.1, o.property.2]

def data : PinningData (Vertex I) C := relabelData (optionMiddleData I) (splitEquiv I)

theorem data_adj (v w : Vertex I) :
    (data I).graph.Adj v w ↔ I.graph.Adj (some (value I v)) (some (value I w)) := Iff.rfl

theorem first_adj (u : First I) : I.graph.Adj none (some u.val) := by
  have hu := u.property
  simpa only [optionRootNeighbours, Finset.mem_filter, Finset.mem_univ, true_and] using hu

theorem independent (hg : 5 ≤ I.graph.egirth) : InsertionGraph.Independent (data I) := by
  intro u v
  exact neighbors_not_adjacent I.graph hg (first_adj I u) (first_adj I v)

theorem separates : Separates (data I) := by
  intro u o h
  exact o.property.2 ⟨u,h⟩

def owner (w : Second I) : First I := Classical.choose w.property.2

theorem owner_adj (w : Second I) : I.graph.Adj (some (owner I w).val) (some w.val) :=
  Classical.choose_spec w.property.2

theorem owner_unique (hg : 5 ≤ I.graph.egirth) (w : Second I) (u : First I) :
    (data I).graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner I w := by
  constructor
  · intro h
    apply Subtype.ext
    exact Option.some.inj (common_neighbor_unique I.graph hg (by simp : (none : Option V) ≠ some w.val)
      (first_adj I u) h (first_adj I (owner I w)) (owner_adj I w))
  · rintro rfl
    exact owner_adj I w

theorem middle_degreeBound {Δ : ℕ} (hd : I.DegreeBound Δ) :
    (optionMiddleData I).DegreeBound Δ := by
  intro v
  have h := hd (some v)
  have he := optionMiddleData_degree I v
  unfold PinningData.constraintDegree at h ⊢
  change (optionMiddleData I).graph.degree v + ∑ c, I.boundaryCount (some v) c ≤ Δ
  omega

theorem degreeBound {Δ : ℕ} (hd : I.DegreeBound Δ) : (data I).DegreeBound Δ :=
  relabelData_degreeBound _ _ (middle_degreeBound I hd)

theorem first_card_le {Δ : ℕ} (hd : I.DegreeBound Δ) : Fintype.card (First I) ≤ Δ := by
  simpa only [First, GraphResponseRoot.Neighbour, Fintype.card_coe] using optionRootNeighbours_card_le I hd

theorem second_card_le {Δ : ℕ} (hd : I.DegreeBound Δ) : Fintype.card (Second I) ≤ Δ ^ 2 := by
  let f : Second I → (Σ u : First I, (optionMiddleData I).graph.neighborSet u.val) :=
    fun w => ⟨owner I w, ⟨w.val, owner_adj I w⟩⟩
  have hi : Function.Injective f := by
    intro w z h
    exact Subtype.ext (congrArg (fun t : Σ u : First I, (optionMiddleData I).graph.neighborSet u.val => t.2.val) h)
  calc
    _ ≤ Fintype.card (Σ u : First I, (optionMiddleData I).graph.neighborSet u.val) := Fintype.card_le_of_injective f hi
    _ = ∑ u : First I, (optionMiddleData I).graph.degree u.val := by
      rw [Fintype.card_sigma]
      simp only [SimpleGraph.card_neighborSet_eq_degree]
    _ ≤ ∑ _u : First I, Δ := Finset.sum_le_sum fun u _ => by
      have hh := middle_degreeBound I hd u.val
      unfold PinningData.constraintDegree at hh
      omega
    _ = Fintype.card (First I) * Δ := by simp
    _ ≤ Δ ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ (first_card_le I hd)

theorem card_lt_parent : Fintype.card (Vertex I) < Fintype.card (Option V) := by
  rw [← Fintype.card_congr (splitEquiv I), Fintype.card_option]
  omega

theorem second_card_lt_parent : Fintype.card (Second I) < Fintype.card (Option V) := by
  have h : Fintype.card (Second I) ≤ Fintype.card V :=
    Fintype.card_le_of_injective (Subtype.val : Second I → V) Subtype.coe_injective
  rw [Fintype.card_option]
  omega

theorem second_distance (w : Second I) : I.graph.dist none (some w.val) = 2 := by
  let u := owner I w
  have ha := first_adj I u
  have hb := owner_adj I w
  let p : I.graph.Walk none (some w.val) := .cons ha (.cons hb .nil)
  have hle : I.graph.dist none (some w.val) ≤ 2 := by simpa [p] using SimpleGraph.dist_le p
  have hne0 : I.graph.dist none (some w.val) ≠ 0 := by
    intro h
    have he := p.reachable.dist_eq_zero_iff.mp h
    simp at he
  have hne1 : I.graph.dist none (some w.val) ≠ 1 := by
    intro h
    apply w.property.1
    have ha := SimpleGraph.dist_eq_one_iff_adj.mp h
    simpa only [optionRootNeighbours, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  omega

theorem second_mem_shell (w : Second I) : some w.val ∈ CI2ZF.BFS.shell I.graph none 2 := by
  exact CI2ZF.BFS.mem_shell.mpr ⟨(first_adj I (owner I w)).reachable.trans (owner_adj I w).reachable,
    second_distance I w⟩

end GraphTwoLayer
end
end CI2ZF.Appendix.Girth
