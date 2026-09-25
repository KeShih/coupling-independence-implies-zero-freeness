import ZeroFreeness.Potts.Model.OptionPartition
import ZeroFreeness.Potts.Geometry.SeparatorRelabel

/-! An arbitrary chosen free root is represented by `none`, while the
remaining vertices retain their actual identities. -/
namespace ZeroFreeness.Potts
open PottsCI Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V C R : Type*} [Fintype V] [Fintype C]

def rootOptionEquiv (v : V) : V ≃ Option {w : V // w ≠ v} :=
  (Equiv.optionSubtypeNe v).symm

@[simp] theorem rootOptionEquiv_root (v : V) : rootOptionEquiv v v = none :=
  Equiv.optionSubtypeNe_symm_self v

@[simp] theorem rootOptionEquiv_symm_none (v : V) :
    (rootOptionEquiv v).symm none = v := rfl

@[simp] theorem rootOptionEquiv_symm_some (v : V) (w : {w : V // w ≠ v}) :
    (rootOptionEquiv v).symm (some w) = w.val := rfl

def rootOptionData (I : PinningData V C) (v : V) :
    PinningData (Option {w : V // w ≠ v}) C := relabelData I (rootOptionEquiv v)

/-- The actual normalized child after pinning the chosen root. Its old
root-boundary conflicts have become pinned-only and are omitted. -/
def rootDeletedData (I : PinningData V C) (v : V) (a : C) :
    PinningData {w : V // w ≠ v} C where
  graph := I.graph.comap Subtype.val
  boundaryCount w c := I.boundaryCount w.val c +
    if I.graph.Adj v w.val ∧ c = a then 1 else 0

theorem optionChildData_rootOptionData (I : PinningData V C) (v : V) (a : C) :
    optionChildData (rootOptionData I v) a = rootDeletedData I v a := by
  unfold optionChildData addBoundarySet optionMiddleData rootDeletedData
  congr 1
  funext w c
  simp only [optionRootNeighbours, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

theorem rootOptionData_constraintDegree (I : PinningData V C) (v : V)
    (w : Option {w : V // w ≠ v}) :
    (rootOptionData I v).constraintDegree w =
      I.constraintDegree ((rootOptionEquiv v).symm w) :=
  relabelData_constraintDegree I _ _

theorem rootOptionData_degreeBound (I : PinningData V C) (v : V)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (rootOptionData I v).DegreeBound Δ :=
  relabelData_degreeBound I _ hd

theorem rootDeletedData_degreeBound (I : PinningData V C) (v : V) (a : C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (rootDeletedData I v a).DegreeBound Δ := by
  rw [← optionChildData_rootOptionData]
  exact optionChildData_degreeBound _ (rootOptionData_degreeBound I v hd) a

theorem rootOptionData_card (v : V) :
    Fintype.card (Option {w : V // w ≠ v}) = Fintype.card V :=
  Fintype.card_congr (rootOptionEquiv v).symm

theorem rootDeletedData_card_lt (v : V) :
    Fintype.card {w : V // w ≠ v} < Fintype.card V := by
  rw [← rootOptionData_card v, Fintype.card_option]
  omega

theorem rootOptionData_partition [CommSemiring R] (I : PinningData V C) (v : V)
    (z : R) : pinningProductPartition (rootOptionData I v) z =
      pinningProductPartition I z := pinningProductPartition_relabel I _ z

theorem root_partition_recursion [CommSemiring R] (I : PinningData V C) (v : V)
    (z : R) : pinningProductPartition I z =
      ∑ a : C, z ^ I.boundaryCount v a *
        pinningProductPartition (rootDeletedData I v a) z := by
  rw [← rootOptionData_partition I v z, option_parent_partition]
  simp only [optionChildData_rootOptionData]
  rfl

end
end ZeroFreeness.Potts
