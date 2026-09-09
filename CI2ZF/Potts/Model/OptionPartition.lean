import CI2ZF.Potts.Model.OptionPinning
import CI2ZF.Potts.Transfer.SeparatorInsidePolynomial

/-! The exact normalized parent recursion for arbitrary boundary-count
data, over a commutative semiring and hence also at complex activity zero. -/

namespace CI2ZF.Potts

open PottsCI Separator
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

variable {O C R : Type*} [Fintype O] [Fintype C]

def optionSeparatorEquiv : Option O ≃ Vertex Empty Unit O where
  toFun
    | none => Sum.inr (Sum.inl ())
    | some o => Sum.inr (Sum.inr o)
  invFun
    | Sum.inl u => u.elim
    | Sum.inr (Sum.inl _) => none
    | Sum.inr (Sum.inr o) => some o
  left_inv w := by cases w <;> rfl
  right_inv w := by rcases w with u | s | o; exact u.elim; cases s; rfl; rfl

def optionSeparatorData (I : PinningData (Option O) C) : PinningData (Vertex Empty Unit O) C :=
  relabelData I optionSeparatorEquiv

theorem optionSeparatorData_separates (I : PinningData (Option O) C) :
    Separates (optionSeparatorData I) := by
  intro u
  exact u.elim

def unitColouringEquiv : (Unit → C) ≃ C where
  toFun ξ := ξ ()
  invFun a := fun _ => a
  left_inv ξ := by funext u; cases u; rfl
  right_inv _ := rfl

lemma optionSeparatorData_exterior (I : PinningData (Option O) C) (ξ : Unit → C) :
    exteriorData (optionSeparatorData I) ξ = optionChildData I (ξ ()) := by
  have hg : (exteriorData (optionSeparatorData I) ξ).graph =
      (optionChildData I (ξ ())).graph := rfl
  have hb : (exteriorData (optionSeparatorData I) ξ).boundaryCount =
      (optionChildData I (ξ ())).boundaryCount := by
    funext o c
    rw [optionChildData_count]
    change I.boundaryCount (some o) c +
      (∑ t : Unit, if I.graph.Adj none (some o) ∧ ξ t = c then 1 else 0) = _
    rw [Fintype.sum_unique]
    simp only [eq_comm (a := ξ ()) (b := c)]
  exact congrArg₂ PinningData.mk hg hb

variable [CommSemiring R]

lemma optionSeparator_insideWeight (I : PinningData (Option O) C) (z : R)
    (α : Empty → C) (ξ : Unit → C) :
    insideWeight (optionSeparatorData I) z α ξ = z ^ I.boundaryCount none (ξ ()) := by
  rw [insideWeight_eq_pinningProductWeight]
  have hu (u : Empty ⊕ Unit) : u = Sum.inr () := by
    rcases u with u | u
    · exact u.elim
    · cases u
      rfl
  have he : (insideData (optionSeparatorData I)).graph.edgeFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, hu u, hu v]
      exact (insideData (optionSeparatorData I)).graph.loopless.irrefl _
  unfold pinningProductWeight
  rw [he, Finset.prod_empty, mul_one, Fintype.prod_sum_type]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, Fintype.prod_unique]
  rfl

lemma optionSeparator_insidePartition (I : PinningData (Option O) C) (z : R) (ξ : Unit → C) :
    insidePartition (optionSeparatorData I) z ξ = z ^ I.boundaryCount none (ξ ()) := by
  unfold insidePartition
  simp only [optionSeparator_insideWeight]
  simp

lemma optionSeparator_exteriorPartition (I : PinningData (Option O) C) (z : R) (ξ : Unit → C) :
    exteriorPartition (optionSeparatorData I) z ξ = pinningProductPartition (optionChildData I (ξ ())) z := by
  unfold exteriorPartition pinningProductPartition
  apply Finset.sum_congr rfl
  intro ζ _
  rw [exteriorWeight_eq_pinningProductWeight _ (optionSeparatorData_separates I),
    optionSeparatorData_exterior]

/-- Every root colour contributes its original boundary monomial times
the genuine normalized child partition. -/
theorem option_parent_partition (I : PinningData (Option O) C) (z : R) :
    pinningProductPartition I z =
      ∑ a : C, z ^ I.boundaryCount none a * pinningProductPartition (optionChildData I a) z := by
  have hp : pinningProductPartition I z = partition (optionSeparatorData I) z := by
    rw [← pinningProductPartition_relabel I optionSeparatorEquiv]
    unfold pinningProductPartition partition pinningProductWeight weight optionSeparatorData
    congr 2
    exact Subsingleton.elim _ _
  rw [hp, partition_factorization _ (optionSeparatorData_separates I)]
  simp only [optionSeparator_insidePartition, optionSeparator_exteriorPartition]
  convert Fintype.sum_equiv unitColouringEquiv
    (fun ξ : Unit → C => z ^ I.boundaryCount none (ξ ()) *
      pinningProductPartition (optionChildData I (ξ ())) z)
    (fun a : C => z ^ I.boundaryCount none a * pinningProductPartition (optionChildData I a) z)
    (fun _ => rfl) using 1
  congr 2
  exact Subsingleton.elim _ _

end
end CI2ZF.Potts
