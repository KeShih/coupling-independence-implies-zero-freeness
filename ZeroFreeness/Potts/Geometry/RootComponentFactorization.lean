import ZeroFreeness.Potts.Geometry.ComponentFactorization
import ZeroFreeness.Potts.Model.PinningPolynomial
import ZeroFreeness.Potts.Model.RootChildren

/-! Polynomial component factorization and cancellation of the common
outside factor in the actual two root-child partition functions. -/
namespace ZeroFreeness.Potts.Component
open PottsCI ZeroFreeness.Potts.Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) (A : Type*) : DecidableEq A := Classical.decEq A
variable {V C : Type*} [Fintype V] [Fintype C]

theorem component_polynomial_factorization (I : PinningData V C) (v : V) :
    pinningPolynomial I = pinningPolynomial (componentData I v) *
      pinningPolynomial (remainderData I v) := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_mul, pinningPolynomial_eval, pinningPolynomial_eval, pinningPolynomial_eval]
  exact component_partition_factorization I v z

/-- The polynomial is the normalized polynomial of the original arbitrary
partial coloring; the two factors come from its actual free graph. -/
theorem normalizedPolynomial_component_factorization (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) :
    normalizedPolynomial tau G = pinningPolynomial (componentData (tau.toPinningData G) r) *
      pinningPolynomial (remainderData (tau.toPinningData G) r) := by
  rw [← pinningPolynomial_toPinningData]
  exact component_polynomial_factorization _ r

/-- Remaining vertices belonging to the root component before the root was
pinned. This set is independent of the new root color. -/
def childInRootComponent (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (u : RootRemaining tau r) : Prop :=
  (tau.toPinningData G).graph.Reachable r (rootRemainingToFree tau r u)

def componentChildData (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    PinningData {u : RootRemaining tau r // childInRootComponent tau G r u} C :=
  restrictData (rootChildData tau G r a) (childInRootComponent tau G r)

/-- The original exterior components receive no new root-boundary factor. -/
def commonRemainderData (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) :
    PinningData {u : RootRemaining tau r // ¬ childInRootComponent tau G r u} C :=
  restrictData (rootMiddleData tau G r) (fun u => ¬ childInRootComponent tau G r u)

omit [Fintype V] [Fintype C] in
lemma childInRootComponent_closed (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (u : RootRemaining tau r)
    (hu : childInRootComponent tau G r u) (w : RootRemaining tau r)
    (hadj : (rootChildData tau G r a).graph.Adj u w) :
    childInRootComponent tau G r w := by
  exact hu.trans (show (tau.toPinningData G).graph.Adj
    (rootRemainingToFree tau r u) (rootRemainingToFree tau r w) from hadj).reachable

omit [Fintype V] [Fintype C] in
lemma outside_not_root_adj (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (u : RootRemaining tau r)
    (hu : ¬ childInRootComponent tau G r u) : ¬ G.Adj u.val r.val := by
  intro hadj
  exact hu (show (tau.toPinningData G).graph.Adj r (rootRemainingToFree tau r u)
    from hadj.symm).reachable

/-- In particular the exterior pinning datum is literally the same for
every newly chosen root color. -/
lemma child_remainder_eq_common (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    restrictData (rootChildData tau G r a) (fun u => ¬ childInRootComponent tau G r u) =
      commonRemainderData tau G r := by
  unfold commonRemainderData restrictData
  congr 1
  funext u c
  rw [rootChildData_boundaryCount]
  simp [outside_not_root_adj tau G r u.val u.property]

/-- Exact factorization of the original normalized root child, before any
nonvanishing or division is used. -/
theorem rootChildPartition_component_factorization (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (a : C) (z : ℂ) :
    rootChildPartition tau G r a z =
      pinningProductPartition (componentChildData tau G r a) z *
        pinningProductPartition (commonRemainderData tau G r) z := by
  rw [rootChildPartition_eq_pinVertex, ← pinningProductPartition_toPinningData]
  change pinningProductPartition (rootChildData tau G r a) z = _
  rw [cut_partition_factorization _ _ (childInRootComponent_closed tau G r a),
    child_remainder_eq_common]
  rfl

theorem rootChildPolynomial_component_factorization (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (a : C) :
    rootChildPolynomial tau G r a = pinningPolynomial (componentChildData tau G r a) *
      pinningPolynomial (commonRemainderData tau G r) := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_mul, pinningPolynomial_eval, pinningPolynomial_eval]
  exact rootChildPartition_component_factorization tau G r a z

/-- Once the common exterior is nonzero, the true root-child ratio depends
only on the root's original free component. -/
theorem rootChildRatio_eq_component (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a b : C) (z : ℂ)
    (hE : pinningProductPartition (commonRemainderData tau G r) z ≠ 0) :
    rootChildPartition tau G r a z / rootChildPartition tau G r b z =
      pinningProductPartition (componentChildData tau G r a) z /
        pinningProductPartition (componentChildData tau G r b) z := by
  rw [rootChildPartition_component_factorization, rootChildPartition_component_factorization]
  exact mul_div_mul_right _ _ hE

theorem normalizedRootChildRatio_eq_component (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C) (x z : ℂ)
    (hEx : pinningProductPartition (commonRemainderData tau G r) x ≠ 0)
    (hEz : pinningProductPartition (commonRemainderData tau G r) z ≠ 0) :
    (rootChildPartition tau G r a z / rootChildPartition tau G r b z) /
        (rootChildPartition tau G r a x / rootChildPartition tau G r b x) =
      (pinningProductPartition (componentChildData tau G r a) z /
        pinningProductPartition (componentChildData tau G r b) z) /
      (pinningProductPartition (componentChildData tau G r a) x /
        pinningProductPartition (componentChildData tau G r b) x) := by
  rw [rootChildRatio_eq_component tau G r a b z hEz,
    rootChildRatio_eq_component tau G r a b x hEx]

theorem componentChildData_degreeBound (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ) :
    (componentChildData tau G r a).DegreeBound Δ :=
  restrictData_degreeBound _ _ (childInRootComponent_closed tau G r a)
    (rootChildData_degreeBound tau G r a hdegree)

omit [Fintype C] in
/-- Bounded root-component size bounds the actual local child state space. -/
theorem componentChild_card_le (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) :
    Fintype.card {u : RootRemaining tau r // childInRootComponent tau G r u} ≤
      Fintype.card (RootComponent (tau.toPinningData G).graph r) := by
  apply Fintype.card_le_of_injective
    (fun u : {u : RootRemaining tau r // childInRootComponent tau G r u} =>
      (⟨rootRemainingToFree tau r u.val, u.property⟩ :
        RootComponent (tau.toPinningData G).graph r))
  intro u w he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun y => y.val.val) he

omit [Fintype C] in
theorem rootRemaining_card_lt (tau : PartialColouring V C) (r : tau.FreeVertex) :
    Fintype.card (RootRemaining tau r) < Fintype.card tau.FreeVertex := by
  apply Fintype.card_lt_of_injective_of_notMem (rootRemainingToFree tau r)
    (fun _ _ he => Subtype.ext (congrArg (fun x : tau.FreeVertex => x.val) he)) (b := r)
  rintro ⟨u, hu⟩
  have hv : u.val = r.val := congrArg Subtype.val hu
  exact u.property (by rw [hv]; exact Finset.mem_insert_self _ _)

omit [Fintype C] in
/-- The local child and the common exterior are both smaller than the
original free graph, as required by strong induction. -/
theorem componentChild_card_lt_parent (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) :
    Fintype.card {u : RootRemaining tau r // childInRootComponent tau G r u} <
      Fintype.card tau.FreeVertex :=
  (Fintype.card_le_of_injective Subtype.val Subtype.coe_injective).trans_lt
    (rootRemaining_card_lt tau r)

omit [Fintype C] in
theorem commonRemainder_card_lt_parent (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) :
    Fintype.card {u : RootRemaining tau r // ¬ childInRootComponent tau G r u} <
      Fintype.card tau.FreeVertex :=
  (Fintype.card_le_of_injective Subtype.val Subtype.coe_injective).trans_lt
    (rootRemaining_card_lt tau r)

theorem commonRemainderData_degreeBound [Nonempty C] (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) :
    (commonRemainderData tau G r).DegreeBound Δ := by
  have hc (u : RootRemaining tau r) (hu : ¬ childInRootComponent tau G r u)
      (w : RootRemaining tau r) (hadj : (rootMiddleData tau G r).graph.Adj u w) :
      ¬ childInRootComponent tau G r w := by
    intro hw
    exact hu (hw.trans (show (tau.toPinningData G).graph.Adj
      (rootRemainingToFree tau r w) (rootRemainingToFree tau r u) from hadj.symm).reachable)
  convert restrictData_degreeBound (rootMiddleData tau G r)
    (fun u => ¬ childInRootComponent tau G r u) hc
    (rootMiddleData_degreeBound tau G r hdegree) using 1
  rfl

end
end ZeroFreeness.Potts.Component
