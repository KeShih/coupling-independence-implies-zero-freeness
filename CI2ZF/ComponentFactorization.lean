import CI2ZF.SeparatorRelabel

/-! Actual Potts product and partition factorization over the root's free
graph component and its complement. Boundary counts are retained unchanged. -/
namespace CI2ZF.Potts.Component
open Finset PottsCI CI2ZF.Potts.Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) (A : Type*) : DecidableEq A := Classical.decEq A
variable {U O V C R : Type*}

def leftEmbedding : U ↪ U ⊕ O where
  toFun := Sum.inl
  inj' := Sum.inl_injective

def rightEmbedding : O ↪ U ⊕ O where
  toFun := Sum.inr
  inj' := Sum.inr_injective

def leftData (I : PinningData (U ⊕ O) C) : PinningData U C where
  graph := I.graph.comap leftEmbedding
  boundaryCount u := I.boundaryCount (Sum.inl u)

def rightData (I : PinningData (U ⊕ O) C) : PinningData O C where
  graph := I.graph.comap rightEmbedding
  boundaryCount o := I.boundaryCount (Sum.inr o)

def Separated (I : PinningData (U ⊕ O) C) : Prop :=
  ∀ u o, ¬ I.graph.Adj (Sum.inl u) (Sum.inr o)

section SumSplit
variable [Fintype U] [Fintype O]

lemma edges_disjoint (I : PinningData (U ⊕ O) C) :
    Disjoint ((leftData I).graph.edgeFinset.map leftEmbedding.sym2Map)
      ((rightData I).graph.edgeFinset.map rightEmbedding.sym2Map) := by
  apply disjoint_left.mpr
  intro e hl hr
  obtain ⟨l, _, hel⟩ := mem_map.mp hl
  obtain ⟨r, _, her⟩ := mem_map.mp hr
  have h := hel.trans her.symm
  induction l using Sym2.ind with
  | _ u v =>
    induction r using Sym2.ind with
    | _ o p =>
      change s(Sum.inl u, Sum.inl v) = s(Sum.inr o, Sum.inr p) at h
      simp at h

lemma edges_eq_union (I : PinningData (U ⊕ O) C) (hsep : Separated I) :
    I.graph.edgeFinset =
      (leftData I).graph.edgeFinset.map leftEmbedding.sym2Map ∪
        (rightData I).graph.edgeFinset.map rightEmbedding.sym2Map := by
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      have ha : I.graph.Adj a b := SimpleGraph.mem_edgeFinset.mp he
      rcases a with u | o <;> rcases b with v | p
      · exact mem_union_left _ (mem_map.mpr
          ⟨s(u, v), SimpleGraph.mem_edgeFinset.mpr ha, rfl⟩)
      · exact (hsep u p ha).elim
      · exact (hsep v o ha.symm).elim
      · exact mem_union_right _ (mem_map.mpr
          ⟨s(o, p), SimpleGraph.mem_edgeFinset.mpr ha, rfl⟩)
  · intro he
    rcases mem_union.mp he with hl | hr
    · obtain ⟨e, hf, rfl⟩ := mem_map.mp hl
      induction e using Sym2.ind with
      | _ u v =>
        have ha : (leftData I).graph.Adj u v := SimpleGraph.mem_edgeFinset.mp hf
        exact SimpleGraph.mem_edgeFinset.mpr ha
    · obtain ⟨e, hf, rfl⟩ := mem_map.mp hr
      induction e using Sym2.ind with
      | _ u v =>
        have ha : (rightData I).graph.Adj u v := SimpleGraph.mem_edgeFinset.mp hf
        exact SimpleGraph.mem_edgeFinset.mpr ha

variable [CommSemiring R]

lemma weight_join (I : PinningData (U ⊕ O) C) (hsep : Separated I)
    (z : R) (α : U → C) (β : O → C) :
    pinningProductWeight I z (Sum.elim α β) =
      pinningProductWeight (leftData I) z α * pinningProductWeight (rightData I) z β := by
  have hl (e : Sym2 U) : edgeWeight z (Sum.elim α β) (leftEmbedding.sym2Map e) =
      edgeWeight z α e := by
    induction e using Sym2.ind with | _ u v => rfl
  have hr (e : Sym2 O) : edgeWeight z (Sum.elim α β) (rightEmbedding.sym2Map e) =
      edgeWeight z β e := by
    induction e using Sym2.ind with | _ u v => rfl
  unfold pinningProductWeight
  rw [edges_eq_union I hsep, prod_union (edges_disjoint I), prod_map, prod_map]
  simp only [hl, hr, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    leftData, rightData]
  ring

def colouringEquiv : ((U ⊕ O) → C) ≃ (U → C) × (O → C) where
  toFun σ := (fun u => σ (Sum.inl u), fun o => σ (Sum.inr o))
  invFun p := Sum.elim p.1 p.2
  left_inv σ := by funext v; cases v <;> rfl
  right_inv p := by cases p; rfl

variable [Fintype C]

/-- This identity is obtained by splitting the actual edge factors and the
actual finite configuration sum. It holds at zero and complex activities. -/
theorem partition_factorization (I : PinningData (U ⊕ O) C) (hsep : Separated I)
    (z : R) :
    pinningProductPartition I z =
      pinningProductPartition (leftData I) z * pinningProductPartition (rightData I) z := by
  unfold pinningProductPartition
  trans ∑ p : (U → C) × (O → C), pinningProductWeight I z (Sum.elim p.1 p.2)
  · exact Fintype.sum_equiv colouringEquiv _ _
      (fun σ => by congr 1; exact (colouringEquiv.left_inv σ).symm)
  simp only [Fintype.sum_prod_type, weight_join I hsep]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

end SumSplit

/-- The actual instance induced on a chosen collection of free vertices,
with all original pinned-neighbour multiplicities retained. -/
def restrictData (I : PinningData V C) (p : V → Prop) : PinningData {v // p v} C where
  graph := I.graph.comap Subtype.val
  boundaryCount v := I.boundaryCount v.val

def cutEquiv (p : V → Prop) : V ≃ {v // p v} ⊕ {v // ¬ p v} where
  toFun v := if h : p v then Sum.inl ⟨v, h⟩ else Sum.inr ⟨v, h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv v := by dsimp only; split_ifs <;> rfl
  right_inv v := by rcases v with ⟨v, h⟩ | ⟨v, h⟩ <;> simp [h]

section Cut
variable [Fintype V] [Fintype C]

/-- A union of actual connected components gives a product decomposition. -/
theorem cut_partition_factorization [CommSemiring R]
    (I : PinningData V C) (p : V → Prop)
    (hclosed : ∀ u, p u → ∀ w, I.graph.Adj u w → p w) (z : R) :
    pinningProductPartition I z = pinningProductPartition (restrictData I p) z *
      pinningProductPartition (restrictData I (fun v => ¬ p v)) z := by
  rw [← pinningProductPartition_relabel I (cutEquiv p)]
  apply partition_factorization
  intro u o hadj
  exact o.property (hclosed u.val u.property o.val hadj)

theorem restrictData_degreeBound (I : PinningData V C) (p : V → Prop)
    (hclosed : ∀ u, p u → ∀ w, I.graph.Adj u w → p w)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (restrictData I p).DegreeBound Δ := by
  intro u
  have hg : (restrictData I p).graph.degree u = I.graph.degree u.val := by
    apply SimpleGraph.degree_induce_of_neighborSet_subset
    intro w hw
    exact hclosed u.val u.property w hw
  change (restrictData I p).graph.degree u + (∑ c : C, I.boundaryCount u.val c) ≤ Δ
  rw [hg]
  exact hd u.val

end Cut

abbrev RootComponent (G : SimpleGraph V) (v : V) := {w : V // G.Reachable v w}
abbrev Remainder (G : SimpleGraph V) (v : V) := {w : V // ¬ G.Reachable v w}

def componentEquiv (G : SimpleGraph V) (v : V) :
    V ≃ RootComponent G v ⊕ Remainder G v where
  toFun w := if h : G.Reachable v w then Sum.inl ⟨w, h⟩ else Sum.inr ⟨w, h⟩
  invFun := Sum.elim Subtype.val Subtype.val
  left_inv w := by dsimp only; split_ifs <;> rfl
  right_inv w := by rcases w with ⟨w, h⟩ | ⟨w, h⟩ <;> simp [h]

def componentData (I : PinningData V C) (v : V) : PinningData (RootComponent I.graph v) C where
  graph := I.graph.comap Subtype.val
  boundaryCount w := I.boundaryCount w.val

def remainderData (I : PinningData V C) (v : V) : PinningData (Remainder I.graph v) C where
  graph := I.graph.comap Subtype.val
  boundaryCount w := I.boundaryCount w.val

variable [Fintype V] [Fintype C]

omit [Fintype V] [Fintype C] in
lemma componentSplit_separated (I : PinningData V C) (v : V) :
    Separated (relabelData I (componentEquiv I.graph v)) := by
  intro u o
  change ¬ I.graph.Adj u.val o.val
  exact fun hadj => o.property (u.property.trans hadj.reachable)

/-- The normalized pinned partition factors over the actual free connected
component of the root and all remaining free vertices. -/
theorem component_partition_factorization [CommSemiring R]
    (I : PinningData V C) (v : V) (z : R) :
    pinningProductPartition I z = pinningProductPartition (componentData I v) z *
      pinningProductPartition (remainderData I v) z := by
  rw [← pinningProductPartition_relabel I (componentEquiv I.graph v)]
  exact partition_factorization _ (componentSplit_separated I v) z

theorem componentData_degreeBound (I : PinningData V C) (v : V)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (componentData I v).DegreeBound Δ :=
  restrictData_degreeBound I (I.graph.Reachable v)
    (fun _ hu _ hadj => hu.trans hadj.reachable) hd

theorem remainderData_degreeBound (I : PinningData V C) (v : V)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (remainderData I v).DegreeBound Δ := by
  convert restrictData_degreeBound I (fun w => ¬ I.graph.Reachable v w)
    (fun _ hu _ hadj hw => hu (hw.trans hadj.symm.reachable)) hd using 1
  rfl

end
end CI2ZF.Potts.Component
