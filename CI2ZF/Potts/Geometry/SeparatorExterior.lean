import CI2ZF.Potts.Transfer.SeparatorResponse

/-!
# The separator exterior as a smaller actual Potts instance

Crossing separator--outside edges are converted to boundary occurrences,
while outside--outside edges remain free edges. This file identifies the
edge-filter definition of the exterior with that actual induced instance.
-/

namespace CI2ZF.Potts.Separator

open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section

local instance (priority := 2000) (A B : Type*) : DecidableEq (A → B) := Classical.decEq _

variable {U S O C R : Type*}

/-- The outside vertices embedded in the original three-part vertex set. -/
def outsideEmbedding : O ↪ Vertex U S O where
  toFun o := Sum.inr (Sum.inr o)
  inj' := by intro a b h; simpa using h

@[simp] theorem outsideEmbedding_apply (o : O) :
    (outsideEmbedding : O ↪ Vertex U S O) o = Sum.inr (Sum.inr o) := rfl

/-- A crossing edge has a unique separator endpoint and outside endpoint. -/
def crossingEmbedding : S × O ↪ Sym2 (Vertex U S O) where
  toFun p := s(Sum.inr (Sum.inl p.1), Sum.inr (Sum.inr p.2))
  inj' := by
    intro a b h
    exact Prod.ext ((by simpa [Sym2.eq_iff] using h : a.1 = b.1 ∧ a.2 = b.2).1)
      ((by simpa [Sym2.eq_iff] using h : a.1 = b.1 ∧ a.2 = b.2).2)

@[simp] theorem crossingEmbedding_apply (p : S × O) :
    (crossingEmbedding : S × O ↪ Sym2 (Vertex U S O)) p =
      s(Sum.inr (Sum.inl p.1), Sum.inr (Sum.inr p.2)) := rfl

def allOutside (e : Sym2 (Vertex U S O)) : Prop :=
  Sym2.lift ⟨fun u v => isOutside u ∧ isOutside v, fun u v => by simp [and_comm]⟩ e

@[simp] theorem allOutside_mk (u v : Vertex U S O) :
    allOutside s(u, v) ↔ isOutside u ∧ isOutside v := Iff.rfl

variable [Fintype U] [Fintype S] [Fintype O] [Fintype C]

/-- The genuine smaller outside instance after pinning the separator. -/
def exteriorData (I : PinningData (Vertex U S O) C) (ξ : S → C) : PinningData O C where
  graph := I.graph.comap outsideEmbedding
  boundaryCount o c := I.boundaryCount (outsideEmbedding o) c +
    ∑ s : S, if I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o) ∧ ξ s = c then 1 else 0

/-- Separator--outside edges as distinct endpoint pairs. -/
def crossingPairs (I : PinningData (Vertex U S O) C) : Finset (S × O) :=
  Finset.univ.filter (fun p => I.graph.Adj (Sum.inr (Sum.inl p.1)) (outsideEmbedding p.2))

omit [Fintype C] in
lemma outsideEdges_eq_filter (I : PinningData (Vertex U S O) C) :
    (I.graph.comap outsideEmbedding).edgeFinset.map outsideEmbedding.sym2Map =
      I.graph.edgeFinset.filter allOutside := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp he
    induction f using Sym2.ind with
    | _ a b =>
      apply Finset.mem_filter.mpr
      constructor
      · have hadj : (I.graph.comap outsideEmbedding).Adj a b :=
          SimpleGraph.mem_edgeFinset.mp hf
        exact SimpleGraph.mem_edgeFinset.mpr hadj
      · change True ∧ True
        exact ⟨trivial, trivial⟩
  · intro he
    obtain ⟨hedge, hall⟩ := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      rcases a with u | s | o <;> rcases b with u' | s' | o'
      all_goals simp only [allOutside_mk, isOutside, Sum.elim_inl, Sum.elim_inr,
        false_and, and_false] at hall
      refine Finset.mem_map.mpr ⟨s(o, o'), ?_, rfl⟩
      have hadj : I.graph.Adj (Sum.inr (Sum.inr o)) (Sum.inr (Sum.inr o')) :=
        SimpleGraph.mem_edgeFinset.mp hedge
      exact SimpleGraph.mem_edgeFinset.mpr hadj

omit [Fintype C] in
lemma crossingEdges_eq_filter (I : PinningData (Vertex U S O) C) (hsep : Separates I) :
    (crossingPairs I).map crossingEmbedding =
      I.graph.edgeFinset.filter (fun e => touchesOutside e ∧ ¬ allOutside e) := by
  ext e
  constructor
  · intro he
    obtain ⟨⟨s, o⟩, hpair, rfl⟩ := Finset.mem_map.mp he
    have hadj : I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o) :=
      (Finset.mem_filter.mp hpair).2
    apply Finset.mem_filter.mpr
    refine ⟨SimpleGraph.mem_edgeFinset.mpr hadj, ?_, ?_⟩
    · change False ∨ True
      exact Or.inr trivial
    · change ¬ (False ∧ True)
      simp
  · intro he
    obtain ⟨hedge, hout, hnot⟩ := Finset.mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      have hadj : I.graph.Adj a b := SimpleGraph.mem_edgeFinset.mp hedge
      rcases a with u | s | o <;> rcases b with u' | s' | o'
      all_goals simp only [touchesOutside_mk, allOutside_mk, isOutside, Sum.elim_inl,
        Sum.elim_inr, false_or, or_false, true_and, and_true] at hout hnot
      · exact (hsep u o' hadj).elim
      · refine Finset.mem_map.mpr ⟨(s, o'), ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj⟩
      · exact (hsep u' o hadj.symm).elim
      · refine Finset.mem_map.mpr ⟨(s', o), ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj.symm⟩
        · exact Sym2.eq_swap
      · exact (hnot trivial).elim

omit [Fintype U] [Fintype S] [Fintype O] [Fintype C] in
lemma allOutside_touchesOutside (e : Sym2 (Vertex U S O)) (h : allOutside e) :
    touchesOutside e := by
  induction e using Sym2.ind with
  | _ a b => exact Or.inl h.1

omit [Fintype C] in
lemma exterior_edge_product [CommMonoid R]
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (f : Sym2 (Vertex U S O) → R) :
    (∏ e ∈ I.graph.edgeFinset.filter touchesOutside, f e) =
      (∏ p ∈ crossingPairs I, f (crossingEmbedding p)) *
      ∏ e ∈ (I.graph.comap outsideEmbedding).edgeFinset, f (outsideEmbedding.sym2Map e) := by
  have hout : (I.graph.edgeFinset.filter touchesOutside).filter allOutside =
      I.graph.edgeFinset.filter allOutside := by
    ext e
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩,
      fun h => ⟨⟨h.1, allOutside_touchesOutside e h.2⟩, h.2⟩⟩
  rw [← Finset.prod_filter_not_mul_prod_filter
    (I.graph.edgeFinset.filter touchesOutside) allOutside f]
  rw [Finset.filter_filter, hout, ← crossingEdges_eq_filter I hsep, ← outsideEdges_eq_filter I]
  simp only [Finset.prod_map]

section Weight

variable [CommSemiring R]

omit [Fintype U] [Fintype S] [Fintype O] [Fintype C] in
lemma partialEdgeWeight_crossing (z : R) (ξ : S → C) (ζ : O → C) (p : S × O) :
    partialEdgeWeight z (exteriorColor ξ ζ) (crossingEmbedding (U := U) p) =
      if ξ p.1 = ζ p.2 then z else 1 := by
  simp only [crossingEmbedding_apply, partialEdgeWeight_mk, exteriorColor,
    Sum.elim_inl, Sum.elim_inr, Option.some.injEq]
  by_cases h : ξ p.1 = ζ p.2 <;> simp_all [eq_comm]

omit [Fintype U] [Fintype S] [Fintype O] [Fintype C] in
lemma partialEdgeWeight_outside (z : R) (ξ : S → C) (ζ : O → C) (e : Sym2 O) :
    partialEdgeWeight z (exteriorColor (U := U) ξ ζ) (outsideEmbedding.sym2Map e) =
      edgeWeight z ζ e := by
  induction e using Sym2.ind with
  | _ a b =>
    change (if ∃ c, some (ζ a) = some c ∧ some (ζ b) = some c then z else 1) =
      (if ζ a = ζ b then z else 1)
    by_cases h : ζ a = ζ b <;> simp_all [eq_comm]

omit [Fintype U] [Fintype C] in
lemma crossing_product_eq_boundary (I : PinningData (Vertex U S O) C)
    (z : R) (ξ : S → C) (ζ : O → C) :
    (∏ p ∈ crossingPairs I, if ξ p.1 = ζ p.2 then z else 1) =
      ∏ o : O, z ^ (∑ s : S,
        if I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o) ∧ ξ s = ζ o then 1 else 0) := by
  unfold crossingPairs
  rw [Finset.prod_filter]
  simp only [Fintype.prod_prod_type]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro o _
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro s _
  by_cases ha : I.graph.Adj (Sum.inr (Sum.inl s)) (outsideEmbedding o)
  all_goals by_cases hc : ξ s = ζ o
  all_goals simp_all

/-- Actual boundary and free-edge weight for a general vertex type. -/
def pinningProductWeight {V : Type*} [Fintype V] (I : PinningData V C)
    (z : R) (σ : V → C) : R :=
  (∏ v, z ^ I.boundaryCount v (σ v)) * ∏ e ∈ I.graph.edgeFinset, edgeWeight z σ e

omit [Fintype C] in
/-- The filtered exterior factors are exactly the Potts weight of the
smaller outside instance with the separator colors added to its boundary. -/
theorem exteriorWeight_eq_pinningProductWeight
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (z : R) (ξ : S → C) (ζ : O → C) :
    exteriorWeight I z ξ ζ = pinningProductWeight (exteriorData I ξ) z ζ := by
  unfold exteriorWeight
  rw [exterior_edge_product I hsep]
  simp_rw [partialEdgeWeight_crossing, partialEdgeWeight_outside]
  rw [crossing_product_eq_boundary]
  unfold pinningProductWeight exteriorData
  simp only [pow_add, Finset.prod_mul_distrib]
  dsimp only [outsideEmbedding]
  rw [mul_assoc]
  congr 1

end Weight

/-- At a real activity the smaller instance is exactly the inherited Potts model. -/
theorem exteriorPartition_eq_real_partition (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) (x : ℝ) (ξ : S → C) :
    exteriorPartition I x ξ = (exteriorData I ξ).partition x := by
  unfold exteriorPartition PinningData.partition
  apply Finset.sum_congr rfl
  intro ζ _
  exact exteriorWeight_eq_pinningProductWeight I hsep x ξ ζ

/-- The original real partition expressed using the actual smaller outside
Potts partition, rather than a separately specified exterior factor. -/
theorem real_partition_factorization_actual_exterior
    (I : PinningData (Vertex U S O) C) (hsep : Separates I) (x : ℝ) :
    I.partition x = ∑ ξ : S → C, insidePartition I x ξ * (exteriorData I ξ).partition x := by
  rw [real_partition_factorization I hsep]
  simp_rw [exteriorPartition_eq_real_partition I hsep]

end

end CI2ZF.Potts.Separator
