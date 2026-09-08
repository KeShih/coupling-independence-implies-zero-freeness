import CI2ZF.PottsModel
import CI2ZF.BoundaryData

/-!
# The actual root children and their common middle instance

After a free root is pinned, both child laws live on one common subtype.
The middle instance removes the root without adding its boundary colour.
The difference consists of one labelled boundary occurrence for each
remaining neighbour of the root.
-/

namespace CI2ZF.Potts

open scoped BigOperators
open PottsCI Finset

attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C]

/-- The remaining free vertices, independent of the newly pinned colour. -/
def rootRemainingSet (tau : PartialColouring V C) (r : tau.FreeVertex) : Set V :=
  {v | v ∉ insert r.1 tau.domain}

abbrev RootRemaining (tau : PartialColouring V C) (r : tau.FreeVertex) :=
  rootRemainingSet tau r

def rootRemainingToFree (tau : PartialColouring V C) (r : tau.FreeVertex)
    (u : RootRemaining tau r) : tau.FreeVertex :=
  ⟨u.1, fun hp => u.2 (Finset.mem_insert_of_mem hp)⟩

/-- This is the instance of the actual `pinVertex` operation. -/
def rootChildData (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) : PinningData (RootRemaining tau r) C :=
  (pinVertex tau r a).toPinningData G

/-- Delete the free root and retain the old pinned-neighbour counts. -/
def rootMiddleData (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) : PinningData (RootRemaining tau r) C where
  graph := G.induce {v | v ∉ insert r.1 tau.domain}
  boundaryCount := fun u c => tau.boundaryCount G (rootRemainingToFree tau r u) c

omit [Fintype V] [Fintype C] in
@[simp] theorem rootChildData_graph (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    (rootChildData tau G r a).graph = (rootMiddleData tau G r).graph := rfl

omit [Fintype V] [Fintype C] in
/-- Write pinned colour counts as a sum over original vertices. -/
theorem boundaryCount_eq_sum_colour? (tau : PartialColouring V C) (G : SimpleGraph V)
    (u : tau.FreeVertex) (c : C) :
    tau.boundaryCount G u c =
      ∑ v ∈ tau.domain, if G.Adj u.1 v ∧ tau.colour? v = some c then 1 else 0 := by
  unfold PartialColouring.boundaryCount PartialColouring.pinnedNeighbours
  rw [Finset.filter_filter, Finset.card_filter, ← Finset.sum_coe_sort tau.domain]
  apply Finset.sum_congr rfl
  intro v hv
  simp [PartialColouring.colour?, v.property]

omit [Fintype V] [Fintype C] in
@[simp] theorem pinVertex_colour?_root (tau : PartialColouring V C)
    (r : tau.FreeVertex) (a : C) :
    (pinVertex tau r a).colour? r.1 = some a := by
  simp [PartialColouring.colour?, pinVertex]

omit [Fintype V] [Fintype C] in
theorem pinVertex_colour?_of_ne (tau : PartialColouring V C)
    (r : tau.FreeVertex) (a : C) (v : V) (hv : v ≠ r.1) :
    (pinVertex tau r a).colour? v = tau.colour? v := by
  by_cases hmem : v ∈ tau.domain
  · simp [PartialColouring.colour?, pinVertex, hv, hmem]
  · simp [PartialColouring.colour?, pinVertex, hv, hmem]

/-- Pinning a root adds exactly one occurrence of its colour at each free
neighbour; repeated old occurrences are retained. -/
theorem rootChildData_boundaryCount (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (u : RootRemaining tau r) (c : C) :
    (rootChildData tau G r a).boundaryCount u c =
      (rootMiddleData tau G r).boundaryCount u c +
        if G.Adj u.1 r.1 ∧ a = c then 1 else 0 := by
  change (pinVertex tau r a).boundaryCount G ⟨u.1, u.2⟩ c = _
  rw [boundaryCount_eq_sum_colour?, pinVertex_domain, Finset.sum_insert r.property]
  have hsum : (∑ v ∈ tau.domain,
      if G.Adj u.1 v ∧ (pinVertex tau r a).colour? v = some c then 1 else 0) =
      (rootMiddleData tau G r).boundaryCount u c := by
    change _ = tau.boundaryCount G (rootRemainingToFree tau r u) c
    rw [boundaryCount_eq_sum_colour?]
    apply Finset.sum_congr rfl
    intro v hv
    have hvr : v ≠ r.1 := by intro hh; exact r.2 (hh ▸ hv)
    rw [pinVertex_colour?_of_ne tau r a v hvr]
    rfl
  rw [hsum, pinVertex_colour?_root]
  simp [Nat.add_comm]

/-- The labelled new root-boundary occurrences are indexed by distinct
remaining neighbours, regardless of how many have the same colour. -/
def rootBoundaryVertices (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) : Finset (RootRemaining tau r) :=
  Finset.univ.filter fun u => G.Adj u.1 r.1

omit [Fintype C] in
theorem rootBoundaryVertices_card_le_degree (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) :
    (rootBoundaryVertices tau G r).card ≤ G.degree r.1 := by
  have hsub : (rootBoundaryVertices tau G r).map (Function.Embedding.subtype _) ⊆
      G.neighborFinset r.1 := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    exact (G.mem_neighborFinset r.1 u.1).2 (Finset.mem_filter.mp hu).2.symm
  have hcard := Finset.card_le_card hsub
  simpa only [Finset.card_map, SimpleGraph.card_neighborFinset_eq_degree] using hcard

omit [Fintype C] in
theorem rootBoundaryVertices_card_le (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) : (rootBoundaryVertices tau G r).card ≤ Δ :=
  (rootBoundaryVertices_card_le_degree tau G r).trans (hdegree r.1)

/-- The child has one extra boundary occurrence precisely at a root neighbour. -/
theorem rootChildData_sum_boundaryCount (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (u : RootRemaining tau r) :
    (∑ c, (rootChildData tau G r a).boundaryCount u c) =
      (∑ c, (rootMiddleData tau G r).boundaryCount u c) +
        if G.Adj u.1 r.1 then 1 else 0 := by
  simp_rw [rootChildData_boundaryCount]
  rw [Finset.sum_add_distrib]
  congr 1
  by_cases ha : G.Adj u.1 r.1
  · simp [ha]
  · simp [ha]

/-- The total number of added labelled constraints is exactly the number of
remaining neighbours of the root. -/
theorem rootChildData_total_boundaryCount (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    (∑ u, ∑ c, (rootChildData tau G r a).boundaryCount u c) =
      (∑ u, ∑ c, (rootMiddleData tau G r).boundaryCount u c) +
        (rootBoundaryVertices tau G r).card := by
  simp_rw [rootChildData_sum_boundaryCount]
  rw [Finset.sum_add_distrib]
  congr 1
  exact (Finset.card_filter _ _).symm

/-- Actual root pinning preserves the original maximum constraint-degree bound. -/
theorem rootChildData_degreeBound (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ) :
    (rootChildData tau G r a).DegreeBound Δ :=
  (pinVertex tau r a).degreeBound_of_original G hdegree

/-- The common middle has fewer boundary constraints than either child. -/
theorem rootMiddleData_degreeBound [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ) :
    (rootMiddleData tau G r).DegreeBound Δ := by
  let a : C := Classical.choice inferInstance
  intro u
  have hchild := rootChildData_degreeBound tau G r a hdegree u
  have hle : (rootMiddleData tau G r).constraintDegree u ≤
      (rootChildData tau G r a).constraintDegree u := by
    unfold PinningData.constraintDegree
    rw [rootChildData_graph]
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro c hc
    rw [rootChildData_boundaryCount]
    exact Nat.le_add_right _ _
  exact hle.trans hchild

/-- The common-state child Gibbs law is literally the law of `pinVertex`;
there is no unproved relation to the paper's pinning semantics. -/
theorem rootChildData_gibbs_eq_pinVertex (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < (rootChildData tau G r a).partition x) :
    (rootChildData tau G r a).gibbs x hx hZ =
      (pinVertex tau r a).childGibbs G x hx hZ := rfl

omit [Fintype V] [Fintype C] in
private theorem pinningData_eq_of_fields (I J : PinningData V C)
    (hg : I.graph = J.graph) (hb : I.boundaryCount = J.boundaryCount) : I = J := by
  cases I
  cases J
  cases hg
  cases hb
  rfl

/-- The exact interface for telescoping single-boundary sensitivity over the
root's remaining neighbours. -/
theorem rootChildData_eq_addBoundarySet (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) :
    rootChildData tau G r a =
      addBoundarySet (rootMiddleData tau G r) (rootBoundaryVertices tau G r) a := by
  apply pinningData_eq_of_fields
  · rfl
  · funext u c
    rw [rootChildData_boundaryCount]
    simp [addBoundarySet, rootBoundaryVertices, eq_comm]

end

end CI2ZF.Potts
