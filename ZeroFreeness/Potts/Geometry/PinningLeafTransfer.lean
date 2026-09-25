import ZeroFreeness.Potts.Geometry.PinningLeafGirth
import ZeroFreeness.Potts.Model.PinningPolynomial

/-! # Pinned-leaf realization for an actual pinned graph

`lem:pinned-leaf-realization` (companion, Section 2.1) and the construction
asserted in `rem:additional-potts-transfer` (main text, Appendix A).

Given an actual finite graph `G` and an arbitrary (possibly improper)
partial colouring `τ`, we construct an actual graph `G̃` with an actual
partial colouring `τ̃` such that

* `G̃` has maximum degree at most `Δ` whenever `G` does;
* every vertex of `dom τ̃` is a leaf (degree exactly one);
* the normalized pinned polynomials agree, as polynomials, and hence at
  every complex activity;
* `egirth G̃ = egirth (G[V^τ])` and `girth G̃ = girth (G[V^τ])`
  (the extended girth is `⊤` for acyclic graphs, the paper's convention);
* there is a bijection of free vertices which is a graph isomorphism of the
  free graphs and preserves the degree in the ambient graph, i.e. every free
  vertex keeps its degree in `G`.

The construction is the library's leaf realization `PinningLeaves.graph`
(one new pinned leaf per free--pinned edge), turned into an actual partial
colouring on the active vertices of its `AmbientRealization`.
-/

namespace ZeroFreeness.Potts
open PottsCI ZeroFreeness.Potts Separator
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

universe u v
variable {V : Type u} {C : Type v} [Fintype V] [Fintype C]

/-- The generic pinning polynomial agrees with the normalized polynomial for
an arbitrary decidable-equality instance on the vertex type. -/
theorem pinningPolynomial_toPinningData_gen {W : Type*} [Fintype W] [DecidableEq W]
    (tau : PartialColouring W C) (G : SimpleGraph W) :
    pinningPolynomial (tau.toPinningData G) = normalizedPolynomial tau G := by
  unfold pinningPolynomial normalizedPolynomial
  have he (σ : tau.FreeVertex → C) : pinningExponent (tau.toPinningData G) σ =
      tau.boundaryConflictCount G σ + tau.freeConflictCount G σ := by
    unfold pinningExponent PartialColouring.boundaryConflictCount
      PartialColouring.freeConflictCount
    congr 1
  simp_rw [he]
  congr 2
  exact Subsingleton.elim _ _

/-- The generic pinning polynomial is invariant under relabelling the free
vertices. -/
theorem pinningPolynomial_relabel {W X : Type*} [Fintype W] [Fintype X]
    (I : PinningData W C) (e : W ≃ X) :
    pinningPolynomial (relabelData I e) = pinningPolynomial I := by
  apply Polynomial.funext
  intro z
  rw [pinningPolynomial_eval, pinningPolynomial_eval, pinningProductPartition_relabel]

section Construction
variable (tau : PartialColouring V C) (G : SimpleGraph V)

/-- The boundary-count datum of the pinned graph. -/
abbrev leafData : PinningData tau.FreeVertex C := tau.toPinningData G

/-- The library's leaf realization, as an ambient realization. -/
abbrev leafReal : AmbientRealization (leafData tau G) (PinningLeaves.graph (leafData tau G)) :=
  PinningLeaves.realization (leafData tau G)

/-- Every vertex of the leaf graph is either an original free vertex or a
pinned leaf, so all vertices are active. -/
theorem leafReal_mem_active (a : PinningLeaves.Vertex (leafData tau G)) :
    a ∈ (leafReal tau G).active := by
  cases a with
  | inl w => exact Or.inl ⟨w, rfl⟩
  | inr l =>
    right
    change PinningLeaves.pin (leafData tau G) (Sum.inr l) ≠ none
    simp [PinningLeaves.pin]

/-- The leaf-realization vertex type. -/
abbrev LeafVertex := (leafReal tau G).active

/-- The classical decidable equality used by `AmbientRealization`. -/
instance (priority := 3000) leafVertexDecEq : DecidableEq (LeafVertex tau G) :=
  ambientRealizationDecEq _

/-- The realized graph `G̃`. -/
abbrev leafGraph : SimpleGraph (LeafVertex tau G) := (leafReal tau G).activeGraph

/-- The realized pinning `τ̃`. -/
abbrev leafPinning : PartialColouring (LeafVertex tau G) C := (leafReal tau G).activePinning

/-- `G̃` is isomorphic to the library's leaf graph. -/
def leafIso : leafGraph tau G ≃g PinningLeaves.graph (leafData tau G) where
  toEquiv := Equiv.subtypeUnivEquiv (leafReal_mem_active tau G)
  map_rel_iff' := Iff.rfl

theorem leafGraph_degree (a : LeafVertex tau G) :
    (leafGraph tau G).degree a = (PinningLeaves.graph (leafData tau G)).degree a.val := by
  have h := (leafIso tau G).degree_eq a
  exact h.symm

/-- The pinned vertices of `τ̃` are exactly the new leaves. -/
theorem leafPinning_mem_domain_iff (a : LeafVertex tau G) :
    a ∈ (leafPinning tau G).domain ↔ ∃ l, a.val = Sum.inr l := by
  rw [AmbientRealization.activePinning_mem_domain]
  rcases a with ⟨a, ha⟩
  cases a with
  | inl w =>
    simp only [reduceCtorEq, exists_false, iff_false, not_not]
    rfl
  | inr l =>
    simp only [Sum.inr.injEq, exists_eq', iff_true]
    change PinningLeaves.pin (leafData tau G) (Sum.inr l) ≠ none
    simp [PinningLeaves.pin]

/-- Every pinned vertex of `τ̃` is a leaf. -/
theorem leafPinning_domain_degree (a : LeafVertex tau G) (ha : a ∈ (leafPinning tau G).domain) :
    (leafGraph tau G).degree a = 1 := by
  obtain ⟨l, hl⟩ := (leafPinning_mem_domain_iff tau G a).mp ha
  rw [leafGraph_degree, hl, PinningLeaves.degree_leaf]

/-- A new leaf exists only at a free vertex with a pinned neighbour, so its
degree one is also at most `Δ`; no hypothesis `1 ≤ Δ` is needed. -/
theorem leafGraph_degree_le {Δ : ℕ} (hG : ∀ v, G.degree v ≤ Δ) (a : LeafVertex tau G) :
    (leafGraph tau G).degree a ≤ Δ := by
  rw [leafGraph_degree]
  rcases a with ⟨a, _⟩
  cases a with
  | inl w =>
    change (PinningLeaves.graph (leafData tau G)).degree (Sum.inl w) ≤ Δ
    rw [PinningLeaves.degree_free]
    exact tau.degreeBound_of_original G hG w
  | inr l =>
    change (PinningLeaves.graph (leafData tau G)).degree (Sum.inr l) ≤ Δ
    rw [PinningLeaves.degree_leaf]
    have hpos : 0 < (leafData tau G).boundaryCount l.1 (PinningLeaves.colour _ l) :=
      lt_of_le_of_lt (Nat.zero_le _) l.2.2.isLt
    have hsum : (leafData tau G).boundaryCount l.1 (PinningLeaves.colour _ l) ≤
        ∑ c, (leafData tau G).boundaryCount l.1 c :=
      Finset.single_le_sum (f := fun c => (leafData tau G).boundaryCount l.1 c)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    have hd : (leafData tau G).constraintDegree l.1 ≤ Δ := tau.degreeBound_of_original G hG l.1
    unfold PinningData.constraintDegree at hd
    omega

/-- The normalized pinned polynomials agree exactly. -/
theorem leafPinning_polynomial :
    normalizedPolynomial (leafPinning tau G) (leafGraph tau G) = normalizedPolynomial tau G := by
  rw [← pinningPolynomial_toPinningData_gen, ← pinningPolynomial_toPinningData_gen,
    ← pinningPolynomial_relabel _ (leafReal tau G).activeFreeEquiv.symm,
    AmbientRealization.activePinning_data]

theorem leafPinning_partition (z : ℂ) :
    normalizedPartition (leafPinning tau G) (leafGraph tau G) z = normalizedPartition tau G z := by
  unfold normalizedPartition
  rw [leafPinning_polynomial]

/-- Girth is unchanged, with the free graph `G[V^τ]` on the right. -/
theorem leafGraph_egirth : (leafGraph tau G).egirth = (tau.freeGraph G).egirth := by
  rw [(leafIso tau G).egirth_eq, PinningLeaves.egirth_eq]
  rfl

theorem leafGraph_girth : (leafGraph tau G).girth = (tau.freeGraph G).girth := by
  rw [(leafIso tau G).girth_eq, PinningLeaves.girth_eq]
  rfl

/-- The free-vertex bijection. -/
abbrev leafFreeEquiv : tau.FreeVertex ≃ (leafPinning tau G).FreeVertex :=
  (leafReal tau G).activeFreeEquiv

/-- Every free vertex keeps its degree in the original graph `G`. -/
theorem leafFree_degree (w : tau.FreeVertex) :
    (leafGraph tau G).degree (leafFreeEquiv tau G w).val = G.degree w.val := by
  rw [leafGraph_degree]
  change (PinningLeaves.graph (leafData tau G)).degree (Sum.inl w) = _
  rw [PinningLeaves.degree_free, tau.constraintDegree_eq_degree G w]

/-- The free-vertex bijection is an isomorphism of the free graphs. -/
theorem leafFree_adj (w x : tau.FreeVertex) :
    ((leafPinning tau G).freeGraph (leafGraph tau G)).Adj
        (leafFreeEquiv tau G w) (leafFreeEquiv tau G x) ↔ (tau.freeGraph G).Adj w x :=
  Iff.rfl

end Construction

/-- **Lemma 2.1 (`lem:pinned-leaf-realization`), at full strength.**
For every finite graph `G` of maximum degree at most `Δ` and every partial
colouring `τ` (not necessarily proper), there is a finite graph `G̃` of maximum
degree at most `Δ` with a partial colouring `τ̃` whose domain consists of
leaves, such that the normalized pinned polynomials agree, and
`girth G̃ = girth (G[V^τ])` (both as extended girth, `⊤` for forests, and as
mathlib's natural-valued girth). Moreover a bijection of the free vertices is
an isomorphism of the free graphs and preserves the degree of every free
vertex in the original graph. -/
theorem pinned_leaf_realization (G : SimpleGraph V) (tau : PartialColouring V C)
    {Δ : ℕ} (hG : ∀ v, G.degree v ≤ Δ) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
      (G' : SimpleGraph W) (tau' : PartialColouring W C),
      (∀ w, G'.degree w ≤ Δ) ∧
      (∀ w ∈ tau'.domain, G'.degree w = 1) ∧
      normalizedPolynomial tau' G' = normalizedPolynomial tau G ∧
      (∀ z : ℂ, normalizedPartition tau' G' z = normalizedPartition tau G z) ∧
      G'.egirth = (tau.freeGraph G).egirth ∧
      G'.girth = (tau.freeGraph G).girth ∧
      ∃ e : tau.FreeVertex ≃ tau'.FreeVertex,
        (∀ w, G'.degree (e w).val = G.degree w.val) ∧
        (∀ w x, (tau'.freeGraph G').Adj (e w) (e x) ↔ (tau.freeGraph G).Adj w x) := by
  refine ⟨LeafVertex tau G, inferInstance, inferInstance, leafGraph tau G, leafPinning tau G,
    leafGraph_degree_le tau G hG, leafPinning_domain_degree tau G,
    leafPinning_polynomial tau G, leafPinning_partition tau G,
    leafGraph_egirth tau G, leafGraph_girth tau G, leafFreeEquiv tau G,
    leafFree_degree tau G, ?_⟩
  intro w x
  convert leafFree_adj tau G w x

/-- The girth-class form used in `rem:additional-potts-transfer` and in the
proofs of the girth rows: if `girth(G^τ) ≥ g` (with `⊤` for acyclic free
graphs) then `G̃` lies in the same bounded-degree girth class. -/
theorem pinned_leaf_realization_girth_class (G : SimpleGraph V) (tau : PartialColouring V C)
    {Δ : ℕ} (hG : ∀ v, G.degree v ≤ Δ) {g : ℕ∞} (hg : g ≤ (tau.freeGraph G).egirth) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
      (G' : SimpleGraph W) (tau' : PartialColouring W C),
      (∀ w, G'.degree w ≤ Δ) ∧ g ≤ G'.egirth ∧
      (∀ w ∈ tau'.domain, G'.degree w = 1) ∧
      normalizedPolynomial tau' G' = normalizedPolynomial tau G := by
  obtain ⟨W, i1, i2, G', tau', hd, hl, hp, -, he, -, -⟩ := pinned_leaf_realization G tau hG
  exact ⟨W, i1, i2, G', tau', hd, he ▸ hg, hl, hp⟩

/-- **The transfer step of `rem:additional-potts-transfer`.** Any zero-free
statement proved for all pinned graphs of the class `G_{Δ,g}` (maximum degree
at most `Δ`, girth of the *whole* graph at least `g`, arbitrary pinnings)
applies to every pair `(G, τ)` with maximum degree at most `Δ` and
`girth(G^τ) ≥ g`, by passing to the pinned-leaf realization `(G̃, τ̃)`. -/
theorem zero_free_of_girth_class {Δ : ℕ} {g : ℕ∞} (S : Set ℂ)
    (hclass : ∀ (W : Type u) [Fintype W] [DecidableEq W] (G' : SimpleGraph W)
      (tau' : PartialColouring W C), (∀ w, G'.degree w ≤ Δ) → g ≤ G'.egirth →
        ∀ z ∈ S, normalizedPartition tau' G' z ≠ 0)
    (G : SimpleGraph V) (tau : PartialColouring V C) (hG : ∀ v, G.degree v ≤ Δ)
    (hg : g ≤ (tau.freeGraph G).egirth) :
    ∀ z ∈ S, normalizedPartition tau G z ≠ 0 := by
  intro z hz
  rw [← leafPinning_partition tau G z]
  exact hclass (LeafVertex tau G) (leafGraph tau G) (leafPinning tau G)
    (leafGraph_degree_le tau G hG) (by rw [leafGraph_egirth]; exact hg) z hz

end
end ZeroFreeness.Potts
