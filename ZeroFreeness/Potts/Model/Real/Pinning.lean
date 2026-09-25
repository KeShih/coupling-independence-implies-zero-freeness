import ZeroFreeness.Potts.Model.Real.Model

/-!
# Partial colourings and their induced Potts instances

This file gives the phrase "pin a set of vertices" a literal finite meaning.
A partial colouring consists of a finite domain together with a colour on the
subtype of vertices belonging to that domain.  Its unpinned vertices form the
complementary subtype.  Restricting a graph to those vertices and counting the
colours on adjacent pinned vertices produces `PinningData` from
`PottsCI.Potts.Model`.
-/

namespace PottsCI

open Finset

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V : Type*} {C : Type*}
variable [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- A colouring of an explicitly specified finite set of vertices.  In
particular, `colour` has no irrelevant values outside `domain`. -/
structure PartialColouring (V C : Type*) [DecidableEq V] where
  domain : Finset V
  colour : domain → C

namespace PartialColouring

variable (tau : PartialColouring V C)

/-- The set of vertices not fixed by the partial colouring. -/
def freeSet : Set V := {v | v ∉ tau.domain}

/-- The type of vertices not fixed by the partial colouring. -/
abbrev FreeVertex := tau.freeSet

/-- The colour of `v`, when `v` belongs to the pinning domain. -/
def colour? (v : V) : Option C :=
  if h : v ∈ tau.domain then some (tau.colour ⟨v, h⟩) else none

@[simp]
lemma colour?_of_mem {v : V} (hv : v ∈ tau.domain) :
    tau.colour? v = some (tau.colour ⟨v, hv⟩) := by
  simp [colour?, hv]

@[simp]
lemma colour?_of_not_mem {v : V} (hv : v ∉ tau.domain) : tau.colour? v = none := by
  simp [colour?, hv]

/-- Combine a colouring of the free vertices with the pinned colours. -/
def extend (sigma : tau.FreeVertex → C) (v : V) : C :=
  if h : v ∈ tau.domain then tau.colour ⟨v, h⟩ else sigma ⟨v, h⟩

@[simp]
lemma extend_of_mem (sigma : tau.FreeVertex → C) {v : V} (hv : v ∈ tau.domain) :
    tau.extend sigma v = tau.colour ⟨v, hv⟩ := by
  simp [extend, hv]

@[simp]
lemma extend_of_not_mem (sigma : tau.FreeVertex → C) {v : V} (hv : v ∉ tau.domain) :
    tau.extend sigma v = sigma ⟨v, hv⟩ := by
  simp [extend, hv]

/-- A full colouring agrees with the prescribed colours on the formal
pinning domain. -/
def Extends (sigma : V → C) : Prop :=
  ∀ v (hv : v ∈ tau.domain), sigma v = tau.colour ⟨v, hv⟩

/-- Restrict a full colouring to the free-vertex subtype. -/
def restrictFree (sigma : V → C) : tau.FreeVertex → C := fun v ↦ sigma v.1

@[simp]
lemma restrictFree_extend (sigma : tau.FreeVertex → C) :
    tau.restrictFree (tau.extend sigma) = sigma := by
  funext v
  exact tau.extend_of_not_mem sigma v.2

lemma extend_extends (sigma : tau.FreeVertex → C) : tau.Extends (tau.extend sigma) := by
  intro v hv
  exact tau.extend_of_mem sigma hv

lemma extend_restrictFree {sigma : V → C} (hsigma : tau.Extends sigma) :
    tau.extend (tau.restrictFree sigma) = sigma := by
  funext v
  by_cases hv : v ∈ tau.domain
  · rw [tau.extend_of_mem _ hv, hsigma v hv]
  · rw [tau.extend_of_not_mem _ hv]
    rfl

/-- Free colourings are exactly full colourings extending the pinning. -/
def extensionEquiv : (tau.FreeVertex → C) ≃ {sigma : V → C // tau.Extends sigma} where
  toFun := fun sigma ↦ ⟨tau.extend sigma, tau.extend_extends sigma⟩
  invFun := fun sigma ↦ tau.restrictFree sigma.1
  left_inv := tau.restrictFree_extend
  right_inv := fun sigma ↦ by
    apply Subtype.ext
    exact tau.extend_restrictFree sigma.2

/-- The graph induced by the vertices outside the pinning domain. -/
def freeGraph (G : SimpleGraph V) : SimpleGraph tau.FreeVertex :=
  G.induce tau.freeSet

/-- Pinned neighbours of `u`, regarded as vertices of the domain subtype. -/
noncomputable def pinnedNeighbours (G : SimpleGraph V) (u : tau.FreeVertex) : Finset tau.domain :=
  Finset.univ.filter fun v ↦ G.Adj u.1 v.1

/-- The number of pinned neighbours of `u` carrying colour `c`. -/
noncomputable def boundaryCount (G : SimpleGraph V) (u : tau.FreeVertex) (c : C) : ℕ :=
  (tau.pinnedNeighbours G u).filter (fun v ↦ tau.colour v = c) |>.card

/-- The `PinningData` canonically induced by a graph and a partial colouring. -/
noncomputable def toPinningData (G : SimpleGraph V) : PinningData tau.FreeVertex C where
  graph := tau.freeGraph G
  boundaryCount := tau.boundaryCount G

@[simp]
lemma toPinningData_graph (G : SimpleGraph V) :
    (tau.toPinningData G).graph = tau.freeGraph G := rfl

@[simp]
lemma toPinningData_boundaryCount (G : SimpleGraph V) (u : tau.FreeVertex) (c : C) :
    (tau.toPinningData G).boundaryCount u c = tau.boundaryCount G u c := rfl

lemma sum_boundaryCount (G : SimpleGraph V) (u : tau.FreeVertex) :
    ∑ c, tau.boundaryCount G u c = (tau.pinnedNeighbours G u).card := by
  unfold boundaryCount
  simpa using
    (Finset.sum_card_fiberwise_eq_card_filter (tau.pinnedNeighbours G u)
      (Finset.univ : Finset C) tau.colour)

lemma map_pinnedNeighbours (G : SimpleGraph V) (u : tau.FreeVertex) :
    (tau.pinnedNeighbours G u).map (Function.Embedding.subtype _) =
      (G.neighborFinset u.1).filter (fun v ↦ v ∈ tau.domain) := by
  ext v
  simp [pinnedNeighbours]

lemma card_pinnedNeighbours (G : SimpleGraph V) (u : tau.FreeVertex) :
    (tau.pinnedNeighbours G u).card =
      ((G.neighborFinset u.1).filter (fun v ↦ v ∈ tau.domain)).card := by
  rw [← tau.map_pinnedNeighbours G u, Finset.card_map]

lemma free_degree_eq_card_filter (G : SimpleGraph V) (u : tau.FreeVertex) :
    (tau.freeGraph G).degree u =
      ((G.neighborFinset u.1).filter (fun v ↦ v ∉ tau.domain)).card := by
  change ((tau.freeGraph G).neighborFinset u).card = _
  apply Finset.card_bij (fun v _ ↦ v.1)
  · intro v hv
    refine Finset.mem_filter.mpr ⟨?_, v.2⟩
    rw [SimpleGraph.mem_neighborFinset] at hv ⊢
    exact hv
  · intro v _ w _ heq
    exact Subtype.ext heq
  · intro v hv
    refine ⟨⟨v, (Finset.mem_filter.mp hv).2⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact (G.mem_neighborFinset u.1 v).mp (Finset.mem_filter.mp hv).1

/-- Every original neighbour of a free vertex contributes exactly once:
either as a free edge or as one boundary occurrence. -/
lemma constraintDegree_eq_degree (G : SimpleGraph V) (u : tau.FreeVertex) :
    (tau.toPinningData G).constraintDegree u = G.degree u.1 := by
  rw [PinningData.constraintDegree]
  change (tau.freeGraph G).degree u + ∑ c, tau.boundaryCount G u c = G.degree u.1
  rw [tau.sum_boundaryCount G u,
    tau.card_pinnedNeighbours G u, tau.free_degree_eq_card_filter G u,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  simpa using (Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset u.1) (p := fun v ↦ v ∉ tau.domain))

/-- A maximum-degree bound on the original graph is inherited by the induced
`PinningData`. -/
lemma degreeBound_of_original (G : SimpleGraph V) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) : (tau.toPinningData G).DegreeBound Δ := by
  intro u
  rw [tau.constraintDegree_eq_degree G u]
  exact hdegree u.1

/-! ## The free child weight -/

/-- A free edge is monochromatic under `sigma`. -/
def sameColour (sigma : tau.FreeVertex → C) (e : Sym2 tau.FreeVertex) : Prop :=
  Sym2.lift
    ⟨fun u v ↦ sigma u = sigma v, fun u v ↦ by simp only [eq_comm]⟩ e

@[simp]
lemma sameColour_mk (sigma : tau.FreeVertex → C) (u v : tau.FreeVertex) :
    tau.sameColour sigma s(u, v) ↔ sigma u = sigma v := by
  rfl

/-- Number of monochromatic free edges. -/
noncomputable def freeConflictCount (G : SimpleGraph V) (sigma : tau.FreeVertex → C) : ℕ :=
  ((tau.freeGraph G).edgeFinset.filter (tau.sameColour sigma)).card

/-- Number of monochromatic free--pinned incidences.  A simple graph makes
each such incidence a unique crossing edge. -/
noncomputable def boundaryConflictCount (G : SimpleGraph V) (sigma : tau.FreeVertex → C) : ℕ :=
  ∑ u, tau.boundaryCount G u (sigma u)

lemma edgeFactor_eq_of_sameColour (x : ℝ) (sigma : tau.FreeVertex → C)
    (e : Sym2 tau.FreeVertex) :
    PinningData.edgeFactor x sigma e = if tau.sameColour sigma e then x else 1 := by
  induction e using Sym2.ind with
  | _ u v =>
      by_cases h : sigma u = sigma v <;> simp [sameColour, PinningData.edgeFactor_mk, h]

lemma prod_edgeFactor_eq_pow (G : SimpleGraph V) (x : ℝ)
    (sigma : tau.FreeVertex → C) :
    (∏ e ∈ (tau.freeGraph G).edgeFinset, PinningData.edgeFactor x sigma e) =
      x ^ tau.freeConflictCount G sigma := by
  let S := (tau.freeGraph G).edgeFinset
  have hprod : ∀ T : Finset (Sym2 tau.FreeVertex),
      (∏ e ∈ T, PinningData.edgeFactor x sigma e) =
        x ^ (T.filter (tau.sameColour sigma)).card := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert e T he ih =>
      by_cases hsame : tau.sameColour sigma e
      · have hefilter : e ∉ T.filter (tau.sameColour sigma) :=
          fun he' ↦ he (Finset.mem_filter.mp he').1
        have hcard : ((insert e T).filter (tau.sameColour sigma)).card =
            (T.filter (tau.sameColour sigma)).card + 1 := by
          rw [Finset.filter_insert]
          simp [hsame, hefilter]
        rw [Finset.prod_insert he, ih, tau.edgeFactor_eq_of_sameColour x sigma e,
          if_pos hsame, hcard, pow_succ]
        ring
      · have hcard : ((insert e T).filter (tau.sameColour sigma)).card =
            (T.filter (tau.sameColour sigma)).card := by
          rw [Finset.filter_insert]
          simp [hsame]
        rw [Finset.prod_insert he, ih, tau.edgeFactor_eq_of_sameColour x sigma e,
          if_neg hsame, one_mul, hcard]
  exact hprod S

/-- The induced `PinningData` weight is precisely `x` to the number of
free--free and free--pinned monochromatic constraints.  Thus the factors
depending on the free colouring are neither lost nor duplicated by the
boundary-count representation. -/
lemma childWeight_eq_pow (G : SimpleGraph V) (x : ℝ)
    (sigma : tau.FreeVertex → C) :
    (tau.toPinningData G).weight x sigma =
      x ^ tau.boundaryConflictCount G sigma * x ^ tau.freeConflictCount G sigma := by
  unfold PinningData.weight boundaryConflictCount
  change (∏ u, x ^ tau.boundaryCount G u (sigma u)) *
      (∏ e ∈ (tau.freeGraph G).edgeFinset, PinningData.edgeFactor x sigma e) = _
  rw [Finset.prod_pow_eq_pow_sum, tau.prod_edgeFactor_eq_pow G x sigma]

/-! ## Comparison with the Potts weight on the original graph -/

/-- Both endpoints of an original edge are pinned. -/
def pinnedEdge (e : Sym2 V) : Prop :=
  Sym2.lift
    ⟨fun u v ↦ u ∈ tau.domain ∧ v ∈ tau.domain,
      fun u v ↦ by simp only [and_comm]⟩ e

/-- Both endpoints of an original edge are free. -/
def freeEdge (e : Sym2 V) : Prop :=
  Sym2.lift
    ⟨fun u v ↦ u ∉ tau.domain ∧ v ∉ tau.domain,
      fun u v ↦ by simp only [and_comm]⟩ e

/-- Exactly one endpoint of an original edge is free. -/
def crossingEdge (e : Sym2 V) : Prop :=
  Sym2.lift
    ⟨fun u v ↦
        (u ∉ tau.domain ∧ v ∈ tau.domain) ∨
          (u ∈ tau.domain ∧ v ∉ tau.domain),
      fun u v ↦ by aesop⟩ e

/-- An original edge is monochromatic under a full colouring. -/
def fullSameColour (rho : V → C) (e : Sym2 V) : Prop :=
  Sym2.lift
    ⟨fun u v ↦ rho u = rho v, fun u v ↦ by simp only [eq_comm]⟩ e

/-- A pinned--pinned edge whose two prescribed colours agree.  This predicate
does not mention any colouring of the free vertices. -/
def pinnedSameColour (e : Sym2 V) : Prop :=
  Sym2.lift
    ⟨fun u v ↦ ∃ hu : u ∈ tau.domain, ∃ hv : v ∈ tau.domain,
        tau.colour ⟨u, hu⟩ = tau.colour ⟨v, hv⟩,
      fun u v ↦ by
        apply propext
        constructor
        · rintro ⟨hu, hv, h⟩
          exact ⟨hv, hu, h.symm⟩
        · rintro ⟨hv, hu, h⟩
          exact ⟨hu, hv, h.symm⟩⟩ e

@[simp] lemma pinnedEdge_mk (u v : V) :
    tau.pinnedEdge s(u, v) ↔ u ∈ tau.domain ∧ v ∈ tau.domain := by rfl

@[simp] lemma freeEdge_mk (u v : V) :
    tau.freeEdge s(u, v) ↔ u ∉ tau.domain ∧ v ∉ tau.domain := by rfl

@[simp] lemma crossingEdge_mk (u v : V) :
    tau.crossingEdge s(u, v) ↔
      (u ∉ tau.domain ∧ v ∈ tau.domain) ∨
        (u ∈ tau.domain ∧ v ∉ tau.domain) := by rfl

@[simp] lemma fullSameColour_mk (rho : V → C) (u v : V) :
    fullSameColour rho s(u, v) ↔ rho u = rho v := by rfl

@[simp] lemma pinnedSameColour_mk (u v : V) :
    tau.pinnedSameColour s(u, v) ↔
      ∃ hu : u ∈ tau.domain, ∃ hv : v ∈ tau.domain,
        tau.colour ⟨u, hu⟩ = tau.colour ⟨v, hv⟩ := by rfl

lemma edge_trichotomy (e : Sym2 V) :
    tau.pinnedEdge e ∨ tau.freeEdge e ∨ tau.crossingEdge e := by
  induction e using Sym2.ind with
  | _ u v =>
    by_cases hu : u ∈ tau.domain <;> by_cases hv : v ∈ tau.domain <;>
      simp [hu, hv]

lemma edge_categories_disjoint (e : Sym2 V) :
    ¬ (tau.pinnedEdge e ∧ tau.freeEdge e) ∧
      ¬ (tau.pinnedEdge e ∧ tau.crossingEdge e) ∧
      ¬ (tau.freeEdge e ∧ tau.crossingEdge e) := by
  induction e using Sym2.ind with
  | _ u v =>
    by_cases hu : u ∈ tau.domain <;> by_cases hv : v ∈ tau.domain <;>
      simp [hu, hv]

/-- Monochromatic edges in the original graph. -/
noncomputable def fullConflictEdges (G : SimpleGraph V) (sigma : tau.FreeVertex → C) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter (fullSameColour (tau.extend sigma))

/-- Monochromatic pinned--pinned edges. -/
noncomputable def pinnedConflictEdges (G : SimpleGraph V) : Finset (Sym2 V) :=
  G.edgeFinset.filter tau.pinnedSameColour

/-- Monochromatic crossing edges. -/
noncomputable def crossingConflictEdges (G : SimpleGraph V)
    (sigma : tau.FreeVertex → C) : Finset (Sym2 V) :=
  (tau.fullConflictEdges G sigma).filter tau.crossingEdge

/-- Monochromatic free--free edges, viewed in the original graph. -/
noncomputable def originalFreeConflictEdges (G : SimpleGraph V)
    (sigma : tau.FreeVertex → C) : Finset (Sym2 V) :=
  (tau.fullConflictEdges G sigma).filter tau.freeEdge

/-- The free--pinned incidences counted by `boundaryConflictCount`. -/
noncomputable def boundaryConflictPairs (G : SimpleGraph V)
    (sigma : tau.FreeVertex → C) : Finset (Σ _u : tau.FreeVertex, tau.domain) :=
  Finset.univ.sigma fun u ↦
    (tau.pinnedNeighbours G u).filter (fun v ↦ tau.colour v = sigma u)

lemma card_boundaryConflictPairs (G : SimpleGraph V) (sigma : tau.FreeVertex → C) :
    (tau.boundaryConflictPairs G sigma).card = tau.boundaryConflictCount G sigma := by
  rw [boundaryConflictPairs, Finset.card_sigma]
  simp [boundaryConflictCount, boundaryCount]

lemma card_boundaryConflictPairs_eq_crossing (G : SimpleGraph V)
    (sigma : tau.FreeVertex → C) :
    (tau.boundaryConflictPairs G sigma).card =
      (tau.crossingConflictEdges G sigma).card := by
  apply Finset.card_bij
      (fun z _ ↦ s((z.1 : V), (z.2 : V)))
  · rintro ⟨u, v⟩ huv
    simp only [boundaryConflictPairs, Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_filter] at huv
    rcases huv with ⟨hvu, hcolour⟩
    have hadj : G.Adj u.1 v.1 := by
      simpa [pinnedNeighbours] using hvu
    have hfree : u.1 ∉ tau.domain := u.2
    have hpinned : v.1 ∈ tau.domain := v.2
    have hsame : tau.extend sigma u.1 = tau.extend sigma v.1 := by
      rw [tau.extend_of_not_mem sigma hfree, tau.extend_of_mem sigma hpinned]
      exact hcolour.symm
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset]
      exact (SimpleGraph.mem_edgeSet G).mpr hadj
    · exact hsame
    · exact Or.inl ⟨hfree, hpinned⟩
  · rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · cases u with
      | mk u hufree =>
        cases u' with
        | mk u' hu'free =>
          cases v with
          | mk v hvpin =>
            cases v' with
            | mk v' hv'pin =>
              have huu : (⟨u, hufree⟩ : tau.FreeVertex) = ⟨u', hu'free⟩ :=
                Subtype.ext hu
              have hvv : (⟨v, hvpin⟩ : tau.domain) = ⟨v', hv'pin⟩ :=
                Subtype.ext hv
              cases huu
              cases hvv
              rfl
    · have hufree : u.1 ∉ tau.domain := u.2
      have hv'pin : v'.1 ∈ tau.domain := v'.2
      exact False.elim (hufree (hu.symm ▸ hv'pin))
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [crossingConflictEdges, fullConflictEdges, Finset.mem_filter] at he
      rcases he with ⟨⟨hedge, hsame⟩, hcross⟩
      rw [tau.crossingEdge_mk] at hcross
      rw [fullSameColour_mk] at hsame
      have hadj : G.Adj a b := by
        simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hedge
      rcases hcross with ⟨hafree, hbpin⟩ | ⟨hapin, hbfree⟩
      · let u : tau.FreeVertex := ⟨a, hafree⟩
        let v : tau.domain := ⟨b, hbpin⟩
        have hcolour : tau.colour v = sigma u := by
          simpa [u, v, tau.extend_of_not_mem sigma hafree,
            tau.extend_of_mem sigma hbpin] using hsame.symm
        refine ⟨⟨u, v⟩, ?_, rfl⟩
        simp [boundaryConflictPairs, pinnedNeighbours, u, v, hadj, hcolour]
      · let u : tau.FreeVertex := ⟨b, hbfree⟩
        let v : tau.domain := ⟨a, hapin⟩
        have hcolour : tau.colour v = sigma u := by
          simpa [u, v, tau.extend_of_mem sigma hapin,
            tau.extend_of_not_mem sigma hbfree] using hsame
        refine ⟨⟨u, v⟩, ?_, ?_⟩
        · simp [boundaryConflictPairs, pinnedNeighbours, u, v, hadj.symm, hcolour]
        · exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)

lemma card_originalFreeConflictEdges (G : SimpleGraph V)
    (sigma : tau.FreeVertex → C) :
    (tau.originalFreeConflictEdges G sigma).card = tau.freeConflictCount G sigma := by
  symm
  apply Finset.card_bij
      (fun e _ ↦ (Function.Embedding.subtype (fun x => x ∈ tau.freeSet)).sym2Map e)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Finset.mem_filter] at he
      rcases he with ⟨hedge, hsame⟩
      have hadjFree : (tau.freeGraph G).Adj u v :=
        (SimpleGraph.mem_edgeSet _).mp ((SimpleGraph.mem_edgeFinset).mp hedge)
      have hadj : G.Adj u.1 v.1 := hadjFree
      have hfull : tau.extend sigma u.1 = tau.extend sigma v.1 := by
        rw [tau.extend_of_not_mem sigma u.2, tau.extend_of_not_mem sigma v.2]
        exact hsame
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset]
        exact (SimpleGraph.mem_edgeSet G).mpr hadj
      · exact hfull
      · exact ⟨u.2, v.2⟩
  · intro e he e' he' heq
    exact (Function.Embedding.sym2Map (Function.Embedding.subtype (fun x => x ∈ tau.freeSet))).injective heq
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      simp only [originalFreeConflictEdges, fullConflictEdges, Finset.mem_filter] at he
      rcases he with ⟨⟨hedge, hsame⟩, hfree⟩
      rw [tau.freeEdge_mk] at hfree
      rw [fullSameColour_mk] at hsame
      rcases hfree with ⟨hafree, hbfree⟩
      let u : tau.FreeVertex := ⟨a, hafree⟩
      let v : tau.FreeVertex := ⟨b, hbfree⟩
      have hadj : (tau.freeGraph G).Adj u v := by
        exact (SimpleGraph.mem_edgeSet G).mp ((SimpleGraph.mem_edgeFinset).mp hedge)
      have hcolour : sigma u = sigma v := by
        simpa [u, v, tau.extend_of_not_mem sigma hafree,
          tau.extend_of_not_mem sigma hbfree] using hsame
      refine ⟨s(u, v), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨
        ((SimpleGraph.mem_edgeFinset).mpr ((SimpleGraph.mem_edgeSet _).mpr hadj)), hcolour⟩

lemma pinned_part_eq (G : SimpleGraph V) (sigma : tau.FreeVertex → C) :
    (tau.fullConflictEdges G sigma).filter tau.pinnedEdge = tau.pinnedConflictEdges G := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    by_cases hu : u ∈ tau.domain <;> by_cases hv : v ∈ tau.domain <;>
      simp [fullConflictEdges, pinnedConflictEdges, hu, hv, extend]

lemma conflictEdges_partition (G : SimpleGraph V) (sigma : tau.FreeVertex → C) :
    (tau.fullConflictEdges G sigma).card =
      (tau.pinnedConflictEdges G).card +
        (tau.crossingConflictEdges G sigma).card +
        (tau.originalFreeConflictEdges G sigma).card := by
  let S := tau.fullConflictEdges G sigma
  have hfree :
      (S.filter (fun e ↦ ¬ tau.pinnedEdge e)).filter tau.freeEdge =
        S.filter tau.freeEdge := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      by_cases hu : u ∈ tau.domain <;> by_cases hv : v ∈ tau.domain <;>
        simp [hu, hv]
  have hcross :
      (S.filter (fun e ↦ ¬ tau.pinnedEdge e)).filter (fun e ↦ ¬ tau.freeEdge e) =
        S.filter tau.crossingEdge := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      by_cases hu : u ∈ tau.domain <;> by_cases hv : v ∈ tau.domain <;>
        simp [hu, hv]
  have hfirst := Finset.card_filter_add_card_filter_not
    (s := S) (p := tau.pinnedEdge)
  have hsecond := Finset.card_filter_add_card_filter_not
    (s := S.filter (fun e ↦ ¬ tau.pinnedEdge e)) (p := tau.freeEdge)
  rw [hfree, hcross] at hsecond
  rw [← tau.pinned_part_eq G sigma]
  change S.card = (S.filter tau.pinnedEdge).card +
    (S.filter tau.crossingEdge).card + (S.filter tau.freeEdge).card
  omega

/-- The ordinary Potts edge-product on the original graph. -/
noncomputable def fullPottsWeight (G : SimpleGraph V) (x : ℝ) (rho : V → C) : ℝ :=
  ∏ e ∈ G.edgeFinset, PinningData.edgeFactor x rho e

/-- Number of monochromatic original edges after extending the pinning. -/
noncomputable def fullConflictCount (G : SimpleGraph V)
    (sigma : tau.FreeVertex → C) : ℕ :=
  (tau.fullConflictEdges G sigma).card

/-- Number of monochromatic edges entirely inside the pinning domain. -/
noncomputable def pinnedConflictCount (G : SimpleGraph V) : ℕ :=
  (tau.pinnedConflictEdges G).card

/-- The factor contributed by edges entirely inside the pinning domain. -/
noncomputable def pinnedScalar (G : SimpleGraph V) (x : ℝ) : ℝ :=
  x ^ tau.pinnedConflictCount G

lemma fullPottsWeight_eq_pow (G : SimpleGraph V) (x : ℝ) (rho : V → C) :
    fullPottsWeight G x rho =
      x ^ ((G.edgeFinset.filter (fullSameColour rho)).card) := by
  unfold fullPottsWeight
  have hprod : ∀ T : Finset (Sym2 V),
      (∏ e ∈ T, PinningData.edgeFactor x rho e) =
        x ^ (T.filter (fullSameColour rho)).card := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert e T he ih =>
      by_cases hsame : fullSameColour rho e
      · have hefilter : e ∉ T.filter (fullSameColour rho) :=
          fun he' ↦ he (Finset.mem_filter.mp he').1
        have hcard : ((insert e T).filter (fullSameColour rho)).card =
            (T.filter (fullSameColour rho)).card + 1 := by
          rw [Finset.filter_insert]
          simp [hsame, hefilter]
        rw [Finset.prod_insert he, ih]
        have hedge : PinningData.edgeFactor x rho e = x := by
          induction e using Sym2.ind with
          | _ u v =>
            change rho u = rho v at hsame
            rw [PinningData.edgeFactor_mk, if_pos hsame]
        rw [hedge, hcard, pow_succ]
        ring
      · have hcard : ((insert e T).filter (fullSameColour rho)).card =
            (T.filter (fullSameColour rho)).card := by
          rw [Finset.filter_insert]
          simp [hsame]
        rw [Finset.prod_insert he, ih]
        have hedge : PinningData.edgeFactor x rho e = 1 := by
          induction e using Sym2.ind with
          | _ u v =>
            change rho u ≠ rho v at hsame
            rw [PinningData.edgeFactor_mk, if_neg hsame]
        rw [hedge, one_mul, hcard]
  exact hprod G.edgeFinset

lemma fullConflictCount_add (G : SimpleGraph V) (sigma : tau.FreeVertex → C) :
    tau.fullConflictCount G sigma =
      tau.pinnedConflictCount G + tau.boundaryConflictCount G sigma +
        tau.freeConflictCount G sigma := by
  have hpartition := tau.conflictEdges_partition G sigma
  have hboundary : (tau.crossingConflictEdges G sigma).card =
      tau.boundaryConflictCount G sigma := by
    rw [← tau.card_boundaryConflictPairs_eq_crossing G sigma,
      tau.card_boundaryConflictPairs G sigma]
  have hfree : (tau.originalFreeConflictEdges G sigma).card =
      tau.freeConflictCount G sigma := tau.card_originalFreeConflictEdges G sigma
  unfold fullConflictCount pinnedConflictCount
  omega

/-- Exact factorization of the original Potts weight under a partial
colouring.  The first factor depends only on the pinned vertices; every factor
depending on the free colouring is exactly the `PinningData.weight`. -/
lemma fullPottsWeight_extend (G : SimpleGraph V) (x : ℝ)
    (sigma : tau.FreeVertex → C) :
    fullPottsWeight G x (tau.extend sigma) =
      tau.pinnedScalar G x * (tau.toPinningData G).weight x sigma := by
  rw [fullPottsWeight_eq_pow]
  change x ^ tau.fullConflictCount G sigma = _
  rw [tau.fullConflictCount_add G sigma, tau.childWeight_eq_pow G x sigma]
  unfold pinnedScalar
  rw [pow_add, pow_add]
  ring


/-- The normalized free child law attached to the original graph and the
explicit pinning. -/
noncomputable def childGibbs (G : SimpleGraph V) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < (tau.toPinningData G).partition x) : FinDist (tau.FreeVertex → C) :=
  (tau.toPinningData G).gibbs x hx hZ

@[simp]
lemma childGibbs_apply (G : SimpleGraph V) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < (tau.toPinningData G).partition x) (sigma : tau.FreeVertex → C) :
    (tau.childGibbs G x hx hZ).w sigma =
      (tau.toPinningData G).weight x sigma / (tau.toPinningData G).partition x := rfl

/-- Any positive factor depending only on the pinned part cancels from the
normalized free law.  This is the precise normalization step used after the
full Potts weight is split into a pinned-only scalar and `childWeight`. -/
lemma normalize_pinnedScalar (G : SimpleGraph V) (x kappa : ℝ) (hkappa : 0 < kappa)
    (hx : 0 ≤ x) (hZ : 0 < (tau.toPinningData G).partition x)
    (sigma : tau.FreeVertex → C) :
    (kappa * (tau.toPinningData G).weight x sigma) /
        (∑ eta : tau.FreeVertex → C, kappa * (tau.toPinningData G).weight x eta) =
      (tau.childGibbs G x hx hZ).w sigma := by
  rw [tau.childGibbs_apply G x hx hZ sigma]
  have hsum : (∑ eta : tau.FreeVertex → C,
      kappa * (tau.toPinningData G).weight x eta) =
      kappa * (tau.toPinningData G).partition x := by
    rw [PinningData.partition, Finset.mul_sum]
  rw [hsum]
  field_simp [hkappa.ne', hZ.ne']

/-- The partition function obtained by summing the original-graph weight over
all full colourings extending `tau`.  The equivalence `extensionEquiv` shows
that this sum has exactly one term for every extending full colouring. -/
noncomputable def conditionalFullPartition (G : SimpleGraph V) (x : ℝ) : ℝ :=
  ∑ sigma : tau.FreeVertex → C, fullPottsWeight G x (tau.extend sigma)

lemma conditionalFullPartition_eq (G : SimpleGraph V) (x : ℝ) :
    tau.conditionalFullPartition G x =
      tau.pinnedScalar G x * (tau.toPinningData G).partition x := by
  unfold conditionalFullPartition
  simp_rw [tau.fullPottsWeight_extend G x]
  rw [PinningData.partition, Finset.mul_sum]

/-- Pointwise equality of the normalized original conditional weights and the
`PinningData` Gibbs law.  Positivity of `x` is used only to ensure that the
pinned-only scalar can be cancelled. -/
lemma normalized_fullPottsWeight_eq_childGibbs (G : SimpleGraph V) {x : ℝ}
    (hx : 0 < x) (hZ : 0 < (tau.toPinningData G).partition x)
    (sigma : tau.FreeVertex → C) :
    fullPottsWeight G x (tau.extend sigma) / tau.conditionalFullPartition G x =
      (tau.childGibbs G x hx.le hZ).w sigma := by
  rw [tau.fullPottsWeight_extend G x sigma, tau.conditionalFullPartition_eq G x]
  rw [tau.childGibbs_apply G x hx.le hZ sigma]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hx.ne')

/-- The conditional Potts distribution defined directly from the original
graph, represented on the equivalent free-colouring state space. -/
noncomputable def fullConditionalGibbs (G : SimpleGraph V) (x : ℝ) (hx : 0 < x)
    (hZ : 0 < (tau.toPinningData G).partition x) : FinDist (tau.FreeVertex → C) := by
  have hscalar : 0 < tau.pinnedScalar G x := by
    exact pow_pos hx _
  have hpartition : 0 < tau.conditionalFullPartition G x := by
    rw [tau.conditionalFullPartition_eq G x]
    exact mul_pos hscalar hZ
  exact
    { w := fun sigma ↦
        fullPottsWeight G x (tau.extend sigma) / tau.conditionalFullPartition G x
      nonneg := fun sigma ↦ by
        refine div_nonneg ?_ hpartition.le
        rw [tau.fullPottsWeight_extend G x sigma]
        exact mul_nonneg hscalar.le ((tau.toPinningData G).weight_nonneg hx.le sigma)
      sum_one := by
        rw [← Finset.sum_div, conditionalFullPartition]
        exact div_self hpartition.ne' }

/-- Equality of the two normalized conditional laws, not merely of their
unnormalized weights. -/
lemma fullConditionalGibbs_eq_childGibbs (G : SimpleGraph V) (x : ℝ) (hx : 0 < x)
    (hZ : 0 < (tau.toPinningData G).partition x) :
    tau.fullConditionalGibbs G x hx hZ = tau.childGibbs G x hx.le hZ := by
  ext sigma
  exact tau.normalized_fullPottsWeight_eq_childGibbs G hx hZ sigma

end PartialColouring

end PottsCI
