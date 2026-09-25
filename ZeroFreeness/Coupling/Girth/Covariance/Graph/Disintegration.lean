import ZeroFreeness.Coupling.Girth.Covariance.Graph.TwoLayer
import ZeroFreeness.Potts.Geometry.GenericGibbsRelabel

/-!
# Second-layer disintegration at every activity `x ≥ 0`
(companion Lemma 9.1, `lem:girth5-disintegration`)

Let `I` be a residual instance with free root `v = none`, `U = N_H(v)`,
`S = S₂^H(v)`, `O` the remaining vertices, and `ν = μ_{I-v}` the actual
normalized Gibbs law of `I - v` (root and its incident edges deleted,
boundary counts retained). If `girth(H) ≥ 5`, then

* `U` is independent,
* every `w ∈ S` has a unique neighbour in `U`,
* for every `ξ` with `ν(σ_S = ξ) > 0`,
  `ν(σ_U = α, σ_O = o | σ_S = ξ) = (∏_{u∈U} π_u^ξ(α_u)) · ν_O^ξ(o)`,
  where `π_u^ξ` and `ν_O^ξ` are the conditional marginals of `σ_u` and
  `σ_O` given `σ_S = ξ`.

`InsertionGraph.law_eq_model` gives the last item only for `x > 0` (through
strictly positive heat-bath laws), and the graph facts are split over
several declarations. Here the conditional product decomposition is proved
for every `x ≥ 0`, in particular for the hard-colouring law at `x = 0`,
directly from the exact factorization of the Potts weight over the
independent first layer; no positivity of any single-site law is used.
`second_layer_disintegration` states the whole lemma in one declaration.
-/

namespace ZeroFreeness.Appendix.Girth

open scoped BigOperators
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator ZeroFreeness.Appendix.Girth

noncomputable section

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

/-! ## Conditional product from a product-form weight -/

section Abstract

variable {Ω U O C : Type*} [Fintype U] [Fintype O] [Fintype C] [DecidableEq U]

/-- Conditional marginal of the coordinate `u`, given the shell value `ξ`. -/
def neighbourConditional (W : Ω → (U → C) → O → ℝ) (ξ : Ω) (u : U) (c : C) : ℝ :=
  (∑ α, ∑ o, if α u = c then W ξ α o else 0) / ∑ α, ∑ o, W ξ α o

/-- Conditional marginal of the exterior, given the shell value `ξ`. -/
def exteriorConditional (W : Ω → (U → C) → O → ℝ) (ξ : Ω) (o : O) : ℝ :=
  (∑ α, W ξ α o) / ∑ α, ∑ o, W ξ α o

theorem sum_prod_indicator (a : U → C → ℝ) (u : U) (c : C) :
    (∑ α : U → C, if α u = c then ∏ j, a j (α j) else 0) =
      a u c * ∏ j ∈ Finset.univ.erase u, ∑ d, a j d := by
  let a' : U → C → ℝ := fun j d => if j = u then (if d = c then a j d else 0) else a j d
  have hpt (α : U → C) : (∏ j, a' j (α j)) = if α u = c then ∏ j, a j (α j) else 0 := by
    split_ifs with h
    · apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = u
      · subst hj; simp [a', h]
      · simp [a', hj]
    · apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [a', h]
  have hsum (j : U) : (∑ d, a' j d) = if j = u then a u c else ∑ d, a j d := by
    by_cases hj : j = u
    · subst hj; simp [a']
    · simp [a', hj]
  calc
    _ = ∑ α : U → C, ∏ j, a' j (α j) := Finset.sum_congr rfl fun α _ => (hpt α).symm
    _ = ∏ j, ∑ d, a' j d := (Fintype.prod_sum a').symm
    _ = ∏ j, (if j = u then a u c else ∑ d, a j d) := Finset.prod_congr rfl fun j _ => hsum j
    _ = _ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ u), if_pos rfl]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (Finset.ne_of_mem_erase hj)]

/-- If the joint weight has the form `E(ξ,o) ∏_u a(ξ,u,α_u)`, then given any
shell value of positive mass the conditional law of `(σ_U, σ_O)` is the
product of the conditional marginals. No sign condition is needed. -/
theorem conditional_product (W : Ω → (U → C) → O → ℝ) (E : Ω → O → ℝ)
    (a : Ω → U → C → ℝ) (hW : ∀ ξ α o, W ξ α o = E ξ o * ∏ u, a ξ u (α u))
    (ξ : Ω) (hP : (∑ α, ∑ o, W ξ α o) ≠ 0) (α : U → C) (o : O) :
    W ξ α o / (∑ α, ∑ o, W ξ α o) =
      (∏ u, neighbourConditional W ξ u (α u)) * exteriorConditional W ξ o := by
  set A : U → ℝ := fun u => ∑ d, a ξ u d
  set Es := ∑ o, E ξ o
  have hPform : (∑ α, ∑ o, W ξ α o) = Es * ∏ u, A u := by
    simp_rw [hW]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, Fintype.prod_sum]
  rw [hPform] at hP ⊢
  have hEs : Es ≠ 0 := left_ne_zero_of_mul hP
  have hA : (∏ u, A u) ≠ 0 := right_ne_zero_of_mul hP
  have hAu (u : U) : A u ≠ 0 := by
    intro h
    exact hA (Finset.prod_eq_zero (Finset.mem_univ u) h)
  have hπ (u : U) (c : C) : neighbourConditional W ξ u c = a ξ u c / A u := by
    unfold neighbourConditional
    rw [hPform]
    have hnum : (∑ α : U → C, ∑ o, if α u = c then W ξ α o else 0) =
        Es * (a ξ u c * ∏ j ∈ Finset.univ.erase u, A j) := by
      rw [← sum_prod_indicator (a ξ) u c, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro β _
      split_ifs with h
      · simp_rw [hW]
        rw [← Finset.sum_mul]
      · simp
    rw [hnum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ u)]
    have hrest : (∏ j ∈ Finset.univ.erase u, A j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => hAu j
    field_simp
  have hν : exteriorConditional W ξ o = E ξ o / Es := by
    unfold exteriorConditional
    rw [hPform]
    simp_rw [hW]
    rw [← Finset.mul_sum, ← Fintype.prod_sum]
    change E ξ o * (∏ u, A u) / (Es * ∏ u, A u) = E ξ o / Es
    field_simp
  simp_rw [hπ, hν, hW]
  rw [Finset.prod_div_distrib]
  field_simp

end Abstract

/-! ## The Potts weight factorizes over an independent first layer -/

section Potts

variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq S] [DecidableEq O] [DecidableEq C]
variable (I : PinningData (Vertex U S O) C) (x : ℝ)

/-- The factors not involving any first-layer vertex. -/
def restWeight (σ : Vertex U S O → C) : ℝ :=
  (∏ w : S ⊕ O, x ^ I.boundaryCount (Sum.inr w) (σ (Sum.inr w))) *
    ∏ e ∈ I.graph.edgeFinset.filter (fun e => ¬ ∃ u : U, Sum.inl u ∈ e),
      PinningData.edgeFactor x σ e

/-- Exact factorization of the Potts weight at every real activity. -/
theorem weight_split (hi : InsertionGraph.Independent I) (σ : Vertex U S O → C) :
    I.weight x σ = restWeight I x σ *
      ∏ u, GraphHeatBath.siteWeight I x σ (Sum.inl u) (σ (Sum.inl u)) := by
  have hbi : I.graph.edgeFinset.filter (fun e => ∃ u : U, Sum.inl u ∈ e) =
      Finset.univ.biUnion (fun u : U => I.graph.edgeFinset.filter (fun e => Sum.inl u ∈ e)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨he, u, hu⟩; exact ⟨u, he, hu⟩
    · rintro ⟨u, he, hu⟩; exact ⟨he, u, hu⟩
  have hdisj : ((Finset.univ : Finset U) : Set U).PairwiseDisjoint
      (fun u : U => I.graph.edgeFinset.filter (fun e => Sum.inl u ∈ e)) := by
    intro u _ u' _ huu'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    rw [Finset.mem_filter] at he he'
    have hne : (Sum.inl u : Vertex U S O) ≠ Sum.inl u' := fun h => huu' (Sum.inl_injective h)
    have heq := (Sym2.mem_and_mem_iff hne).mp ⟨he.2, he'.2⟩
    have hadj : I.graph.Adj (Sum.inl u) (Sum.inl u') := by
      have := he.1
      rw [heq, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at this
      exact this
    exact hi u u' hadj
  have hedges : (∏ e ∈ I.graph.edgeFinset, PinningData.edgeFactor x σ e) =
      (∏ u, x ^ ((I.graph.neighborFinset (Sum.inl u)).filter
          (fun w => σ w = σ (Sum.inl u))).card) *
        ∏ e ∈ I.graph.edgeFinset.filter (fun e => ¬ ∃ u : U, Sum.inl u ∈ e),
          PinningData.edgeFactor x σ e := by
    rw [← Finset.prod_filter_mul_prod_filter_not I.graph.edgeFinset
      (fun e => ∃ u : U, Sum.inl u ∈ e), hbi, Finset.prod_biUnion hdisj]
    congr 1
    apply Finset.prod_congr rfl
    intro u _
    exact GraphHeatBath.incident_product I x σ (Sum.inl u)
  unfold PinningData.weight restWeight GraphHeatBath.siteWeight GraphHeatBath.siteCount
  rw [hedges, Fintype.prod_sum_type]
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

theorem restWeight_join (α β : U → C) (ξ : S → C) (o : O → C) :
    restWeight I x (join α ξ o) = restWeight I x (join β ξ o) := by
  unfold restWeight
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  have hn := (Finset.mem_filter.mp he).2
  induction e using Sym2.ind with
  | _ a b =>
    rcases a with a | a
    · exact (hn ⟨a, Sym2.mem_mk_left _ _⟩).elim
    rcases b with b | b
    · exact (hn ⟨b, Sym2.mem_mk_right _ _⟩).elim
    rfl

variable [Nonempty C]

/-- The site weight of a first-layer vertex depends only on the shell. -/
theorem siteWeight_join (hi : InsertionGraph.Independent I) (hs : Separates I)
    (α β : U → C) (ξ : S → C) (o t : O → C) (u : U) (c : C) :
    GraphHeatBath.siteWeight I x (join α ξ o) (Sum.inl u) c =
      GraphHeatBath.siteWeight I x (join β ξ t) (Sum.inl u) c := by
  unfold GraphHeatBath.siteWeight
  rw [InsertionGraph.siteCount_join I hi hs α β ξ o t u c]

/-- The conditional product decomposition for the actual Gibbs law of a
three-part instance, at every activity `x ≥ 0` (including `x = 0`). -/
theorem gibbs_conditional_product (hi : InsertionGraph.Independent I) (hs : Separates I)
    (hx : 0 ≤ x) (hZ : 0 < I.partition x) (ξ : S → C)
    (hP : 0 < ∑ α, ∑ o, (I.gibbs x hx hZ).w (join α ξ o)) (α : U → C) (o : O → C) :
    (I.gibbs x hx hZ).w (join α ξ o) / (∑ α, ∑ o, (I.gibbs x hx hZ).w (join α ξ o)) =
      (∏ u, neighbourConditional (fun ξ α o => (I.gibbs x hx hZ).w (join α ξ o)) ξ u (α u)) *
        exteriorConditional (fun ξ α o => (I.gibbs x hx hZ).w (join α ξ o)) ξ o := by
  let c₀ : C := Classical.arbitrary C
  let E : (S → C) → (O → C) → ℝ := fun ξ o =>
    restWeight I x (join (fun _ => c₀) ξ o) / I.partition x
  let a : (S → C) → U → C → ℝ := fun ξ u c =>
    GraphHeatBath.siteWeight I x (join (fun _ => c₀) ξ (fun _ => c₀)) (Sum.inl u) c
  apply conditional_product (fun ξ α o => (I.gibbs x hx hZ).w (join α ξ o)) E a _ ξ hP.ne' α o
  intro ξ α o
  change I.weight x (join α ξ o) / I.partition x = _
  rw [weight_split I x hi, restWeight_join I x α (fun _ => c₀)]
  have hsite : (∏ u, GraphHeatBath.siteWeight I x (join α ξ o) (Sum.inl u) (join α ξ o (Sum.inl u))) =
      ∏ u, a ξ u (α u) := by
    apply Finset.prod_congr rfl
    intro u _
    exact siteWeight_join I x hi hs α (fun _ => c₀) ξ o (fun _ => c₀) u (α u)
  rw [hsite]
  simp only [E]
  ring

end Potts

/-! ## The paper's lemma for a free root `v = none` -/

section Graph

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]
variable (I : PinningData (Option V) C)

/-- The configuration of `V` assembled from its first-layer, shell, and
exterior parts. -/
def assemble (α : GraphTwoLayer.First I → C) (ξ : GraphTwoLayer.Second I → C)
    (o : GraphTwoLayer.Outside I → C) : V → C :=
  fun v => join α ξ o (GraphTwoLayer.splitEquiv I v)

theorem assemble_bijective :
    Function.Bijective (fun p : (GraphTwoLayer.Second I → C) ×
        ((GraphTwoLayer.First I → C) × (GraphTwoLayer.Outside I → C)) =>
      assemble I p.2.1 p.1 p.2.2) := by
  have h : (fun p : (GraphTwoLayer.Second I → C) ×
        ((GraphTwoLayer.First I → C) × (GraphTwoLayer.Outside I → C)) =>
      assemble I p.2.1 p.1 p.2.2) =
      (relabelColouring (C := C) (GraphTwoLayer.splitEquiv I)).symm ∘ coloringEquiv.symm := by
    funext p
    rfl
  rw [h]
  exact ((relabelColouring (GraphTwoLayer.splitEquiv I)).symm.bijective.comp
    coloringEquiv.symm.bijective)

theorem second_iff_distance_two (w : V) :
    I.graph.dist none (some w) = 2 ↔
      w ∉ optionRootNeighbours I ∧ GraphTwoLayer.HasPredecessor I w := by
  constructor
  · intro h
    have hr : I.graph.Reachable none (some w) :=
      SimpleGraph.Reachable.of_dist_ne_zero (by omega)
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    rw [h] at hp
    refine ⟨?_, ?_⟩
    · intro hw
      have hadj : I.graph.Adj none (some w) := by
        simpa only [optionRootNeighbours, Finset.mem_filter, Finset.mem_univ, true_and] using hw
      have := SimpleGraph.dist_le (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
      simp at this
      omega
    · cases p with
      | cons h1 p =>
        cases p with
        | nil => simp at hp
        | cons h2 p =>
          cases p with
          | cons _ _ => simp at hp
          | nil =>
            rename_i y
            cases y with
            | none => exact (I.graph.irrefl h1).elim
            | some y =>
              have hy : y ∈ optionRootNeighbours I := by
                simpa only [optionRootNeighbours, Finset.mem_filter, Finset.mem_univ,
                  true_and] using h1
              exact ⟨⟨y, hy⟩, h2⟩
  · rintro ⟨hn, hp⟩
    exact GraphTwoLayer.second_distance I ⟨w, hn, hp⟩

/-- Companion Lemma 9.1 (`lem:girth5-disintegration`), in one statement, for
every activity `x ≥ 0`. Here `H = I.graph`, `v = none`, `U = First I` (the
neighbours of `v`), `S = Second I` (the vertices at distance two, by the
third clause), `O = Outside I`, and `ν = μ_{I-v}` is the actual normalized
Gibbs law of `optionMiddleData I`; `assemble` identifies configurations of
`V` with triples `(σ_U, σ_S, σ_O)` bijectively. -/
theorem second_layer_disintegration (hg : 5 ≤ I.graph.egirth) {x : ℝ} (hx : 0 ≤ x)
    (hZ : 0 < (optionMiddleData I).partition x) :
    (∀ u u' : GraphTwoLayer.First I, ¬ I.graph.Adj (some u.val) (some u'.val)) ∧
    (∀ w : GraphTwoLayer.Second I, ∃! u : GraphTwoLayer.First I,
      I.graph.Adj (some u.val) (some w.val)) ∧
    (∀ w : V, I.graph.dist none (some w) = 2 ↔
      w ∉ optionRootNeighbours I ∧ GraphTwoLayer.HasPredecessor I w) ∧
    ∀ ξ : GraphTwoLayer.Second I → C,
      0 < ∑ α, ∑ o, ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o) →
      ∀ α o,
        ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o) /
            (∑ α, ∑ o, ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o)) =
          (∏ u, neighbourConditional
            (fun ξ α o => ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o)) ξ u (α u)) *
          exteriorConditional
            (fun ξ α o => ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o)) ξ o := by
  refine ⟨fun u u' => GraphTwoLayer.independent I hg u u', ?_,
    second_iff_distance_two I, ?_⟩
  · intro w
    refine ⟨GraphTwoLayer.owner I w, GraphTwoLayer.owner_adj I w, ?_⟩
    intro u hu
    exact (GraphTwoLayer.owner_unique I hg w u).mp hu
  · intro ξ hP α o
    have hZ' : 0 < (GraphTwoLayer.data I).partition x :=
      partition_relabel_pos _ _ x hZ
    have hw (α : GraphTwoLayer.First I → C) (ξ : GraphTwoLayer.Second I → C)
        (o : GraphTwoLayer.Outside I → C) :
        ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o) =
          ((GraphTwoLayer.data I).gibbs x hx hZ').w (join α ξ o) := by
      change (optionMiddleData I).weight x _ / (optionMiddleData I).partition x =
        (relabelData (optionMiddleData I) (GraphTwoLayer.splitEquiv I)).weight x _ /
          (relabelData (optionMiddleData I) (GraphTwoLayer.splitEquiv I)).partition x
      rw [weight_relabel, partition_relabel]
      rfl
    simp only [hw] at hP ⊢
    have h := gibbs_conditional_product (GraphTwoLayer.data I) x
      (GraphTwoLayer.independent I hg) (GraphTwoLayer.separates I) hx hZ' ξ hP α o
    simpa only [neighbourConditional, exteriorConditional, hw] using h

/-- The same statement with `ν = μ_{I-v}` well defined from the section's
colour hypothesis: `q ≥ Δ + 1` gives a positive partition function at
every `x ≥ 0`, including the hard-colouring law at `x = 0`. -/
theorem second_layer_disintegration_of_degree (hg : 5 ≤ I.graph.egirth) {Δ : ℕ}
    (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) {x : ℝ} (hx : 0 ≤ x) :
    ∃ hZ : 0 < (optionMiddleData I).partition x,
    (∀ u u' : GraphTwoLayer.First I, ¬ I.graph.Adj (some u.val) (some u'.val)) ∧
    (∀ w : GraphTwoLayer.Second I, ∃! u : GraphTwoLayer.First I,
      I.graph.Adj (some u.val) (some w.val)) ∧
    (∀ w : V, I.graph.dist none (some w) = 2 ↔
      w ∉ optionRootNeighbours I ∧ GraphTwoLayer.HasPredecessor I w) ∧
    ∀ ξ : GraphTwoLayer.Second I → C,
      0 < ∑ α, ∑ o, ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o) →
      ∀ α o,
        ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o) /
            (∑ α, ∑ o, ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o)) =
          (∏ u, neighbourConditional
            (fun ξ α o => ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o)) ξ u (α u)) *
          exteriorConditional
            (fun ξ α o => ((optionMiddleData I).gibbs x hx hZ).w (assemble I α ξ o)) ξ o := by
  have hZ : 0 < (optionMiddleData I).partition x :=
    partition_pos_of_succ_le (optionMiddleData I) hx (GraphTwoLayer.middle_degreeBound I hd) hq
  exact ⟨hZ, second_layer_disintegration I hg hx hZ⟩

end Graph

end

end ZeroFreeness.Appendix.Girth
