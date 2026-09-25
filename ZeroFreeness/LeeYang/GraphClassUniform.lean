import ZeroFreeness.LeeYang.GraphClass

/-!
# Uniform field transfer (main paper, Proposition 5.1, `prop:field-transfer`)

The library theorem `ZeroFreeness.LeeYang.graph_class_normalized_field_transfer`
chooses `θ` after the graph class `F`.  The paper's `θ = θ(q, Δ, C₀)`
depends only on `q`, `Δ` and the coupling-independence constant `C₀`.

We obtain the paper's quantifier order by applying the library theorem once
to the union of all induced-subgraph-closed classes satisfying `C₀`-coupling
independence at `x = 0`.  This union is again a `GraphClass` (closed under
induced pullbacks along embeddings) in the same universe, and it satisfies
the same `C₀` bound, so the resulting `θ` works for every such class.
-/

namespace ZeroFreeness.LeeYang

open PottsCI ZeroFreeness.Potts ZeroFreeness.LeeYang

noncomputable section

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u v

/-- The union of all graph classes (closed under induced subgraphs, up to
relabelling) that satisfy `cost`-coupling independence at `x = 0`. -/
def ciUnionClass (C : Type v) [Fintype C] (cost : ℝ) : GraphClass.{u} where
  contains {A} _ G := ∃ F : GraphClass.{u},
    GraphClassRootCouplingBound F C PinningData.hardParameter cost ∧ F.contains G
  comap_mem := by
    intro A B _ _ G e hG
    obtain ⟨F, hF, hGF⟩ := hG
    exact ⟨F, hF, F.comap_mem G e hGF⟩

/-- The union class satisfies the same coupling-independence bound. -/
theorem ciUnionClass_rootCouplingBound (C : Type v) [Fintype C] (cost : ℝ) :
    GraphClassRootCouplingBound (ciUnionClass.{u, v} C cost) C
      PinningData.hardParameter cost := by
  intro A _ G hG tau r a b ha hb
  obtain ⟨F, hF, hGF⟩ := hG
  exact hF G hGF tau r a b ha hb

/-- Every class with the bound is contained in the union class. -/
theorem mem_ciUnionClass {C : Type v} [Fintype C] {cost : ℝ} (F : GraphClass.{u})
    (hF : GraphClassRootCouplingBound F C PinningData.hardParameter cost)
    {A : Type u} [Fintype A] {G : SimpleGraph A} (hG : F.contains G) :
    (ciUnionClass.{u, v} C cost).contains G :=
  ⟨F, hF, hG⟩

/-- **Uniform field transfer.** For every colour type `C`, degree bound `Δ`
with `Δ + 1 ≤ |C|`, and constant `cost`, there is one `θ ∈ (0, 1/2]` such that
for *every* graph class `F` satisfying `cost`-coupling independence at `x = 0`,
every `G ∈ F` of maximum degree at most `Δ`, every pinning `tau` and every
field `ℓ` within `θ` of `1` at the free vertices (closed polydisc), the
normalized pinned field polynomial is nonzero. -/
theorem uniform_graph_class_normalized_field_transfer
    (C : Type v) [Fintype C] (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ F : GraphClass.{u},
        GraphClassRootCouplingBound F C PinningData.hardParameter cost →
        ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
          (∀ v, G.degree v ≤ Δ) →
          ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ),
            (∀ (u : tau.FreeVertex) (c : C), ‖ℓ u.val c - 1‖ ≤ θ) →
            normalizedFieldPartition tau G ℓ ≠ 0 := by
  have : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨θ, hθ, hθ1, h⟩ :=
    graph_class_normalized_field_transfer (ciUnionClass.{u, v} C cost) Δ hq cost
      (ciUnionClass_rootCouplingBound C cost)
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro F hF V _ G hG hd tau ℓ hℓ
  exact h G (mem_ciUnionClass F hF hG) hd tau ℓ hℓ

/-- Uniform version of `graph_class_field_transfer`: the same `θ` also
controls the unnormalized pinned field polynomial when the pinned field
factors are nonzero. -/
theorem uniform_graph_class_field_transfer
    (C : Type v) [Fintype C] (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ F : GraphClass.{u},
        GraphClassRootCouplingBound F C PinningData.hardParameter cost →
        ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
          (∀ v, G.degree v ≤ Δ) →
          ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ),
            (∀ (u : tau.FreeVertex) (c : C), ‖ℓ u.val c - 1‖ ≤ θ) →
            normalizedFieldPartition tau G ℓ ≠ 0 ∧
              ((∀ w : tau.domain, ℓ w.val (tau.colour w) ≠ 0) →
                (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G)) := by
  have : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨θ, hθ, hθ1, h⟩ :=
    graph_class_field_transfer (ciUnionClass.{u, v} C cost) Δ hq cost
      (ciUnionClass_rootCouplingBound C cost)
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro F hF V _ G hG hd tau ℓ hℓ
  exact h G (mem_ciUnionClass F hF hG) hd tau ℓ hℓ

/-- **Proposition 5.1 (field transfer), paper form.**
Fix integers `q, Δ` with `Δ ≥ 2` and `q ≥ Δ + 1`, let `C₀ ∈ [0, ∞)`.
There is `θ = θ(q, Δ, C₀) ∈ (0, 1/2]` such that for every class
`𝒢 ⊆ 𝒢_Δ` closed under taking induced subgraphs and satisfying
`C₀`-coupling independence at `x = 0`, every `G ∈ 𝒢` and every pinning
`τ`, `Z̃_G^τ(λ) ≠ 0` whenever `|λ_{u,c} - 1| < θ` for `u ∈ V^τ`, `c ∈ [q]`.

The colours are `Fin q`.  The hypotheses `Δ ≥ 2` and `C₀ ≥ 0` are stated
for fidelity to the paper; they are not needed. -/
theorem prop_field_transfer (q Δ : ℕ) (_hΔ : 2 ≤ Δ) (hq : Δ + 1 ≤ q)
    (C₀ : ℝ) (_hC₀ : 0 ≤ C₀) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      ∀ 𝒢 : GraphClass.{u},
        (∀ {V : Type u} [Fintype V] (G : SimpleGraph V), 𝒢.contains G →
          ∀ v, G.degree v ≤ Δ) →
        GraphClassRootCouplingBound 𝒢 (Fin q) PinningData.hardParameter C₀ →
        ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), 𝒢.contains G →
          ∀ (tau : PartialColouring V (Fin q)) (ℓ : V → Fin q → ℂ),
            (∀ (u : tau.FreeVertex) (c : Fin q), ‖ℓ u.val c - 1‖ < θ) →
            normalizedFieldPartition tau G ℓ ≠ 0 := by
  have hq' : Δ + 1 ≤ Fintype.card (Fin q) := by simpa using hq
  obtain ⟨θ, hθ, hθ1, h⟩ := uniform_graph_class_normalized_field_transfer.{u, 0}
    (Fin q) Δ hq' C₀
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro 𝒢 hdeg hCI V _ G hG tau ℓ hℓ
  exact h 𝒢 hCI G hG (hdeg G hG) tau ℓ (fun u c => (hℓ u c).le)

section Sanity

/-- The same decidable-equality instance as in `GraphClassInputs.lean`, so
that `RootBoundGraph` elaborates exactly like `GraphClassRootCouplingBound`.
It is local to this section and does not affect the main theorems. -/
local instance (priority := 3000) gapFieldDecEq (T : Type*) : DecidableEq T :=
  Classical.decEq T

/-- The `cost`-coupling-independence bound at `x = 0` for one graph: every
pinning, free root and pair of root colours. -/
def RootBoundGraph (C : Type v) [Fintype C] (cost : ℝ) {A : Type u} [Fintype A]
    (G : SimpleGraph A) : Prop :=
  ∀ (tau : PartialColouring A C) (r : tau.FreeVertex) (a b : C)
    (ha : 0 < (rootChildData tau G r a).partition PinningData.hardParameter)
    (hb : 0 < (rootChildData tau G r b).partition PinningData.hardParameter),
    PottsCI.FinDist.W PottsCI.ham
      ((rootChildData tau G r a).gibbs PinningData.hardParameter
        PinningData.hardParameter.property ha)
      ((rootChildData tau G r b).gibbs PinningData.hardParameter
        PinningData.hardParameter.property hb) ≤ cost

/-- Sanity check: the union class is exactly the class of all graphs every
induced subgraph (up to relabelling) of which satisfies the bound. -/
theorem mem_ciUnionClass_iff (C : Type v) [Fintype C] (cost : ℝ)
    {A : Type u} [Fintype A] (G : SimpleGraph A) :
    (ciUnionClass.{u, v} C cost).contains G ↔
      ∀ {B : Type u} [Fintype B] (e : B ↪ A), RootBoundGraph C cost (G.comap e) := by
  constructor
  · rintro ⟨F, hF, hGF⟩ B _ e tau r a b ha hb
    exact hF (G.comap e) (F.comap_mem G e hGF) tau r a b ha hb
  · intro h
    let U : GraphClass.{u} :=
      { contains := fun {A'} _ G' =>
          ∀ {B : Type u} [Fintype B] (e : B ↪ A'), RootBoundGraph C cost (G'.comap e)
        comap_mem := by
          intro A' B' _ _ G' e hG' B'' _ e'
          exact hG' (e'.trans e) }
    refine ⟨U, ?_, h⟩
    intro A' _ G' hG' tau r a b ha hb
    exact hG' (Function.Embedding.refl A') tau r a b ha hb

end Sanity

end

end ZeroFreeness.LeeYang
