import CI2ZF.Holant.Theorem
import CI2ZF.Holant.Applications

/-! Public orthant, diagonal, matching and edge-cover conclusions. All
analytic input parameters of the reusable application lemmas are discharged
by the proved uniform Holant theorem. -/
namespace CI2ZF.Holant
open Set
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

theorem holant_uniform_tubes (F : Finset Signature) (Δ : ℕ) :
    UniformGraphTubes.{u} Δ F := by
  intro R hR
  obtain ⟨ε, hε, h⟩ := exists_uniform_holant_polytube.{u} F Δ hR.le
  exact ⟨ε, hε, fun V _ _ G hΔ f harity hf z hz => h V G hΔ f hf harity z hz⟩

/-- One width function for all graphs and all signature assignments. -/
def holantWidth (F : Finset Signature) (Δ : ℕ) : ℝ → ℝ :=
  tubeWidth (holant_uniform_tubes.{u} F Δ)

theorem holantWidth_pos (F : Finset Signature) (Δ : ℕ) (R : ℝ) :
    0 < holantWidth.{u} F Δ R := tubeWidth_pos _ R

/-- The full orthant statement of the main-text Holant theorem. -/
theorem holant_orthant (F : Finset Signature) (Δ : ℕ)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (f : V → Signature)
    (harity : ∀ v, (f v).arity = G.degree v) (hf : ∀ v, f v ∈ F) :
    IsOpen (edgeOrthantNeighborhood G.edgeFinset (holantWidth.{u} F Δ)) ∧
      (∀ x : Sym2 V → ℝ, (∀ e ∈ G.edgeFinset, 0 ≤ x e) →
        (fun e => (x e : ℂ)) ∈ edgeOrthantNeighborhood G.edgeFinset (holantWidth.{u} F Δ)) ∧
      ∀ z ∈ edgeOrthantNeighborhood G.edgeFinset (holantWidth.{u} F Δ),
        graphPartition G (complexValues f) z ≠ 0 :=
  graphPartition_orthant (holant_uniform_tubes F Δ) G hΔ f harity hf

/-- The scalar domain is chosen before all graphs, vertex types and signatures. -/
theorem holant_uniform_diagonal (F : Finset Signature) (Δ : ℕ) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, 0 ≤ x → (x : ℂ) ∈ U) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ f : V → Signature,
          (∀ v, (f v).arity = G.degree v) → (∀ v, f v ∈ F) →
          ∀ z ∈ U, graphPartition G (complexValues f) (fun _ => z) ≠ 0 :=
  graphPartition_uniform_diagonal (holant_uniform_tubes F Δ)

/-- Main-text b-matching corollary, with no remaining analytic hypothesis. -/
theorem bmatching_uniform_polytube (Δ : ℕ) {R : ℝ} (hR : 0 < R) :
    ∃ ε > 0, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
        ∀ z ∈ edgePolytube G.edgeFinset ε 0 R,
          matchingPartition graphIncidence G.edgeFinset b z ≠ 0 :=
  matching_uniform_polytube (holant_uniform_tubes (capacityFamily Δ) Δ) hR

theorem bmatching_orthant (Δ : ℕ)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v) :
    IsOpen (edgeOrthantNeighborhood G.edgeFinset (holantWidth.{u} (capacityFamily Δ) Δ)) ∧
      (∀ x : Sym2 V → ℝ, (∀ e ∈ G.edgeFinset, 0 ≤ x e) →
        (fun e => (x e : ℂ)) ∈
          edgeOrthantNeighborhood G.edgeFinset (holantWidth.{u} (capacityFamily Δ) Δ)) ∧
      ∀ z ∈ edgeOrthantNeighborhood G.edgeFinset (holantWidth.{u} (capacityFamily Δ) Δ),
        matchingPartition graphIncidence G.edgeFinset b z ≠ 0 :=
  matching_orthant (holant_uniform_tubes (capacityFamily Δ) Δ) G hΔ b hb

theorem bmatching_uniform_diagonal (Δ : ℕ) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, 0 ≤ x → (x : ℂ) ∈ U) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          ∀ z ∈ U, matchingPartition graphIncidence G.edgeFinset b (fun _ => z) ≠ 0 :=
  matching_uniform_diagonal (holant_uniform_tubes (capacityFamily Δ) Δ)

/-- b-edge-cover corollary in the order `∀ a c, ∃ ε` (`cor_bcover_short` gives
the main-text order), obtained through the proved exact
complement identity and a uniform reciprocal-neighborhood estimate. -/
theorem bcover_uniform_polytube (Δ : ℕ) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    ∃ ε > 0, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
        ∀ z ∈ edgePolytube G.edgeFinset ε a c,
          coverPartition graphIncidence G.edgeFinset b z ≠ 0 :=
  cover_uniform_polytube (holant_uniform_tubes (capacityFamily Δ) Δ) ha hac

def bcoverWidth (Δ : ℕ) : ℝ → ℝ → ℝ :=
  coverTubeWidth (holant_uniform_tubes.{u} (capacityFamily Δ) Δ)

theorem bcover_orthant (Δ : ℕ)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v) :
    IsOpen (edgePositiveOrthantNeighborhood G.edgeFinset (bcoverWidth.{u} Δ)) ∧
      (∀ x : Sym2 V → ℝ, (∀ e ∈ G.edgeFinset, 0 < x e) →
        (fun e => (x e : ℂ)) ∈
          edgePositiveOrthantNeighborhood G.edgeFinset (bcoverWidth.{u} Δ)) ∧
      ∀ z ∈ edgePositiveOrthantNeighborhood G.edgeFinset (bcoverWidth.{u} Δ),
        coverPartition graphIncidence G.edgeFinset b z ≠ 0 :=
  cover_orthant (holant_uniform_tubes (capacityFamily Δ) Δ) G hΔ b hb

theorem bcover_uniform_diagonal (Δ : ℕ) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, 0 < x → (x : ℂ) ∈ U) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          ∀ z ∈ U, coverPartition graphIncidence G.edgeFinset b (fun _ => z) ≠ 0 :=
  cover_uniform_diagonal (holant_uniform_tubes (capacityFamily Δ) Δ)

end
end CI2ZF.Holant
