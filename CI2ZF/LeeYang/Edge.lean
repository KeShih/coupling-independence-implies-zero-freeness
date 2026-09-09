import CI2ZF.LeeYang.GraphClass
import CI2ZF.Potts.Regions.Edge.ZeroFree

/-! The main-text edge-colouring Lee--Yang corollary at q ≥ 3Δ.
Independent fields are indexed by the actual edges and their colours. -/
namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts CI2ZF.Appendix.Edge
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) (A : Type*) : DecidableEq A := Classical.decEq A
universe u v

/-- A single field radius works for every finite graph, every edge
pinning (including improper pinnings), and every free edge-colour field.
The ordinary partition is nonzero exactly for proper pinnings when the
specified pinned field factors are nonzero. -/
theorem edge_lee_yang (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) →
        ∀ (tau : PartialColouring G.edgeSet C) (ℓ : G.edgeSet → C → ℂ),
        (∀ (e : tau.FreeVertex) c, ‖ℓ e.val c - 1‖ ≤ θ) →
        normalizedFieldPartition tau G.lineGraph ℓ ≠ 0 ∧
          ((∀ e : tau.domain, ℓ e.val (tau.colour e) ≠ 0) →
            (fullFieldPartition tau G.lineGraph ℓ ≠ 0 ↔ ProperPinning tau G.lineGraph)) := by
  have hd1 : 1 ≤ Δ := (by decide : 1 ≤ 2).trans hΔ
  have hqL : 2 * Δ - 2 + 1 ≤ Fintype.card C :=
    (Nat.le_succ _).trans (lineGraph_colours_slack hd1 hq)
  obtain ⟨θ, hθ, hθ1, h⟩ := graph_class_field_transfer (edgeGraphClass.{u} Δ)
    (2 * Δ - 2) hqL ((Δ : ℝ) - 1)
    (edgeGraphClass_rootCoupling C hd1 hq PinningData.hardParameter (by norm_num))
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro V _ G hd tau ℓ hℓ
  have hm := lineGraph_mem_edgeGraphClass G hd
  exact h G.lineGraph hm (edgeGraphClass_degree _ hm) tau ℓ hℓ

/-- The closed polydisc version also includes all pinned coordinates. -/
theorem edge_lee_yang_all_fields (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : 3 * Δ ≤ Fintype.card C) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) →
        ∀ (tau : PartialColouring G.edgeSet C) (ℓ : G.edgeSet → C → ℂ),
        (∀ e c, ‖ℓ e c - 1‖ ≤ θ) →
        normalizedFieldPartition tau G.lineGraph ℓ ≠ 0 ∧
          (fullFieldPartition tau G.lineGraph ℓ ≠ 0 ↔ ProperPinning tau G.lineGraph) := by
  obtain ⟨θ, hθ, hθ1, h⟩ := edge_lee_yang C hΔ hq
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro V _ G hd tau ℓ hℓ
  obtain ⟨hn, hf⟩ := h G hd tau ℓ (fun e c => hℓ e.val c)
  exact ⟨hn, hf (fun e => field_ne_zero_of_close (hθ1.trans_lt (by norm_num)) hℓ _ _)⟩

end
end CI2ZF.LeeYang
