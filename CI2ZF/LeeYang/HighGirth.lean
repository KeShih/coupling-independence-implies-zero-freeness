import CI2ZF.LeeYang.GraphClass
import CI2ZF.Potts.Regions.Girth.High.Theorem

/-! The q ≥ Δ+3 Lee–Yang regime follows from the proved large-girth
coupling theorem. The stronger residual-girth statement allows short
cycles entirely outside the free residual graph. -/
namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts CI2ZF.Appendix CI2ZF.Appendix.Girth
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

theorem high_girth_field_transfer
    (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ g : ℕ, 3 ≤ g ∧ ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (I : PinningData V C),
        (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ → ∀ ℓ : V → C → ℂ,
        (∀ v c, ‖ℓ v c - 1‖ ≤ θ) → fieldPartition I ℓ ≠ 0 := by
  obtain ⟨g, K, hg, _, hcouple⟩ := high_girth_coupling transfer Δ hΔ hq
  obtain ⟨θ, hθ, hθ1, hn⟩ := uniform_field_transfer_closed
    (largeGirthFamily.{u,v} C g) Δ (by omega) K
    (hcouple PinningData.hardParameter (by norm_num [PinningData.hardParameter]))
  exact ⟨g, hg, θ, hθ, hθ1, hn⟩

theorem high_girth_residual_original_field_transfer
    (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ g : ℕ, 3 ≤ g ∧ ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ (tau : PartialColouring V C),
        (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth → ∀ ℓ : V → C → ℂ,
        (∀ (v : tau.FreeVertex) c, ‖ℓ v.val c - 1‖ ≤ θ) →
        normalizedFieldPartition tau G ℓ ≠ 0 ∧
          ((∀ v : tau.domain, ℓ v.val (tau.colour v) ≠ 0) →
            (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G)) := by
  obtain ⟨g, hg, θ, hθ, hθ1, hn⟩ := high_girth_field_transfer transfer Δ hΔ hq
  refine ⟨g, hg, θ, hθ, hθ1, ?_⟩
  intro V _ G hd tau hfree ℓ hℓ
  have hnorm : normalizedFieldPartition tau G ℓ ≠ 0 := by
    rw [normalizedFieldPartition_eq]
    exact hn _ hfree (tau.degreeBound_of_original G hd) (fun v => ℓ v.val) hℓ
  exact ⟨hnorm, fun hp => fullFieldPartition_ne_zero_iff_proper tau G ℓ hp hnorm⟩

/-- This is the original-graph form of the third vertex-colour regime,
with the paper's free-coordinate field condition and proper-pinning clause. -/
theorem high_girth_original_field_transfer
    (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ g : ℕ, 3 ≤ g ∧ ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        (g : ℕ∞) ≤ G.egirth → (∀ v, G.degree v ≤ Δ) →
        ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ),
        (∀ (v : tau.FreeVertex) c, ‖ℓ v.val c - 1‖ < θ) →
        normalizedFieldPartition tau G ℓ ≠ 0 ∧
          ((∀ v : tau.domain, ℓ v.val (tau.colour v) ≠ 0) →
            (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G)) := by
  obtain ⟨g, hg, θ, hθ, hθ1, hn⟩ :=
    high_girth_residual_original_field_transfer transfer Δ hΔ hq
  refine ⟨g, hg, θ, hθ, hθ1, ?_⟩
  intro V _ G hG hd tau ℓ hℓ
  have hfree : (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth :=
    hG.trans (SimpleGraph.Embedding.comap
      (⟨Subtype.val, Subtype.val_injective⟩ : tau.FreeVertex ↪ V) G).isContained.egirth_le
  exact hn G hd tau hfree ℓ (fun v c => (hℓ v c).le)

end
end CI2ZF.LeeYang
