import CI2ZF.LeeYang.VertexCoupling
import CI2ZF.LeeYang.GraphClass

/-! The two ordinary-graph vertex-colour Lee--Yang regions, uniformly in
graph size and arbitrary pinning. Fields at pinned vertices need only be
nonzero when the full, rather than normalized, partition is requested. -/

namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts CI2ZF.Appendix
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

def UniformVertexFieldZeroFree (C : Type v) [Fintype C] (Δ : ℕ) (θ : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    (∀ v, G.degree v ≤ Δ) → ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ),
    (∀ (v : tau.FreeVertex) c, ‖ℓ v.val c - 1‖ ≤ θ) →
    normalizedFieldPartition tau G ℓ ≠ 0 ∧
      ((∀ v : tau.domain, ℓ v.val (tau.colour v) ≠ 0) →
        (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G))

variable (C : Type v) [Fintype C] [Nonempty C]

theorem all_vertex_field_transfer (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C)
    (cost : ℝ) (hCI : RootCouplingBound.{u,v} C Δ hq PinningData.hardParameter cost) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧ UniformVertexFieldZeroFree.{u,v} C Δ θ := by
  obtain ⟨θ, hθ, hθ1, h⟩ := uniform_field_transfer_closed (allPinningFamily.{u,v} C)
    Δ hq cost ((allPinningFamily C).rootCouplingBound_of_all (hq := hq) hCI)
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro V _ G hd tau ℓ hℓ
  have hn : normalizedFieldPartition tau G ℓ ≠ 0 := by
    rw [normalizedFieldPartition_eq]
    exact h (tau.toPinningData G) trivial (tau.degreeBound_of_original G hd)
      (fun v => ℓ v.val) hℓ
  exact ⟨hn, fun hp => fullFieldPartition_ne_zero_iff_proper tau G ℓ hp hn⟩

/-- Regime (ii), with no external literature hypothesis. -/
theorem cv_vertex_field_zero_free {Δ : ℕ} (hΔ : 125 ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧ UniformVertexFieldZeroFree.{u,v} C Δ θ := by
  have hcolours : Δ + 1 ≤ Fintype.card C := colours_succ_of_cv (by omega) hq
  obtain ⟨cost, hCI⟩ := cv_hard_coupling.{u,v} C hΔ hq hcolours
  exact all_vertex_field_transfer C Δ hcolours cost hCI

/-- Regime (i), retaining CFFGZZ Theorem 20 only at the at most twenty
critical integer pairs left by the proved near-Vigoda reduction. -/
theorem near_vigoda_vertex_field_zero_free {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C)
    (critical : ∀ j : ℕ, 1 ≤ j → j ≤ 20 → Δ = 6 * j → Fintype.card C = 11 * j →
      ExternalCriticalHardColouringTheorem.{u,v} C Δ) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧ UniformVertexFieldZeroFree.{u,v} C Δ θ := by
  have hcolours := colours_succ_of_nearVigoda hΔ hq
  obtain ⟨cost, hCI⟩ := near_vigoda_hard_coupling C hΔ hq hcolours critical
  exact all_vertex_field_transfer C Δ hcolours cost hCI

omit [Nonempty C] in
theorem UniformVertexFieldZeroFree.all_fields {Δ : ℕ} {θ : ℝ}
    (h : UniformVertexFieldZeroFree.{u,v} C Δ θ) (hθ : θ ≤ (1 / 2 : ℝ))
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hd : ∀ v, G.degree v ≤ Δ)
    (tau : PartialColouring V C) (ℓ : V → C → ℂ)
    (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ θ) :
    normalizedFieldPartition tau G ℓ ≠ 0 ∧
      (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G) := by
  obtain ⟨hn, hf⟩ := h G hd tau ℓ (fun v c => hℓ v.val c)
  exact ⟨hn, hf (fun v => field_ne_zero_of_close (hθ.trans_lt (by norm_num)) hℓ _ _)⟩

end
end CI2ZF.LeeYang
