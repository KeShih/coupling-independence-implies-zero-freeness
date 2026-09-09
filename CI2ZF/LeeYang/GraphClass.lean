import CI2ZF.LeeYang.Transfer
import CI2ZF.LeeYang.Polydisc
import CI2ZF.LeeYang.Pinning
import CI2ZF.GraphClassCoupling

/-! Uniform coupling independence implies a field polydisc for every
actual member of the restriction-closed family. The public original-graph
statement only restricts fields at free vertices. -/
namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

theorem fullFieldPartition_ne_zero_iff_proper {V : Type u} [Fintype V]
    (tau : PartialColouring V C) (G : SimpleGraph V) (ℓ : V → C → ℂ)
    (hpin : ∀ v : tau.domain, ℓ v.val (tau.colour v) ≠ 0)
    (hn : normalizedFieldPartition tau G ℓ ≠ 0) :
    fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G := by
  constructor
  · intro h
    by_contra hp
    exact h (fullFieldPartition_of_improper tau G ℓ hp)
  · intro hp
    exact fullFieldPartition_ne_zero_of_proper tau G ℓ hp hpin hn

theorem uniform_field_transfer_closed (F : PinningFamily.{u, v} C) (Δ : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : F.RootCouplingBound Δ hq PinningData.hardParameter cost) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
        I.DegreeBound Δ → ∀ ℓ : V → C → ℂ,
        (∀ v c, ‖ℓ v c - 1‖ ≤ θ) → fieldPartition I ℓ ≠ 0 := by
  obtain ⟨r, hr, hnz⟩ := uniform_curve_transfer F Δ hq cost hCI
  let θ : ℝ := min (r / 2) (1 / 2)
  have hθ : 0 < θ := lt_min (by positivity) (by norm_num)
  have hθr : θ < r := (min_le_left _ _).trans_lt (by linarith)
  refine ⟨θ, hθ, min_le_right _ _, ?_⟩
  intro V _ I hI hd ℓ hℓ
  exact fieldPartition_ne_zero_of_all_curves I hθ hθr (hnz I hI hd) ℓ hℓ

theorem uniform_field_transfer (F : PinningFamily.{u, v} C) (Δ : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : F.RootCouplingBound Δ hq PinningData.hardParameter cost) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
        I.DegreeBound Δ → ∀ ℓ : V → C → ℂ,
        (∀ v c, ‖ℓ v c - 1‖ < θ) → fieldPartition I ℓ ≠ 0 := by
  obtain ⟨θ, hθ, hθ1, h⟩ := uniform_field_transfer_closed F Δ hq cost hCI
  exact ⟨θ, hθ, hθ1, fun I hI hd ℓ hℓ => h I hI hd ℓ (fun v c => (hℓ v c).le)⟩

theorem graph_class_normalized_field_transfer (F : GraphClass.{u}) (Δ : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : GraphClassRootCouplingBound F C PinningData.hardParameter cost) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
        (∀ v, G.degree v ≤ Δ) → ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ),
        (∀ (v : tau.FreeVertex) c, ‖ℓ v.val c - 1‖ ≤ θ) →
        normalizedFieldPartition tau G ℓ ≠ 0 := by
  obtain ⟨θ, hθ, hθ1, h⟩ :=
    uniform_field_transfer_closed (F.pinningFamily C) Δ hq cost (hCI.to_pinningFamily hq)
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro V _ G hG hd tau ℓ hℓ
  rw [normalizedFieldPartition_eq]
  exact h (tau.toPinningData G) (F.original_pinning_mem C G hG tau)
    (tau.degreeBound_of_original G hd) (fun v => ℓ v.val) hℓ

/-- Pinned field factors need only be nonzero. No closeness condition is
imposed on pinned vertices in this original-graph statement. -/
theorem graph_class_field_transfer (F : GraphClass.{u}) (Δ : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : GraphClassRootCouplingBound F C PinningData.hardParameter cost) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
        (∀ v, G.degree v ≤ Δ) → ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ),
        (∀ (v : tau.FreeVertex) c, ‖ℓ v.val c - 1‖ ≤ θ) →
        normalizedFieldPartition tau G ℓ ≠ 0 ∧
          ((∀ v : tau.domain, ℓ v.val (tau.colour v) ≠ 0) →
            (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G)) := by
  obtain ⟨θ, hθ, hθ1, h⟩ := graph_class_normalized_field_transfer F Δ hq cost hCI
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro V _ G hG hd tau ℓ hℓ
  have hn := h G hG hd tau ℓ hℓ
  exact ⟨hn, fun hp => fullFieldPartition_ne_zero_iff_proper tau G ℓ hp hn⟩

theorem graph_class_all_fields_transfer (F : GraphClass.{u}) (Δ : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : GraphClassRootCouplingBound F C PinningData.hardParameter cost) :
    ∃ θ > 0, θ ≤ (1 / 2 : ℝ) ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
        (∀ v, G.degree v ≤ Δ) → ∀ (tau : PartialColouring V C) (ℓ : V → C → ℂ),
        (∀ v c, ‖ℓ v c - 1‖ ≤ θ) → normalizedFieldPartition tau G ℓ ≠ 0 ∧
          (fullFieldPartition tau G ℓ ≠ 0 ↔ ProperPinning tau G) := by
  obtain ⟨θ, hθ, hθ1, h⟩ := graph_class_field_transfer F Δ hq cost hCI
  refine ⟨θ, hθ, hθ1, ?_⟩
  intro V _ G hG hd tau ℓ hℓ
  obtain ⟨hn, hf⟩ := h G hG hd tau ℓ (fun v c => hℓ v.val c)
  exact ⟨hn, hf (fun v => field_ne_zero_of_close (hθ1.trans_lt (by norm_num)) hℓ _ _)⟩

end
end CI2ZF.LeeYang
