import CI2ZF.PinningFamily
import CI2ZF.TransferCouplingInputs

/-! Coupling hypotheses restricted to the actual admissible family.
These definitions never require a coupling bound on unrelated graphs. -/
namespace CI2ZF.Potts.PinningFamily
open PottsCI PottsCI.FinDist
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

def RootCouplingBound (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (cost : ℝ) : Prop :=
  ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C), F.contains I →
    ∀ (hd : I.DegreeBound Δ) (a b : C),
    W ham
      ((optionChildData I a).gibbs x x.property
        (partition_pos_of_succ_le _ x.property (optionChildData_degreeBound I hd a) hq))
      ((optionChildData I b).gibbs x x.property
        (partition_pos_of_succ_le _ x.property (optionChildData_degreeBound I hd b) hq)) ≤ cost

structure TransferCouplingInputs (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) : Prop where
  hard : ∃ cost : ℝ, F.RootCouplingBound Δ hq PinningData.hardParameter cost
  positive : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ cost : ℝ,
    ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ∈ Set.Icc δ 1 →
      F.RootCouplingBound Δ hq x cost

/-- Restricting an already uniform CI theorem to a family preserves its
constant. The general family transfer will not require this stronger input. -/
theorem rootCouplingBound_of_all (F : PinningFamily.{u, v} C)
    {Δ : ℕ} {hq : Δ + 1 ≤ Fintype.card C}
    {x : PinningData.NonnegativeParameter} {cost : ℝ}
    (h : Potts.RootCouplingBound.{u, v} C Δ hq x cost) :
    F.RootCouplingBound Δ hq x cost := by
  intro O _ I _ hd a b
  exact h I hd a b

theorem transferCouplingInputs_of_all (F : PinningFamily.{u, v} C)
    {Δ : ℕ} {hq : Δ + 1 ≤ Fintype.card C}
    (h : Potts.TransferCouplingInputs.{u, v} C Δ hq) : F.TransferCouplingInputs Δ hq := by
  constructor
  · obtain ⟨cost, hc⟩ := h.hard
    exact ⟨cost, F.rootCouplingBound_of_all (hq := hq) hc⟩
  · intro δ hδ hδ1
    obtain ⟨cost, hc⟩ := h.positive δ hδ hδ1
    refine ⟨cost, ?_⟩
    intro x hx O _ I hI hd a b
    exact hc x hx I hd a b

end
end CI2ZF.Potts.PinningFamily
