import CI2ZF.OptionCI

/-! The exact real coupling inputs to the Potts transfer. The hard input
at the critical line is intentionally an explicit theorem parameter.
Its external source is Chen--Feng--Guo--Zhang--Zou, arXiv:2410.23225v2,
Theorem 20 (second regime), with the conditional-list convention in its
proof. No external result is installed as a Lean axiom. -/
namespace CI2ZF.Potts
open PottsCI PottsCI.FinDist
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

/-- Genuine normalized child laws, using only the transfer theorem's
colour threshold `q ≥ Δ + 1`. -/
def RootCouplingBound (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (cost : ℝ) : Prop :=
  ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C)
    (hd : I.DegreeBound Δ) (a b : C),
    W ham
      ((optionChildData I a).gibbs x x.property
        (partition_pos_of_succ_le _ x.property (optionChildData_degreeBound I hd a) hq))
      ((optionChildData I b).gibbs x x.property
        (partition_pos_of_succ_le _ x.property (optionChildData_degreeBound I hd b) hq)) ≤ cost

/-- The two real hypotheses of the transfer, with constants preceding
the graph instance and pinning. -/
structure TransferCouplingInputs (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) : Prop where
  hard : ∃ cost : ℝ, RootCouplingBound.{u, v} C Δ hq PinningData.hardParameter cost
  positive : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ cost : ℝ,
    ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ∈ Set.Icc δ 1 →
      RootCouplingBound.{u, v} C Δ hq x cost

/-- This is precisely the normalized root-deleted hard CI statement
used from the external colouring theorem; it asserts no zero-freeness. -/
def CriticalHardColouringInput (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) : Prop :=
  ∃ cost : ℝ, RootCouplingBound.{u, v} C Δ hq PinningData.hardParameter cost

/-- Above the Vigoda line both transfer inputs are fully proved by the
actual coupled kernels, including the hard endpoint. -/
theorem strict_transfer_coupling_inputs (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (11 / 6 : ℝ) * Δ < Fintype.card C)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    TransferCouplingInputs.{u, v} C Δ hcolours := by
  have hb (x : PinningData.NonnegativeParameter) (hx : (x : ℝ) ≤ 1) :
      RootCouplingBound.{u, v} C Δ hcolours x (2 / ciGap (Fintype.card C) Δ) := by
    intro O _ I hd a b
    exact option_root_strict_uniform_ci I hΔ hd hq a b x hx
  constructor
  · exact ⟨_, hb PinningData.hardParameter (by norm_num [PinningData.hardParameter])⟩
  · intro δ _ _
    exact ⟨_, fun x hx => hb x hx.2⟩

/-- At equality the positive-temperature input is proved here. The
only external hypothesis is the separately named hard colouring input. -/
theorem critical_transfer_coupling_inputs (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C)
    (hardInput : CriticalHardColouringInput.{u, v} C Δ hcolours) :
    TransferCouplingInputs.{u, v} C Δ hcolours := by
  constructor
  · exact hardInput
  · intro δ hδ _
    refine ⟨12 / (11 * δ), ?_⟩
    intro x hx O _ I hd a b
    exact option_root_critical_uniform_ci I hΔ hd hq a b hδ x hx

end
end CI2ZF.Potts
