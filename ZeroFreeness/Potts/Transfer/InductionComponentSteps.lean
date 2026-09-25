import ZeroFreeness.Potts.Transfer.TransferLocalControls

/-! Closing the small-root-component branch from the actual strictly
smaller common remainder, in the simultaneous induction language. -/
namespace ZeroFreeness.Potts
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem positive_small_component_response_step {O : Type u} {C : Type v}
    [Fintype O] [Fintype C] {Δ B : ℕ} {K : Set ℂ} {x : ℂ} {r alpha : ℝ}
    (hlocal : PositiveLocalControls.{u, v} C Δ B K r alpha)
    (ha : 0 ≤ alpha) (hx : x ∈ K) (I : PinningData (Option O) C)
    (hd : I.DegreeBound Δ) (hB : Fintype.card (Component.RootComponent I.graph none) ≤ B)
    (hNZ : SmallerPartitionsNonzero.{u, v} C Δ (Fintype.card (Option O)) x r) :
    OptionRootResponses I x r alpha := by
  have hE : PartitionNonzeroOn (Component.optionCommonRemainderData I) x r :=
    hNZ _ (Component.optionCommonRemainderData_degreeBound I hd)
      (Component.optionCommonRemainder_card_lt_parent I)
  intro a b
  exact HasSmallResponseLog.mono_bound (hlocal.component I hd hB x hx hE a b) (by linarith)

theorem hard_small_component_response_step {O : Type u} {C : Type v}
    [Fintype O] [Fintype C] {Δ B : ℕ} {r alpha : ℝ}
    (hlocal : HardLocalControls.{u, v} C Δ B r alpha)
    (ha : 0 ≤ alpha) (I : PinningData (Option O) C)
    (hd : I.DegreeBound Δ) (hB : Fintype.card (Component.RootComponent I.graph none) ≤ B)
    (hNZ : SmallerPartitionsNonzero.{u, v} C Δ (Fintype.card (Option O)) 0 r) :
    OptionRootResponses I 0 r alpha := by
  have hE : PartitionNonzeroOn (Component.optionCommonRemainderData I) 0 r :=
    hNZ _ (Component.optionCommonRemainderData_degreeBound I hd)
      (Component.optionCommonRemainder_card_lt_parent I)
  intro a b
  exact HasSmallResponseLog.mono_bound (hlocal.component I hd hB hE a b) (by linarith)

end
end ZeroFreeness.Potts
