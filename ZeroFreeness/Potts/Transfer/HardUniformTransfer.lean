import ZeroFreeness.Potts.Transfer.HardBFSResponseStep
import ZeroFreeness.Potts.Transfer.InductionComponentSteps
import ZeroFreeness.Potts.Transfer.InductionParentSteps
import ZeroFreeness.Potts.Transfer.UniformInduction
import ZeroFreeness.Potts.Transfer.TransferCouplingInputs

/-! The hard-endpoint uniform induction, with actual defective-term
control and no assumed complex nonvanishing or response estimate. -/
namespace ZeroFreeness.Potts
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

/-- A genuine hard CI bound implies a disk of graph-independent radius
about zero, simultaneously with the normalized root-response bound. -/
theorem hard_uniform_transfer (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : RootCouplingBound.{u, v} C Δ hq PinningData.hardParameter cost) :
    ∃ r > 0, ∃ alpha > 0,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C),
        I.DegreeBound Δ → PartitionNonzeroOn I 0 r) ∧
      ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
        I.DegreeBound Δ → OptionRootResponses I 0 r alpha := by
  obtain ⟨L, B, hL, hcost, hB, alpha, ha, ha1, haB⟩ :=
    exists_geometric_transfer_scales Δ cost
  obtain ⟨eps, heps, hcontrols⟩ := exists_hard_local_controls.{u, v} C Δ B hq ha
  obtain ⟨r, hr, hre, hr1, hdefect, hparent⟩ :=
    exists_hard_transfer_radius (Fintype.card C) Δ B ha heps
  have hlocal := hcontrols r hr hre
  refine ⟨r, hr, alpha, ha, ?_⟩
  apply uniform_induction.{u, v} C Δ 0 r alpha
  · intro O _ I hd hNZ hRoot
    by_cases hsmall : Fintype.card (Component.RootComponent I.graph none) ≤ B
    · exact hard_small_component_response_step hlocal ha.le I hd hsmall hNZ
    · intro a b
      apply OptionBFS.hard_bfs_response_step I a b hd hq hL hB
        (Nat.lt_of_not_ge hsmall) hr hr1 ha.le ha1 haB hcost
      · exact hCI I hd a b
      · exact hNZ
      · exact hRoot
      · exact hdefect
  · intro O _ I hd hchildren hresponses
    exact hard_parent_step hq (by linarith) hr1 hparent.le I hd hchildren hresponses

end
end ZeroFreeness.Potts
