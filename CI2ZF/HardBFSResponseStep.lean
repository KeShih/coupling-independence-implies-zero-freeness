import CI2ZF.OptionBFSMarginals
import CI2ZF.OptionBFSResponseGeometry
import CI2ZF.TransferScales

/-! The hard-endpoint large-component response step. The chosen separator
is an actual BFS shell, its exterior logarithms come from strictly smaller
instances, and the defective terms are controlled by the uniform budget. -/
namespace CI2ZF.Potts.OptionBFS
open PottsCI PottsCI.FinDist Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] optionBFSMarginalInsideEq optionBFSMarginalShellEq
  optionBFSMarginalOutsideEq optionBFSMarginalInsideFintype optionBFSMarginalOutsideFintype
universe u v
variable {O : Type u} {C : Type v} [Fintype O] [Fintype C] [Nonempty C]

private theorem ham_update_le_one {V D : Type*} [Fintype V] [DecidableEq V] [DecidableEq D]
    (σ : V → D) (u : V) (c : D) : ham (Function.update σ u c) σ ≤ 1 := by
  have hc : (Finset.univ.filter fun w => Function.update σ u c w ≠ σ w).card ≤ 1 := by
    calc
      _ ≤ ({u} : Finset V).card := Finset.card_le_card (by
        intro w hw
        by_contra hwu
        have hn : w ≠ u := by simpa only [Finset.mem_singleton] using hwu
        exact (Finset.mem_filter.mp hw).2 (Function.update_of_ne hn _ _))
      _ = 1 := Finset.card_singleton u
  unfold ham hamCard
  exact_mod_cast hc

/-- A genuine hard one-root response bound for the large-component
branch. The hypotheses contain only smaller-instance induction statements,
an actual Gibbs transportation bound, and graph-independent scalar budgets.
The colour assumption is exactly `Δ + 1 ≤ q`. -/
theorem hard_bfs_response_step
    (I : PinningData (Option O) C) (a b : C) {Δ L B : ℕ}
    (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (hL : 0 < L)
    (hB : (∑ j ∈ Finset.range (L + 2), Δ ^ j) ≤ B)
    (hlarge : B < Fintype.card (RootComponent I.graph))
    {r alpha cost : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ (1 / 16 : ℝ))
    (haB : alpha * B ≤ (1 / 16 : ℝ)) (hcost : 64 * cost ≤ (L : ℝ))
    (hCI : W ham
      ((optionChildData I a).gibbs 0 le_rfl
        (partition_zero_pos_of_succ_le _ (optionChildData_degreeBound I hd a) hq))
      ((optionChildData I b).gibbs 0 le_rfl
        (partition_zero_pos_of_succ_le _ (optionChildData_degreeBound I hd b) hq)) ≤ cost)
    (hNZ : SmallerPartitionsNonzero.{u, v} C Δ (Fintype.card (Option O)) 0 r)
    (hRoot : SmallerRootResponses.{u, v} C Δ (Fintype.card (Option O)) 0 r alpha)
    (hsmall : (3 / 2 : ℝ) * hardErrorCoefficient (Fintype.card C) Δ B B alpha * r ≤ alpha / 8) :
    HasSmallResponseLog (pinningProductPartition (optionChildData I a))
      (pinningProductPartition (optionChildData I b)) 0 r alpha := by
  obtain ⟨k, hk, hkL, hW⟩ := exists_low_childGibbsShellLaw_of_ci I a b 0 le_rfl _ _ hL hCI
  have hB' : (∑ j ∈ Finset.range (L + 1), Δ ^ j) ≤ B := by
    apply le_trans _ hB
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have hs := shell_nonempty_of_component_card_gt_bound I Δ L B hd hB' hlarge k hkL
  have hcard := inside_shell_card_le_bound I hd hB k hkL
  have hU : Fintype.card (Inside I.graph k) ≤ B := by omega
  have hS : Fintype.card (BFS.Shell I.graph none k) ≤ B := by omega
  obtain ⟨h, hh0, hhD, hhE, hhLip⟩ := childSplit_exterior_response_logs I a hd k hk hs hr hNZ hRoot
  have hcommon (ξ : BFS.Shell I.graph none k → C) :
      exteriorData (childSplit I a k) ξ = exteriorData (childSplit I b k) ξ := by
    rw [childSplit_exterior_eq_parent, childSplit_exterior_eq_parent]
  obtain ⟨_, H, hH0, hHD, hHE, hHB⟩ := exists_hard_separator_quotient_log
    (childSplit I a k) (childSplit I b k) (childSplit_separates I a k) (childSplit_separates I b k)
    hcommon (childSplit_degreeBound I a k hd) (childSplit_degreeBound I b k hd) hq hU hS
    hr hr1 ha (show alpha / 8 ∈ Set.Icc 0 (1 / 2 : ℝ) by constructor <;> linarith)
    (haB.trans (by norm_num)) hsmall h hhD hh0 (fun z hz ξ => hhE ξ z hz)
    (fun z hz ξ s c => (hhLip z hz (Function.update ξ s c) ξ).trans (by
      exact (mul_le_mul_of_nonneg_left (ham_update_le_one ξ s c) ha).trans_eq (mul_one alpha)))
  refine ⟨H, hH0, hHD, ?_, ?_⟩
  · intro z hz
    simpa only [childSplit_partition] using hHE z hz
  · intro z hz
    apply (hHB z hz).trans
    apply hard_shell_budget_closes hL hcost ha _ (le_refl _)
    exact hW

end
end CI2ZF.Potts.OptionBFS
