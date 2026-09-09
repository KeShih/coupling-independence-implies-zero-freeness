import CI2ZF.LeeYang.Exterior
import CI2ZF.LeeYang.SeparatorLog
import CI2ZF.Potts.Transfer.FamilyCouplingInputs

/-! The low-Wasserstein BFS shell closes the large-component field
response step using the actual hard-colouring shell marginals. -/
namespace CI2ZF.LeeYang
open PottsCI PottsCI.FinDist CI2ZF.Potts CI2ZF.Potts.Separator CI2ZF.Potts.OptionBFS
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] optionBFSMarginalInsideEq optionBFSMarginalShellEq
  optionBFSMarginalOutsideEq optionBFSMarginalInsideFintype optionBFSMarginalOutsideFintype
universe u v
variable {O : Type u} {C : Type v} [Fintype O] [Fintype C] [Nonempty C]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _

theorem bfs_curve_response_step (F : PinningFamily.{u, v} C)
    (I : PinningData (Option O) C) (hI : F.contains I) (a b : C)
    {Δ L B : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (hL : 0 < L)
    (hB : (∑ j ∈ Finset.range (L + 2), Δ ^ j) ≤ B)
    (hlarge : B < Fintype.card (RootComponent I.graph))
    {r α cost : ℝ} (hr : 0 < r) (hrB : r ≤ localFieldRadius B α)
    (ha : 0 < α) (ha1 : α ≤ 1) (haB : α * (B : ℝ) ≤ 1 / 8)
    (hcost : 64 * cost ≤ (L : ℝ))
    (hCI : W ham
      ((optionChildData I a).gibbs 0 le_rfl
        (partition_zero_pos_of_succ_le _ (optionChildData_degreeBound I hd a) hq))
      ((optionChildData I b).gibbs 0 le_rfl
        (partition_zero_pos_of_succ_le _ (optionChildData_degreeBound I hd b) hq)) ≤ cost)
    (hNZ : SmallerCurvesNonzero F Δ (Fintype.card (Option O)) r)
    (hRoot : SmallerCurveResponses F Δ (Fintype.card (Option O)) r α)
    (d : Option O → C → ℂ) (hdir : DirectionBound d) :
    HasSmallResponseLog (fieldCurve (optionChildData I a) (fieldPull some d))
      (fieldCurve (optionChildData I b) (fieldPull some d)) 0 r α := by
  obtain ⟨k, hk, hkL, hW⟩ := exists_low_childGibbsShellLaw_of_ci I a b 0 le_rfl _ _ hL hCI
  have hs := shell_nonempty_of_component_card_gt_bound I Δ (L + 1) B hd
    (by simpa only [Nat.add_assoc] using hB) hlarge k (by omega)
  have hcard := inside_shell_card_le_bound I hd hB k hkL
  have hda := childSplit_degreeBound I a k hd
  have hdb := childSplit_degreeBound I b k hd
  have hsa := childSplit_separates I a k
  have hsb := childSplit_separates I b k
  obtain ⟨h, hzero, hdiff, hexp, hlip⟩ :=
    childSplit_exterior_response_logs F I hI a d hdir hd k hs hr hNZ hRoot
  have hosc (z : ℂ) (hz : z ∈ Metric.ball 0 r)
      (ξ ξ' : BFS.Shell I.graph none k → C) : ‖h ξ z - h ξ' z‖ ≤ (1 / 8 : ℝ) := by
    apply (hlip z hz ξ ξ').trans
    apply le_trans (mul_le_mul_of_nonneg_left (ham_le_card ξ ξ') ha.le)
    have hsB : Fintype.card (BFS.Shell I.graph none k) ≤ B := by omega
    have hsB' : (Fintype.card (BFS.Shell I.graph none k) : ℝ) ≤ B := by exact_mod_cast hsB
    exact (mul_le_mul_of_nonneg_left hsB' ha.le).trans haB
  have hcommon (ξ : BFS.Shell I.graph none k → C) :
      exteriorData (childSplit I a k) ξ = exteriorData (childSplit I b k) ξ := by
    rw [childSplit_exterior_eq_parent, childSplit_exterior_eq_parent]
  have hZA := partition_zero_pos_of_succ_le (childSplit I a k) hda hq
  have hZB := partition_zero_pos_of_succ_le (childSplit I b k) hdb hq
  obtain ⟨H, hH0, hHD, hHE, hHB⟩ := exists_field_separator_quotient_log
    (childSplit I a k) (childSplit I b k) hsa hsb hcommon hZA hZB hcard
    ha ha1 hrB (fieldPull (parentValue I.graph k) d) (hdir.pull _) h
    hdiff hzero (fun z hz ξ => hexp ξ z hz) hlip hosc
  refine ⟨H, hH0, hHD, ?_, ?_⟩
  · intro z hz
    simpa only [fieldCurve_childSplit] using hHE z hz
  · intro z hz
    apply (hHB z hz).trans
    have hw := positive_shell_budget_closes hL hcost ha.le hW (le_refl (α / 8))
    simpa only [childGibbsShellLaw, show 4 * (α / 8) = α / 2 by ring] using hw

end
end CI2ZF.LeeYang
