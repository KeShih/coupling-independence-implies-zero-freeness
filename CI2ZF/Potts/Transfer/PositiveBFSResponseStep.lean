import CI2ZF.Potts.Transfer.OptionBFSResponseGeometry
import CI2ZF.Potts.Geometry.OptionBFSMarginals
import CI2ZF.Potts.Transfer.PositiveSeparatorLog
import CI2ZF.Potts.Transfer.TransferScales
import CI2ZF.Potts.Transfer.TransferLocalControls

/-! The large-component positive response step uses genuine BFS shell
marginals and the smaller-instance induction hypotheses. -/
namespace CI2ZF.Potts.OptionBFS
open PottsCI PottsCI.FinDist Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {O : Type u} {C : Type v} [Fintype O] [Fintype C] [Nonempty C]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _
attribute [local instance] optionBFSMarginalInsideEq optionBFSMarginalShellEq
  optionBFSMarginalOutsideEq optionBFSMarginalInsideFintype optionBFSMarginalOutsideFintype

/-- A real coupling bound for the two actual children closes one full
large-component response step. All exterior hypotheses concern strictly
smaller actual instances, and the local input is the controlled principal
logarithm of the actual bounded inside polynomial. -/
theorem positive_bfs_response_step
    (I : PinningData (Option O) C) (a b : C) {Δ L B : ℕ}
    (hd : I.DegreeBound Δ) (hL : 0 < L)
    (hB : (∑ j ∈ Finset.range (L + 2), Δ ^ j) ≤ B)
    (hlarge : B < Fintype.card (RootComponent I.graph))
    {x ε α cost : ℝ} (hx : 0 < x) (hε : 0 < ε)
    (ha : 0 ≤ α) (hα1 : α ≤ 1) (hαB : α * (B : ℝ) ≤ 1 / 8)
    (hcost : 64 * cost ≤ (L : ℝ))
    (hCI : W ham
      ((optionChildData I a).gibbs x hx.le
        ((optionChildData I a).partition_pos_of_parameter_pos hx))
      ((optionChildData I b).gibbs x hx.le
        ((optionChildData I b).partition_pos_of_parameter_pos hx)) ≤ cost)
    (hNZ : SmallerPartitionsNonzero.{u, v} C Δ (Fintype.card (Option O)) (x : ℂ) ε)
    (hRoot : SmallerRootResponses.{u, v} C Δ (Fintype.card (Option O)) (x : ℂ) ε α)
    (hLocal : ∀ {U S E : Type u} [Fintype U] [Fintype S] [Fintype E]
      (J : PinningData (Separator.Vertex U S E) C), J.DegreeBound Δ →
      Fintype.card U + Fintype.card S ≤ B → ∀ ξ : S → C,
      PrincipalResponseControl (fun z => insidePartition J z ξ) (x : ℂ) ε (α / 8)) :
    HasSmallResponseLog (pinningProductPartition (optionChildData I a))
      (pinningProductPartition (optionChildData I b)) (x : ℂ) ε α := by
  obtain ⟨k, hk, hkL, hW⟩ := exists_low_childGibbsShellLaw_of_ci I a b x hx.le
    ((optionChildData I a).partition_pos_of_parameter_pos hx)
    ((optionChildData I b).partition_pos_of_parameter_pos hx) hL hCI
  have hs := shell_nonempty_of_component_card_gt_bound I Δ (L + 1) B hd
    (by simpa only [Nat.add_assoc] using hB) hlarge k (by omega)
  have hcard := inside_shell_card_le_bound I hd hB k hkL
  have hda := childSplit_degreeBound I a k hd
  have hdb := childSplit_degreeBound I b k hd
  have hsa := childSplit_separates I a k
  have hsb := childSplit_separates I b k
  obtain ⟨h, hzero, hdiff, hexp, hlip⟩ :=
    childSplit_exterior_response_logs I a hd k hk hs hε hNZ hRoot
  let eta := fun ξ => principalResponseLog (fun z => insidePartition (childSplit I a k) z ξ) (x : ℂ)
  let theta := fun ξ => principalResponseLog (fun z => insidePartition (childSplit I b k) z ξ) (x : ℂ)
  have heta (ξ : BFS.Shell I.graph none k → C) := hLocal _ hda hcard ξ
  have htheta (ξ : BFS.Shell I.graph none k → C) := hLocal _ hdb hcard ξ
  have hosc (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) ε)
      (ξ ξ' : BFS.Shell I.graph none k → C) : ‖h ξ z - h ξ' z‖ ≤ (1 / 8 : ℝ) := by
    apply (hlip z hz ξ ξ').trans
    apply le_trans (mul_le_mul_of_nonneg_left (ham_le_card ξ ξ') ha)
    have hsB : Fintype.card (BFS.Shell I.graph none k) ≤ B := by omega
    have hsB' : (Fintype.card (BFS.Shell I.graph none k) : ℝ) ≤ B := by exact_mod_cast hsB
    apply le_trans (mul_le_mul_of_nonneg_left hsB' ha)
    exact hαB
  have hcommon (ξ : BFS.Shell I.graph none k → C) :
      exteriorData (childSplit I a k) ξ = exteriorData (childSplit I b k) ξ :=
    (childSplit_exterior_eq_parent I a k ξ).trans (childSplit_exterior_eq_parent I b k ξ).symm
  have hdelta : α / 8 ∈ Set.Icc 0 (1 / 8 : ℝ) := ⟨by positivity, by linarith⟩
  obtain ⟨_, ℓ, hℓzero, hℓdiff, hℓexp, hℓbound⟩ :=
    exists_positive_separator_quotient_log (childSplit I a k) (childSplit I b k)
      hsa hsb hcommon hx ha hdelta h eta theta hdiff
      (fun ξ => (heta ξ).2.1) (fun ξ => (htheta ξ).2.1)
      hzero (fun ξ => (heta ξ).1) (fun ξ => (htheta ξ).1)
      (fun z hz ξ => hexp ξ z hz)
      (fun z hz ξ => (heta ξ).2.2.1 z hz) (fun z hz ξ => (htheta ξ).2.2.1 z hz)
      hlip hosc (fun z hz ξ => (heta ξ).2.2.2 z hz) (fun z hz ξ => (htheta ξ).2.2.2 z hz)
  refine ⟨ℓ, hℓzero, hℓdiff, ?_, ?_⟩
  · intro z hz
    simpa only [childSplit_partition] using hℓexp z hz
  · intro z hz
    apply (hℓbound z hz).trans
    apply positive_shell_budget_closes hL hcost ha _ le_rfl
    simpa only [childGibbsShellLaw] using hW

end
end CI2ZF.Potts.OptionBFS
