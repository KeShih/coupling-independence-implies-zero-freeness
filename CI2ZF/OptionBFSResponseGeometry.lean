import CI2ZF.OptionBFSCardinality
import CI2ZF.ExteriorAnalyticResponses
import CI2ZF.InductionState

/-! The actual BFS children inherit the smaller-instance analytic
induction hypotheses through their common exterior. -/
namespace CI2ZF.Potts.OptionBFS
open PottsCI PottsCI.FinDist Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {O : Type u} {C : Type v} [Fintype O] [Fintype C]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _

theorem childSplit_partition {R : Type*} [CommSemiring R]
    (I : PinningData (Option O) C) (a : C) (k : ℕ) (z : R) :
    partition (childSplit I a k) z = pinningProductPartition (optionChildData I a) z := by
  convert pinningProductPartition_relabel (optionChildData I a) (childEquiv I.graph k) z using 1
  unfold partition pinningProductPartition weight pinningProductWeight
  congr 2
  exact Subsingleton.elim _ _

theorem inside_shell_card_le_bound (I : PinningData (Option O) C) {Δ L B : ℕ}
    (hd : I.DegreeBound Δ) (hB : (∑ j ∈ Finset.range (L + 2), Δ ^ j) ≤ B)
    (k : ℕ) (hk : k ≤ L) :
    Fintype.card (Inside I.graph k) + Fintype.card (BFS.Shell I.graph none k) ≤ B := by
  apply (inside_shell_card_le_geom I k Δ hd).trans
  apply le_trans _ hB
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono (by omega)

/-- Both the logarithms and their coordinate control are derived from
the actual smaller exterior and temporarily unpinned exterior data. -/
theorem childSplit_exterior_response_logs
    (I : PinningData (Option O) C) (a : C) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (k : ℕ) (hk : 1 ≤ k) (hs : Nonempty (BFS.Shell I.graph none k))
    {x : ℂ} {ε α : ℝ} (hε : 0 < ε)
    (hNZ : SmallerPartitionsNonzero.{u, v} C Δ (Fintype.card (Option O)) x ε)
    (hRoot : SmallerRootResponses.{u, v} C Δ (Fintype.card (Option O)) x ε α) :
    ∃ h : (BFS.Shell I.graph none k → C) → ℂ → ℂ,
      (∀ ξ, h ξ x = 0) ∧
      (∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball x ε)) ∧
      (∀ ξ, ∀ z ∈ Metric.ball x ε, Complex.exp (h ξ z) =
        exteriorPartition (childSplit I a k) z ξ /
          exteriorPartition (childSplit I a k) x ξ) ∧
      ∀ z ∈ Metric.ball x ε, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ' := by
  have : Nonempty (Inside I.graph k) := inside_nonempty_of_shell_nonempty I.graph k hk hs
  have hsep := childSplit_separates I a k
  have hdegree := childSplit_degreeBound I a k hd
  have hnz (ξ : BFS.Shell I.graph none k → C) (z : ℂ) (hz : z ∈ Metric.ball x ε) :
      exteriorPartition (childSplit I a k) z ξ ≠ 0 := by
    rw [exteriorPartition_eq_pinningProductPartition _ hsep]
    exact hNZ (exteriorData (childSplit I a k) ξ)
      (exteriorData_degreeBound _ hsep hdegree ξ) (outside_card_lt_parent I.graph k) z hz
  obtain ⟨h, hzero, hdiff, hexp⟩ := exists_exterior_response_logs _ hsep hε hnz
  refine ⟨h, hzero, hdiff, hexp, ?_⟩
  apply exterior_logs_lipschitz_of_smaller_root_responses _ hsep hdegree hε h hzero hdiff hexp
  intro J hJ _ a b
  exact hRoot J hJ (unpinOutside_card_lt_parent I.graph k hs) a b

end
end CI2ZF.Potts.OptionBFS
