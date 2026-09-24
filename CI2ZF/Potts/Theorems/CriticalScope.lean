import CI2ZF.Potts.Model.PottsModel
import CI2ZF.Potts.Theorems.PottsExternalTheorem

/-! # `rem:critical-scope`: list slack and the critical-line endpoint input

Companion, Appendix "additional Potts results", Remark 4.4.

* (a) The list-slack inequality
  `|L_u^τ| - deg_{G^τ}(u) ≥ q - Δ`, stated for boundary-count data and for an
  actual graph with an arbitrary (possibly improper) partial colouring, and its
  critical-line value `q - Δ = 5Δ/6`.
* The integrality statement: every integer pair with `q = 11Δ/6` and `Δ ≥ 2`
  is `(Δ, q) = (6j, 11j)` with `j ≥ 1`, so `Δ ≥ 6`.
* The conclusion of the remark, i.e. the hard-endpoint coupling input of
  `def:potts-ci` at `x = 0` on original graphs with arbitrary pinnings, along
  the entire critical line. The paper obtains it from CFFGZZ Theorem 20 and
  Proposition 22; Lean proves the same conclusion by the library's
  Carlson--Vigoda contraction (`external_critical_hard_colouring_theorem`).
-/

namespace CI2ZF.Potts
open PottsCI CI2ZF.Potts
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

universe u v
variable {V : Type u} {C : Type v} [Fintype V] [Fintype C]

/-- **List slack** for boundary-count data: at most `∑_c b_u(c)` colours are
blocked, and `deg_{G^τ}(u) + ∑_c b_u(c) ≤ Δ`. -/
theorem hardList_slack (I : PinningData V C) {Δ : ℕ} (hdegree : I.DegreeBound Δ) (u : V) :
    (Fintype.card C : ℤ) - Δ ≤ ((I.hardList u).card : ℤ) - I.graph.degree u := by
  have hsplit : (Finset.univ.filter fun c => I.boundaryCount u c = 0).card +
      (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card = Fintype.card C := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hforbidden : (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card ≤
      ∑ c, I.boundaryCount u c := by
    calc
      (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card =
          ∑ c ∈ Finset.univ.filter (fun c => ¬ I.boundaryCount u c = 0), 1 := by
            rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ c ∈ Finset.univ.filter (fun c => ¬ I.boundaryCount u c = 0),
          I.boundaryCount u c := by
            refine Finset.sum_le_sum fun c hc => ?_
            have hcpos := (Finset.mem_filter.mp hc).2
            omega
      _ ≤ ∑ c, I.boundaryCount u c := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro c _ _
            exact Nat.zero_le _
  have htotal := hdegree u
  unfold PinningData.constraintDegree at htotal
  unfold PinningData.hardList
  omega

/-- The paper's hard effective list `L_u^τ = {c : b_u^τ(c) = 0}` is the
library's `hardList` of the pinned datum. -/
theorem hardList_toPinningData (tau : PartialColouring V C) (G : SimpleGraph V)
    (u : tau.FreeVertex) :
    (tau.toPinningData G).hardList u =
      Finset.univ.filter fun c => tau.boundaryCount G u c = 0 := rfl

/-- **List slack on an actual graph with an arbitrary pinning**:
`|L_u^τ| - deg_{G^τ}(u) ≥ q - Δ` whenever `G` has maximum degree at most `Δ`.
No properness of `τ` is assumed. -/
theorem hardList_slack_original (tau : PartialColouring V C) (G : SimpleGraph V)
    {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ) (u : tau.FreeVertex) :
    (Fintype.card C : ℤ) - Δ ≤
      ((Finset.univ.filter fun c => tau.boundaryCount G u c = 0).card : ℤ) -
        (tau.freeGraph G).degree u :=
  hardList_slack (tau.toPinningData G) (tau.degreeBound_of_original G hdegree) u

/-- **The critical-line value** `q - Δ = 5Δ/6` of the list slack. -/
theorem hardList_slack_critical (tau : PartialColouring V C) (G : SimpleGraph V)
    {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ) (hq : (Fintype.card C : ℝ) = 11 / 6 * Δ)
    (u : tau.FreeVertex) :
    (Fintype.card C : ℝ) - Δ = 5 / 6 * Δ ∧
      5 / 6 * (Δ : ℝ) ≤
        ((Finset.univ.filter fun c => tau.boundaryCount G u c = 0).card : ℝ) -
          (tau.freeGraph G).degree u := by
  have h := hardList_slack_original tau G hdegree u
  have h' : ((Fintype.card C : ℤ) : ℝ) - ((Δ : ℤ) : ℝ) ≤
      (((Finset.univ.filter fun c => tau.boundaryCount G u c = 0).card : ℤ) : ℝ) -
        (((tau.freeGraph G).degree u : ℤ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  constructor <;> linarith

/-- At `x = 0` the normalized pinned law is the uniform law on proper
list-colourings of the free graph with the lists `L_u^τ`: hard admissibility is
exactly properness plus membership in the hard lists, and the law gives equal
mass to every admissible colouring and none to the others. -/
theorem hardAdmissible_iff (I : PinningData V C) (σ : V → C) :
    I.HardAdmissible σ ↔ (∀ u v, I.graph.Adj u v → σ u ≠ σ v) ∧ ∀ u, σ u ∈ I.hardList u := by
  unfold PinningData.HardAdmissible PinningData.hardList
  simp

theorem partition_zero_eq_filter_card (I : PinningData V C) :
    I.partition 0 = ((Finset.univ.filter fun σ : V → C => I.HardAdmissible σ).card : ℝ) := by
  unfold PinningData.partition
  simp_rw [I.weight_zero_eq]
  rw [Finset.sum_boole]

theorem gibbs_zero_uniform (I : PinningData V C) (hZ : 0 < I.partition 0) (σ : V → C) :
    (I.gibbs 0 le_rfl hZ).w σ =
      if I.HardAdmissible σ then
        1 / ((Finset.univ.filter fun τ : V → C => I.HardAdmissible τ).card : ℝ)
      else 0 := by
  change I.weight 0 σ / I.partition 0 = _
  rw [I.weight_zero_eq, partition_zero_eq_filter_card]
  split_ifs <;> simp

/-- Every integer pair on the critical line with `Δ ≥ 2` is `(6j, 11j)`, `j ≥ 1`. -/
theorem critical_line_pairs {q Δ : ℕ} (hq : 6 * q = 11 * Δ) (hΔ : 2 ≤ Δ) :
    ∃ j : ℕ, 1 ≤ j ∧ Δ = 6 * j ∧ q = 11 * j := by
  refine ⟨Δ / 6, ?_, ?_, ?_⟩ <;> omega

theorem critical_line_pairs_real {Δ : ℕ} (hq : (Fintype.card C : ℝ) = 11 / 6 * Δ)
    (hΔ : 2 ≤ Δ) :
    ∃ j : ℕ, 1 ≤ j ∧ Δ = 6 * j ∧ Fintype.card C = 11 * j := by
  have hq' : 6 * Fintype.card C = 11 * Δ := by
    have : (6 * Fintype.card C : ℝ) = 11 * Δ := by rw [hq]; ring
    exact_mod_cast this
  exact critical_line_pairs hq' hΔ

/-- **The conclusion of `rem:critical-scope`.** Along the entire critical
line `q = 11Δ/6` (`Δ ≥ 2`), the hard-colouring coupling input of
`def:potts-ci` at `x = 0` holds with one finite constant for every original
graph of maximum degree at most `Δ`, every arbitrary (possibly improper)
pinning, every free root `r` and all root colours, with the two laws
restricted to `V^τ \ {r}`. -/
theorem critical_line_hard_endpoint [Nonempty C] {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : (Fintype.card C : ℝ) = 11 / 6 * Δ) :
    ExternalCriticalHardColouringTheorem.{u, v} C Δ := by
  obtain ⟨j, hj, hΔj, _⟩ := critical_line_pairs_real hq hΔ
  exact external_critical_hard_colouring_theorem C (by omega) hq.symm.le

end
end CI2ZF.Potts
