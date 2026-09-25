import ZeroFreeness.Holant.SeparatorCoefficients
import ZeroFreeness.Holant.InstanceSeparator
import ZeroFreeness.Holant.Paths
import ZeroFreeness.Holant.TransferParameters

/-! All numerical inputs for the separator transfer engine, derived from
actual local Holant coefficients, finite shell states and one common choice
of transfer parameters. -/
namespace ZeroFreeness.Holant
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

namespace RootSeparator
variable {H : NormalizedInstance V E} {e : E} (P : RootSeparator H e)

/-- Both root children retain the same finite residual family. -/
theorem child_family (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (b : Bool) (v : V) : (P.child he hs b).signature v ∈ residualFamily F := by
  cases b
  · exact H.zeroChild_family F hF e v
  · exact H.oneChild_family F hF e he hs v

theorem local_parent_subset : P.shell ∪ P.interior ⊆ H.edges :=
  Finset.union_subset
    (P.shell_subset.trans (Finset.erase_subset e H.edges))
    (P.interior_subset.trans (Finset.erase_subset e H.edges))

/-- Feasible shell states form a subset of the shell powerset. -/
theorem state_card_le_pow {N : ℕ} (hlocal : (P.shell ∪ P.interior).card ≤ N) :
    Fintype.card P.State ≤ 2 ^ N := by
  have hshell : P.shell.card ≤ N :=
    (Finset.card_le_card Finset.subset_union_left).trans hlocal
  have hs : P.states ⊆ P.shell.powerset := by
    intro ξ hξ
    exact Finset.mem_powerset.mpr (P.state_subset ⟨ξ, hξ⟩)
  calc
    Fintype.card P.State = P.states.card := Fintype.card_coe _
    _ ≤ P.shell.powerset.card := Finset.card_le_card hs
    _ = 2 ^ P.shell.card := Finset.card_powerset _
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hshell

/-- Bound the shell oscillation budget using the actual local edge count. -/
theorem shell_alpha_le {D : ℕ} {A R C : ℝ} (p : TransferParameters D A R C)
    (hlocal : (P.shell ∪ P.interior).card ≤ p.localSize) :
    P.shell.card * p.alpha ≤ 1 / 8 := by
  have hshell : P.shell.card ≤ p.localSize :=
    (Finset.card_le_card Finset.subset_union_left).trans hlocal
  have hcast : (P.shell.card : ℝ) ≤ p.localSize := by exact_mod_cast hshell
  exact (mul_le_mul_of_nonneg_right hcast p.alpha_pos.le).trans p.oscillation_small

/-- Summing the uniform local error over the feasible state space fits the
single graph-independent total-error budget. -/
theorem state_error_budget (F : Finset Signature) {D : ℕ} {R C : ℝ}
    (p : TransferParameters D (residualGrowthBound F) R C) (hR : 0 ≤ R)
    (hlocal : (P.shell ∪ P.interior).card ≤ p.localSize) :
    Fintype.card P.State * p.localErrorBound * (4 / 3) ≤ p.totalErrorBound := by
  have hcard : (Fintype.card P.State : ℝ) ≤ (2 : ℝ) ^ p.localSize := by
    exact_mod_cast P.state_card_le_pow hlocal
  have hβ := p.localErrorBound_nonneg (residualGrowthBound_nonneg F) hR
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcard hβ) (by norm_num)

/-- The actual separator coefficients satisfy the transfer engine's local
error bound at every point of the activity path. -/
theorem coefficient_path_error (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    {D : ℕ} {R C : ℝ} (p : TransferParameters D (residualGrowthBound F) R C)
    (hR : 0 ≤ R) (hlocal : (P.shell ∪ P.interior).card ≤ p.localSize)
    (htwo : ∀ a ∈ H.edges, (Finset.univ.filter fun v => H.incidence a v).card = 2)
    (path : ActivityPath H.edges R p.epsilon) (b : Bool) (ξ : P.State)
    (t : ℂ) (ht : t ∈ Metric.ball 0 path.radius) :
    ‖P.coefficientComplex he hs b ξ (path.activity t) -
      (P.coefficientReal he hs b ξ path.base : ℂ)‖ ≤ p.localErrorBound := by
  have hbase : ∀ a ∈ P.shell ∪ P.interior, ‖(path.base a : ℂ)‖ ≤ R + 1 := by
    intro a ha
    have hx := path.realBox a (P.local_parent_subset ha)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    linarith [hx.2]
  have hactivity : ∀ a ∈ P.shell ∪ P.interior, ‖path.activity t a‖ ≤ R + 1 := by
    intro a ha
    have hparent := P.local_parent_subset ha
    have hx := path.realBox a hparent
    have hnear := path.near t ht a hparent
    have hnorm := norm_sub_norm_le (path.activity t a) (path.base a : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1] at hnorm
    linarith [hx.2, p.epsilon_le_one]
  rw [← P.coefficientComplex_ofReal he hs b ξ path.base]
  exact separatorCoefficient_lipschitz F H.incidence (P.child he hs b).signature
    (P.child_family he hs F hF b) P.interior P.shell P.exterior ξ.val
    P.separated P.shell_interior (P.state_subset ξ)
    (fun a ha => htwo a (P.local_parent_subset ha))
    (path.activity t) (fun a => (path.base a : ℂ)) hlocal
    (by linarith : 1 ≤ R + 1) p.epsilon_pos.le hactivity hbase
    (fun a ha => (path.near t ht a (P.local_parent_subset ha)).le)

/-- The estimates needed by the engine are available together from the
same parameter choice and the same actual root separator. -/
theorem separator_estimates (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    {D : ℕ} {R C : ℝ} (p : TransferParameters D (residualGrowthBound F) R C)
    (hR : 0 ≤ R) (hlocal : (P.shell ∪ P.interior).card ≤ p.localSize)
    (htwo : ∀ a ∈ H.edges, (Finset.univ.filter fun v => H.incidence a v).card = 2)
    (path : ActivityPath H.edges R p.epsilon) :
    Fintype.card P.State ≤ 2 ^ p.localSize ∧
    (∀ b ξ t, t ∈ Metric.ball 0 path.radius →
      ‖P.coefficientComplex he hs b ξ (path.activity t) -
        (P.coefficientReal he hs b ξ path.base : ℂ)‖ ≤ p.localErrorBound) ∧
    Fintype.card P.State * p.localErrorBound * (4 / 3) ≤ p.totalErrorBound ∧
    P.shell.card * p.alpha ≤ 1 / 8 :=
  ⟨P.state_card_le_pow hlocal,
    fun b ξ t ht => P.coefficient_path_error he hs F hF p hR hlocal htwo path b ξ t ht,
    P.state_error_budget F p hR hlocal, P.shell_alpha_le p hlocal⟩

end RootSeparator
end
end ZeroFreeness.Holant
