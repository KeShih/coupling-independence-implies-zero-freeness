import CI2ZF.Appendix.EdgeFiniteResidual

/-! The four-row table applied to the true finite endpoint-label Gibbs
laws gives the recursive single-replacement contraction. -/
namespace CI2ZF.Appendix.Edge.FiniteSystem
open PottsCI PottsCI.FinDist Finset FiniteLaw
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L] [Nonempty A]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq A := Classical.decEq A
local instance (priority := 2000) : DecidableEq L := Classical.decEq L

theorem single_replacement_step (I : FiniteSystem V E A L) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    {t : ℝ} (ht : 0 ≤ t) (hsmall : ∀ e, (I.remove e).SingleReplacementCI Δ t) :
    I.SingleReplacementCI Δ (((Δ : ℝ) - 1) / (2 * Δ) * (1 + 2 * t)) := by
  intro B v α β hα0 hβ0 hB hD
  have hd : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  by_cases heq : α = β
  · subst β
    rw [W_self ham_nonneg ham_self]
    exact mul_nonneg (div_nonneg (by linarith) (by positivity)) (by linarith)
  let μ := I.validLaw (addBoundary B v α) hB
  let ν := I.validLaw (addBoundary B v β) hD
  let P := I.Occurs v β
  let Q := I.Occurs v α
  let zμ := eventMass μ (I.Avoids v β)
  let zν := eventMass ν (I.Avoids v α)
  have hzμ : 0 < zμ := by
    change 0 < eventMass (I.gibbs (addBoundary B v α) _) (I.Avoids v β)
    rw [I.gibbs_avoidance_mass]
    exact div_pos (hB.add_partition_pos I _ v β) (hB.partition_pos I _)
  have hzν : 0 < zν := by
    change 0 < eventMass (I.gibbs (addBoundary B v β) _) (I.Avoids v α)
    rw [I.gibbs_avoidance_mass]
    exact div_pos (hD.add_partition_pos I _ v α) (hD.partition_pos I _)
  let μ₀ := conditional μ (I.Avoids v β)
  have hzero : conditional ν (I.Avoids v α) = μ₀ := by
    change conditional (I.gibbs (addBoundary B v β) _) (I.Avoids v α) =
      conditional (I.gibbs (addBoundary B v α) _) (I.Avoids v β)
    rw [I.conditional_gibbs_avoidance _ _ _ _ (hD.add_partition_pos I _ v α),
      I.conditional_gibbs_avoidance _ _ _ _ (hB.add_partition_pos I _ v β)]
    simp only [addBoundary_comm B v β α]
  let ρ : ↑(I.incident v) → ℝ := fun j => eventMass μ (P j) / zμ
  let σ : ↑(I.incident v) → ℝ := fun j => eventMass ν (Q j) / zν
  let μj := fun j => conditional μ (P j)
  let νj := fun j => conditional ν (Q j)
  have hρ : ∀ j, 0 ≤ ρ j := fun j => div_nonneg (eventMass_nonneg μ _) hzμ.le
  have hσ : ∀ j, 0 ≤ σ j := fun j => div_nonneg (eventMass_nonneg ν _) hzν.le
  have hρpos (j : ↑(I.incident v)) (hj : 0 < ρ j) : 0 < eventMass μ (P j) :=
    (div_pos_iff_of_pos_right hzμ).mp hj
  have hσpos (j : ↑(I.incident v)) (hj : 0 < σ j) : 0 < eventMass ν (Q j) :=
    (div_pos_iff_of_pos_right hzν).mp hj
  have hμ : ∀ x, μ₀.w x + ∑ j, ρ j * (μj j).w x = (1 + ∑ j, ρ j) * μ.w x := by
    intro x
    exact exposure_identity μ (I.Avoids v β) P hzμ
      (I.gibbs_exposure_partition _ _ v β) x
  have hν : ∀ x, μ₀.w x + ∑ j, σ j * (νj j).w x = (1 + ∑ j, σ j) * ν.w x := by
    intro x
    have hh := exposure_identity ν (I.Avoids v α) Q hzν
      (I.gibbs_exposure_partition _ _ v α) x
    simpa only [hzero] using hh
  have hm : ∀ j, 0 < ρ j → 0 < σ j → W ham (μj j) (νj j) ≤ 1 + t := by
    intro j hj hk
    apply I.W_occurrences_le _ _ hB hD v β α j (hρpos j hj) (hσpos j hk)
    intro a b hac hbc hav hbv
    exact I.matched_residual_le B v α β hB hD j (hsmall j.val) a b hac hbc hav hbv
  have hl : ∀ j, 0 < ρ j → W ham (μj j) ν ≤ 1 + 2 * t := by
    intro j hj
    apply I.W_occurrence_full_le _ _ hB hD v β j (hρpos j hj)
    intro a b hac hbc hav
    exact I.unmatched_residual_le B v α β hα0 heq hB hD j (hsmall j.val) a b hac hbc hav
  have hr : ∀ j, 0 < σ j → W ham μ (νj j) ≤ 1 + 2 * t := by
    intro j hj
    apply I.W_full_occurrence_le _ _ hB hD v α j (hσpos j hj)
    intro a b hac hbc hbv
    rw [W_ham_comm]
    exact I.unmatched_residual_le B v β α hβ0 (Ne.symm heq) hD hB j (hsmall j.val) b a hbc hac hbv
  have hW := W_exposure_le_supported μ ν μ₀ μj νj ρ σ hρ hσ hμ hν
    ham ham_nonneg ham_self ht hm hl hr
  have hρb (j : ↑(I.incident v)) : ρ j ≤ 1 / ((Δ : ℝ) + 1) :=
    I.occurrence_odds_le _ hB v β j
  have hσb (j : ↑(I.incident v)) : σ j ≤ 1 / ((Δ : ℝ) + 1) :=
    I.occurrence_odds_le _ hD v α j
  have hb := occurrence_budget (by positivity : 0 ≤ (Δ : ℝ)) ρ σ hρb hσb (I.occurrence_index_card B v α hB)
  have hf := occurrence_fraction hd (exposureBudget_nonneg ρ σ hρ) hb
  exact hW.trans (mul_le_mul_of_nonneg_right hf (by linarith))

end
end CI2ZF.Appendix.Edge.FiniteSystem
