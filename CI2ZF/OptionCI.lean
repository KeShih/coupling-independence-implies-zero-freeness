import CI2ZF.OptionPinning
import CI2ZF.PottsCITheorem

/-! Coupling independence for the actual normalized children of arbitrary
boundary-count data with one distinguished free root. -/

namespace CI2ZF.Potts

open PottsCI PottsCI.FinDist PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
noncomputable section

variable {O C : Type*} [Fintype O] [Fintype C] [Nonempty C]

theorem optionChild_soft_boundary_W_le [Nonempty O]
    (I : PinningData (Option O) C) {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (a : C) (X : O → C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softVigodaKernel (optionChildData I a) x hx0 hx1 X)
      (softVigodaKernel (optionMiddleData I) x hx0 hx1 X) ≤
        (1 - x) * Δ / ((Fintype.card O : ℝ) * Fintype.card C) := by
  have hb := softVigodaKernel_addBoundarySet_W_le (optionMiddleData I)
    (optionRootNeighbours I) a X x hx0 hx1
  apply hb.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact_mod_cast optionRootNeighbours_card_le I hdegree

/-- Both actual soft contractions and both boundary perturbation bounds
are derived for the concrete children, with no coupling premise. -/
theorem option_softVigoda_inputs [Nonempty O]
    (I : PinningData (Option O) C) {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (a b : C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    SoftVigodaCouplingInputs (optionChildData I a) (optionChildData I b)
      (optionMiddleData I) Δ x hx0 hx1 := by
  apply softVigoda_inputs_of_conditional_hard
    (optionChildData I a) (optionChildData I b) (optionMiddleData I)
    (optionChildData_degreeBound I hdegree a) (optionChildData_degreeBound I hdegree b)
    (conditionalHardCouplingEstimate _) (conditionalHardCouplingEstimate _) x hx0 hx1
  · exact fun X => optionChild_soft_boundary_W_le I hdegree a X x hx0 hx1
  · exact fun X => optionChild_soft_boundary_W_le I hdegree b X x hx0 hx1

/-- The strict-line exact CI bound for arbitrary root children, including
empty `O` and the activities `0` and `1`. -/
theorem option_root_strict_ci (I : PinningData (Option O) C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C) (a b : C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      ((optionChildData I a).nonnegativeGibbs (optionChildData_degreeBound I hdegree a)
        (colours_slack_of_vigoda_line hΔ hq.le) x)
      ((optionChildData I b).nonnegativeGibbs (optionChildData_degreeBound I hdegree b)
        (colours_slack_of_vigoda_line hΔ hq.le) x) ≤ ciBound (Fintype.card C) Δ x := by
  apply strict_ci_including_empty (optionChildData I a) (optionChildData I b) (optionMiddleData I)
    hΔ (optionChildData_degreeBound I hdegree a) (optionChildData_degreeBound I hdegree b) hq
  · intro hO y hy0 hy1
    exact option_softVigoda_inputs I hdegree a b y hy0 hy1
  · exact hx1

/-- The strict-line CI constant is uniform over the entire physical interval. -/
theorem option_root_strict_uniform_ci (I : PinningData (Option O) C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (11 / 6 : ℝ) * Δ < Fintype.card C) (a b : C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      ((optionChildData I a).nonnegativeGibbs (optionChildData_degreeBound I hdegree a)
        (colours_slack_of_vigoda_line hΔ hq.le) x)
      ((optionChildData I b).nonnegativeGibbs (optionChildData_degreeBound I hdegree b)
        (colours_slack_of_vigoda_line hΔ hq.le) x) ≤ 2 / ciGap (Fintype.card C) Δ := by
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hΔ)
  exact (option_root_strict_ci I hΔ hdegree hq a b x hx1).trans
    (ciBound_le_strict_uniform hΔpos ⟨x.property, hx1⟩ hq)

/-- The critical-line CI bound away from zero, also including empty `O`
and activity `1`. The critical hard endpoint is not asserted. -/
theorem option_root_critical_uniform_ci (I : PinningData (Option O) C)
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hdegree : I.DegreeBound Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ) (a b : C)
    {δ : ℝ} (hδ : 0 < δ) (x : PinningData.NonnegativeParameter)
    (hx : (x : ℝ) ∈ Set.Icc δ 1) :
    W ham
      ((optionChildData I a).nonnegativeGibbs (optionChildData_degreeBound I hdegree a)
        (colours_slack_of_vigoda_line hΔ hq.ge) x)
      ((optionChildData I b).nonnegativeGibbs (optionChildData_degreeBound I hdegree b)
        (colours_slack_of_vigoda_line hΔ hq.ge) x) ≤ 12 / (11 * δ) := by
  apply critical_uniform_ci_including_empty
    (optionChildData I a) (optionChildData I b) (optionMiddleData I)
    hΔ (optionChildData_degreeBound I hdegree a) (optionChildData_degreeBound I hdegree b) hq
  · intro hO y hy0 hy1
    exact option_softVigoda_inputs I hdegree a b y hy0 hy1
  · exact hδ
  · exact hx

end
end CI2ZF.Potts
