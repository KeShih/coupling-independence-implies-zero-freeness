import CI2ZF.Potts.Transfer.PositiveSeparatorLog
import CI2ZF.Potts.Transfer.HardSeparatorStep
import CI2ZF.Potts.Transfer.HardAnalyticAverage

/-! The actual hard separator quotient: all defective terms are included,
their analytic correction is controlled, and a normalized logarithm of
the two partition responses is constructed on the entire hard disk. -/
namespace CI2ZF.Potts.Separator
open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C] [Nonempty C]

omit [Nonempty C] in
theorem partition_differentiable (I : PinningData (Vertex U S O) C) :
    Differentiable ℂ (partition I : ℂ → ℂ) := by
  have he : (partition I : ℂ → ℂ) = (pinningPolynomial I).eval := by
    funext z
    convert (pinningPolynomial_eval I z).symm using 1
    unfold partition pinningProductPartition weight pinningProductWeight
    congr 2
    exact Subsingleton.elim _ _
  rw [he]
  exact Polynomial.differentiable _

def hardSeparatorError (I : PinningData (Vertex U S O) C)
    (h : (S → C) → ℂ → ℂ) (z : ℂ) : ℂ :=
  hardEndpointError (insidePartition I z) (insidePartition I (0 : ℂ))
    (exteriorPartition I (0 : ℝ)) (fun ξ => h ξ z) (I.partition 0)

omit [Nonempty C] in
theorem hardSeparatorError_zero (I : PinningData (Vertex U S O) C)
    (h : (S → C) → ℂ → ℂ) : hardSeparatorError I h 0 = 0 := by
  simp [hardSeparatorError, hardEndpointError]

omit [Nonempty C] in
theorem hardSeparatorError_differentiable (I : PinningData (Vertex U S O) C)
    (h : (S → C) → ℂ → ℂ) (D : Set ℂ) (hh : ∀ ξ, DifferentiableOn ℂ (h ξ) D) :
    DifferentiableOn ℂ (hardSeparatorError I h) D := by
  unfold hardSeparatorError hardEndpointError
  apply DifferentiableOn.div_const
  apply DifferentiableOn.fun_sum
  intro ξ _
  have hd : DifferentiableOn ℂ (fun z : ℂ => insidePartition I z ξ) D := by
    have he : (fun z : ℂ => insidePartition I z ξ) = (insidePolynomial I ξ).eval := by
      funext z
      exact (insidePolynomial_eval I ξ z).symm
    rw [he]
    exact (Polynomial.differentiable _).differentiableOn
  exact ((hd.sub_const _).mul_const _).mul (hh ξ).cexp

def hardErrorCoefficient (q Δ N s : ℕ) (alpha : ℝ) : ℝ :=
  (q : ℝ) ^ (N + s) * ((q : ℝ) ^ Δ) ^ s * Real.exp (alpha * s)

omit [Fintype U] [Fintype S] [Fintype O] [Fintype C] [Nonempty C] in
theorem hardErrorCoefficient_nonneg (q Δ N s : ℕ) (alpha : ℝ) :
    0 ≤ hardErrorCoefficient q Δ N s alpha := by unfold hardErrorCoefficient; positivity

theorem hardSeparatorError_div_main_le (I : PinningData (Vertex U S O) C)
    (hi : Separates I) {Δ N s : ℕ} (hd : I.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (hU : Fintype.card U ≤ N) (hS : Fintype.card S ≤ s)
    (h : (S → C) → ℂ → ℂ) {alpha : ℝ} (ha : 0 ≤ alpha)
    (hphase : alpha * s ≤ (1 / 4 : ℝ)) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (hstep : ∀ ξ u c, ‖h (Function.update ξ u c) z - h ξ z‖ ≤ alpha) :
    ‖hardSeparatorError I h z /
      mainAverage (shellMarginal I 0 le_rfl (partition_zero_pos_of_succ_le I hd hq)) h z‖ ≤
      (3 / 2 : ℝ) * hardErrorCoefficient (Fintype.card C) Δ N s alpha * ‖z‖ := by
  obtain ⟨anchor, _, _, herr⟩ := exists_actual_hard_separator_error_bound
    I hi hd hq hU hS z hz (fun ξ => h ξ z) ha hstep
  have ho (ξ : S → C) : ‖h ξ z - h anchor z‖ ≤ (1 / 4 : ℝ) := by
    apply (norm_sub_le_card_of_coordinates (fun ξ => h ξ z) ha hstep ξ anchor).trans
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hS) ha).trans hphase
  exact defect_div_main_bound _ _ anchor ho (hardSeparatorError I h z)
    (hardErrorCoefficient_nonneg _ _ _ _ _) (norm_nonneg z) herr

/-- A hard separator pair admits a small analytic quotient logarithm.
The radius conditions are scalar budgets independent of the vertex names;
all anchor, weight-comparison and defective-polynomial inputs are proved. -/
theorem exists_hard_separator_quotient_log
    (I J : PinningData (Vertex U S O) C) (hi : Separates I) (hj : Separates J)
    (hcommon : ∀ ξ, exteriorData I ξ = exteriorData J ξ)
    {Δ N s : ℕ} (hdi : I.DegreeBound Δ) (hdj : J.DegreeBound Δ)
    (hq : Δ + 1 ≤ Fintype.card C) (hU : Fintype.card U ≤ N) (hS : Fintype.card S ≤ s)
    {r alpha delta : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 ≤ alpha)
    (hd : delta ∈ Set.Icc 0 (1 / 2 : ℝ)) (hphase : alpha * s ≤ (1 / 8 : ℝ))
    (hsmall : (3 / 2 : ℝ) * hardErrorCoefficient (Fintype.card C) Δ N s alpha * r ≤ delta)
    (h : (S → C) → ℂ → ℂ)
    (hh : ∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball (0 : ℂ) r))
    (hh0 : ∀ ξ, h ξ 0 = 0)
    (hexp : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ ξ, Complex.exp (h ξ z) =
      exteriorPartition I z ξ / exteriorPartition I (0 : ℂ) ξ)
    (hstep : ∀ z ∈ Metric.ball (0 : ℂ) r, ∀ ξ u c,
      ‖h (Function.update ξ u c) z - h ξ z‖ ≤ alpha) :
    let μ := shellMarginal I 0 le_rfl (partition_zero_pos_of_succ_le I hdi hq)
    let ν := shellMarginal J 0 le_rfl (partition_zero_pos_of_succ_le J hdj hq)
    (∀ z ∈ Metric.ball (0 : ℂ) r, partition I z ≠ 0 ∧ partition J z ≠ 0) ∧
    ∃ L : ℂ → ℂ, L 0 = 0 ∧ DifferentiableOn ℂ L (Metric.ball (0 : ℂ) r) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r, Complex.exp (L z) =
        (partition I z / partition I (0 : ℂ)) / (partition J z / partition J (0 : ℂ))) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r, ‖L z‖ ≤ 2 * alpha * W ham μ ν + 3 * delta := by
  dsimp only
  let μ := shellMarginal I 0 le_rfl (partition_zero_pos_of_succ_le I hdi hq)
  let ν := shellMarginal J 0 le_rfl (partition_zero_pos_of_succ_le J hdj hq)
  let E := hardSeparatorError I h
  let F := hardSeparatorError J h
  let K := hardErrorCoefficient (Fintype.card C) Δ N s alpha
  have hK : 0 ≤ K := hardErrorCoefficient_nonneg _ _ _ _ _
  have hzle (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) : ‖z‖ ≤ r := by
    exact (show ‖z‖ < r by simpa only [Metric.mem_ball, dist_zero_right] using hz).le
  have hbudget (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) : (3 / 2 : ℝ) * K * ‖z‖ ≤ delta :=
    (mul_le_mul_of_nonneg_left (hzle z hz) (by positivity)).trans hsmall
  have ho (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) (ξ ξ' : S → C) :
      ‖h ξ z - h ξ' z‖ ≤ (1 / 8 : ℝ) := by
    apply (norm_sub_le_card_of_coordinates (fun ξ => h ξ z) ha (hstep z hz) ξ ξ').trans
    exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hS) ha).trans hphase
  have hquarter : alpha * s ≤ (1 / 4 : ℝ) := hphase.trans (by norm_num)
  have heJ (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) (ξ : S → C) :
      Complex.exp (h ξ z) = exteriorPartition J z ξ / exteriorPartition J (0 : ℂ) ξ := by
    rw [hexp z hz, exteriorPartition_eq_of_data_eq I J hi hj hcommon,
      exteriorPartition_eq_of_data_eq I J hi hj hcommon]
  have hnz (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) : partition I z ≠ 0 ∧ partition J z ≠ 0 := by
    constructor
    · exact hard_separator_nonzero_of_exterior_responses I hi hdi hq hU hS z
        ((hzle z hz).trans hr1) _ ha (hexp z hz) (hstep z hz) hquarter ((hbudget z hz).trans hd.2)
    · exact hard_separator_nonzero_of_exterior_responses J hj hdj hq hU hS z
        ((hzle z hz).trans hr1) _ ha (heJ z hz) (hstep z hz) hquarter ((hbudget z hz).trans hd.2)
  obtain ⟨Li, hLi0, hLiD, hLiE⟩ := exists_normalized_log_on_ball (partition I) hr
    (partition_differentiable I).differentiableOn (fun z hz => (hnz z hz).1)
  obtain ⟨Lj, hLj0, hLjD, hLjE⟩ := exists_normalized_log_on_ball (partition J) hr
    (partition_differentiable J).differentiableOn (fun z hz => (hnz z hz).2)
  have hLi : DifferentiableOn ℂ Li (Metric.ball (0 : ℂ) r) :=
    fun z hz => (hLiD z hz).differentiableAt.differentiableWithinAt
  have hLj : DifferentiableOn ℂ Lj (Metric.ball (0 : ℂ) r) :=
    fun z hz => (hLjD z hz).differentiableAt.differentiableWithinAt
  have hL0 : Li 0 - Lj 0 = 0 := by rw [hLi0, hLj0, sub_self]
  have hLE (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
      Complex.exp (Li z - Lj z) =
        (partition I z / partition I (0 : ℂ)) / (partition J z / partition J (0 : ℂ)) := by
    rw [Complex.exp_sub, hLiE z hz, hLjE z hz]
  refine ⟨hnz, fun z => Li z - Lj z, hL0, hLi.sub hLj, hLE, ?_⟩
  apply continued_hard_average_log_bound μ ν h E F (fun _ => Classical.choice (inferInstance : Nonempty C))
    ham hr ha hd hh (hardSeparatorError_differentiable I h _ hh)
    (hardSeparatorError_differentiable J h _ hh) hh0
    (hardSeparatorError_zero I h) (hardSeparatorError_zero J h)
    (fun z hz => norm_sub_le_ham_of_coordinates (fun ξ => h ξ z) (hstep z hz)) ho
    (fun z hz => (hardSeparatorError_div_main_le I hi hdi hq hU hS h ha hquarter z
      ((hzle z hz).trans hr1) (hstep z hz)).trans (hbudget z hz))
    (fun z hz => (hardSeparatorError_div_main_le J hj hdj hq hU hS h ha hquarter z
      ((hzle z hz).trans hr1) (hstep z hz)).trans (hbudget z hz))
    (fun z => Li z - Lj z) (hLi.sub hLj) hL0
  intro z hz
  rw [hLE z hz, hard_response_eq_main_add_error I hi (partition_zero_pos_of_succ_le I hdi hq)
    (exteriorPartition_zero_pos I hi hdi hq) z _ (hexp z hz),
    hard_response_eq_main_add_error J hj (partition_zero_pos_of_succ_le J hdj hq) (exteriorPartition_zero_pos J hj hdj hq) z _ (heJ z hz)]
  rfl

end
end CI2ZF.Potts.Separator
