import CI2ZF.LeeYang.LocalSupport
import CI2ZF.LeeYang.Separator
import CI2ZF.LeeYang.Analytic

/-! The supported-monomial estimates applied to actual field partitions
and actual separator coefficients. Hard-defective shell assignments are
identically zero in all fields and receive the constant zero logarithm. -/
namespace CI2ZF.LeeYang
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

section Partition
variable {V C : Type*} [Fintype V] [Fintype C]

def fieldSupport (I : PinningData V C) : Finset (V → C) :=
  Finset.univ.filter I.HardAdmissible

theorem fieldPartition_eq_supported (I : PinningData V C) (ℓ : V → C → ℂ) :
    fieldPartition I ℓ = supportedFieldPartition (fieldSupport I) id ℓ := by
  simp only [fieldPartition, fieldWeight, supportedFieldPartition, fieldSupport, Finset.sum_filter,
    id_eq]

theorem fieldSupport_nonempty_of_base_ne_zero (I : PinningData V C)
    (hbase : fieldPartition I oneField ≠ 0) : (fieldSupport I).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hz
  apply hbase
  rw [fieldPartition_eq_supported, hz]
  simp [supportedFieldPartition]

theorem fieldPartition_local_control (I : PinningData V C)
    (hbase : fieldPartition I oneField ≠ 0) {B : ℕ} (hB : Fintype.card V ≤ B)
    {α : ℝ} (hα : 0 < α) (ℓ : V → C → ℂ)
    (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ localFieldRadius B α) :
    ‖fieldPartition I ℓ / fieldPartition I oneField - 1‖ ≤ min (1 / 2) (α / 12) := by
  simpa [fieldPartition_eq_supported, supportedFieldPartition, oneField] using
    supportedFieldPartition_local_control (fieldSupport I) id
      (fieldSupport_nonempty_of_base_ne_zero I hbase) hB hα ℓ hℓ

theorem fieldLine_local_bound {B : ℕ} {α r : ℝ} (hr : r ≤ localFieldRadius B α)
    {d : V → C → ℂ} (hd : DirectionBound d) {z : ℂ} (hz : z ∈ Metric.ball 0 r)
    (v : V) (c : C) : ‖fieldLine d z v c - 1‖ ≤ localFieldRadius B α := by
  have hz' : ‖z‖ < r := by simpa using hz
  exact (fieldLine_dist_one_le hd z v c).trans (hz'.le.trans hr)

/-- The bounded-component estimate has a common radius for all graph
sizes up to `B`, all boundary data and all bounded field directions. -/
theorem bounded_fieldCurve_log_control (I : PinningData V C)
    (hbase : fieldPartition I oneField ≠ 0) {B : ℕ} (hB : Fintype.card V ≤ B)
    {α r : ℝ} (hα : 0 < α) (hr : r ≤ localFieldRadius B α)
    (d : V → C → ℂ) (hd : DirectionBound d) :
    principalResponseLog (fieldCurve I d) 0 0 = 0 ∧
      DifferentiableOn ℂ (principalResponseLog (fieldCurve I d) 0) (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, Complex.exp (principalResponseLog (fieldCurve I d) 0 z) =
        fieldCurve I d z / fieldCurve I d 0) ∧
      ∀ z ∈ Metric.ball 0 r, ‖principalResponseLog (fieldCurve I d) 0 z‖ ≤ α / 8 := by
  apply principalResponseLog_control
  · exact (fieldCurve_differentiable I d).differentiableOn
  · simpa only [fieldCurve, fieldLine_zero] using hbase
  · intro z hz
    change ‖fieldPartition I (fieldLine d z) / fieldPartition I (fieldLine d 0) - 1‖ ≤ _
    rw [fieldLine_zero]
    apply fieldPartition_local_control I hbase hB hα
    intro v c
    have hz' : ‖z‖ ≤ localFieldRadius B α := (by simpa using hz : ‖z‖ < r).le.trans hr
    simp only [fieldLine, add_sub_cancel_left, norm_mul]
    exact (mul_le_mul_of_nonneg_left (hd v c) (norm_nonneg z)).trans (by simpa using hz')

theorem bounded_fieldCurve_nonzero (I : PinningData V C)
    (hbase : fieldPartition I oneField ≠ 0) {B : ℕ} (hB : Fintype.card V ≤ B)
    {α r : ℝ} (hα : 0 < α) (hr : r ≤ localFieldRadius B α)
    (d : V → C → ℂ) (hd : DirectionBound d) : CurveNonzeroOn I d r := by
  have h := bounded_fieldCurve_log_control I hbase hB hα hr d hd
  intro z hz hz0
  have he := h.2.2.1 z hz
  rw [hz0, zero_div] at he
  exact Complex.exp_ne_zero _ he

end Partition

section Separator
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

def insideFieldSupport (I : PinningData (Vertex U S O) C) (ξ : S → C) : Finset (U → C) :=
  Finset.univ.filter (fun α => insideExponent I α ξ = 0)

theorem insideFieldWeight_eq_ite (I : PinningData (Vertex U S O) C)
    (ℓ : Vertex U S O → C → ℂ) (α : U → C) (ξ : S → C) :
    insideFieldWeight I ℓ α ξ = if insideExponent I α ξ = 0 then
      ∏ v : U ⊕ S, insideField ℓ v (Sum.elim α ξ v) else 0 := by
  simp only [insideFieldWeight, insideWeight_zero_eq]
  split_ifs <;> simp [insideField, Fintype.prod_sum_type]

theorem insideFieldPartition_eq_supported (I : PinningData (Vertex U S O) C)
    (ℓ : Vertex U S O → C → ℂ) (ξ : S → C) :
    insideFieldPartition I ℓ ξ = supportedFieldPartition (insideFieldSupport I ξ)
      (fun α => Sum.elim α ξ) (insideField ℓ) := by
  simp only [insideFieldPartition, supportedFieldPartition, insideFieldSupport, Finset.sum_filter,
    insideFieldWeight_eq_ite]

theorem insideFieldPartition_zero_of_zero_at_one (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (hz : insideFieldPartition I oneField ξ = 0) (ℓ : Vertex U S O → C → ℂ) :
    insideFieldPartition I ℓ ξ = 0 := by
  rw [insideFieldPartition_eq_supported, insideField_one] at hz
  rw [insideFieldPartition_eq_supported]
  exact supportedFieldPartition_zero_of_zero_at_one _ _ hz _

theorem insideFieldSupport_nonempty_of_base_ne_zero (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (hbase : insideFieldPartition I oneField ξ ≠ 0) :
    (insideFieldSupport I ξ).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hz
  apply hbase
  rw [insideFieldPartition_eq_supported, hz]
  simp [supportedFieldPartition]

theorem insideFieldPartition_local_control (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (hbase : insideFieldPartition I oneField ξ ≠ 0)
    {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B) {α : ℝ} (hα : 0 < α)
    (ℓ : Vertex U S O → C → ℂ)
    (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ localFieldRadius B α) :
    ‖insideFieldPartition I ℓ ξ / insideFieldPartition I oneField ξ - 1‖ ≤
      min (1 / 2) (α / 12) := by
  rw [insideFieldPartition_eq_supported, insideFieldPartition_eq_supported, insideField_one]
  exact supportedFieldPartition_local_control _ _
    (insideFieldSupport_nonempty_of_base_ne_zero I ξ hbase)
    (by simpa only [Fintype.card_sum] using hB) hα _ (fun v c => hℓ (insideEmbedding v) c)

/-- Defective assignments use the constant zero branch. -/
def insideFieldLog (I : PinningData (Vertex U S O) C)
    (ℓ : Vertex U S O → C → ℂ) (ξ : S → C) : ℂ :=
  if insideFieldPartition I oneField ξ = 0 then 0
  else Complex.log (insideFieldPartition I ℓ ξ / insideFieldPartition I oneField ξ)

@[simp] theorem insideFieldLog_one (I : PinningData (Vertex U S O) C) (ξ : S → C) :
    insideFieldLog I oneField ξ = 0 := by
  unfold insideFieldLog
  split_ifs with hz
  · rfl
  · simp

theorem insideFieldLog_bound (I : PinningData (Vertex U S O) C) (ξ : S → C)
    {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B) {α : ℝ} (hα : 0 < α)
    (ℓ : Vertex U S O → C → ℂ)
    (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ localFieldRadius B α) :
    ‖insideFieldLog I ℓ ξ‖ ≤ α / 8 := by
  unfold insideFieldLog
  split_ifs with hz
  · simp only [norm_zero]
    positivity
  · have hc := insideFieldPartition_local_control I ξ hz hB hα ℓ hℓ
    have hl := Complex.norm_log_one_add_half_le_self (hc.trans (min_le_left _ _))
    simp only [add_sub_cancel] at hl
    have ha := hc.trans (min_le_right _ _)
    linarith

/-- The multiplicative identity covers zero support without a division. -/
theorem insideFieldLog_exp_mul (I : PinningData (Vertex U S O) C) (ξ : S → C)
    {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B) {α : ℝ} (hα : 0 < α)
    (ℓ : Vertex U S O → C → ℂ)
    (hℓ : ∀ v c, ‖ℓ v c - 1‖ ≤ localFieldRadius B α) :
    insideFieldPartition I oneField ξ * Complex.exp (insideFieldLog I ℓ ξ) =
      insideFieldPartition I ℓ ξ := by
  by_cases hz : insideFieldPartition I oneField ξ = 0
  · rw [hz, zero_mul, insideFieldPartition_zero_of_zero_at_one I ξ hz ℓ]
  · have hc := insideFieldPartition_local_control I ξ hz hB hα ℓ hℓ
    have hslit := Complex.mem_slitPlane_of_norm_lt_one
      ((hc.trans (min_le_left _ _)).trans_lt (by norm_num))
    simp only [add_sub_cancel] at hslit
    rw [insideFieldLog, if_neg hz, Complex.exp_log (Complex.slitPlane_ne_zero hslit)]
    exact mul_div_cancel₀ _ hz

theorem insideFieldPartition_curve_differentiable (I : PinningData (Vertex U S O) C)
    (d : Vertex U S O → C → ℂ) (ξ : S → C) :
    Differentiable ℂ (fun z => insideFieldPartition I (fieldLine d z) ξ) := by
  have he : (fun z => insideFieldPartition I (fieldLine d z) ξ) =
      (fun z => supportedFieldPartition (insideFieldSupport I ξ)
        (fun α => Sum.elim α ξ) (insideField (fieldLine d z))) :=
    funext (fun z => insideFieldPartition_eq_supported I _ ξ)
  rw [he]
  unfold supportedFieldPartition
  apply Differentiable.fun_sum
  intro a _
  apply Differentiable.fun_finsetProd
  intro v _
  exact (differentiable_const (1 : ℂ)).add
    (differentiable_id.mul_const (d (insideEmbedding v) (Sum.elim a ξ v)))

theorem insideFieldLog_curve_differentiableOn (I : PinningData (Vertex U S O) C)
    (ξ : S → C) {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B)
    {α r : ℝ} (hα : 0 < α) (hr : r ≤ localFieldRadius B α)
    (d : Vertex U S O → C → ℂ) (hd : DirectionBound d) :
    DifferentiableOn ℂ (fun z => insideFieldLog I (fieldLine d z) ξ) (Metric.ball 0 r) := by
  unfold insideFieldLog
  split_ifs with hz
  · exact differentiableOn_const _
  · apply ((insideFieldPartition_curve_differentiable I d ξ).differentiableOn.div_const _).clog
    intro z hzr
    have hc := insideFieldPartition_local_control I ξ hz hB hα (fieldLine d z)
      (fieldLine_local_bound hr hd hzr)
    have hs := Complex.mem_slitPlane_of_norm_lt_one
      ((hc.trans (min_le_left _ _)).trans_lt (by norm_num))
    simpa only [add_sub_cancel] using hs

@[simp] theorem insideFieldLog_curve_zero (I : PinningData (Vertex U S O) C)
    (d : Vertex U S O → C → ℂ) (ξ : S → C) :
    insideFieldLog I (fieldLine d 0) ξ = 0 := by rw [fieldLine_zero, insideFieldLog_one]

theorem insideFieldLog_curve_bound (I : PinningData (Vertex U S O) C)
    (ξ : S → C) {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B)
    {α r : ℝ} (hα : 0 < α) (hr : r ≤ localFieldRadius B α)
    (d : Vertex U S O → C → ℂ) (hd : DirectionBound d)
    {z : ℂ} (hz : z ∈ Metric.ball 0 r) :
    ‖insideFieldLog I (fieldLine d z) ξ‖ ≤ α / 8 :=
  insideFieldLog_bound I ξ hB hα _ (fieldLine_local_bound hr hd hz)

theorem insideFieldLog_curve_exp_mul (I : PinningData (Vertex U S O) C)
    (ξ : S → C) {B : ℕ} (hB : Fintype.card U + Fintype.card S ≤ B)
    {α r : ℝ} (hα : 0 < α) (hr : r ≤ localFieldRadius B α)
    (d : Vertex U S O → C → ℂ) (hd : DirectionBound d)
    {z : ℂ} (hz : z ∈ Metric.ball 0 r) :
    insideFieldPartition I oneField ξ * Complex.exp (insideFieldLog I (fieldLine d z) ξ) =
      insideFieldPartition I (fieldLine d z) ξ :=
  insideFieldLog_exp_mul I ξ hB hα _ (fieldLine_local_bound hr hd hz)

end Separator
end
end CI2ZF.LeeYang
