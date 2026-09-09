import CI2ZF.Analysis.AnalyticComplexAverage
import CI2ZF.Potts.Transfer.HardMainPerturbation

/-! Activity-variable continuation of the hard main average plus defects.
The correction logarithms are analytic on the whole disk; equality to an
arbitrary normalized analytic response branch is proved by uniqueness. -/
namespace CI2ZF
open PottsCI PottsCI.FinDist
noncomputable section
variable {S : Type*} [Fintype S]

def mainAverage (μ : FinDist S) (h : S → ℂ → ℂ) (z : ℂ) : ℂ :=
  expectComplex μ (fun i => Complex.exp (h i z))

def errorCorrection (μ : FinDist S) (h : S → ℂ → ℂ) (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.log (1 + E z / mainAverage μ h z)

theorem mainAverage_differentiable (μ : FinDist S) (h : S → ℂ → ℂ) (D : Set ℂ)
    (hh : ∀ i, DifferentiableOn ℂ (h i) D) :
    DifferentiableOn ℂ (mainAverage μ h) D := by
  unfold mainAverage expectComplex
  exact DifferentiableOn.fun_sum fun i _ => (hh i).cexp.const_mul (μ.w i : ℂ)

theorem errorCorrection_differentiable (μ : FinDist S) (h : S → ℂ → ℂ)
    (E : ℂ → ℂ) (anchor : S) (D : Set ℂ)
    (hh : ∀ i, DifferentiableOn ℂ (h i) D) (hE : DifferentiableOn ℂ E D)
    (hosc : ∀ z ∈ D, ∀ i, ‖h i z - h anchor z‖ ≤ (1 / 4 : ℝ))
    (herror : ∀ z ∈ D, ‖E z / mainAverage μ h z‖ ≤ (1 / 2 : ℝ)) :
    DifferentiableOn ℂ (errorCorrection μ h E) D := by
  apply DifferentiableOn.clog
  · exact (differentiableOn_const 1).add
      (hE.div (mainAverage_differentiable μ h D hh)
        (fun z hz => main_average_ne_zero μ _ anchor (hosc z hz)))
  · intro z hz
    exact Complex.mem_slitPlane_of_norm_lt_one ((herror z hz).trans_lt (by norm_num))

theorem errorCorrection_exp (μ : FinDist S) (h : S → ℂ → ℂ)
    (E : ℂ → ℂ) (anchor : S) (z : ℂ)
    (hosc : ∀ i, ‖h i z - h anchor z‖ ≤ (1 / 4 : ℝ))
    (herror : ‖E z / mainAverage μ h z‖ ≤ (1 / 2 : ℝ)) :
    Complex.exp (errorCorrection μ h E z) =
      (mainAverage μ h z + E z) / mainAverage μ h z := by
  have hm : mainAverage μ h z ≠ 0 := main_average_ne_zero μ _ anchor hosc
  have hs := Complex.mem_slitPlane_of_norm_lt_one (herror.trans_lt (by norm_num))
  rw [errorCorrection, Complex.exp_log (Complex.slitPlane_ne_zero hs)]
  rw [add_div, div_self hm]

/-- The hard analogue of the paper's complex-average estimate. `delta`
controls the two actual additive defects relative to their main terms. -/
theorem continued_hard_average_log_bound (μ ν : FinDist S) (h : S → ℂ → ℂ)
    (E F : ℂ → ℂ) (anchor : S) (d : S → S → ℝ)
    {x : ℂ} {r A delta : ℝ} (hr : 0 < r) (hA : 0 ≤ A)
    (hd : delta ∈ Set.Icc 0 (1 / 2 : ℝ))
    (hh : ∀ i, DifferentiableOn ℂ (h i) (Metric.ball x r))
    (hE : DifferentiableOn ℂ E (Metric.ball x r))
    (hF : DifferentiableOn ℂ F (Metric.ball x r))
    (hh0 : ∀ i, h i x = 0) (hE0 : E x = 0) (hF0 : F x = 0)
    (hlip : ∀ z ∈ Metric.ball x r, ∀ i j, ‖h i z - h j z‖ ≤ A * d i j)
    (hosc : ∀ z ∈ Metric.ball x r, ∀ i j, ‖h i z - h j z‖ ≤ (1 / 8 : ℝ))
    (hbE : ∀ z ∈ Metric.ball x r, ‖E z / mainAverage μ h z‖ ≤ delta)
    (hbF : ∀ z ∈ Metric.ball x r, ‖F z / mainAverage ν h z‖ ≤ delta)
    (L : ℂ → ℂ) (hL : DifferentiableOn ℂ L (Metric.ball x r)) (hL0 : L x = 0)
    (hexp : ∀ z ∈ Metric.ball x r, Complex.exp (L z) =
      (mainAverage μ h z + E z) / (mainAverage ν h z + F z)) :
    ∀ z ∈ Metric.ball x r, ‖L z‖ ≤ 2 * A * W d μ ν + 3 * delta := by
  have ho (z : ℂ) (hz : z ∈ Metric.ball x r) (i : S) :
      ‖h i z - h anchor z‖ ≤ (1 / 4 : ℝ) := (hosc z hz i anchor).trans (by norm_num)
  have hhalfE (z : ℂ) (hz : z ∈ Metric.ball x r) :
      ‖E z / mainAverage μ h z‖ ≤ (1 / 2 : ℝ) := (hbE z hz).trans hd.2
  have hhalfF (z : ℂ) (hz : z ∈ Metric.ball x r) :
      ‖F z / mainAverage ν h z‖ ≤ (1 / 2 : ℝ) := (hbF z hz).trans hd.2
  let k := errorCorrection μ h E
  let l := errorCorrection ν h F
  have hk := errorCorrection_differentiable μ h E anchor _ hh hE ho hhalfE
  have hl := errorCorrection_differentiable ν h F anchor _ hh hF ho hhalfF
  have hk0 : k x = 0 := by simp [k, errorCorrection, hE0]
  have hl0 : l x = 0 := by simp [l, errorCorrection, hF0]
  have hbranch := continued_average_log_bound μ ν h (fun _ _ => 0) (fun _ _ => 0)
    anchor d hr hA (show (0 : ℝ) ∈ Set.Icc 0 (1 / 8 : ℝ) by norm_num)
    hh (fun _ => differentiableOn_const 0) (fun _ => differentiableOn_const 0)
    hh0 (fun _ => rfl) (fun _ => rfl) hlip hosc
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    (fun z => L z - k z + l z) ((hL.sub hk).add hl)
    (by rw [hL0, hk0, hl0]; ring) ?_
  · intro z hz
    have hbase := hbranch z hz
    simp only [mul_zero, add_zero] at hbase
    have hkbound : ‖k z‖ ≤ (3 / 2 : ℝ) * delta :=
      (Complex.norm_log_one_add_half_le_self (hhalfE z hz)).trans
        (mul_le_mul_of_nonneg_left (hbE z hz) (by norm_num))
    have hlbound : ‖l z‖ ≤ (3 / 2 : ℝ) * delta :=
      (Complex.norm_log_one_add_half_le_self (hhalfF z hz)).trans
        (mul_le_mul_of_nonneg_left (hbF z hz) (by norm_num))
    have hdecomp : L z = (L z - k z + l z) + k z - l z := by ring
    calc
      ‖L z‖ = ‖(L z - k z + l z) + k z - l z‖ := congrArg norm hdecomp
      _ ≤ ‖L z - k z + l z‖ + ‖k z‖ + ‖l z‖ :=
        by have ht := norm_sub_le ((L z - k z + l z) + k z) (l z)
           have ha := norm_add_le (L z - k z + l z) (k z)
           linarith
      _ ≤ 2 * A * W d μ ν + 3 * delta := by linarith
  · intro z hz
    have hm : mainAverage μ h z ≠ 0 := main_average_ne_zero μ _ anchor (ho z hz)
    have hn : mainAverage ν h z ≠ 0 := main_average_ne_zero ν _ anchor (ho z hz)
    have he := errorCorrection_exp μ h E anchor z (ho z hz) (hhalfE z hz)
    have hf := errorCorrection_exp ν h F anchor z (ho z hz) (hhalfF z hz)
    have hemp : mainAverage μ h z + E z ≠ 0 := by
      have hne := Complex.exp_ne_zero (k z)
      rw [he] at hne
      exact fun hzero => hne (by rw [hzero, zero_div])
    have hfnp : mainAverage ν h z + F z ≠ 0 := by
      have hne := Complex.exp_ne_zero (l z)
      rw [hf] at hne
      exact fun hzero => hne (by rw [hzero, zero_div])
    rw [Complex.exp_add, Complex.exp_sub, hexp z hz]
    change ((mainAverage μ h z + E z) / (mainAverage ν h z + F z)) /
      Complex.exp (errorCorrection μ h E z) * Complex.exp (errorCorrection ν h F z) = _
    rw [he, hf]
    simp only [add_zero]
    change _ = mainAverage μ h z / mainAverage ν h z
    field_simp [hm, hn, hemp, hfnp]

end
end CI2ZF
