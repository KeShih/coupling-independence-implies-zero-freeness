import CI2ZF.Holant.InstanceSeparator
import CI2ZF.Holant.AnalyticContinuation
import CI2ZF.Holant.Paths
import CI2ZF.Holant.CouplingTransport

/-! The additive analytic comparison applied to an actual root separator.
The local coefficient may vanish at the real base; it is never a denominator. -/
namespace CI2ZF.Holant
open PottsCI PottsCI.FinDist HolantCoupling Set Metric
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
set_option linter.unusedSectionVars false

theorem norm_exponential_le_anchor (h a : ℂ) (ha : ‖h - a‖ ≤ (1 / 8 : ℝ)) :
    ‖Complex.exp h‖ ≤ (4 / 3 : ℝ) * ‖Complex.exp a‖ := by
  have hb := norm_exp_sub_one_le_third (h - a) (ha.trans (by norm_num))
  have ht := norm_sub_norm_le (Complex.exp (h - a)) (1 : ℂ)
  rw [norm_one] at ht
  have hh : ‖Complex.exp (h - a)‖ ≤ (4 / 3 : ℝ) := by linarith
  have heq : Complex.exp h = Complex.exp (h - a) * Complex.exp a := by
    rw [← Complex.exp_add, sub_add_cancel]
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)

namespace RootSeparator
variable {H : NormalizedInstance V E} {e : E}

theorem localError_bound (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (ξ : P.State) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) (z : E → ℂ)
    (h : P.State → ℂ) {β : ℝ} (hβ : 0 ≤ β)
    (hD : ‖P.coefficientComplex he hs b ξ z - (P.coefficientReal he hs b ξ x : ℂ)‖ ≤ β)
    (hdom : (P.exteriorInstance ξ).toInstance.realPartition x ≤
      (P.child he hs b).toInstance.realPartition x)
    (hexp : Complex.exp (h ξ) = (P.exteriorInstance ξ).toInstance.complexPartition z /
      ((P.exteriorInstance ξ).toInstance.realPartition x : ℂ))
    (hosc : ‖h ξ - h P.emptyState‖ ≤ (1 / 8 : ℝ)) :
    ‖P.localError he hs b ξ x z‖ ≤ β * (4 / 3) * ‖Complex.exp (h P.emptyState)‖ := by
  let Q := (P.exteriorInstance ξ).toInstance.realPartition x
  let Z := (P.child he hs b).toInstance.realPartition x
  have hQ : 0 < Q := P.exterior_real_pos ξ x hx
  have hZ : 0 < Z := P.child_real_pos he hs b x hx
  have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have heq : (P.exteriorInstance ξ).toInstance.complexPartition z = Complex.exp (h ξ) * (Q : ℂ) :=
    (eq_div_iff hQc).mp hexp |>.symm
  have hh := norm_exponential_le_anchor (h ξ) (h P.emptyState) hosc
  unfold localError
  rw [heq, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  have hr : Q / Z ≤ 1 := (div_le_one hZ).mpr hdom
  have hr0 : 0 ≤ Q / Z := (div_pos hQ hZ).le
  calc
    _ = ‖P.coefficientComplex he hs b ξ z - (P.coefficientReal he hs b ξ x : ℂ)‖ *
        (Q / Z) * ‖Complex.exp (h ξ)‖ := by ring
    _ ≤ β * 1 * ((4 / 3) * ‖Complex.exp (h P.emptyState)‖) :=
      mul_le_mul (mul_le_mul hD hr hr0 hβ) hh (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem totalError_bound (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) (z : E → ℂ)
    (h : P.State → ℂ) {β δ : ℝ} (hβ : 0 ≤ β)
    (hbudget : (Fintype.card P.State : ℝ) * β * (4 / 3) ≤ δ)
    (hD : ∀ ξ, ‖P.coefficientComplex he hs b ξ z - (P.coefficientReal he hs b ξ x : ℂ)‖ ≤ β)
    (hdom : ∀ ξ, (P.exteriorInstance ξ).toInstance.realPartition x ≤
      (P.child he hs b).toInstance.realPartition x)
    (hexp : ∀ ξ, Complex.exp (h ξ) = (P.exteriorInstance ξ).toInstance.complexPartition z /
      ((P.exteriorInstance ξ).toInstance.realPartition x : ℂ))
    (hosc : ∀ ξ, ‖h ξ - h P.emptyState‖ ≤ (1 / 8 : ℝ)) :
    ‖∑ ξ, P.localError he hs b ξ x z‖ ≤ δ * ‖Complex.exp (h P.emptyState)‖ := by
  calc
    _ ≤ ∑ ξ, ‖P.localError he hs b ξ x z‖ := norm_sum_le _ _
    _ ≤ ∑ _ξ : P.State, β * (4 / 3) * ‖Complex.exp (h P.emptyState)‖ :=
      Finset.sum_le_sum fun ξ _ => P.localError_bound he hs b ξ x hx z h hβ
        (hD ξ) (hdom ξ) (hexp ξ) (hosc ξ)
    _ = ((Fintype.card P.State : ℝ) * β * (4 / 3)) * ‖Complex.exp (h P.emptyState)‖ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (norm_nonneg _)

/-- The actual separator closes the continued edge response once smaller
instances supply the exterior logarithms and the real coupling selects a
shell. The errors are estimated from the actual finite coefficients. -/
theorem response_bound_of_exterior_logs (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) {R ε α β δ : ℝ} (p : ActivityPath H.edges R ε)
    (hα : 0 < α) (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 2 / 9)
    (hδbudget : δ ≤ α / 16)
    (hbudget : (Fintype.card P.State : ℝ) * β * (4 / 3) ≤ δ)
    (h : P.State → ℂ → ℂ)
    (hh : ∀ ξ, DifferentiableOn ℂ (h ξ) (ball 0 p.radius))
    (hh0 : ∀ ξ, h ξ 0 = 0)
    (hexp : ∀ t ∈ ball 0 p.radius, ∀ ξ, Complex.exp (h ξ t) =
      (P.exteriorInstance ξ).toInstance.complexPartition (p.activity t) /
        ((P.exteriorInstance ξ).toInstance.realPartition p.base : ℂ))
    (hlip : ∀ t ∈ ball 0 p.radius, ∀ ξ ζ,
      ‖h ξ t - h ζ t‖ ≤ α * subsetHam ξ.val ζ.val)
    (hosc : ∀ t ∈ ball 0 p.radius, ∀ ξ ζ, ‖h ξ t - h ζ t‖ ≤ (1 / 8 : ℝ))
    (hD : ∀ b t, t ∈ ball 0 p.radius → ∀ ξ,
      ‖P.coefficientComplex he hs b ξ (p.activity t) -
        (P.coefficientReal he hs b ξ p.base : ℂ)‖ ≤ β)
    (hdom : ∀ b ξ, (P.exteriorInstance ξ).toInstance.realPartition p.base ≤
      (P.child he hs b).toInstance.realPartition p.base)
    (hW : W (fun ξ ζ : P.State => subsetHam ξ.val ζ.val)
      (P.law he hs true p.base (fun a ha => (p.realBox a (Finset.mem_of_mem_erase ha)).1))
      (P.law he hs false p.base (fun a ha => (p.realBox a (Finset.mem_of_mem_erase ha)).1)) ≤ 1 / 64) :
    ResponseBound H e he hs p α := by
  let hx : ∀ a ∈ H.edges.erase e, 0 ≤ p.base a :=
    fun a ha => (p.realBox a (Finset.mem_of_mem_erase ha)).1
  let μ (b : Bool) := P.law he hs b p.base hx
  let Z (b : Bool) (t : ℂ) := (P.child he hs b).toInstance.complexPartition (p.activity t)
  let X (b : Bool) := (P.child he hs b).toInstance.realPartition p.base
  let err (b : Bool) (t : ℂ) := Z b t / (X b : ℂ) -
    exponentialAverage (μ b) (fun ξ => h ξ t)
  have hX (b : Bool) : 0 < X b := P.child_real_pos he hs b p.base hx
  have hXc (b : Bool) : (X b : ℂ) ≠ 0 := by exact_mod_cast (hX b).ne'
  have hsubset (b : Bool) : (P.child he hs b).edges ⊆ H.edges := by
    cases b <;> exact Finset.erase_subset e H.edges
  have hZdiff (b : Bool) : DifferentiableOn ℂ (Z b) (ball 0 p.radius) :=
    (p.restrict (hsubset b)).instance_differentiable (P.child he hs b).toInstance
  have hZ0 (b : Bool) : Z b 0 = (X b : ℂ) :=
    (p.restrict (hsubset b)).instance_at_zero (P.child he hs b).toInstance
  have herrdiff (b : Bool) : DifferentiableOn ℂ (err b) (ball 0 p.radius) :=
    (hZdiff b |>.div_const (X b : ℂ)).sub
      (exponentialAverage_differentiable (μ b) h (ball 0 p.radius) hh)
  have herr0 (b : Bool) : err b 0 = 0 := by
    simp [err, hZ0, hXc, exponentialAverage, hh0]
  have herrEq (b : Bool) (t : ℂ) (ht : t ∈ ball 0 p.radius) :
      err b t = ∑ ξ, P.localError he hs b ξ p.base (p.activity t) := by
    have heq := P.response_eq_average_add_error he hs b p.base hx (p.activity t)
    simp_rw [← hexp t ht] at heq
    change Z b t / (X b : ℂ) = exponentialAverage (μ b) (fun ξ => h ξ t) + _ at heq
    dsimp only [err]
    rw [heq, add_sub_cancel_left]
  have herrbound (b : Bool) (t : ℂ) (ht : t ∈ ball 0 p.radius) :
      ‖err b t‖ ≤ δ * ‖Complex.exp (h P.emptyState t)‖ := by
    rw [herrEq b t ht]
    exact P.totalError_bound he hs b p.base hx (p.activity t) (fun ξ => h ξ t) hβ hbudget
      (hD b t ht) (hdom b) (hexp t ht) (fun ξ => hosc t ht ξ P.emptyState)
  intro L hL hL0 hLexp t ht
  have hb := continued_additive_response (μ true) (μ false) h P.emptyState
    (err true) (err false) L (fun ξ ζ : P.State => subsetHam ξ.val ζ.val)
    p.radius_pos hα hδ hδsmall hδbudget hW hh (herrdiff true) (herrdiff false) hL
    hh0 (herr0 true) (herr0 false) hL0 hlip hosc (herrbound true) (herrbound false)
    (by
      intro u hu
      have heq (b : Bool) : exponentialAverage (μ b) (fun ξ => h ξ u) + err b u = Z b u / (X b : ℂ) := by
        dsimp [err]
        ring
      rw [heq true, heq false]
      exact hLexp u hu) t ht
  exact hb.le

end RootSeparator
end
end CI2ZF.Holant
