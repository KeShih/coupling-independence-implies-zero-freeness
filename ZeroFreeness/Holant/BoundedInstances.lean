import ZeroFreeness.Holant.ResidualModel
import ZeroFreeness.Holant.CoefficientBounds
import ZeroFreeness.Holant.LocalResponse

/-! Uniform local stability for actual normalized incidence instances.
The explicit radius depends only on the residual signature family, the
edge bound, the real box and the error budget. No bound on the number of
isolated vertices is required. -/
namespace ZeroFreeness.Holant
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq E]
set_option linter.unusedSectionVars false

@[simp] theorem signatureWeight_ofReal (inc : E → V → Prop) (g : V → ℕ → ℝ)
    (S : Finset E) : signatureWeight inc (fun v k => (g v k : ℂ)) S =
      ((signatureWeight (R := ℝ) inc g S : ℝ) : ℂ) := by
  simp [signatureWeight, Complex.ofReal_prod]

def instanceLocalRadius (F : Finset Signature) (N : ℕ) (R α : ℝ) : ℝ :=
  localRadius N (residualGrowthBound F ^ (2 * N)) R α

theorem instanceLocalRadius_pos (F : Finset Signature) (N : ℕ)
    {R α : ℝ} (hR : 0 ≤ R) (hα : 0 < α) : 0 < instanceLocalRadius F N R α :=
  localRadius_pos N (pow_nonneg (zero_le_one.trans (residualGrowthBound_one_le F)) _) hR hα

theorem normalized_instance_local_relative_bound (F : Finset Signature)
    (H : NormalizedInstance V E) {N : ℕ} {R α : ℝ}
    (hF : ∀ v, H.signature v ∈ residualFamily F)
    (htwo : ∀ e ∈ H.edges, (Finset.univ.filter (H.incidence e)).card = 2)
    (hN : H.edges.card ≤ N) (hR : 0 ≤ R) (hα : 0 < α)
    (x : E → ℝ) (z : E → ℂ) (hx : ∀ e ∈ H.edges, x e ∈ Set.Icc 0 R)
    (hz : ∀ e ∈ H.edges, ‖z e - (x e : ℂ)‖ < instanceLocalRadius F N R α) :
    ‖H.toInstance.complexPartition z /
      H.toInstance.complexPartition (fun e => (x e : ℂ)) - 1‖ ≤ α / 8 := by
  have hB : 0 ≤ residualGrowthBound F ^ (2 * N) :=
    pow_nonneg (zero_le_one.trans (residualGrowthBound_one_le F)) _
  let c : Finset E → ℂ := signatureWeight H.incidence (complexValues H.signature)
  have hc : ∀ S ⊆ H.edges, ‖c S‖ ≤ residualGrowthBound F ^ (2 * N) := by
    intro S hS
    have hnonneg : 0 ≤ signatureWeight H.incidence (realValues H.signature) S :=
      Finset.prod_nonneg (fun v _ => (H.signature v).nonneg _)
    have heq : c S = ((signatureWeight H.incidence (realValues H.signature) S : ℝ) : ℂ) :=
      signatureWeight_ofReal H.incidence (realValues H.signature) S
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact signatureWeight_le_growthBound_of_card F H.incidence H.signature hF S
      (fun e he => htwo e (hS he)) ((Finset.card_le_card hS).trans hN)
  have hge : 1 ≤ H.toInstance.realPartition x :=
    normalized_partition_ge_one H.incidence H.edges (realValues H.signature) x
      (fun v k => (H.signature v).nonneg k) H.normalized (fun e he => (hx e he).1)
  have hbase : 1 ≤ ‖multilinear H.edges c (fun e => (x e : ℂ))‖ := by
    change 1 ≤ ‖H.toInstance.complexPartition (fun e => (x e : ℂ))‖
    rw [H.toInstance.complexPartition_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hge)]
    exact hge
  exact local_polynomial_relative_bound H.edges c x z hN hB hR hα hc hx hz hbase

/-- The bounded-component zero-free radius is truly uniform over vertex
and edge types: it is the explicit number `instanceLocalRadius F N R (1/4)`. -/
theorem normalized_instance_local_nonzero (F : Finset Signature)
    (H : NormalizedInstance V E) {N : ℕ} {R : ℝ}
    (hF : ∀ v, H.signature v ∈ residualFamily F)
    (htwo : ∀ e ∈ H.edges, (Finset.univ.filter (H.incidence e)).card = 2)
    (hN : H.edges.card ≤ N) (hR : 0 ≤ R)
    (x : E → ℝ) (z : E → ℂ) (hx : ∀ e ∈ H.edges, x e ∈ Set.Icc 0 R)
    (hz : ∀ e ∈ H.edges, ‖z e - (x e : ℂ)‖ < instanceLocalRadius F N R (1 / 4)) :
    H.toInstance.complexPartition z ≠ 0 := by
  have hb := normalized_instance_local_relative_bound F H hF htwo hN hR
    (by norm_num : (0 : ℝ) < 1 / 4) x z hx hz
  intro hn
  rw [hn, zero_div, zero_sub, norm_neg, norm_one] at hb
  norm_num at hb

end
end ZeroFreeness.Holant
