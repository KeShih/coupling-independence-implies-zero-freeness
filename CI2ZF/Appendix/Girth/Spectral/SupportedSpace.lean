import CI2ZF.Appendix.Girth.Analysis.Covariance
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Supported finite L² as an actual Euclidean space

Functions are represented on positive-mass configurations by multiplying
by √μ. The resulting finite real inner product space has no null vectors
and no arbitrary choices of values at zero-mass configurations.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {Ω : Type*} [Fintype Ω]

abbrev SupportedSpace (μ : FinDist Ω) := EuclideanSpace ℝ {ω : Ω // 0 < μ.w ω}

def supportedEmbed (μ : FinDist Ω) : (Ω → ℝ) →ₗ[ℝ] SupportedSpace μ where
  toFun f := WithLp.toLp 2 (fun ω => Real.sqrt (μ.w ω.1) * f ω.1)
  map_add' f g := by
    ext ω
    simp only [WithLp.ofLp_add, Pi.add_apply]
    ring
  map_smul' a f := by
    ext ω
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def supportedRepresent (μ : FinDist Ω) : SupportedSpace μ →ₗ[ℝ] (Ω → ℝ) where
  toFun z ω := if h : 0 < μ.w ω then z ⟨ω, h⟩ / Real.sqrt (μ.w ω) else 0
  map_add' z w := by
    funext ω
    by_cases h : 0 < μ.w ω
    · simp only [h, dite_true, Pi.add_apply]
      rw [PiLp.add_apply]
      ring
    · simp only [h, dite_false, Pi.add_apply, zero_add]
  map_smul' a z := by
    funext ω
    by_cases h : 0 < μ.w ω
    · simp only [h, dite_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [PiLp.smul_apply]
      simp only [smul_eq_mul]
      ring
    · simp only [h, dite_false, Pi.smul_apply, smul_eq_mul, mul_zero, RingHom.id_apply]

theorem supportedEmbed_represent (μ : FinDist Ω) (z : SupportedSpace μ) :
    supportedEmbed μ (supportedRepresent μ z) = z := by
  ext ω
  change Real.sqrt (μ.w ω.1) * (if h : 0 < μ.w ω.1 then z ⟨ω.1, h⟩ / Real.sqrt (μ.w ω.1) else 0) = z ω
  rw [dif_pos ω.2]
  have hs : Real.sqrt (μ.w ω.1) ≠ 0 := (Real.sqrt_pos.mpr ω.2).ne'
  field_simp

theorem supportedEmbed_inner (μ : FinDist Ω) (f g : Ω → ℝ) :
    ⟪supportedEmbed μ f, supportedEmbed μ g⟫_ℝ = expectReal μ (fun ω => f ω * g ω) := by
  rw [PiLp.inner_apply]
  simp only [supportedEmbed, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply, Real.inner_apply]
  have he (ω : {ω : Ω // 0 < μ.w ω}) :
      (Real.sqrt (μ.w ω.1) * f ω.1) * (Real.sqrt (μ.w ω.1) * g ω.1) =
        μ.w ω.1 * (f ω.1 * g ω.1) := by
    calc
      _ = Real.sqrt (μ.w ω.1) ^ 2 * (f ω.1 * g ω.1) := by ring
      _ = _ := by rw [Real.sq_sqrt (μ.nonneg _)]
  simp_rw [he]
  rw [← Finset.sum_subtype (s := Finset.univ.filter (fun ω : Ω => 0 < μ.w ω))
    (fun ω => by simp) (fun ω => μ.w ω * (f ω * g ω))]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : 0 < μ.w ω
  · simp only [h, ite_true]
  · have hz : μ.w ω = 0 := by linarith [μ.nonneg ω]
    simp only [hz, zero_mul, lt_self_iff_false, ite_false]

theorem supportedEmbed_norm_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    ‖supportedEmbed μ f‖ ^ 2 = expectReal μ (fun ω => f ω ^ 2) := by
  rw [← real_inner_self_eq_norm_sq, supportedEmbed_inner]
  simp only [pow_two]

theorem supportedRepresent_inner (μ : FinDist Ω) (z w : SupportedSpace μ) :
    expectReal μ (fun ω => supportedRepresent μ z ω * supportedRepresent μ w ω) = ⟪z, w⟫_ℝ := by
  rw [← supportedEmbed_inner, supportedEmbed_represent, supportedEmbed_represent]

theorem supportedEmbed_eq_iff (μ : FinDist Ω) (f g : Ω → ℝ) :
    supportedEmbed μ f = supportedEmbed μ g ↔ ∀ ω, 0 < μ.w ω → f ω = g ω := by
  constructor
  · intro h ω hω
    have he := congrArg (fun z : SupportedSpace μ => z ⟨ω, hω⟩) h
    change Real.sqrt (μ.w ω) * f ω = Real.sqrt (μ.w ω) * g ω at he
    exact mul_left_cancel₀ (Real.sqrt_pos.mpr hω).ne' he
  · intro h
    ext ω
    change Real.sqrt (μ.w ω.1) * f ω.1 = Real.sqrt (μ.w ω.1) * g ω.1
    rw [h ω.1 ω.2]

end

end CI2ZF.Appendix.Girth
