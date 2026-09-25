import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Uniform local stability and endpoint patching

The finite-family compactness argument below supplies the analytic uniformity
step in the local-model argument of `main.tex:945`. It does not assert that
all graph instances are a finite family: the combinatorial reduction to a
bounded family is proved separately (`Potts.Transfer.BoundedLocalFamily`).

The final theorem is the endpoint-patching step of `main.tex:1255`. Its two
nonvanishing inputs are explicit here; `bounded_degree_potts_transfer`
derives them from coupling independence.
-/

namespace ZeroFreeness

open Set Metric

noncomputable section

/-- A finite family of continuous functions, nonzero on a compact set, has a
common relative perturbation bound near every point of that set. The radius
is chosen before the index and the base point. -/
theorem finite_family_relative_stability {ι : Type*} [Finite ι]
    (f : ι → ℂ → ℂ) (hf : ∀ i, Continuous (f i))
    (K : Set ℂ) (hK : IsCompact K)
    (hnz : ∀ i, ∀ x ∈ K, f i x ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ i, ∀ x ∈ K, ∀ z : ℂ, dist z x < ε →
      ‖f i z / f i x - 1‖ < η := by
  let D : Set (ℂ × ℂ) := (fun x : ℂ => (x, x)) '' K
  let U : Set (ℂ × ℂ) := ⋂ i, {p | ‖f i p.2 - f i p.1‖ < η * ‖f i p.1‖}
  have hD : IsCompact D := hK.image (continuous_id.prodMk continuous_id)
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro i
    exact isOpen_lt ((hf i).comp continuous_snd |>.sub ((hf i).comp continuous_fst) |>.norm)
      (continuous_const.mul ((hf i).comp continuous_fst |>.norm))
  have hDU : D ⊆ U := by
    rintro p ⟨x, hx, rfl⟩
    apply mem_iInter.mpr
    intro i
    change ‖f i x - f i x‖ < η * ‖f i x‖
    simpa using mul_pos hη (norm_pos_iff.mpr (hnz i x hx))
  obtain ⟨ε, hε, hnear⟩ := hD.exists_thickening_subset_open hU hDU
  refine ⟨ε, hε, ?_⟩
  intro i x hx z hzx
  have hp : (x, z) ∈ thickening ε D := by
    apply mem_thickening_iff.mpr
    refine ⟨(x, x), ⟨x, hx, rfl⟩, ?_⟩
    simpa only [dist_prod_same_left] using hzx
  have hb : ‖f i z - f i x‖ < η * ‖f i x‖ :=
    mem_iInter.mp (hnear hp) i
  rw [div_sub_one (hnz i x hx), norm_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr (hnz i x hx))).mpr hb

/-- Nonvanishing for a finite family follows from relative stability with
budget one. This includes empty index sets and empty compact sets. -/
theorem finite_family_zero_free {ι : Type*} [Finite ι]
    (f : ι → ℂ → ℂ) (hf : ∀ i, Continuous (f i))
    (K : Set ℂ) (hK : IsCompact K)
    (hnz : ∀ i, ∀ x ∈ K, f i x ≠ 0) :
    ∃ ε > 0, ∀ i, ∀ z ∈ thickening ε K, f i z ≠ 0 := by
  obtain ⟨ε, hε, hrel⟩ := finite_family_relative_stability f hf K hK hnz
    (η := 1) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro i z hz heq
  obtain ⟨x, hx, hzx⟩ := mem_thickening_iff.mp hz
  have h := hrel i x hx z hzx
  simp [heq] at h

/-- The finite-polynomial form used for bounded local Potts systems. -/
theorem finite_polynomial_relative_stability {ι : Type*} [Finite ι]
    (p : ι → Polynomial ℂ) (K : Set ℂ) (hK : IsCompact K)
    (hnz : ∀ i, ∀ x ∈ K, (p i).eval x ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ i, ∀ x ∈ K, ∀ z : ℂ, dist z x < ε →
      ‖(p i).eval z / (p i).eval x - 1‖ < η :=
  finite_family_relative_stability (fun i z => (p i).eval z)
    (fun i => (p i).continuous) K hK hnz hη

/-- The embedded antiferromagnetic real interval. -/
def pottsInterval : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) 1

theorem pottsInterval_isCompact : IsCompact pottsInterval :=
  isCompact_Icc.image Complex.continuous_ofReal

/-- Patch a uniform disk at zero with uniform positive-base neighborhoods.
The index type can be infinite, e.g. all bounded-degree graph/pinning
instances. No uniformity as the positive base approaches zero is assumed. -/
theorem patch_endpoint_and_positive {ι : Type*} (F : ι → ℂ → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hzero : ∀ i, ∀ z : ℂ, ‖z‖ < ρ → F i z ≠ 0)
    (hpositive : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∃ ε > 0, ∀ i, ∀ x ∈ Icc δ 1, ∀ z : ℂ,
        dist z (x : ℂ) < ε → F i z ≠ 0) :
    ∃ ε > 0, ∀ i, ∀ z ∈ thickening ε pottsInterval, F i z ≠ 0 := by
  let δ : ℝ := min (1 / 2) (ρ / 4)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδρ : δ ≤ ρ / 4 := min_le_right _ _
  obtain ⟨εp, hεp, hp⟩ := hpositive δ hδ (by linarith)
  refine ⟨min εp δ, lt_min hεp hδ, ?_⟩
  intro i z hz
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
  obtain ⟨x, hx, rfl⟩ := hw
  by_cases hxd : x ≤ δ
  · apply hzero i z
    have hdist : dist z (x : ℂ) < δ := lt_of_lt_of_le hzw (min_le_right _ _)
    have hnorm : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    have htri : ‖z‖ ≤ dist z (x : ℂ) + ‖(x : ℂ)‖ := by
      simpa only [dist_zero_right] using dist_triangle z (x : ℂ) 0
    rw [hnorm] at htri
    linarith
  · exact hp i x ⟨le_of_not_ge hxd, hx.2⟩ z
      (lt_of_lt_of_le hzw (min_le_left _ _))

end
end ZeroFreeness
