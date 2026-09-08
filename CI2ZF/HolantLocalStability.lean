import CI2ZF.LocalStability
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-! Multivariate compactness and the product domains in the Holant theorem.
The radius in `finite_family_relative_stability` is uniform over a finite
family and a compact real box, including its zero-activity faces. -/

namespace CI2ZF.Holant
open Set Metric
noncomputable section

/-- The diagonal-neighborhood compactness argument in any metric domain. -/
theorem finite_family_relative_stability {ι X : Type*} [Finite ι] [MetricSpace X]
    (f : ι → X → ℂ) (hf : ∀ i, Continuous (f i))
    (K : Set X) (hK : IsCompact K)
    (hnz : ∀ i, ∀ x ∈ K, f i x ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ i, ∀ x ∈ K, ∀ z, dist z x < ε →
      ‖f i z / f i x - 1‖ < η := by
  let D : Set (X × X) := (fun x : X => (x, x)) '' K
  let U : Set (X × X) := ⋂ i, {p | ‖f i p.2 - f i p.1‖ < η * ‖f i p.1‖}
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
    exact ⟨(x, x), ⟨x, hx, rfl⟩, by simpa only [dist_prod_same_left] using hzx⟩
  have hb : ‖f i z - f i x‖ < η * ‖f i x‖ := mem_iInter.mp (hnear hp) i
  rw [div_sub_one (hnz i x hx), norm_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr (hnz i x hx))).mpr hb

def realInterval (a b : ℝ) : Set ℂ := Complex.ofReal '' Icc a b

def realBox (E : Type*) (a b : ℝ) : Set (E → ℂ) :=
  Set.pi Set.univ (fun _ => realInterval a b)

/-- Cartesian power is taken before any union over the common upper bound. -/
def polytube (E : Type*) (ε a b : ℝ) : Set (E → ℂ) :=
  Set.pi Set.univ (fun _ => thickening ε (realInterval a b))

theorem realInterval_isCompact (a b : ℝ) : IsCompact (realInterval a b) :=
  isCompact_Icc.image Complex.continuous_ofReal

theorem realBox_isCompact (E : Type*) (a b : ℝ) : IsCompact (realBox E a b) := by
  exact isCompact_univ_pi fun _ => realInterval_isCompact a b

theorem polytube_isOpen (E : Type*) [Finite E] (ε a b : ℝ) :
    IsOpen (polytube E ε a b) := by
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_thickening

theorem mem_polytube_iff {E : Type*} (z : E → ℂ) (ε a b : ℝ) :
    z ∈ polytube E ε a b ↔
      ∃ x : E → ℝ, (∀ e, x e ∈ Icc a b) ∧ (∀ e, ‖z e - (x e : ℂ)‖ < ε) := by
  constructor
  · intro hz
    have hx : ∀ e, ∃ x : ℝ, x ∈ Icc a b ∧ ‖z e - (x : ℂ)‖ < ε := by
      intro e
      obtain ⟨w, ⟨x, hx, rfl⟩, hw⟩ := mem_thickening_iff.mp (hz e (mem_univ e))
      exact ⟨x, hx, by simpa [dist_eq_norm] using hw⟩
    choose x hx hzx using hx
    exact ⟨x, hx, hzx⟩
  · rintro ⟨x, hx, hzx⟩ e _
    apply mem_thickening_iff.mpr
    exact ⟨(x e : ℂ), ⟨x e, hx e, rfl⟩, by simpa [dist_eq_norm] using hzx e⟩

theorem finite_family_box_stability {ι E : Type*} [Finite ι] [Fintype E]
    (f : ι → (E → ℂ) → ℂ) (hf : ∀ i, Continuous (f i)) (a b : ℝ)
    (hnz : ∀ i, ∀ x : E → ℝ, (∀ e, x e ∈ Icc a b) → f i (fun e => (x e : ℂ)) ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ i, ∀ x : E → ℝ, (∀ e, x e ∈ Icc a b) →
      ∀ z : E → ℂ, (∀ e, ‖z e - (x e : ℂ)‖ < ε) →
        ‖f i z / f i (fun e => (x e : ℂ)) - 1‖ < η := by
  have hnz' : ∀ i, ∀ x ∈ realBox E a b, f i x ≠ 0 := by
    intro i x hx
    have hs : ∀ e, ∃ t : ℝ, t ∈ Icc a b ∧ (t : ℂ) = x e := fun e => hx e (mem_univ e)
    choose t ht heq using hs
    have hfun : (fun e => (t e : ℂ)) = x := funext heq
    rw [← hfun]
    exact hnz i t ht
  obtain ⟨ε, hε, hrel⟩ := finite_family_relative_stability f hf (realBox E a b)
    (realBox_isCompact E a b) hnz' hη
  refine ⟨ε, hε, ?_⟩
  intro i x hx z hzx
  apply hrel i (fun e => (x e : ℂ)) (fun e _ => ⟨x e, hx e, rfl⟩) z
  exact (dist_pi_lt_iff hε).mpr (fun e => by simpa [dist_eq_norm] using hzx e)

theorem finite_family_box_zero_free {ι E : Type*} [Finite ι] [Fintype E]
    (f : ι → (E → ℂ) → ℂ) (hf : ∀ i, Continuous (f i)) (a b : ℝ)
    (hnz : ∀ i, ∀ x : E → ℝ, (∀ e, x e ∈ Icc a b) → f i (fun e => (x e : ℂ)) ≠ 0) :
    ∃ ε > 0, ∀ i, ∀ z ∈ polytube E ε a b, f i z ≠ 0 := by
  obtain ⟨ε, hε, hrel⟩ := finite_family_box_stability f hf a b hnz (η := 1) (by norm_num)
  refine ⟨ε, hε, ?_⟩
  intro i z hz heq
  obtain ⟨x, hx, hzx⟩ := (mem_polytube_iff z ε a b).mp hz
  have h := hrel i x hx z hzx
  simp [heq] at h

end
end CI2ZF.Holant
