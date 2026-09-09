import CI2ZF.Holant.LocalStability
import Mathlib.Tactic

/-! The topology and reciprocal change of variables used at the end of
the Holant argument. All neighborhood widths are chosen before dimension. -/
namespace CI2ZF.Holant
open Set Metric
noncomputable section

def orthantNeighborhood (E : Type*) (width : ℝ → ℝ) : Set (E → ℂ) :=
  ⋃ R > 0, polytube E (width R) 0 R

theorem orthantNeighborhood_isOpen (E : Type*) [Finite E] (width : ℝ → ℝ) :
    IsOpen (orthantNeighborhood E width) :=
  isOpen_iUnion fun R => isOpen_iUnion fun _ => polytube_isOpen E (width R) 0 R

/-- Finiteness chooses one common real upper bound before taking the product. -/
theorem nonnegative_mem_orthantNeighborhood {E : Type*} [Fintype E]
    (width : ℝ → ℝ) (hwidth : ∀ R > 0, 0 < width R)
    (x : E → ℝ) (hx : ∀ e, 0 ≤ x e) :
    (fun e => (x e : ℂ)) ∈ orthantNeighborhood E width := by
  let R := 1 + ∑ e, x e
  have hR : 0 < R := by
    have hs : 0 ≤ ∑ e, x e := Finset.sum_nonneg (fun e _ => hx e)
    dsimp [R]
    linarith
  refine mem_iUnion₂.mpr ⟨R, hR, ?_⟩
  apply (mem_polytube_iff _ _ _ _).mpr
  refine ⟨x, ?_, ?_⟩
  · intro e
    refine ⟨hx e, ?_⟩
    have he := Finset.single_le_sum (fun a _ => hx a) (Finset.mem_univ e)
    dsimp [R]
    linarith
  · intro e
    simpa using hwidth R hR

def diagonalNeighborhood (width : ℝ → ℝ) : Set ℂ :=
  ⋃ R > 0, thickening (width R) (realInterval 0 R)

theorem diagonalNeighborhood_isOpen (width : ℝ → ℝ) :
    IsOpen (diagonalNeighborhood width) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_thickening

theorem diagonal_mem_orthantNeighborhood {E : Type*} (width : ℝ → ℝ)
    {z : ℂ} (hz : z ∈ diagonalNeighborhood width) :
    (fun _ : E => z) ∈ orthantNeighborhood E width := by
  obtain ⟨R, hR, hzR⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion₂.mpr ⟨R, hR, fun _ _ => hzR⟩

theorem nonnegative_mem_diagonalNeighborhood (width : ℝ → ℝ)
    (hwidth : ∀ R > 0, 0 < width R) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) ∈ diagonalNeighborhood width := by
  have hR : 0 < x + 1 := by linarith
  apply mem_iUnion₂.mpr ⟨x + 1, hR, ?_⟩
  exact mem_thickening_iff.mpr ⟨(x : ℂ), ⟨x, ⟨hx, by linarith⟩, rfl⟩,
    by simpa using hwidth (x + 1) hR⟩

/-- Uniform scalar inversion estimate, with the lower endpoint kept away
from zero. This bound has no dependence on the number of coordinates. -/
theorem inversion_bound {a x ε : ℝ} (ha : 0 < a) (hax : a ≤ x)
    (hε : ε ≤ a / 2) (z : ℂ) (hz : ‖z - (x : ℂ)‖ < ε) :
    z ≠ 0 ∧ ‖z⁻¹ - ((x⁻¹ : ℝ) : ℂ)‖ < 2 * ε / a ^ 2 := by
  have hx : 0 < x := ha.trans_le hax
  have hxnorm : ‖(x : ℂ)‖ = x := by simp [abs_of_pos hx]
  have ht := norm_sub_norm_le (x : ℂ) z
  rw [hxnorm, norm_sub_rev] at ht
  have hzlower : a / 2 < ‖z‖ := by linarith
  have hzn : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hxn : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  refine ⟨hzn, ?_⟩
  rw [Complex.ofReal_inv, inv_sub_inv hzn hxn, norm_div, norm_mul, norm_sub_rev, hxnorm]
  have hden : a ^ 2 / 2 ≤ ‖z‖ * x := by nlinarith
  have hdenpos : 0 < ‖z‖ * x := mul_pos (norm_pos_iff.mpr hzn) hx
  apply (div_lt_iff₀ hdenpos).mpr
  have hεpos : 0 < ε := (norm_nonneg _).trans_lt hz
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hmul := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 2 * ε / a ^ 2 from div_nonneg (by positivity) ha2.le)
  have hid : (2 * ε / a ^ 2) * (a ^ 2 / 2) = ε := by field_simp
  rw [hid] at hmul
  exact hz.trans_le hmul

/-- A sufficient common width for passing from a positive cover box to
the matching box in reciprocal coordinates. -/
theorem reciprocal_polytube {E : Type*} {a b δ ε : ℝ}
    (ha : 0 < a) (hεa : ε ≤ a / 2) (hεδ : 2 * ε / a ^ 2 ≤ δ)
    (z : E → ℂ) (hz : z ∈ polytube E ε a b) :
    (∀ e, z e ≠ 0) ∧ (fun e => (z e)⁻¹) ∈ polytube E δ 0 a⁻¹ := by
  obtain ⟨x, hx, hzx⟩ := (mem_polytube_iff _ _ _ _).mp hz
  have hi := fun e => inversion_bound ha (hx e).1 hεa (z e) (hzx e)
  refine ⟨fun e => (hi e).1, ?_⟩
  apply (mem_polytube_iff _ _ _ _).mpr
  refine ⟨fun e => (x e)⁻¹, ?_, fun e => (hi e).2.trans_le hεδ⟩
  intro e
  have hxe : 0 < x e := ha.trans_le (hx e).1
  exact ⟨inv_nonneg.mpr hxe.le, inv_anti₀ ha (hx e).1⟩

theorem exists_reciprocal_width {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∃ ε > 0, ε ≤ a / 2 ∧ 2 * ε / a ^ 2 ≤ δ := by
  refine ⟨min (a / 2) (δ * a ^ 2 / 2), lt_min (by positivity) (by positivity),
    min_le_left _ _, ?_⟩
  have hmin := min_le_right (a / 2) (δ * a ^ 2 / 2)
  apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
  linarith

end
end CI2ZF.Holant
