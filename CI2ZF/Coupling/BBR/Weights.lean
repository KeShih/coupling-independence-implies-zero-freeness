import CI2ZF.Coupling.BBR.Differential

/-! Actual segment weights and the uniform cavity annulus. -/
namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open CI2ZF.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

def segment (t : ℝ) (R R' : C → ℝ) (c : C) : ℝ := t * R c + (1 - t) * R' c
@[simp] theorem segment_zero (R R' : C → ℝ) : segment 0 R R' = R' := by
  funext c
  simp only [segment, zero_mul, sub_zero, one_mul, zero_add]
def segmentWeightSet (x : ℝ) (R R' : C → ℝ) : Set ℝ :=
  {z | ∃ t ∈ Icc (0 : ℝ) 1, ∃ c, z = squareMass (segment t R R') / excludedMass x (segment t R R') c ^ 2}
def segmentWeightSquare (x : ℝ) (R R' : C → ℝ) : ℝ := sSup (segmentWeightSet x R R')

theorem segment_lower {m : ℝ} (R R' : C → ℝ) (hR : ∀ c, m ≤ R c)
    (hR' : ∀ c, m ≤ R' c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (c : C) :
    m ≤ segment t R R' c := by
  have h := mul_le_mul_of_nonneg_left (hR c) ht.1
  have h' := mul_le_mul_of_nonneg_left (hR' c) (sub_nonneg.mpr ht.2)
  unfold segment
  nlinarith

theorem segment_mass_lower {m : ℝ} (hm : 0 ≤ m) (R R' : C → ℝ)
    (hR : ∀ c, m ≤ R c) (hR' : ∀ c, m ≤ R' c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (Fintype.card C : ℝ) * m ^ 2 ≤ squareMass (segment t R R') := by
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ =>
    pow_le_pow_left₀ hm (segment_lower R R' hR hR' ht c) 2)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, squareMass] using hh

theorem ratio_weight_bound {x a : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (ha : 0 < a)
    (y : C → ℝ) (hS : a ≤ squareMass y) (c : C) :
    squareMass y / excludedMass x y c ^ 2 ≤ 1 / (x ^ 2 * a) := by
  have hS0 := ha.trans_le hS
  have hSi := excludedMass_pos hx hx1 y hS0 c
  have hsq := pow_le_pow_left₀ (mul_pos hx hS0).le (excludedMass_bounds hx hx1 y c).1 2
  have hmass := mul_le_mul_of_nonneg_left hS (mul_nonneg (sq_nonneg x) hS0.le)
  apply (div_le_div_iff₀ (sq_pos_of_pos hSi) (mul_pos (sq_pos_of_pos hx) ha)).2
  rw [mul_pow] at hsq
  nlinarith

theorem segmentWeightSet_nonempty (x : ℝ) (R R' : C → ℝ) : (segmentWeightSet x R R').Nonempty := by
  obtain ⟨c⟩ := ‹Nonempty C›
  exact ⟨_, 0, by norm_num, c, rfl⟩

theorem segmentWeight_bound {x m : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hm : 0 < m)
    (R R' : C → ℝ) (hR : ∀ c, m ≤ R c) (hR' : ∀ c, m ≤ R' c) :
    segmentWeightSquare x R R' ≤ 1 / (x ^ 2 * ((Fintype.card C : ℝ) * m ^ 2)) := by
  have ha : 0 < (Fintype.card C : ℝ) * m ^ 2 := mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (sq_pos_of_pos hm)
  apply csSup_le (segmentWeightSet_nonempty x R R')
  rintro z ⟨t, ht, c, rfl⟩
  exact ratio_weight_bound hx hx1 ha _ (segment_mass_lower hm.le R R' hR hR' ht) c

theorem segmentWeightSet_bddAbove {x m : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hm : 0 < m)
    (R R' : C → ℝ) (hR : ∀ c, m ≤ R c) (hR' : ∀ c, m ≤ R' c) :
    BddAbove (segmentWeightSet x R R') := by
  have ha : 0 < (Fintype.card C : ℝ) * m ^ 2 := mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (sq_pos_of_pos hm)
  refine ⟨1 / (x ^ 2 * ((Fintype.card C : ℝ) * m ^ 2)), ?_⟩
  rintro z ⟨t, ht, c, rfl⟩
  exact ratio_weight_bound hx hx1 ha _ (segment_mass_lower hm.le R R' hR hR' ht) c

theorem pointWeight_le_segmentWeight {x m : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hm : 0 < m)
    (R : C → ℝ) (hR : ∀ c, m ≤ R c) :
    pointWeightSquare x R ≤ segmentWeightSquare x R R := by
  apply Finset.sup'_le
  intro c _
  apply le_csSup (segmentWeightSet_bddAbove hx hx1 hm R R hR hR)
  refine ⟨0, by norm_num, c, ?_⟩
  rw [segment_zero]

theorem segmentWeightSquare_nonneg {x m : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hm : 0 < m)
    (R R' : C → ℝ) (hR : ∀ c, m ≤ R c) (hR' : ∀ c, m ≤ R' c) :
    0 ≤ segmentWeightSquare x R R' := by
  obtain ⟨c⟩ := ‹Nonempty C›
  have hmem : squareMass R' / excludedMass x R' c ^ 2 ∈ segmentWeightSet x R R' := by
    refine ⟨0, by norm_num, c, ?_⟩
    rw [segment_zero]
  exact (div_nonneg (squareMass_nonneg _) (sq_nonneg _)).trans
    (le_csSup (segmentWeightSet_bddAbove hx hx1 hm R R' hR hR') hmem)

namespace CavityTree

theorem message_uniform_lower {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x) (hx1 : x ≤ 1)
    (t : Girth.CavityTree C) (D : ℕ) (hD : t.degree + ∑ c, t.boundary c ≤ D) (c : C) :
    Real.sqrt (x₀ ^ D) ≤ t.message x c := by
  have hp : x₀ ^ D ≤ x ^ (t.degree + ∑ c, t.boundary c) :=
    (pow_le_pow_of_le_one hx₀.le (hx.trans hx1) hD).trans
      (pow_le_pow_left₀ hx₀.le hx _)
  exact (Real.sqrt_le_sqrt hp).trans (t.message_bounds (hx₀.trans_le hx) hx1 c).1

end CavityTree

end
end CI2ZF.Appendix.BBR
