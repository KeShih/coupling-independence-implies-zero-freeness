import CI2ZF.Appendix.GirthProduct
import CI2ZF.Appendix.GirthChannel

/-! The exact mass-sensitive Jensen and occupancy estimates for the
additive sector of a supported conditional star. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
variable {C D : Type*} [Fintype C] [Fintype D]

lemma log_one_sub_uniform_lower {B y : ℝ} (hB : B < 1) (hy0 : 0 ≤ y) (hyB : y ≤ B) :
    -y / (1 - B) ≤ Real.log (1 - y) := by
  have hb : 0 < 1 - B := sub_pos.mpr hB
  have hy : 0 < 1 - y := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hy
  have he : 1 - (1 - y)⁻¹ = -y / (1 - y) := by field_simp; ring
  rw [he] at hh
  have hm := div_le_div_of_nonneg_left hy0 hb (by linarith : 1 - B ≤ 1 - y)
  have hm' : -y / (1 - B) ≤ -y / (1 - y) := by
    simpa only [neg_div] using neg_le_neg hm
  exact hm'.trans hh

lemma weighted_log_mass_lower {B s : ℝ} (hB : B < 1)
    (a y : C → ℝ) (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1)
    (hy : ∀ c, 0 ≤ y c ∧ y c ≤ B) (hmass : ∑ c, y c ≤ s) :
    -s / (1 - B) ≤ ∑ c, a c * Real.log (1 - y c) := by
  have hmass' : ∑ c, a c * y c ≤ s :=
    (Finset.sum_le_sum (fun c _ =>
      (mul_le_mul_of_nonneg_right (ha c).2 (hy c).1).trans_eq (one_mul _))).trans hmass
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    mul_le_mul_of_nonneg_left (log_one_sub_uniform_lower hB (hy c).1 (hy c).2) (ha c).1)
  calc
    _ ≤ -(∑ c, a c * y c) / (1 - B) := by
      apply div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ = ∑ c, a c * (-y c / (1 - B)) := by
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ ≤ _ := hsum

/-- Weighted Jensen retains the actual total edge mass s, including s=0. -/
theorem weighted_messagePartition_lower_mass (a : C → ℝ) (m : D → C → ℝ) {B s : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA : 0 < ∑ c, a c) (hB : B < 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ B) (hmass : ∀ i, ∑ c, m i c ≤ s) :
    (∑ c, a c) * Real.exp (-(s * Fintype.card D) / ((∑ c, a c) * (1 - B))) ≤
      messagePartition a m := by
  let A : ℝ := ∑ c, a c
  let z : C → ℝ := fun c => ∏ i, (1 - m i c)
  have hz (c : C) : 0 < z c := Finset.prod_pos fun i _ => by linarith [(hm i c).2]
  have hw : ∀ c ∈ (Finset.univ : Finset C), 0 ≤ a c / A :=
    fun c _ => div_nonneg (ha c).1 hA.le
  have hw1 : ∑ c, a c / A = 1 := by rw [← Finset.sum_div]; exact div_self hA.ne'
  have hj := convexOn_exp.map_sum_le hw hw1 (fun c _ => Set.mem_univ (Real.log (z c)))
  simp only [smul_eq_mul] at hj
  simp_rw [Real.exp_log (hz _)] at hj
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun i _ =>
    weighted_log_mass_lower hB a (m i) ha (hm i) (hmass i))
  have hdiv := div_le_div_of_nonneg_right hsum hA.le
  have hid : (∑ i, ∑ c, a c * Real.log (1 - m i c)) / A =
      ∑ c, (a c / A) * Real.log (z c) := by
    rw [Finset.sum_comm, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    dsimp [z]
    rw [Real.log_prod (fun i _ => (show 0 < 1 - m i c by linarith [(hm i c).2]).ne'),
      ← Finset.mul_sum]
    ring
  rw [hid] at hdiv
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hdiv
  have he : -(s * Fintype.card D) / (A * (1 - B)) ≤
      ∑ c, (a c / A) * Real.log (z c) := by
    calc
      _ = (Fintype.card D : ℝ) * (-s / (1 - B)) / A := by
        rw [div_mul_eq_div_div]
        ring
      _ ≤ _ := hdiv
  have hmul := mul_le_mul_of_nonneg_left ((Real.exp_le_exp.mpr he).trans hj) hA.le
  calc
    _ ≤ A * ∑ c, (a c / A) * z c := hmul
    _ = messagePartition a m := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      change A * (a c / A * z c) = a c * z c
      field_simp [show A ≠ 0 from hA.ne']

/-- The elementary occupancy coefficient has a strict delta margin.
The exponential is already at most one under the stated cap. -/
theorem occupancy_coefficient_le {δ B u : ℝ} (hδ : 0 < δ) (hB0 : 0 ≤ B)
    (hB : B ≤ δ / (8 * (1 + δ))) (hu0 : 0 ≤ u) (hu : u ≤ 1 / (1 + δ)) :
    u / (1 - B) ^ 2 * Real.exp (u / (1 - B) - 1) ≤ 1 / (1 + 3 * δ / 4) := by
  have hd : 0 < 1 + δ := by linarith
  have hb := (le_div_iff₀ (by positivity : 0 < 8 * (1 + δ))).mp hB
  have hsmall : B ≤ 1 / 8 := by nlinarith
  have hden : 0 < 1 - B := by linarith
  have hden2 : 0 < (1 - B) ^ 2 := sq_pos_of_pos hden
  have hu' := (le_div_iff₀ hd).mp hu
  have hr : u ≤ 1 - B := by nlinarith
  have hexp : Real.exp (u / (1 - B) - 1) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have := (div_le_one hden).mpr hr
    linarith
  have hpoly : 1 + 3 * δ / 4 ≤ (1 + δ) * (1 - B) ^ 2 := by
    have hs := mul_nonneg hd.le (sq_nonneg B)
    nlinarith
  have hratio : u / (1 - B) ^ 2 ≤ 1 / (1 + 3 * δ / 4) := by
    apply (div_le_div_iff₀ hden2 (by positivity : 0 < 1 + 3 * δ / 4)).mpr
    have hm := mul_le_mul_of_nonneg_left hpoly hu0
    have hm' := mul_le_mul_of_nonneg_right hu' hden2.le
    nlinarith
  exact (mul_le_mul_of_nonneg_left hexp (div_nonneg hu0 hden2.le)).trans (by simpa using hratio)

lemma channel_variance_factor_lower {δ B : ℝ} (hδ : 0 < δ) (hB0 : 0 ≤ B)
    (hB : B ≤ δ / (8 * (1 + δ))) :
    1 - 2 * B ≤ 1 - B / (1 - B) ^ 2 ∧
    1 + δ / 2 ≤ (1 + 3 * δ / 4) * (1 - B / (1 - B) ^ 2) := by
  have hb := (le_div_iff₀ (by positivity : 0 < 8 * (1 + δ))).mp hB
  have hsmall : B ≤ 1 / 8 := by nlinarith
  have hden : 0 < (1 - B) ^ 2 := sq_pos_of_pos (by linarith)
  have hr : B / (1 - B) ^ 2 ≤ 2 * B := by
    apply (div_le_iff₀ hden).mpr
    have hs : 1 / 2 ≤ (1 - B) ^ 2 := by nlinarith
    nlinarith
  constructor
  · linarith
  · have hm := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 1 + 3 * δ / 4)
    nlinarith [mul_nonneg hB0 hδ.le]

/-- The occupancy numerator and mass-sensitive Jensen denominator refer
to the same actual weighted message recursion. -/
theorem message_occupancy_bound_mass
    (a : C → ℝ) (m : D → C → ℝ) {B s : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA : 0 < ∑ c, a c) (hB : B < 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ B) (hmass : ∀ i, ∑ c, m i c ≤ s) (c : C) :
    messageMarginal a m c * (∑ i, m i c) ≤
      Real.exp (s * Fintype.card D / ((∑ c, a c) * (1 - B)) - 1) / (∑ c, a c) := by
  let A : ℝ := ∑ c, a c
  let H : ℝ := s * Fintype.card D / (A * (1 - B))
  have hlow := weighted_messagePartition_lower_mass a m ha hA hB hm hmass
  have hlow' : A * Real.exp (-H) ≤ messagePartition a m := by
    simpa only [H, neg_div] using hlow
  have hlpos : 0 < A * Real.exp (-H) := mul_pos hA (Real.exp_pos _)
  have hZ : 0 < messagePartition a m := hlpos.trans_le hlow'
  have hm1 : ∀ i, 0 ≤ m i c ∧ m i c ≤ 1 :=
    fun i => ⟨(hm i c).1, (hm i c).2.trans hB.le⟩
  have hnum := occupancy_numerator_le (fun i => m i c) hm1
  have hn0 : 0 ≤ (∑ i, m i c) * ∏ i, (1 - m i c) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => (hm i c).1)
      (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hm1 i).2)
  have hnum' : messageWeight a m c * (∑ i, m i c) ≤ Real.exp (-1) := by
    calc
      _ = a c * ((∑ i, m i c) * ∏ i, (1 - m i c)) := by unfold messageWeight; ring
      _ ≤ 1 * ((∑ i, m i c) * ∏ i, (1 - m i c)) :=
        mul_le_mul_of_nonneg_right (ha c).2 hn0
      _ ≤ Real.exp (-1) := by simpa using hnum
  calc
    _ = (messageWeight a m c * (∑ i, m i c)) / messagePartition a m := by
      unfold messageMarginal
      ring
    _ ≤ Real.exp (-1) / messagePartition a m := div_le_div_of_nonneg_right hnum' hZ.le
    _ ≤ Real.exp (-1) / (A * Real.exp (-H)) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hlpos hlow'
    _ = (Real.exp (-1) / A) * Real.exp H := by
      rw [Real.exp_neg H, div_mul_eq_div_div, div_inv_eq_mul]
    _ = (Real.exp (-1) * Real.exp H) / A := by ring
    _ = Real.exp (H - 1) / A := by
      rw [← Real.exp_add]
      congr 2
      ring

namespace ConditionalStar
variable [DecidableEq C] (S : ConditionalStar C D)

lemma occupancy_ratio_budget {δ Δ : ℝ} (hδ : 0 < δ)
    (hd : (Fintype.card D : ℝ) ≤ Δ)
    (hA : S.s * ((Fintype.card D : ℝ) + δ * Δ) ≤ S.palette) :
    S.s * Fintype.card D / S.palette ≤ 1 / (1 + δ) := by
  apply (div_le_div_iff₀ S.palette_pos (by positivity : 0 < 1 + δ)).mpr
  have hh := mul_le_mul_of_nonneg_left hd (mul_nonneg S.s_nonneg hδ.le)
  nlinarith

/-- The displayed star occupancy bound holds for every centre colour,
including zero-probability colours and zero activity. -/
theorem star_occupancy_le {δ Δ B : ℝ} (hδ : 0 < δ) (hB0 : 0 ≤ B)
    (hB : B ≤ δ / (8 * (1 + δ)))
    (hd : (Fintype.card D : ℝ) ≤ Δ)
    (hA : S.s * ((Fintype.card D : ℝ) + δ * Δ) ≤ S.palette)
    (hm : ∀ i c, S.s * (S.cavity i).w c ≤ B) (c : C) :
    ((Fintype.card D : ℝ) * S.s ^ 2 / (1 - B) ^ 2) *
      (S.centreLaw.w c * ∑ i, (S.cavity i).w c) ≤ 1 / (1 + 3 * δ / 4) := by
  let u : ℝ := S.s * Fintype.card D / S.palette
  have hu0 : 0 ≤ u := div_nonneg (mul_nonneg S.s_nonneg (Nat.cast_nonneg _)) S.palette_pos.le
  have hu := S.occupancy_ratio_budget hδ hd hA
  have hb := (le_div_iff₀ (by positivity : 0 < 8 * (1 + δ))).mp hB
  have hB1 : B < 1 := by nlinarith
  have hh := message_occupancy_bound_mass (s := S.s) S.unary (fun i c => S.s * (S.cavity i).w c)
    (fun c => ⟨S.unary_nonneg c, S.unary_le_one c⟩) S.palette_pos hB1
    (fun i c => ⟨mul_nonneg S.s_nonneg ((S.cavity i).nonneg c), hm i c⟩)
    (fun i => by simp only [← Finset.mul_sum, FinDist.sum_one, mul_one, le_refl]) c
  change S.centreLaw.w c * (∑ i, S.s * (S.cavity i).w c) ≤
    Real.exp (S.s * Fintype.card D / (S.palette * (1 - B)) - 1) / S.palette at hh
  have hh' := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (Fintype.card D : ℝ) * S.s / (1 - B) ^ 2 from
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) S.s_nonneg) (sq_nonneg _))
  have hcoef := occupancy_coefficient_le hδ hB0 hB hu0 hu
  have hid : S.s * Fintype.card D / (S.palette * (1 - B)) = u / (1 - B) := by
    dsimp [u]
    rw [div_mul_eq_div_div]
  rw [hid] at hh'
  rw [← Finset.mul_sum] at hh'
  have he : ((Fintype.card D : ℝ) * S.s ^ 2 / (1 - B) ^ 2) *
      (S.centreLaw.w c * ∑ i, (S.cavity i).w c) ≤
      u / (1 - B) ^ 2 * Real.exp (u / (1 - B) - 1) := by
    calc
      _ = (Fintype.card D : ℝ) * S.s / (1 - B) ^ 2 *
          (S.centreLaw.w c * (S.s * ∑ i, (S.cavity i).w c)) := by ring
      _ ≤ (Fintype.card D : ℝ) * S.s / (1 - B) ^ 2 *
          (Real.exp (u / (1 - B) - 1) / S.palette) := hh'
      _ = _ := by
        dsimp [u]
        ring
  exact he.trans hcoef

end ConditionalStar

end
end CI2ZF.Appendix.Girth
