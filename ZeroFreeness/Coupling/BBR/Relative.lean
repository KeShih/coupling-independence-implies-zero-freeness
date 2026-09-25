import ZeroFreeness.Coupling.BBR.Spatial
import ZeroFreeness.Coupling.BBR.Jacobian
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform relative SSM. A direct derivative bound for the normalized
squares proves the ratio estimate globally, avoiding a small-error case
split and retaining the appendix's advertised constant. -/
namespace ZeroFreeness.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open ZeroFreeness.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

def squareProbability (y : C → ℝ) (c : C) : ℝ := y c ^ 2 / squareMass y

theorem hasDerivAt_squareProbability {y : ℝ → C → ℝ} {z : C → ℝ} {a : ℝ}
    (hy : ∀ c, HasDerivAt (fun t => y t c) (z c) a) (hS : 0 < squareMass (y a)) (c : C) :
    HasDerivAt (fun t => squareProbability (y t) c)
      (2 * y a c / squareMass (y a) * projection (y a) z c) a := by
  have h := ((hy c).pow 2).div (hasDerivAt_squareMass hy) hS.ne'
  apply h.congr_deriv
  unfold projection
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, Pi.pow_apply]
  field_simp [hS.ne']

theorem squareMass_pos_of_lower {m : ℝ} (hm : 0 < m) (y : C → ℝ) (hy : ∀ c, m ≤ y c) :
    0 < squareMass y := Finset.sum_pos (fun c _ => sq_pos_of_pos (hm.trans_le (hy c))) Finset.univ_nonempty

theorem squareProbability_derivative_bound {m : ℝ} (hm : 0 < m) (y z : C → ℝ)
    (hy : ∀ c, m ≤ y c) (c : C) :
    |2 * y c / squareMass y * projection y z c| ≤ 2 / m * Real.sqrt (squareMass z) := by
  have hS := squareMass_pos_of_lower hm y hy
  have hy0 := hm.trans_le (hy c)
  have hratio : y c / squareMass y ≤ 1 / m := by
    apply (div_le_div_iff₀ hS hm).2
    have hh := mul_le_mul_of_nonneg_left (hy c) hy0.le
    nlinarith [coordinate_sq_le_mass y c]
  have hproj : |projection y z c| ≤ Real.sqrt (squareMass z) := by
    have he := (coordinate_sq_le_mass (projection y z) c).trans (projection_energy_le y z hS)
    have hs := Real.sq_sqrt (squareMass_nonneg z)
    have hsn := Real.sqrt_nonneg (squareMass z)
    nlinarith [sq_abs (projection y z c), abs_nonneg (projection y z c)]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * y c / squareMass y)]
  have hratio2 : 2 * y c / squareMass y ≤ 2 / m := by
    have h := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [mul_div_assoc, mul_one_div] using h
  exact mul_le_mul hratio2 hproj (abs_nonneg _) (by positivity)

theorem squareProbability_lipschitz {m : ℝ} (hm : 0 < m) (R R' : C → ℝ)
    (hR : ∀ c, m ≤ R c) (hR' : ∀ c, m ≤ R' c) (c : C) :
    |squareProbability R c - squareProbability R' c| ≤
      2 / m * Real.sqrt (squareMass (fun c => R c - R' c)) := by
  let z : C → ℝ := fun c => R c - R' c
  let y : ℝ → C → ℝ := fun t => segment t R R'
  have hy (a : ℝ) (c : C) : HasDerivAt (fun t => y t c) (z c) a := by
    have h := ((hasDerivAt_id a).mul_const (R c)).add
      (((hasDerivAt_const a 1).sub (hasDerivAt_id a)).mul_const (R' c))
    apply h.congr_deriv
    dsimp [z]
    ring
  have hlow (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (c : C) : m ≤ y t c := segment_lower R R' hR hR' ht c
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := hasDerivAt_squareProbability (hy t)
    (squareMass_pos_of_lower hm (y t) (hlow t ht)) c
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact squareProbability_derivative_bound hm (y t) z (hlow t ht) c)
    (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have h0 : y 0 = R' := segment_zero R R'
  have h1 : y 1 = R := by funext c; simp only [y, segment, one_mul, sub_self, zero_mul, add_zero]
  simpa only [h0, h1, Real.norm_eq_abs, sub_zero, abs_one, mul_one, z] using hh

theorem squareProbability_lower {m : ℝ} (hm : 0 < m) (R : C → ℝ)
    (hR : ∀ c, m ≤ R c) (hR1 : ∀ c, R c ≤ 1) (c : C) :
    m ^ 2 / Fintype.card C ≤ squareProbability R c := by
  have hq : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hS := squareMass_pos_of_lower hm R hR
  have hm2 := pow_le_pow_left₀ hm.le (hR c) 2
  have hmass : squareMass R ≤ Fintype.card C := by
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ =>
      pow_le_one₀ (hm.le.trans (hR c)) (hR1 c) (n := 2))
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, squareMass] using hs
  exact (div_le_div_of_nonneg_right hm2 hq.le).trans (div_le_div_of_nonneg_left (sq_nonneg _) hS hmass)

theorem squareProbability_ratio_bound {m : ℝ} (hm : 0 < m) (R R' : C → ℝ)
    (hR : ∀ c, m ≤ R c) (hR' : ∀ c, m ≤ R' c) (hR'1 : ∀ c, R' c ≤ 1) (c : C) :
    |squareProbability R c / squareProbability R' c - 1| ≤
      2 * (Fintype.card C : ℝ) / m ^ 3 * Real.sqrt (squareMass (fun c => R c - R' c)) := by
  have hq : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hlow := squareProbability_lower hm R' hR' hR'1 c
  have hp : 0 < squareProbability R' c := (div_pos (sq_pos_of_pos hm) hq).trans_le hlow
  have hlip := squareProbability_lipschitz hm R R' hR hR' c
  have hidentity : squareProbability R c / squareProbability R' c - 1 =
      (squareProbability R c - squareProbability R' c) / squareProbability R' c := by field_simp [hp.ne']
  rw [hidentity, abs_div, abs_of_pos hp]
  calc
    _ ≤ (2 / m * Real.sqrt (squareMass (fun c => R c - R' c))) / squareProbability R' c :=
      div_le_div_of_nonneg_right hlip hp.le
    _ ≤ (2 / m * Real.sqrt (squareMass (fun c => R c - R' c))) / (m ^ 2 / Fintype.card C) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    _ = _ := by field_simp [hm.ne', hq.ne']

def relativeConstant (q Δ : ℕ) (x₀ : ℝ) : ℝ :=
  4 * q * Real.sqrt ((Δ : ℝ) * q) / (Real.sqrt (x₀ ^ Δ)) ^ 3 / contractionSquare Δ

theorem root_relative_ssm (bbr : Literature C) {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (k d : ℕ) (b : C → ℕ) (t u : Fin d → Girth.CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (t i).DegreeBudget Δ) (hu : ∀ i, (u i).DegreeBudget Δ)
    (hdom : ∀ i, CLMM.SameDomain (t i) (u i)) (hag : ∀ i, Girth.CavityTree.Agreement k (t i) (u i)) (c : C) :
    |(Girth.CavityTree.node d b t).probability x c / (Girth.CavityTree.node d b u).probability x c - 1| ≤
      relativeConstant (Fintype.card C) Δ (start (Fintype.card C) Δ) * contractionRate Δ ^ (k + 2) := by
  let x₀ := start (Fintype.card C) Δ
  let T := Girth.CavityTree.node d b t
  let U := Girth.CavityTree.node d b u
  let m := Real.sqrt (x₀ ^ Δ)
  have hx₀ := start_mem hq hr
  have hx0 := hx₀.1.trans_le hx.1
  have hm : 0 < m := Real.sqrt_pos.2 (pow_pos hx₀.1 Δ)
  have hdq := degree_gt_colours (Nat.cast_pos.mpr Fintype.card_pos) hr
  have hdqn : Fintype.card C < Δ := by exact_mod_cast hdq
  have hΔ : 2 ≤ Δ := by omega
  have hθ := (contractionRate_mem hΔ).1.le
  have hκ := (contractionSquare_mem hΔ).1
  have hT (c : C) : m ≤ T.message x c := CavityTree.message_uniform_lower hx₀.1 hx.1 hx.2 T Δ hroot c
  have hU (c : C) : m ≤ U.message x c := CavityTree.message_uniform_lower hx₀.1 hx.1 hx.2 U Δ hroot c
  have hratio := squareProbability_ratio_bound hm (T.message x) (U.message x) hT hU
    (fun c => (U.message_bounds hx0 hx.2 c).2) c
  have hdecay := root_spatial_energy bbr hq hr hx k d b t u hroot ht hu hdom hag
  have hsq : (Real.sqrt ((Δ : ℝ) * Fintype.card C) * contractionRate Δ ^ k) ^ 2 =
      (Δ : ℝ) * Fintype.card C * contractionSquare Δ ^ k := by
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm k 2, pow_mul, contractionRate_sq hΔ]
  have hE : Real.sqrt (messageDistance x T U) ≤ Real.sqrt ((Δ : ℝ) * Fintype.card C) * contractionRate Δ ^ k := by
    have hnon : 0 ≤ Real.sqrt ((Δ : ℝ) * Fintype.card C) * contractionRate Δ ^ k := by positivity
    have he := Real.sq_sqrt (messageDistance_nonneg x T U)
    nlinarith [Real.sqrt_nonneg (messageDistance x T U)]
  rw [T.probability_eq_square hx0, U.probability_eq_square hx0]
  calc
    _ ≤ 2 * (Fintype.card C : ℝ) / m ^ 3 * Real.sqrt (messageDistance x T U) := hratio
    _ ≤ 2 * (Fintype.card C : ℝ) / m ^ 3 * (Real.sqrt ((Δ : ℝ) * Fintype.card C) * contractionRate Δ ^ k) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ 4 * (Fintype.card C : ℝ) / m ^ 3 * (Real.sqrt ((Δ : ℝ) * Fintype.card C) * contractionRate Δ ^ k) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg (Fintype.card C) : (0 : ℝ) ≤ Fintype.card C)])
        (pow_nonneg hm.le _)
    _ = _ := by
      unfold relativeConstant
      rw [pow_add, contractionRate_sq hΔ]
      dsimp [m, x₀]
      field_simp [hκ.ne']

end
end ZeroFreeness.Appendix.BBR
