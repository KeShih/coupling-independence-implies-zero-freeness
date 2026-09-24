import CI2ZF.Coupling.BBR.Weights
import CI2ZF.Coupling.BBR.CertificateArithmetic

/-!
# The BBR contraction certificate on actual cavity messages

The BBR results used are Proposition 2.6(i), with its printed degree
assumption unchanged, and Theorem 2.5, collected in `Literature`. Both are
proved, in `CI2ZF.Coupling.BBR.Proposition26` and
`CI2ZF.Coupling.BBR.Theorem25`, and `literature` there supplies the bundle.
The four gap-two pairs are handled directly from the annulus, as is
`(q,Δ)=(3,4)`.
Published source: EJP 30 (2025), article 65, doi:10.1214/25-EJP1327.
The arXiv v2 versions are Proposition 8(i) and Theorem 7:
https://arxiv.org/html/2310.04338v2.
-/
namespace CI2ZF.Appendix
open scoped BigOperators
open Finset Set PottsCI
open Girth
noncomputable section
set_option linter.unusedSectionVars false

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

theorem CLMM.SameDomain.refl (t : CavityTree C) : CLMM.SameDomain t t := by
  induction t with
  | node d b child ih => exact CLMM.SameDomain.node d b b child child rfl ih

namespace BBR

/-- BBR Proposition 2.6(i) and Theorem 2.5 for the actual cavity messages.
Proved as `literature` in `CI2ZF.Coupling.BBR.Proposition26`. -/
structure Literature (C : Type*) [Fintype C] [DecidableEq C] [Nonempty C] : Prop where
  proposition_2_6_i : ∀ (Δ : ℕ) (_hq : 3 ≤ Fintype.card C)
    (_hgap : Fintype.card C + 3 ≤ Δ) (x : ℝ), 0 < x → x < 1 →
    1 - (Fintype.card C : ℝ) / Δ ≤ x →
    ∀ (t u : Girth.CavityTree C), t.DegreeBudget Δ → u.DegreeBudget Δ →
      CLMM.SameDomain t u → t.boundary = u.boundary →
      segmentWeightSquare x (t.message x) (u.message x) ≤
        publishedWeightBound (Fintype.card C) Δ t.degree
  theorem_2_5 : ∀ (Δ : ℕ) (_hΔ : 3 ≤ Δ) (_hq : 2 ≤ Fintype.card C) (x : ℝ), 0 < x → x < 1 →
    ∀ (d : ℕ) (b : C → ℕ) (t u : Fin d → Girth.CavityTree C),
      d + (∑ c, b c) ≤ Δ → (∀ i, (t i).DegreeBudget Δ) → (∀ i, (u i).DegreeBudget Δ) →
      (∀ i, CLMM.SameDomain (t i) (u i)) →
      squareMass (fun c => (Girth.CavityTree.node d b t).message x c -
        (Girth.CavityTree.node d b u).message x c) ≤
        ∑ i, ((1 - x) / Real.exp 1 * segmentWeightSquare x ((t i).message x) ((u i).message x)) *
          squareMass (fun c => (t i).message x c - (u i).message x c)

theorem cavity_total_degree {Δ : ℕ} (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) :
    t.degree + (∑ c, t.boundary c) ≤ Δ - 1 := by
  cases t with
  | node d b child => exact Nat.le_sub_one_of_lt ht.1

theorem cavity_segment_bound {Δ : ℕ} (hΔ : 2 ≤ Δ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (t u : Girth.CavityTree C) (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ) :
    segmentWeightSquare x (t.message x) (u.message x) ≤
      1 / ((Fintype.card C : ℝ) * x ^ (Δ + 1)) := by
  have hfloor (v : Girth.CavityTree C) (hv : v.DegreeBudget Δ) (c : C) :
      Real.sqrt (x ^ (Δ - 1)) ≤ v.message x c :=
    CavityTree.message_uniform_lower hx le_rfl hx1 v (Δ - 1) (cavity_total_degree v hv) c
  have hm := Real.sqrt_pos.2 (pow_pos hx (Δ - 1))
  have h := segmentWeight_bound hx hx1 hm (t.message x) (u.message x) (hfloor t ht) (hfloor u hu)
  rw [Real.sq_sqrt (pow_nonneg hx.le _)] at h
  have hp : x ^ 2 * x ^ (Δ - 1) = x ^ (Δ + 1) := by rw [← pow_add]; congr 1; omega
  have he : x ^ 2 * ((Fintype.card C : ℝ) * x ^ (Δ - 1)) =
      (Fintype.card C : ℝ) * x ^ (Δ + 1) := by rw [← hp]; ring
  exact h.trans_eq (by rw [he])

theorem cavity_segment_nonneg {Δ : ℕ} {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (t u : Girth.CavityTree C) (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ) :
    0 ≤ segmentWeightSquare x (t.message x) (u.message x) := by
  have hfloor (v : Girth.CavityTree C) (hv : v.DegreeBudget Δ) (c : C) :
      Real.sqrt (x ^ (Δ - 1)) ≤ v.message x c :=
    CavityTree.message_uniform_lower hx le_rfl hx1 v (Δ - 1) (cavity_total_degree v hv) c
  exact segmentWeightSquare_nonneg hx hx1 (Real.sqrt_pos.2 (pow_pos hx _))
    (t.message x) (u.message x) (hfloor t ht) (hfloor u hu)

/-- The complete certificate, with all exceptional arithmetic internal. -/
theorem contraction_certificate (bbr : Literature C) {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (t u : Girth.CavityTree C) (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ)
    (hdom : CLMM.SameDomain t u) (hb : t.boundary = u.boundary) :
    (t.degree : ℝ) * ((1 - x) / Real.exp 1) * segmentWeightSquare x (t.message x) (u.message x) ≤
      contractionSquare Δ := by
  have hx0 := (start_mem hq hr).1.trans_le hx.1
  have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hdq := degree_gt_colours hq0 hr
  have hdqn : Fintype.card C < Δ := by exact_mod_cast hdq
  have hΔ : 2 ≤ Δ := by omega
  have htdegree : t.degree ≤ Δ - 1 := (Nat.le_add_right _ _).trans (cavity_total_degree t ht)
  have hL0 := cavity_segment_nonneg hx0 hx.2 t u ht hu
  have hL := cavity_segment_bound hΔ hx0 hx.2 t u ht hu
  by_cases hxone : x = 1
  · rw [hxone]
    simpa only [sub_self, zero_div, mul_zero, zero_mul] using (contractionSquare_mem hΔ).1.le
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxone
  by_cases hex : Fintype.card C = 3 ∧ Δ = 4
  · have hstart : start (Fintype.card C) Δ = 3 / 4 := by simp only [start, if_pos hex]
    have hd4 := hex.2
    have hh := exceptional_certificate (by simpa [hd4] using htdegree)
      (hstart ▸ hx.1) hx.2 hL0 (by simpa [hex.1, hd4] using hL)
    have hk4 : contractionSquare Δ = 3 / 4 := by rw [hd4]; norm_num [contractionSquare]
    rw [hk4]
    exact hh
  have hstart : start (Fintype.card C) Δ = intervalStart (Fintype.card C) Δ := by simp only [start, if_neg hex]
  have hxstart : intervalStart (Fintype.card C) Δ ≤ x := hstart ▸ hx.1
  by_cases hgap : Fintype.card C + 3 ≤ Δ
  · have hkΔ := parameter_lt_degree hq (show Fintype.card C + 2 ≤ Δ by omega)
    have hbasic := intervalStart_ge_basic hq0 hdq (parameter_pos hq0 hdq) hkΔ
    have hpublished := bbr.proposition_2_6_i Δ hq hgap x hx0 hxlt (hbasic.trans hxstart) t u ht hu hdom hb
    have hfreer : (t.degree : ℝ) ≤ (Δ : ℝ) - 1 := by
      have hh : (t.degree : ℝ) + 1 ≤ Δ := by exact_mod_cast (show t.degree + 1 ≤ Δ by omega)
      linarith
    exact certificate_of_published_bound hq0 (by exact_mod_cast (show 1 < Δ by omega)) hr hkΔ
      ⟨Nat.cast_nonneg _, hfreer⟩ hxstart hx.2 hpublished
  · have hgap2 : Δ = Fintype.card C + 2 := by
      have hh := (integer_degree_gap hq hr).resolve_left hex
      omega
    exact small_degree_certificate hq hΔ (by have := gap_two_colours_le_six hq hgap2 hr; omega)
      htdegree ((gap_two_start_lower hq hgap2 hr).trans hxstart) hx.2 hL0 hL

def pointCoefficient (x : ℝ) (t : Girth.CavityTree C) : ℝ :=
  (1 - x) / Real.exp 1 * pointWeightSquare x (t.message x)

theorem point_coefficient_nonneg {x : ℝ} (hx : x ≤ 1) (t : Girth.CavityTree C) :
    0 ≤ pointCoefficient x t :=
  mul_nonneg (div_nonneg (sub_nonneg.mpr hx) (Real.exp_pos _).le) (pointWeightSquare_nonneg _ _)

theorem point_certificate (bbr : Literature C) {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) :
    (t.degree : ℝ) * pointCoefficient x t ≤ contractionSquare Δ := by
  have hx0 := (start_mem hq hr).1.trans_le hx.1
  have hfloor := CavityTree.message_uniform_lower hx0 le_rfl hx.2 t (Δ - 1) (cavity_total_degree t ht)
  have hp := pointWeight_le_segmentWeight hx0 hx.2 (Real.sqrt_pos.2 (pow_pos hx0 _)) (t.message x) hfloor
  have h := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (Nat.cast_nonneg t.degree) (div_nonneg (sub_nonneg.mpr hx.2) (Real.exp_pos 1).le))
  have h' : (t.degree : ℝ) * pointCoefficient x t ≤
      (t.degree : ℝ) * ((1 - x) / Real.exp 1) * segmentWeightSquare x (t.message x) (t.message x) := by
    simpa only [pointCoefficient, mul_assoc] using h
  exact h'.trans (contraction_certificate bbr hq hr hx t t ht ht (CLMM.SameDomain.refl t) rfl)

end BBR
end
end CI2ZF.Appendix
