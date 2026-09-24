import CI2ZF.Coupling.BBR.Certificate

/-! The branch-normalized finite-difference induction on actual messages.
The source supplies only its local inequality; all spatial decay is proved. -/
namespace CI2ZF.Appendix
open scoped BigOperators
open Finset Set PottsCI
open Girth
noncomputable section
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

theorem CLMM.SameDomain.children {d : ℕ} {b b' : C → ℕ} {t u : Fin d → CavityTree C}
    (h : CLMM.SameDomain (.node d b t) (.node d b' u)) (i : Fin d) : CLMM.SameDomain (t i) (u i) := by
  cases h with
  | node _ _ _ _ _ _ ht => exact ht i

theorem Girth.CavityTree.Agreement.boundary_eq {k : ℕ} {t u : CavityTree C}
    (h : Girth.CavityTree.Agreement (k + 1) t u) : t.boundary = u.boundary := by
  cases h
  rfl

theorem Girth.CavityTree.message_one (t : CavityTree C) (c : C) : t.message 1 c = 1 := by
  cases t with
  | node d b child => simp [Girth.CavityTree.message, Girth.CavityTree.ratioSquare]

namespace BBR

def messageDistance (x : ℝ) (t u : Girth.CavityTree C) : ℝ :=
  squareMass (fun c => t.message x c - u.message x c)

theorem messageDistance_nonneg (x : ℝ) (t u : Girth.CavityTree C) : 0 ≤ messageDistance x t u := squareMass_nonneg _

theorem messageDistance_le_card {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (t u : Girth.CavityTree C) :
    messageDistance x t u ≤ Fintype.card C := by
  have hh : ∀ c, (t.message x c - u.message x c) ^ 2 ≤ 1 := by
    intro c
    have ht0 := (t.message_pos hx c).le
    have hu0 := (u.message_pos hx c).le
    have ht1 := (t.message_bounds hx hx1 c).2
    have hu1 := (u.message_bounds hx hx1 c).2
    have hd : |t.message x c - u.message x c| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    nlinarith [sq_abs (t.message x c - u.message x c), abs_nonneg (t.message x c - u.message x c)]
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hh c)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, messageDistance, squareMass] using hs

@[simp] theorem messageDistance_one (t u : Girth.CavityTree C) : messageDistance 1 t u = 0 := by
  simp [messageDistance, squareMass, Girth.CavityTree.message_one]

theorem finite_difference_step (bbr : Literature C) {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1) (hx1 : x < 1)
    (d : ℕ) (b : C → ℕ) (t u : Fin d → Girth.CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (t i).DegreeBudget Δ) (hu : ∀ i, (u i).DegreeBudget Δ)
    (hdom : ∀ i, CLMM.SameDomain (t i) (u i)) (hb : ∀ i, (t i).boundary = (u i).boundary)
    {T : ℝ} (hT : 0 ≤ T)
    (hchild : ∀ i, messageDistance x (t i) (u i) ≤ ((t i).degree : ℝ) * T) :
    messageDistance x (.node d b t) (.node d b u) ≤ (d : ℝ) * contractionSquare Δ * T := by
  have hx0 := (start_mem hq hr).1.trans_le hx.1
  have hdq := degree_gt_colours (Nat.cast_pos.mpr Fintype.card_pos) hr
  have hdqn : Fintype.card C < Δ := by exact_mod_cast hdq
  have hΔ : 3 ≤ Δ := by omega
  have hlocal := bbr.theorem_2_5 Δ hΔ (by omega) x hx0 hx1 d b t u hroot ht hu hdom
  let w : Fin d → ℝ := fun i => (1 - x) / Real.exp 1 * segmentWeightSquare x ((t i).message x) ((u i).message x)
  have hw (i : Fin d) : 0 ≤ w i := mul_nonneg (div_nonneg (sub_nonneg.mpr hx.2) (Real.exp_pos _).le)
    (cavity_segment_nonneg hx0 hx.2 (t i) (u i) (ht i) (hu i))
  have hcert (i : Fin d) : ((t i).degree : ℝ) * w i ≤ contractionSquare Δ := by
    simpa only [w, mul_assoc] using contraction_certificate bbr hq hr hx (t i) (u i) (ht i) (hu i) (hdom i) (hb i)
  calc
    _ ≤ ∑ i, w i * messageDistance x (t i) (u i) := hlocal
    _ ≤ ∑ i, w i * (((t i).degree : ℝ) * T) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hchild i) (hw i)
    _ = ∑ i, (((t i).degree : ℝ) * w i) * T := Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ _i : Fin d, contractionSquare Δ * T := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcert i) hT
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem cavity_spatial_energy (bbr : Literature C) {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (k : ℕ) (t u : Girth.CavityTree C) (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ)
    (hdom : CLMM.SameDomain t u) (hag : Girth.CavityTree.Agreement (k + 1) t u) :
    messageDistance x t u ≤ (t.degree : ℝ) * (Fintype.card C : ℝ) * contractionSquare Δ ^ k := by
  have hx0 := (start_mem hq hr).1.trans_le hx.1
  have hdq := degree_gt_colours (Nat.cast_pos.mpr Fintype.card_pos) hr
  have hdqn : Fintype.card C < Δ := by exact_mod_cast hdq
  have hΔ : 2 ≤ Δ := by omega
  have hκ := (contractionSquare_mem hΔ).1.le
  by_cases hxone : x = 1
  · rw [hxone, messageDistance_one]
    positivity
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxone
  induction k generalizing t u with
  | zero =>
    cases hag with
    | succ _ d b t u hag =>
      by_cases hd : d = 0
      · subst d
        simp [messageDistance, squareMass, Girth.CavityTree.message, Girth.CavityTree.ratioSquare, Girth.CavityTree.degree]
      · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
        have hh := mul_le_mul_of_nonneg_right hd1 (Nat.cast_nonneg (Fintype.card C) : (0 : ℝ) ≤ Fintype.card C)
        exact (messageDistance_le_card hx0 hx.2 _ _).trans (by simpa [Girth.CavityTree.degree] using hh)
  | succ k ih =>
    cases hag with
    | succ _ d b t u hag =>
      have hc (i : Fin d) : messageDistance x (t i) (u i) ≤
          ((t i).degree : ℝ) * ((Fintype.card C : ℝ) * contractionSquare Δ ^ k) := by
        simpa only [mul_assoc] using ih (t i) (u i) (ht.2 i) (hu.2 i) (hdom.children i) (hag i)
      have hh := finite_difference_step bbr hq hr hx hxlt d b t u (by have := ht.1; omega)
        ht.2 hu.2 hdom.children (fun i => (hag i).boundary_eq) (by positivity) hc
      simpa only [Girth.CavityTree.degree, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh

/-- Message SSM at distance `k+2`, including the global root of degree Δ. -/
theorem root_spatial_energy (bbr : Literature C) {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (k d : ℕ) (b : C → ℕ) (t u : Fin d → Girth.CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (t i).DegreeBudget Δ) (hu : ∀ i, (u i).DegreeBudget Δ)
    (hdom : ∀ i, CLMM.SameDomain (t i) (u i)) (hag : ∀ i, Girth.CavityTree.Agreement k (t i) (u i)) :
    messageDistance x (.node d b t) (.node d b u) ≤
      (Δ : ℝ) * (Fintype.card C : ℝ) * contractionSquare Δ ^ k := by
  have hx0 := (start_mem hq hr).1.trans_le hx.1
  have hdq := degree_gt_colours (Nat.cast_pos.mpr Fintype.card_pos) hr
  have hdqn : Fintype.card C < Δ := by exact_mod_cast hdq
  have hΔ : 2 ≤ Δ := by omega
  have hκ := (contractionSquare_mem hΔ).1.le
  by_cases hxone : x = 1
  · rw [hxone, messageDistance_one]
    positivity
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hxone
  cases k with
  | zero =>
    have hΔ1 : (1 : ℝ) ≤ Δ := by exact_mod_cast (show 1 ≤ Δ by omega)
    have hh := mul_le_mul_of_nonneg_right hΔ1 (Nat.cast_nonneg (Fintype.card C) : (0 : ℝ) ≤ Fintype.card C)
    exact (messageDistance_le_card hx0 hx.2 _ _).trans (by simpa using hh)
  | succ k =>
    have hc (i : Fin d) : messageDistance x (t i) (u i) ≤
        ((t i).degree : ℝ) * ((Fintype.card C : ℝ) * contractionSquare Δ ^ k) := by
      simpa only [mul_assoc] using cavity_spatial_energy bbr hq hr hx k (t i) (u i) (ht i) (hu i) (hdom i) (hag i)
    have hh := finite_difference_step bbr hq hr hx hxlt d b t u hroot ht hu hdom
      (fun i => (hag i).boundary_eq) (by positivity) hc
    have hd : (d : ℝ) ≤ Δ := by exact_mod_cast (show d ≤ Δ by omega)
    calc
      _ ≤ (d : ℝ) * contractionSquare Δ * ((Fintype.card C : ℝ) * contractionSquare Δ ^ k) := hh
      _ ≤ (Δ : ℝ) * contractionSquare Δ * ((Fintype.card C : ℝ) * contractionSquare Δ ^ k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hκ) (by positivity)
      _ = _ := by rw [pow_succ]; ring

end BBR
end
end CI2ZF.Appendix
