import CI2ZF.Coupling.BBR.Certificate
import CI2ZF.Coupling.BBR.Jacobian

/-! Simultaneous tree-level Jacobian contraction. The induction retains
the free-child count and handles vanishing branches without division. -/
namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open CI2ZF.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

def uniformA (q : ℕ) (Δ : ℕ) (x₀ : ℝ) : ℝ :=
  (1 - x₀) / (Real.exp 1 * q * x₀ ^ (Δ + 1))

theorem uniformA_nonneg {q Δ : ℕ} {x₀ : ℝ} (hx₀ : 0 ≤ x₀) (hx₀1 : x₀ ≤ 1) :
    0 ≤ uniformA q Δ x₀ := by unfold uniformA; positivity

theorem uniformA_pos {q Δ : ℕ} (hq : 0 < q) {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    0 < uniformA q Δ x₀ := by unfold uniformA; positivity

theorem point_coefficient_uniform {Δ : ℕ} (hΔ : 2 ≤ Δ)
    {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x₀ ≤ x) (hx1 : x ≤ 1)
    (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) :
    pointCoefficient x t ≤ uniformA (Fintype.card C) Δ x₀ := by
  have hx0 := hx₀.trans_le hx
  have hfloor := CavityTree.message_uniform_lower hx0 le_rfl hx1 t (Δ - 1) (cavity_total_degree t ht)
  have hp := (pointWeight_le_segmentWeight hx0 hx1 (Real.sqrt_pos.2 (pow_pos hx0 _)) (t.message x) hfloor).trans
    (cavity_segment_bound hΔ hx0 hx1 t t ht ht)
  have hq : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hd0 : (0 : ℝ) < Fintype.card C * x₀ ^ (Δ + 1) := by positivity
  have hden := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx₀.le hx (Δ + 1)) hq.le
  have hratio : 1 / ((Fintype.card C : ℝ) * x ^ (Δ + 1)) ≤
      1 / ((Fintype.card C : ℝ) * x₀ ^ (Δ + 1)) := div_le_div_of_nonneg_left (by norm_num) hd0 hden
  calc
    _ ≤ ((1 - x) / Real.exp 1) * (1 / ((Fintype.card C : ℝ) * x ^ (Δ + 1))) :=
      mul_le_mul_of_nonneg_left hp (div_nonneg (sub_nonneg.mpr hx1) (Real.exp_pos _).le)
    _ ≤ ((1 - x₀) / Real.exp 1) * (1 / ((Fintype.card C : ℝ) * x₀ ^ (Δ + 1))) :=
      mul_le_mul (div_le_div_of_nonneg_right (by linarith) (Real.exp_pos _).le) hratio
        (by positivity) (by have := hx.trans hx1; positivity)
    _ = _ := by unfold uniformA; ring

def RootBudget (Δ : ℕ) : Girth.CavityTree C → Prop
  | .node d b child => d + (∑ c, b c) ≤ Δ ∧ ∀ i, (child i).DegreeBudget Δ

theorem rootBudget_of_cavity {Δ : ℕ} (t : Girth.CavityTree C) (ht : t.DegreeBudget Δ) : RootBudget Δ t := by
  cases t with
  | node d b child => exact ⟨by have := ht.1; omega, ht.2⟩

theorem node_differential {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (d : ℕ) (b : C → ℕ) (child : Fin d → Girth.CavityTree C) (z : Fin d → C → ℝ) :
    squareMass (fun c => ∑ i, jacobianBlock x ((Girth.CavityTree.node d b child).message x)
      ((child i).message x) (z i) c) ≤
      ∑ i, pointCoefficient x (child i) * squareMass (z i) := by
  let B : C → ℝ := fun c => Real.sqrt (x ^ b c)
  let R : Fin d → C → ℝ := fun i => (child i).message x
  have hB (c : C) : B c ^ 2 ≤ 1 := by
    dsimp [B]
    rw [Real.sq_sqrt (pow_nonneg hx.le _)]
    exact pow_le_one₀ hx.le hx1
  have h := differential_contraction hx hx1 B hB R z (fun i => (child i).squareMass_pos hx)
  have heq : localRoot x B R = (Girth.CavityTree.node d b child).message x := by
    funext c
    exact (Girth.CavityTree.message_node hx hx1 d b child c).symm
  rw [heq] at h
  exact h

def response (x : ℝ) : (t : Girth.CavityTree C) → (k : ℕ) → (t.Level k → C → ℝ) → C → ℝ
  | t, 0, h => fun c => t.message x c * h () c
  | .node d b child, k + 1, h => fun c =>
      ∑ i, jacobianBlock x ((Girth.CavityTree.node d b child).message x) ((child i).message x)
        (response x (child i) k (fun v => h ⟨i, v⟩)) c

theorem terminal_response_bound {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (t : Girth.CavityTree C) (h : t.Level 0 → C → ℝ) {H : ℝ}
    (hh : ∀ v, squareMass (h v) ≤ H) : squareMass (response x t 0 h) ≤ H := by
  calc
    _ ≤ squareMass (h ()) := by
      apply Finset.sum_le_sum
      intro c _
      rw [response]
      change (t.message x c * h () c) ^ 2 ≤ h () c ^ 2
      rw [mul_pow]
      have hm := (t.ratioSquare_bounds hx hx1 c).2
      rw [← t.message_sq hx c] at hm
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (sq_nonneg (h () c))
    _ ≤ H := hh ()

/-- Exact branch-count induction for all perturbations on a sphere. -/
theorem response_energy (bbr : Literature C) {Δ : ℕ}
    (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (k : ℕ) (t : Girth.CavityTree C) (ht : RootBudget Δ t)
    (h : t.Level (k + 1) → C → ℝ) {H : ℝ} (hH : 0 ≤ H) (hh : ∀ v, squareMass (h v) ≤ H) :
    squareMass (response x t (k + 1) h) ≤ (t.degree : ℝ) *
      uniformA (Fintype.card C) Δ (start (Fintype.card C) Δ) * contractionSquare Δ ^ k * H := by
  have hstart := start_mem hq hr
  have hx0 := hstart.1.trans_le hx.1
  have hdq := degree_gt_colours (Nat.cast_pos.mpr Fintype.card_pos) hr
  have hn : Fintype.card C < Δ := by exact_mod_cast hdq
  have hΔ : 2 ≤ Δ := by omega
  have hκ := (contractionSquare_mem hΔ).1.le
  let A := uniformA (Fintype.card C) Δ (start (Fintype.card C) Δ)
  have hA : 0 ≤ A := uniformA_nonneg hstart.1.le hstart.2.le
  induction k generalizing t with
  | zero =>
    cases t with
    | node d b child =>
      have hlocal := node_differential hx0 hx.2 d b child
        (fun i => response x (child i) 0 (fun v => h ⟨i, v⟩))
      have hs : (∑ i, pointCoefficient x (child i) *
          squareMass (response x (child i) 0 (fun v => h ⟨i, v⟩))) ≤ (d : ℝ) * A * H := by
        calc
          _ ≤ ∑ _i : Fin d, A * H := Finset.sum_le_sum fun i _ =>
            mul_le_mul (point_coefficient_uniform hΔ hstart.1 hx.1 hx.2 (child i) (ht.2 i))
              (terminal_response_bound hx0 hx.2 (child i) _ (fun v => hh ⟨i, v⟩))
              (squareMass_nonneg _) hA
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      simpa only [response, Girth.CavityTree.degree, pow_zero, mul_one, A] using hlocal.trans hs
  | succ k ih =>
    cases t with
    | node d b child =>
      let z : Fin d → C → ℝ := fun i => response x (child i) (k + 1) (fun v => h ⟨i, v⟩)
      let T := A * contractionSquare Δ ^ k * H
      have hT : 0 ≤ T := mul_nonneg (mul_nonneg hA (pow_nonneg hκ _)) hH
      have hchild (i : Fin d) : squareMass (z i) ≤ ((child i).degree : ℝ) * T := by
        have hh' := ih (child i) (rootBudget_of_cavity (child i) (ht.2 i))
          (fun v => h ⟨i, v⟩) (fun v => hh ⟨i, v⟩)
        simpa only [z, T, A, mul_assoc] using hh'
      have hlocal := node_differential hx0 hx.2 d b child z
      have hs : (∑ i, pointCoefficient x (child i) * squareMass (z i)) ≤
          (d : ℝ) * A * contractionSquare Δ ^ (k + 1) * H := by
        calc
          _ ≤ ∑ i, pointCoefficient x (child i) * (((child i).degree : ℝ) * T) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hchild i) (point_coefficient_nonneg hx.2 _)
          _ = ∑ i, (((child i).degree : ℝ) * pointCoefficient x (child i)) * T := by
            exact Finset.sum_congr rfl fun _ _ => by ring
          _ ≤ ∑ _i : Fin d, contractionSquare Δ * T := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_right (point_certificate bbr hq hr hx (child i) (ht.2 i)) hT
          _ = _ := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, T, pow_succ]
            ring
      simpa only [response, z, Girth.CavityTree.degree, A] using hlocal.trans hs

end
end CI2ZF.Appendix.BBR
