import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Normalized analytic logarithms on disks

These are logarithms of functions, rather than pointwise principal
logarithms. Their derivative and base value make the branch explicit.
This is the branch infrastructure required by the Potts shell induction.
-/

namespace CI2ZF

open Set Metric Complex

noncomputable section

/-- A holomorphic nonzero function on a disk has a logarithm of its response
relative to the center. This construction does not require its image to
avoid the principal-logarithm branch cut. -/
theorem exists_normalized_log_on_ball (f : ℂ → ℂ) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hnz : ∀ z ∈ ball c r, f z ≠ 0) :
    ∃ L : ℂ → ℂ, L c = 0 ∧
      (∀ z ∈ ball c r, HasDerivAt L (deriv f z / f z) z) ∧
      ∀ z ∈ ball c r, exp (L z) = f z / f c := by
  have hc : c ∈ ball c r := mem_ball_self hr
  have hquot : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball c r) :=
    (hf.deriv isOpen_ball).div hf hnz
  obtain ⟨L, hLc, hL⟩ := hquot.isExactOn_ball.with_val_at c 0
  refine ⟨L, hLc, hL, ?_⟩
  have hprod : ∀ z ∈ ball c r,
      HasDerivAt (fun w => f w * exp (-L w)) 0 z := by
    intro z hz
    have hd := (hf.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.mul
      ((hL z hz).neg.cexp)
    convert hd using 1 <;> first | rfl | (field_simp [hnz z hz]; ring)
  intro z hz
  have heq : f z * exp (-L z) = f c * exp (-L c) :=
    isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      (fun w hw => (hprod w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hprod w hw).deriv) hz hc
  rw [hLc, neg_zero, exp_zero, mul_one, exp_neg, ← div_eq_mul_inv] at heq
  apply (eq_div_iff (hnz c hc)).mpr
  have hmul := (div_eq_iff (exp_ne_zero (L z))).mp heq
  simpa only [mul_comm] using hmul.symm

/-- Equal derivatives and an equal center value fix a branch uniquely. -/
theorem normalized_log_unique_on_ball {c : ℂ} {r : ℝ} (hr : 0 < r)
    (L M g : ℂ → ℂ)
    (hL : ∀ z ∈ ball c r, HasDerivAt L (g z) z)
    (hM : ∀ z ∈ ball c r, HasDerivAt M (g z) z)
    (hc : L c = M c) : EqOn L M (ball c r) := by
  apply isOpen_ball.eqOn_of_deriv_eq (convex_ball c r).isPreconnected
    (fun z hz => (hL z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hM z hz).differentiableAt.differentiableWithinAt)
  · intro z hz
    rw [(hL z hz).deriv, (hM z hz).deriv]
  · exact mem_ball_self hr
  · exact hc

/-- Two holomorphic logarithm branches of the same nonzero function agree
on the disk once their center values agree. This discharges the branch
identifications used when changing a shell color. -/
theorem logs_eq_on_ball_of_exp_eq {c : ℂ} {r : ℝ} (hr : 0 < r)
    (L M : ℂ → ℂ)
    (hL : DifferentiableOn ℂ L (ball c r))
    (hM : DifferentiableOn ℂ M (ball c r))
    (hexp : EqOn (fun z => exp (L z)) (fun z => exp (M z)) (ball c r))
    (hc : L c = M c) : EqOn L M (ball c r) := by
  apply isOpen_ball.eqOn_of_deriv_eq (convex_ball c r).isPreconnected hL hM
  · intro z hz
    have hDL := (hL.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.cexp
    have hDM := (hM.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.cexp
    have heq := hexp.deriv isOpen_ball hz
    rw [hDL.deriv, hDM.deriv] at heq
    have hexpz : exp (L z) = exp (M z) := hexp hz
    rw [hexpz] at heq
    exact mul_left_cancel₀ (exp_ne_zero (M z)) heq
  · exact mem_ball_self hr
  · exact hc

end
end CI2ZF
