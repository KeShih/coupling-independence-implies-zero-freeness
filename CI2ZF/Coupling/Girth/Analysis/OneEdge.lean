import CI2ZF.Coupling.Girth.Analysis.Covariance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The complete one-edge variance bound

This is the colour-direction bound `girth5-one-edge-variance`. It is proved
for arbitrary finite cavity and update laws with the stated atom bounds,
including distributions with zero atoms. The proof retains the paper's
constant `(1 + sqrt(q / (m + 1))) / m`.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

noncomputable section

variable {C : Type*} [Fintype C]

theorem mean_sq_le_atom_bound (r : FinDist C) (h : C → ℝ) {p : ℝ}
    (hp : ∀ c, r.w c ≤ p) :
    expectReal r h ^ 2 ≤ p * ∑ c, h c ^ 2 := by
  have hv := variance_nonneg r h
  rw [← covariance_self, covariance_eq_moment] at hv
  have hm : expectReal r (fun c => h c * h c) ≤ p * ∑ c, h c ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    simpa only [pow_two] using mul_le_mul_of_nonneg_right (hp c) (sq_nonneg (h c))
  nlinarith

/-- Quantitative bound for subtracting a mean taken under a nonuniform
colour law in the unweighted Euclidean norm. -/
theorem centered_energy_bound (r : FinDist C) (h : C → ℝ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp : ∀ c, r.w c ≤ p) :
    (∑ c, (h c - expectReal r h) ^ 2) ≤
      (1 + Real.sqrt ((Fintype.card C : ℝ) * p)) ^ 2 * ∑ c, h c ^ 2 := by
  let H : ℝ := ∑ c, h c ^ 2
  let A : ℝ := ∑ c, h c
  let E : ℝ := expectReal r h
  let q : ℝ := Fintype.card C
  have hH : 0 ≤ H := Finset.sum_nonneg fun c _ => sq_nonneg (h c)
  have hq : 0 ≤ q := Nat.cast_nonneg _
  have hE : E ^ 2 ≤ p * H := mean_sq_le_atom_bound r h hp
  have hA : A ^ 2 ≤ q * H := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C) h (fun _ => (1 : ℝ))
    simpa [A, H, q, mul_comm] using hcs
  have hsqrt : Real.sqrt (q * p) ^ 2 = q * p := Real.sq_sqrt (mul_nonneg hq hp0)
  have hproduct : (E * A) ^ 2 ≤ (Real.sqrt (q * p) * H) ^ 2 := by
    have hmul := mul_le_mul hE hA (sq_nonneg A) (mul_nonneg hp0 hH)
    calc
      (E * A) ^ 2 = E ^ 2 * A ^ 2 := mul_pow _ _ _
      _ ≤ p * H * (q * H) := hmul
      _ = (Real.sqrt (q * p) * H) ^ 2 := by rw [mul_pow, hsqrt]; ring
  have hcross : -(Real.sqrt (q * p) * H) ≤ E * A := by
    have habs : |E * A| ≤ Real.sqrt (q * p) * H := by
      apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hH)).mp
      simpa only [sq_abs] using hproduct
    exact (abs_le.mp habs).1
  have hid : (∑ c, (h c - E) ^ 2) = H - 2 * E * A + q * E ^ 2 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [H, A, q]
    rw [← Finset.mul_sum]
    ring
  have hqE := mul_le_mul_of_nonneg_left hE hq
  change (∑ c, (h c - E) ^ 2) ≤ (1 + Real.sqrt (q * p)) ^ 2 * H
  rw [hid]
  nlinarith

/-- Expectation across an antiferromagnetic edge, viewed as a function of
the colour at the opposite endpoint. -/
def edgeResponse (s : ℝ) (r : FinDist C) (h : C → ℝ) (t : C) : ℝ :=
  (expectReal r h - s * r.w t * h t) / (1 - s * r.w t)

theorem edgeResponse_centered {s : ℝ} (r : FinDist C) (h : C → ℝ) (t : C)
    (hd : 1 - s * r.w t ≠ 0) :
    edgeResponse s r h t - expectReal r h =
      -(s * r.w t / (1 - s * r.w t)) * (h t - expectReal r h) := by
  unfold edgeResponse
  field_simp
  ring

theorem edge_occupancy_bound {s m : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hm : 0 < m)
    (r : FinDist C) (hr : ∀ c, r.w c ≤ 1 / (m + 1)) (c : C) :
    0 < 1 - s * r.w c ∧
      0 ≤ s * r.w c / (1 - s * r.w c) ∧
      s * r.w c / (1 - s * r.w c) ≤ 1 / m := by
  have hsr0 := mul_nonneg hs0 (r.nonneg c)
  have hsr : s * r.w c ≤ 1 / (m + 1) := by
    exact (mul_le_mul_of_nonneg_right hs1 (r.nonneg c)).trans (by simpa using hr c)
  have hm1 : 0 < m + 1 := by linarith
  have hmul := (le_div_iff₀ hm1).mp hsr
  have hlt : s * r.w c < 1 := by nlinarith
  have hd : 0 < 1 - s * r.w c := by linarith
  refine ⟨hd, div_nonneg hsr0 hd.le, ?_⟩
  apply (div_le_div_iff₀ hd hm).mpr
  nlinarith

/-- The exact variance constant of the paper, with no independence or
strict positivity assumption on the two finite colour distributions. -/
theorem one_edge_variance_bound {s m B : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hm : 0 < m) (hB : 0 ≤ B)
    (r ρ : FinDist C) (hr : ∀ c, r.w c ≤ 1 / (m + 1))
    (hρ : ∀ c, ρ.w c ≤ B) (h : C → ℝ) :
    variance ρ (edgeResponse s r h) ≤
      B * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m + 1))) / m) ^ 2 *
        ∑ c, h c ^ 2 := by
  have hp0 : 0 ≤ 1 / (m + 1) := by positivity
  have hc := centered_energy_bound r h hp0 hr
  have hpoint (c : C) : (edgeResponse s r h c - expectReal r h) ^ 2 ≤
      (1 / m) ^ 2 * (h c - expectReal r h) ^ 2 := by
    obtain ⟨hd, ht0, ht1⟩ := edge_occupancy_bound hs0 hs1 hm r hr c
    rw [edgeResponse_centered r h c hd.ne', mul_pow, neg_sq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht1 2) (sq_nonneg _)
  calc
    _ ≤ B * ∑ c, (edgeResponse s r h c - expectReal r h) ^ 2 :=
      variance_le_atom_bound ρ _ hρ _
    _ ≤ B * ((1 / m) ^ 2 * ∑ c, (h c - expectReal r h) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hB
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun c _ => hpoint c
    _ ≤ B * ((1 / m) ^ 2 *
        ((1 + Real.sqrt ((Fintype.card C : ℝ) * (1 / (m + 1)))) ^ 2 *
          ∑ c, h c ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc (sq_nonneg _)) hB
    _ = _ := by
      rw [mul_one_div]
      ring

end

end CI2ZF.Appendix.Girth
