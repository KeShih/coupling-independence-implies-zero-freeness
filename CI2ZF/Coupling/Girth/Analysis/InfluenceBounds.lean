import CI2ZF.Coupling.Girth.Analysis.Scaled

/-!
# Root and terminal factors in the tree influence identity

The root marginal cancels algebraically before an energy estimate is
taken. Neither norm bound requires a lower bound on a marginal atom.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

noncomputable section

variable {C : Type*} [Fintype C]

theorem probability_atom_le_one (p : FinDist C) (c : C) : p.w c ≤ 1 := by
  have h := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset C)) => p.nonneg b)
    (Finset.mem_univ c)
  simpa only [p.sum_one] using h

def centerByLaw (p : FinDist C) (z : C → ℝ) (c : C) : ℝ := z c - expectReal p z

/-- The Euclidean norm of `I - 1 pᵀ` is at most `1 + √q`. -/
theorem centerByLaw_energy [Nonempty C] (p : FinDist C) (z : C → ℝ) :
    (∑ c, centerByLaw p z c ^ 2) ≤
      (1 + Real.sqrt (Fintype.card C : ℝ)) ^ 2 * ∑ c, z c ^ 2 := by
  let q : ℝ := Fintype.card C
  let r : ℝ := Real.sqrt q
  let Z : ℝ := ∑ c, z c ^ 2
  let t : ℝ := expectReal p z
  have hq : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0 < r := Real.sqrt_pos.mpr hq
  have hr2 : r ^ 2 = q := Real.sq_sqrt hq.le
  have ht : t ^ 2 ≤ Z := by
    have hv := variance_nonneg p z
    rw [← covariance_self, covariance_eq_moment] at hv
    have he : expectReal p (fun c => z c * z c) ≤ Z := by
      apply Finset.sum_le_sum
      intro c _
      simpa only [pow_two] using
        mul_le_of_le_one_left (sq_nonneg (z c)) (probability_atom_le_one p c)
    change 0 ≤ expectReal p (fun c => z c * z c) - t * t at hv
    nlinarith
  have hpoint (c : C) : r * (z c - t) ^ 2 ≤
      (1 + r) * (r * z c ^ 2 + t ^ 2) := by nlinarith [sq_nonneg (r * z c + t)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hpoint c)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  have hbound : r * (∑ c, centerByLaw p z c ^ 2) ≤ r * ((1 + r) ^ 2 * Z) := by
    calc
      _ ≤ (1 + r) * (r * Z + q * t ^ 2) := hsum
      _ ≤ (1 + r) * (r * Z + q * Z) := mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left ht hq.le) _) (by linarith)
      _ = _ := by rw [← hr2]; ring
  exact (mul_le_mul_iff_right₀ hr).mp hbound

def rootInfluenceAction (p : FinDist C) (m h : C → ℝ) (c : C) : ℝ :=
  -centerByLaw p (fun b => Real.sqrt (m b) * h b) c

theorem rootInfluenceAction_energy [Nonempty C] (p : FinDist C) (m h : C → ℝ)
    (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1 / 4) :
    (∑ c, rootInfluenceAction p m h c ^ 2) ≤
      ((1 + Real.sqrt (Fintype.card C : ℝ)) / 2) ^ 2 * ∑ c, h c ^ 2 := by
  have hdiag : (∑ c, (Real.sqrt (m c) * h c) ^ 2) ≤ (1 / 4 : ℝ) * ∑ c, h c ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    rw [mul_pow, Real.sq_sqrt (hm c).1]
    exact mul_le_mul_of_nonneg_right (hm c).2 (sq_nonneg _)
  calc
    _ = ∑ c, centerByLaw p (fun b => Real.sqrt (m b) * h b) c ^ 2 := by
      simp only [rootInfluenceAction, neg_sq]
    _ ≤ (1 + Real.sqrt (Fintype.card C : ℝ)) ^ 2 *
        ∑ c, (Real.sqrt (m c) * h c) ^ 2 := centerByLaw_energy _ _
    _ ≤ (1 + Real.sqrt (Fintype.card C : ℝ)) ^ 2 * ((1 / 4 : ℝ) * ∑ c, h c ^ 2) :=
      mul_le_mul_of_nonneg_left hdiag (sq_nonneg _)
    _ = _ := by ring

def terminalInfluenceAction (p : FinDist C) (m h : C → ℝ) (c : C) : ℝ :=
  Real.sqrt (m c) / (1 - m c) * centerByLaw p h c

theorem terminal_diagonal_bound {m : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1 / 4) :
    0 ≤ Real.sqrt m / (1 - m) ∧ Real.sqrt m / (1 - m) ≤ 2 / 3 := by
  have hd : 0 < 1 - m := by linarith
  have hs : Real.sqrt m ≤ 1 / 2 := by nlinarith [Real.sqrt_nonneg m, Real.sq_sqrt hm]
  refine ⟨div_nonneg (Real.sqrt_nonneg _) hd.le, ?_⟩
  apply (div_le_iff₀ hd).mpr
  linarith

theorem terminalInfluenceAction_energy [Nonempty C] (p : FinDist C) (m h : C → ℝ)
    (hm : ∀ c, 0 ≤ m c ∧ m c ≤ 1 / 4) :
    (∑ c, terminalInfluenceAction p m h c ^ 2) ≤
      (2 * (1 + Real.sqrt (Fintype.card C : ℝ)) / 3) ^ 2 * ∑ c, h c ^ 2 := by
  have hd : (∑ c, terminalInfluenceAction p m h c ^ 2) ≤
      (4 / 9 : ℝ) * ∑ c, centerByLaw p h c ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    rw [terminalInfluenceAction, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hb := terminal_diagonal_bound (hm c).1 (hm c).2
    nlinarith [hb.1, hb.2]
  calc
    _ ≤ (4 / 9 : ℝ) * ∑ c, centerByLaw p h c ^ 2 := hd
    _ ≤ (4 / 9 : ℝ) * ((1 + Real.sqrt (Fintype.card C : ℝ)) ^ 2 * ∑ c, h c ^ 2) :=
      mul_le_mul_of_nonneg_left (centerByLaw_energy p h) (by norm_num)
    _ = _ := by ring

variable [DecidableEq C]

/-- Exact cancellation of the root diagonal in one transformed block. -/
theorem root_factor_cancellation {D : Type*} [Fintype D]
    (p : FinDist C) (m : D → C → ℝ) (i : D) (c b : C) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hp : 0 < p.w c) (hp1 : p.w c < 1) :
    (scaledRowFactor s (p.w c) * transformedBlock p m i c b) /
      (Real.sqrt (s * p.w c) / (1 - s * p.w c)) =
        (p.w b - if b = c then 1 else 0) * Real.sqrt (m i b) := by
  have hsp : s * p.w c < 1 := (mul_le_of_le_one_left hp.le hs1).trans_lt hp1
  unfold scaledRowFactor transformedBlock potentialDiagonal
  rw [Real.sqrt_mul hs.le]
  field_simp [show Real.sqrt s ≠ 0 from (Real.sqrt_pos.mpr hs).ne',
    show Real.sqrt (p.w c) ≠ 0 from (Real.sqrt_pos.mpr hp).ne',
    show 1 - p.w c ≠ 0 by linarith, show 1 - s * p.w c ≠ 0 by linarith]
  field_simp [show 1 - p.w c * s ≠ 0 by nlinarith]

end

end CI2ZF.Appendix.Girth
