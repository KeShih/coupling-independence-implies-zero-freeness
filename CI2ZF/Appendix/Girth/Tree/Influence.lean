import CI2ZF.Appendix.Girth.Tree.Levels

/-!
# Simultaneous aggregation of a whole tree level

The response is the actual product of the proved transformed update blocks,
with the exact root and terminal factors. The block contraction is applied
simultaneously to every branch, avoiding a factor exponential in the number
of descendants.
-/

namespace CI2ZF.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset Set PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

def levelResponse {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hq : Δ + 3 ≤ Fintype.card C) : (t : CavityTree C) → t.DegreeBudget Δ →
      (k : ℕ) → (t.Level k → C → ℝ) → C → ℝ
  | t, _, 0, h => terminalInfluenceAction (t.probabilityLaw x hx)
      (fun c => (1 - x) * t.probability x c) (h ())
  | .node d b child, ht, k + 1, h =>
      let I := localData x d b child hx hx1 hq ht
      fun c => scaledRowFactor (1 - x) (I.law.w c) *
        blockAction I.law I.input
          (fun i => levelResponse x hx hx1 hq (child i) (ht.2 i) k (fun v => h ⟨i, v⟩)) c

def terminalEnergyBound (q H : ℝ) : ℝ :=
  Real.exp (1 / 6) * (2 * (1 + Real.sqrt q) / 3) ^ 2 * H

theorem terminalEnergyBound_nonneg {q H : ℝ} (hH : 0 ≤ H) :
    0 ≤ terminalEnergyBound q H := by unfold terminalEnergyBound; positivity

/-- The weighted squared response energy decays once per non-root update. -/
theorem levelResponse_energy {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hq : Δ + 3 ≤ Fintype.card C) (t : CavityTree C) (ht : t.DegreeBudget Δ)
    (k : ℕ) (h : t.Level k → C → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hh : ∀ v, (∑ c, h v c ^ 2) ≤ H) :
    t.weightSquare x * (∑ c, levelResponse x hx hx1 hq t ht k h c ^ 2) ≤
      Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k * terminalEnergyBound (Fintype.card C) H := by
  induction k generalizing t with
  | zero =>
    have hterm := terminalInfluenceAction_energy (t.probabilityLaw x hx)
      (fun c => (1 - x) * t.probability x c) (h ())
      (t.scaled_probability_domain hx hx1 hq ht).1
    have hterm' := hterm.trans (mul_le_mul_of_nonneg_left (hh ()) (sq_nonneg _))
    have hterm'' : (∑ c, levelResponse x hx hx1 hq t ht 0 h c ^ 2) ≤
        (2 * (1 + Real.sqrt (Fintype.card C : ℝ)) / 3) ^ 2 * H := by
      simpa only [levelResponse] using hterm'
    simp only [pow_zero, one_mul]
    calc
      _ ≤ Real.exp (1 / 6) * (∑ c, levelResponse x hx hx1 hq t ht 0 h c ^ 2) :=
        mul_le_mul_of_nonneg_right (weightSquare_upper hx.le hq ht)
          (Finset.sum_nonneg fun c _ => sq_nonneg _)
      _ ≤ Real.exp (1 / 6) * ((2 * (1 + Real.sqrt (Fintype.card C : ℝ)) / 3) ^ 2 * H) :=
        mul_le_mul_of_nonneg_left hterm'' (Real.exp_pos _).le
      _ = _ := by unfold terminalEnergyBound; ring
  | succ k ih =>
    cases t with
    | node d b child =>
      let I := localData x d b child hx hx1 hq ht
      let g : Fin d → C → ℝ := fun i =>
        levelResponse x hx hx1 hq (child i) (ht.2 i) k (fun v => h ⟨i, v⟩)
      let T : ℝ := Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k * terminalEnergyBound (Fintype.card C) H
      have hT : 0 ≤ T := mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (terminalEnergyBound_nonneg hH)
      have hg (i : Fin d) : (∑ c, g i c ^ 2) ≤ T * (1 - I.childEntropy i) := by
        have hchild := ih (child i) (ht.2 i) (fun v => h ⟨i, v⟩) (fun v => hh ⟨i, v⟩)
        have he : 0 < 1 - (child i).entropy x := sub_pos.mpr (entropy_lt_one hx.le hq (ht.2 i))
        apply (div_le_iff₀ he).mp
        simpa only [weightSquare, one_div_mul_eq_div] using hchild
      have hlocal := I.weighted_scaled_matrix_contraction g
        (show 0 ≤ 1 - x by linarith) (show 1 - x ≤ 1 by linarith)
        ((CavityTree.node d b child).palette_le_card hx1) hT hg
      have heq : Real.exp (-8 / (81 * (Fintype.card C : ℝ))) * T =
          Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ (k + 1) * terminalEnergyBound (Fintype.card C) H := by
        unfold T
        rw [pow_succ]
        ring
      rw [heq] at hlocal
      simpa only [levelResponse, I, g, localData, LocalRecursion.parentEntropy,
        LocalRecursion.parentOdds, Fintype.card_fin, degree, weightSquare, entropy] using hlocal

def rootLevelResponse {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hq : Δ + 3 ≤ Fintype.card C) (p : FinDist C) (d : ℕ) (child : Fin d → CavityTree C)
    (ht : ∀ i, (child i).DegreeBudget Δ) (k : ℕ)
    (h : ((i : Fin d) × (child i).Level k) → C → ℝ) (c : C) : ℝ :=
  ∑ i, rootInfluenceAction p (fun b => (1 - x) * (child i).probability x b)
    (levelResponse x hx hx1 hq (child i) (ht i) k (fun v => h ⟨i, v⟩)) c

/-- The root costs at most its number of children, and all deeper levels
contract. This is the operator estimate used to convert to total influence. -/
theorem rootLevelResponse_energy {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hq : Δ + 3 ≤ Fintype.card C) (p : FinDist C) (d : ℕ) (child : Fin d → CavityTree C)
    (ht : ∀ i, (child i).DegreeBudget Δ) (k : ℕ)
    (h : ((i : Fin d) × (child i).Level k) → C → ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hh : ∀ v, (∑ c, h v c ^ 2) ≤ H) :
    (∑ c, rootLevelResponse x hx hx1 hq p d child ht k h c ^ 2) ≤
      (d : ℝ) ^ 2 * ((1 + Real.sqrt (Fintype.card C : ℝ)) / 2) ^ 2 *
        (Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k * terminalEnergyBound (Fintype.card C) H) := by
  let T : ℝ := Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k * terminalEnergyBound (Fintype.card C) H
  let g : Fin d → C → ℝ := fun i => levelResponse x hx hx1 hq (child i) (ht i) k (fun v => h ⟨i, v⟩)
  let f : Fin d → C → ℝ := fun i => rootInfluenceAction p
    (fun b => (1 - x) * (child i).probability x b) (g i)
  have hg (i : Fin d) : (∑ c, g i c ^ 2) ≤ T := by
    have hchild := levelResponse_energy x hx hx1 hq (child i) (ht i) k
      (fun v => h ⟨i, v⟩) hH (fun v => hh ⟨i, v⟩)
    have hm := mul_le_mul_of_nonneg_right (weightSquare_lower hx.le hq (ht i))
      (Finset.sum_nonneg (s := (Finset.univ : Finset C)) (fun c _ => sq_nonneg (g i c)))
    have hm' : (∑ c, g i c ^ 2) ≤ (child i).weightSquare x * (∑ c, g i c ^ 2) := by
      simpa only [one_mul] using hm
    exact hm'.trans hchild
  have hf (i : Fin d) : (∑ c, f i c ^ 2) ≤
      ((1 + Real.sqrt (Fintype.card C : ℝ)) / 2) ^ 2 * T := by
    exact (rootInfluenceAction_energy p (fun b => (1 - x) * (child i).probability x b) (g i)
      ((child i).scaled_probability_domain hx hx1 hq (ht i)).1).trans
        (mul_le_mul_of_nonneg_left (hg i) (sq_nonneg _))
  have hpoint (c : C) : (∑ i, f i c) ^ 2 ≤ (d : ℝ) * ∑ i, f i c ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ)) (fun i => f i c)
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using hcs
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hpoint c)
  have hsumf := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ => hf i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumf
  rw [← Finset.mul_sum, Finset.sum_comm] at hsum
  calc
    _ ≤ (d : ℝ) * ∑ i, ∑ c, f i c ^ 2 := hsum
    _ ≤ (d : ℝ) * ((d : ℝ) * (((1 + Real.sqrt (Fintype.card C : ℝ)) / 2) ^ 2 * T)) :=
      mul_le_mul_of_nonneg_left hsumf (Nat.cast_nonneg _)
    _ = _ := by ring

end

end CI2ZF.Appendix.Girth.CavityTree
