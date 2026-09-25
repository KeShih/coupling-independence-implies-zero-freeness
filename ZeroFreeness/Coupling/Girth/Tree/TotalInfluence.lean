import ZeroFreeness.Coupling.Girth.Tree.Influence

/-!
# Total influence from the cited influence/Jacobian identity

The only cited result in this file is the exact general tree
factorization of CLMM2023, Lemma 8.7, a hypothesis here proved as
`clmmInfluenceIdentity` in `InfluenceIdentity`. Its interface is an equality between
the actual conditional Gibbs marginals and the explicit derivative-block
product. It assumes no decay, coupling bound, or CI conclusion. All norm
estimates and the total-influence conversion are proved below.
-/

namespace ZeroFreeness.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset Set PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- CLMM2023, Lemma 8.7, in finite-tree configuration coordinates. The row
and terminal factors were derived in `Analysis.InfluenceBounds`; this field
is only the general influence factorization identity. Proved as
`clmmInfluenceIdentity` in `ZeroFreeness.Coupling.Girth.Tree.InfluenceIdentity`. -/
structure CLMMInfluenceIdentity (C : Type*) [Fintype C] [DecidableEq C] [Nonempty C] : Prop where
  factorization : ∀ {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x < 1)
    (hq : Δ + 3 ≤ Fintype.card C) (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    (_hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (child i).DegreeBudget Δ) (k : ℕ)
    (h : (CavityTree.node d b child).Level (k + 1) → C → ℝ) (a : C),
    (∑ v, ∑ c, (CavityTree.node d b child).influenceBlock x hx (k + 1) v a c * h v c) =
      rootLevelResponse x hx hx1.le hq ((CavityTree.node d b child).probabilityLaw x hx)
        d child ht k h a

def totalInfluenceConstant (d q : ℝ) : ℝ :=
  d * Real.exp (1 / 12) * Real.sqrt q * (1 + Real.sqrt q) ^ 2 / 3

theorem totalInfluenceConstant_nonneg {d q : ℝ} (hd : 0 ≤ d) :
    0 ≤ totalInfluenceConstant d q := by unfold totalInfluenceConstant; positivity

def signWitness (r : ℝ) : ℝ := if 0 ≤ r then 1 else -1

theorem mul_signWitness (r : ℝ) : r * signWitness r = |r| := by
  unfold signWitness
  split_ifs with hr
  · simp only [mul_one, abs_of_nonneg hr]
  · simp only [mul_neg, mul_one, abs_of_neg (lt_of_not_ge hr)]

theorem signWitness_sq (r : ℝ) : signWitness r ^ 2 = 1 := by unfold signWitness; split_ifs <;> norm_num

theorem source_amplitude_square (d : ℕ) (k : ℕ) :
    (totalInfluenceConstant d (Fintype.card C) * decayRate (Fintype.card C) ^ k) ^ 2 =
      (d : ℝ) ^ 2 * ((1 + Real.sqrt (Fintype.card C : ℝ)) / 2) ^ 2 *
        (Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k *
          terminalEnergyBound (Fintype.card C) (Fintype.card C)) := by
  have he : Real.exp (1 / 12 : ℝ) ^ 2 = Real.exp (1 / 6) := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hr : (decayRate (Fintype.card C) ^ k) ^ 2 =
      (decayRate (Fintype.card C) ^ 2) ^ k := by simp only [← pow_mul, Nat.mul_comm]
  unfold totalInfluenceConstant terminalEnergyBound
  rw [mul_pow, div_pow, mul_pow, mul_pow, mul_pow, he,
    Real.sq_sqrt (Nat.cast_nonneg _), hr, decayRate_sq]
  ring

/-- Every source row has uniformly bounded total absolute influence over
the whole level. The test signs are chosen from the actual influence row. -/
theorem absolute_influence_row_bound (identity : CLMMInfluenceIdentity C)
    {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (hq : Δ + 3 ≤ Fintype.card C)
    (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (child i).DegreeBudget Δ) (k : ℕ) (a : C) :
    (∑ v, ∑ c, |(CavityTree.node d b child).influenceBlock x hx (k + 1) v a c|) ≤
      totalInfluenceConstant d (Fintype.card C) * decayRate (Fintype.card C) ^ k := by
  let tree := CavityTree.node d b child
  let h : tree.Level (k + 1) → C → ℝ := fun v c => signWitness (tree.influenceBlock x hx (k + 1) v a c)
  let R := rootLevelResponse x hx hx1.le hq (tree.probabilityLaw x hx) d child ht k h
  have hh (v : tree.Level (k + 1)) : (∑ c, h v c ^ 2) ≤ (Fintype.card C : ℝ) := by
    simp only [h, signWitness_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, le_refl]
  have henergy := rootLevelResponse_energy x hx hx1.le hq (tree.probabilityLaw x hx)
    d child ht k h (Nat.cast_nonneg (Fintype.card C)) hh
  have hid : (∑ v, ∑ c, |tree.influenceBlock x hx (k + 1) v a c|) = R a := by
    have hf := identity.factorization x hx hx1 hq d b child hroot ht k h a
    simpa only [h, tree, R, mul_signWitness] using hf
  have hs : R a ^ 2 ≤ ∑ c, R c ^ 2 :=
    Finset.single_le_sum (fun c _ => sq_nonneg _) (Finset.mem_univ a)
  have hM0 : 0 ≤ totalInfluenceConstant d (Fintype.card C) * decayRate (Fintype.card C) ^ k :=
    mul_nonneg (totalInfluenceConstant_nonneg (Nat.cast_nonneg _)) (pow_nonneg (decayRate_pos _).le _)
  have hS0 : 0 ≤ ∑ v, ∑ c, |tree.influenceBlock x hx (k + 1) v a c| :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  have hsq := hs.trans henergy
  rw [← source_amplitude_square (C := C) d k, ← hid] at hsq
  nlinarith

/-- CLMM's general influence identity plus the proved contraction gives
the exact appendix total-influence decay bound on actual Gibbs marginals. -/
theorem total_influence_decay (identity : CLMMInfluenceIdentity C)
    {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (hq : Δ + 3 ≤ Fintype.card C)
    (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (child i).DegreeBudget Δ)
    (k : ℕ) (a z : C) :
    (CavityTree.node d b child).levelTotalVariation x hx (k + 1) a z ≤
      totalInfluenceConstant Δ (Fintype.card C) * decayRate (Fintype.card C) ^ k := by
  let tree := CavityTree.node d b child
  have hpoint (v : tree.Level (k + 1)) (c : C) :
      |tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx a) v c -
        tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx z) v c| ≤
      |tree.influenceBlock x hx (k + 1) v a c| + |tree.influenceBlock x hx (k + 1) v z c| := by
    have he : tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx a) v c -
        tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx z) v c =
        tree.influenceBlock x hx (k + 1) v a c - tree.influenceBlock x hx (k + 1) v z c := by
      unfold influenceBlock
      ring
    rw [he]
    exact abs_sub _ _
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (tree.Level (k + 1)))) (fun v _ =>
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hpoint v c))
      (by norm_num : (0 : ℝ) ≤ 1 / 2))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have ha := absolute_influence_row_bound identity x hx hx1 hq d b child hroot ht k a
  have hz := absolute_influence_row_bound identity x hx hx1 hq d b child hroot ht k z
  have hlocal : tree.levelTotalVariation x hx (k + 1) a z ≤
      totalInfluenceConstant d (Fintype.card C) * decayRate (Fintype.card C) ^ k := by
    unfold levelTotalVariation
    rw [← Finset.mul_sum]
    dsimp only [tree] at hsum ⊢
    linarith
  have hd : (d : ℝ) ≤ Δ := by exact_mod_cast (show d ≤ Δ by omega)
  have hconst : totalInfluenceConstant d (Fintype.card C) ≤ totalInfluenceConstant Δ (Fintype.card C) := by
    unfold totalInfluenceConstant
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd
        (Real.exp_pos _).le) (Real.sqrt_nonneg _)) (sq_nonneg _)) (by norm_num)
  exact hlocal.trans (mul_le_mul_of_nonneg_right hconst (pow_nonneg (decayRate_pos _).le _))

end

end ZeroFreeness.Appendix.Girth.CavityTree
