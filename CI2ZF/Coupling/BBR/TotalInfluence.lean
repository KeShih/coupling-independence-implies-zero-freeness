import CI2ZF.Coupling.BBR.Response
import CI2ZF.Coupling.Girth.Tree.TotalInfluence

/-! Total influence from actual square-root message derivatives. The only
external boundary is the general covariance/recursion chain identity of
CLMM2023, Lemma 8.7. The recursion, its derivative, the terminal scaling,
and all decay and norm estimates are explicit below. -/
namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open CI2ZF.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false
variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- CLMM2023, Lemma 8.7, in square-root partition-ratio coordinates.
The factor two in differentiating log probability cancels the one-half
in differentiating the terminal square root. Root normalization is the
orthogonal projection already proved in `BBRDifferential`. No decay or
coupling conclusion is assumed. -/
structure InfluenceIdentity (C : Type*) [Fintype C] [DecidableEq C] [Nonempty C] : Prop where
  factorization : ∀ (x : ℝ) (hx : 0 < x) (_hx1 : x ≤ 1) (t : Girth.CavityTree C)
    (k : ℕ) (h : t.Level (k + 1) → C → ℝ) (a : C),
    (∑ v, ∑ c, t.influenceBlock x hx (k + 1) v a c * h v c) =
      projection (t.message x) (response x t (k + 1) h) a / t.message x a

def totalInfluenceConstant (q Δ : ℕ) (x₀ : ℝ) : ℝ :=
  Real.sqrt (2 * Δ * uniformA q Δ x₀ * q) / Real.sqrt (x₀ ^ Δ)

theorem totalInfluenceConstant_pos {q Δ : ℕ} (hq : 0 < q) (hΔ : 0 < Δ)
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ < 1) :
    0 < totalInfluenceConstant q Δ x₀ := by
  have hA := uniformA_pos hq hx₀ hx₀1 (Δ := Δ)
  unfold totalInfluenceConstant
  positivity

/-- The displayed appendix constant, with the half exponent written as
an ordinary square root. -/
theorem totalInfluenceConstant_eq {q Δ : ℕ} (hq : 0 < q)
    {x₀ : ℝ} (hx₀ : 0 < x₀) (hx₀1 : x₀ ≤ 1) :
    totalInfluenceConstant q Δ x₀ =
      Real.sqrt (2 * Δ * (1 - x₀) / (Real.exp 1 * x₀ ^ (2 * Δ + 1))) := by
  have hA := uniformA_nonneg hx₀.le hx₀1 (q := q) (Δ := Δ)
  unfold totalInfluenceConstant
  rw [← Real.sqrt_div (by positivity)]
  congr 1
  unfold uniformA
  have hq0 : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have heq : x₀ ^ (2 * Δ + 1) = x₀ ^ (Δ + 1) * x₀ ^ Δ := by
    rw [← pow_add]
    congr 1
    omega
  rw [heq]
  field_simp [hx₀.ne', hq0]

/-- Source rows are tested against their actual signs. Projection at the
root does not increase squared energy. -/
theorem absolute_influence_row_bound (external : Literature C) (identity : InfluenceIdentity C)
    {Δ : ℕ} (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (t : Girth.CavityTree C) (ht : RootBudget Δ t) (k : ℕ) (a : C) :
    (∑ v, ∑ c, |t.influenceBlock x ((start_mem hq hr).1.trans_le hx.1) (k + 1) v a c|) ≤
      totalInfluenceConstant (Fintype.card C) Δ (start (Fintype.card C) Δ) * contractionRate Δ ^ k := by
  let x₀ := start (Fintype.card C) Δ
  have hx₀ := start_mem hq hr
  have hx0 := hx₀.1.trans_le hx.1
  have hΔq := degree_gt_colours (Nat.cast_pos.mpr Fintype.card_pos) hr
  have hΔqn : Fintype.card C < Δ := by exact_mod_cast hΔq
  have hΔ : 2 ≤ Δ := by omega
  let h : t.Level (k + 1) → C → ℝ := fun v c =>
    CavityTree.signWitness (t.influenceBlock x hx0 (k + 1) v a c)
  let z := response x t (k + 1) h
  let m := Real.sqrt (x₀ ^ Δ)
  let A := uniformA (Fintype.card C) Δ x₀
  let B := Real.sqrt (2 * Δ * A * Fintype.card C) * contractionRate Δ ^ k
  have hm : 0 < m := Real.sqrt_pos.2 (pow_pos hx₀.1 _)
  have hA : 0 ≤ A := uniformA_nonneg hx₀.1.le hx₀.2.le
  have hh (v : t.Level (k + 1)) : squareMass (h v) ≤ (Fintype.card C : ℝ) := by
    simp only [squareMass, h, CavityTree.signWitness_sq, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, le_refl]
  have hen := response_energy external hq hr hx k t ht h (Nat.cast_nonneg _) hh
  have hd : (t.degree : ℝ) ≤ Δ := by
    cases t with
    | node d b ch => exact_mod_cast (show d ≤ Δ by have := ht.1; omega)
  have hroot : m ≤ t.message x a := by
    cases t with
    | node d b ch => exact CavityTree.message_uniform_lower hx₀.1 hx.1 hx.2 (.node d b ch) Δ ht.1 a
  have he : squareMass z ≤ (Δ : ℝ) * A * contractionSquare Δ ^ k * Fintype.card C := by
    exact hen.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hA)
        (pow_nonneg (contractionSquare_mem hΔ).1.le _)) (Nat.cast_nonneg _))
  have hproj := (coordinate_sq_le_mass (projection (t.message x) z) a).trans
    (projection_energy_le (t.message x) z (t.squareMass_pos hx0))
  have hB : 0 ≤ B := by dsimp [B]; exact mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (contractionRate_mem hΔ).1.le _)
  have hBsq : B ^ 2 = 2 * Δ * A * Fintype.card C * contractionSquare Δ ^ k := by
    dsimp [B]
    rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, Nat.mul_comm k 2,
      pow_mul, contractionRate_sq hΔ]
  have hcoord : |projection (t.message x) z a| ≤ B := by
    have hκ := (contractionSquare_mem hΔ).1.le
    have hnon : 0 ≤ (Δ : ℝ) * A * contractionSquare Δ ^ k * Fintype.card C := by positivity
    nlinarith [sq_abs (projection (t.message x) z a), abs_nonneg (projection (t.message x) z a)]
  have hid := identity.factorization x hx0 hx.2 t k h a
  simp only [h, CavityTree.mul_signWitness] at hid
  rw [hid]
  calc
    _ ≤ |projection (t.message x) z a| / t.message x a :=
      div_le_div_of_nonneg_right (le_abs_self _) (t.message_pos hx0 a).le
    _ ≤ B / m := div_le_div₀ hB hcoord hm hroot
    _ = _ := by unfold totalInfluenceConstant; dsimp [B, A, m, x₀]; ring

/-- Actual conditional marginals have total-influence decay uniformly on
all of the BBR interval, including activity one. -/
theorem total_influence_decay (external : Literature C) (identity : InfluenceIdentity C)
    {Δ : ℕ} (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C)
    {x : ℝ} (hx : x ∈ Icc (start (Fintype.card C) Δ) 1)
    (d : ℕ) (b : C → ℕ) (child : Fin d → Girth.CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (child i).DegreeBudget Δ)
    (k : ℕ) (a z : C) :
    (Girth.CavityTree.node d b child).levelTotalVariation x ((start_mem hq hr).1.trans_le hx.1) (k + 1) a z ≤
      totalInfluenceConstant (Fintype.card C) Δ (start (Fintype.card C) Δ) * contractionRate Δ ^ k := by
  let tree := Girth.CavityTree.node d b child
  have hx0 := (start_mem hq hr).1.trans_le hx.1
  have hpoint (v : tree.Level (k + 1)) (c : C) :
      |tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx0 a) v c -
        tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx0 z) v c| ≤
      |tree.influenceBlock x hx0 (k + 1) v a c| + |tree.influenceBlock x hx0 (k + 1) v z c| := by
    have he : tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx0 a) v c -
        tree.levelMarginal (k + 1) (tree.rootConditionalLaw x hx0 z) v c =
        tree.influenceBlock x hx0 (k + 1) v a c - tree.influenceBlock x hx0 (k + 1) v z c := by
      unfold CavityTree.influenceBlock
      ring
    rw [he]
    exact abs_sub _ _
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (tree.Level (k + 1)))) (fun v _ =>
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hpoint v c))
      (by norm_num : (0 : ℝ) ≤ 1 / 2))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have ha := absolute_influence_row_bound external identity hq hr hx tree ⟨hroot, ht⟩ k a
  have hz := absolute_influence_row_bound external identity hq hr hx tree ⟨hroot, ht⟩ k z
  unfold CavityTree.levelTotalVariation
  rw [← Finset.mul_sum]
  dsimp only [tree] at hsum ⊢
  linarith

end
end CI2ZF.Appendix.BBR
