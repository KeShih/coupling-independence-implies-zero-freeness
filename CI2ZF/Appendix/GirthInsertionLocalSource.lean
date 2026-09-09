import CI2ZF.Appendix.GirthResponseScore
import CI2ZF.Appendix.GirthInsertionAffine

/-! Exact local-source covariance under the conditional product law,
followed by its first-moment bound from the proved beta second moment. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω U O C : Type*} [Fintype Ω] [Fintype U] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq C]

theorem covariance_sum_left (μ : FinDist Ω) (f : U → Ω → ℝ) (g : Ω → ℝ) :
    covariance μ (fun ω => ∑ u, f u ω) g = ∑ u, covariance μ (f u) g := by
  rw [covariance_comm, covariance_sum_right]
  apply Finset.sum_congr rfl
  intro u _
  exact covariance_comm μ g (f u)

theorem covariance_const_left (μ : FinDist Ω) (a : ℝ) (f : Ω → ℝ) :
    covariance μ (fun _ => a) f = 0 := by rw [covariance_comm, covariance_const_right]

theorem product_coordinate_tensor (p : U → FinDist C) (u : U) (f : C → ℝ) (g : U → C → ℝ) :
    expectReal (CI2ZF.productLaw p) (fun σ => f (σ u) * ∏ j, g j (σ j)) =
      expectReal (p u) (fun c => f c * g u c) * ∏ j ∈ Finset.univ.erase u, expectReal (p j) (g j) := by
  let h : U → C → ℝ := fun j c => if j = u then f c * g j c else g j c
  have hp (σ : U → C) : (∏ j, h j (σ j)) = f (σ u) * ∏ j, g j (σ j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ u),
      ← Finset.prod_erase_mul Finset.univ (fun j => g j (σ j)) (Finset.mem_univ u)]
    have he : (∏ j ∈ Finset.univ.erase u, h j (σ j)) = ∏ j ∈ Finset.univ.erase u, g j (σ j) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact if_neg (Finset.ne_of_mem_erase hj)
    rw [he]
    simp only [h, if_true]
    ring
  calc
    _ = expectReal (CI2ZF.productLaw p) (fun σ => ∏ j, h j (σ j)) := by simp_rw [hp]
    _ = ∏ j, expectReal (p j) (h j) := CI2ZF.expectReal_productLaw p h
    _ = _ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ u)]
      have he : (∏ j ∈ Finset.univ.erase u, expectReal (p j) (h j)) =
          ∏ j ∈ Finset.univ.erase u, expectReal (p j) (g j) := by
        apply Finset.prod_congr rfl
        intro j hj
        congr 1
        funext c
        exact if_neg (Finset.ne_of_mem_erase hj)
      rw [he]
      simp only [h, if_true]
      ring

theorem product_coordinate_covariance (p : U → FinDist C) (u : U) (f : C → ℝ) (g : U → C → ℝ) :
    covariance (CI2ZF.productLaw p) (fun σ => f (σ u)) (fun σ => ∏ j, g j (σ j)) =
      covariance (p u) f (g u) * ∏ j ∈ Finset.univ.erase u, expectReal (p j) (g j) := by
  rw [covariance_eq_moment, product_coordinate_tensor, CI2ZF.expectReal_product_coordinate,
    CI2ZF.expectReal_productLaw p g,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ u), covariance_eq_moment]
  ring

theorem product_coordinate_pair_covariance (p : U → FinDist C) (u v : U) (f g : C → ℝ) :
    covariance (CI2ZF.productLaw p) (fun σ => f (σ u)) (fun σ => g (σ v)) =
      if u = v then covariance (p u) f g else 0 := by
  let h : U → C → ℝ := fun j c => if j = v then g c else 1
  have hp (σ : U → C) : (∏ j, h j (σ j)) = g (σ v) := by simp [h]
  have hh := product_coordinate_covariance p u f h
  simp_rw [hp] at hh
  rw [hh]
  by_cases huv : u = v
  · subst v
    simp only [h, if_true]
    have hz : (∏ j ∈ Finset.univ.erase u, expectReal (p j) (fun c => if j = u then g c else 1)) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      simp only [if_neg (Finset.ne_of_mem_erase hj), expectReal_const]
    rw [hz, mul_one]
  · simp only [h, if_neg huv, covariance_const_right, zero_mul]

theorem covariance_indicator (p : FinDist C) (f : C → ℝ) (c : C) :
    covariance p f (colourIndicator c) = p.w c * (f c - expectReal p f) := by
  rw [covariance_eq_moment, expect_colourIndicator]
  have he : expectReal p (fun t => f t * colourIndicator c t) = p.w c * f c := by
    simp [expectReal, colourIndicator]
  rw [he]
  ring

theorem expectReal_abs_bound (μ : FinDist Ω) (f : Ω → ℝ) {a : ℝ}
    (hf : ∀ ω, |f ω| ≤ a) : |expectReal μ f| ≤ a := by
  apply abs_le.mpr
  constructor
  · calc
      -a = expectReal μ (fun _ => -a) := (expectReal_const _ _).symm
      _ ≤ _ := expectReal_mono μ (fun ω => (abs_le.mp (hf ω)).1)
  · calc
      _ ≤ expectReal μ (fun _ => a) := expectReal_mono μ (fun ω => (abs_le.mp (hf ω)).2)
      _ = _ := expectReal_const _ _

theorem covariance_indicator_abs (p : FinDist C) (f : C → ℝ) (c : C) {a : ℝ}
    (hf : ∀ t, |f t| ≤ a) : |covariance p f (colourIndicator c)| ≤ 2 * a * p.w c := by
  rw [covariance_indicator, abs_mul, abs_of_nonneg (p.nonneg c)]
  have he := expectReal_abs_bound p f hf
  have hdiff : |f c - expectReal p f| ≤ 2 * a := (abs_sub _ _).trans (by linarith [hf c])
  calc
    _ ≤ p.w c * (2 * a) := mul_le_mul_of_nonneg_left hdiff (p.nonneg c)
    _ = _ := by ring

theorem abs_expectReal_le (μ : FinDist Ω) (f : Ω → ℝ) :
    |expectReal μ f| ≤ expectReal μ (fun ω => |f ω|) := by
  calc
    _ ≤ ∑ ω, |μ.w ω * f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (μ.nonneg _), expectReal]

theorem expect_abs_le_of_second_moment (μ : FinDist Ω) (f : Ω → ℝ) {b : ℝ}
    (hb : 0 ≤ b) (hf : expectReal μ (fun ω => f ω ^ 2) ≤ b ^ 2) :
    expectReal μ (fun ω => |f ω|) ≤ b := by
  have h := variance_nonneg μ (fun ω => |f ω|)
  rw [← covariance_self, covariance_eq_moment] at h
  have he : expectReal μ (fun t => |f t| * |f t|) = expectReal μ (fun t => f t ^ 2) := by
    simp only [← pow_two, sq_abs]
  rw [he] at h
  nlinarith

namespace InsertionModel
variable (M : InsertionModel Ω U O C)

theorem conditional_coordinate_residual (s : ℝ) (ξ : Ω) (u : U) (f : C → ℝ) (c : C) :
    covariance (CI2ZF.productLaw (M.cavity ξ)) (fun σ => f (σ u)) (M.residual s c) =
      M.beta s u c ξ * covariance (M.cavity ξ u) f (colourIndicator c) := by
  change covariance (CI2ZF.productLaw (M.cavity ξ)) (fun σ => f (σ u))
    (fun σ => M.F s c σ / M.T s c - 1 + ∑ j, M.alpha s j c * (colourIndicator c (σ j) - M.p j c)) = _
  rw [covariance_add_right, covariance_sub_right, covariance_const_right, sub_zero,
    covariance_sum_right]
  have hdiv : (fun σ => M.F s c σ / M.T s c) = fun σ => (M.T s c)⁻¹ * M.F s c σ := by funext σ; ring
  rw [hdiv, covariance_const_mul_right]
  simp_rw [covariance_const_mul_right, covariance_sub_right, covariance_const_right, sub_zero,
    product_coordinate_pair_covariance]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  change (M.T s c)⁻¹ * covariance (CI2ZF.productLaw (M.cavity ξ)) (fun σ => f (σ u))
    (fun σ => ∏ j, (1 - s * colourIndicator c (σ j))) + _ = _
  rw [product_coordinate_covariance (M.cavity ξ) u f (fun _ t => 1 - s * colourIndicator c t)]
  simp_rw [covariance_sub_right, covariance_const_right, covariance_const_mul_right,
    zero_sub, expectReal_sub, expectReal_const, expectReal_const_mul, expect_colourIndicator]
  unfold beta pi
  ring

theorem conditional_local_residual (s : ℝ) (ξ : Ω) (f : U → C → ℝ) (c : C) :
    covariance (CI2ZF.productLaw (M.cavity ξ)) (fun σ => ∑ u, f u (σ u)) (M.residual s c) =
      ∑ u, M.beta s u c ξ * covariance (M.cavity ξ u) (f u) (colourIndicator c) := by
  rw [covariance_sum_left]
  apply Finset.sum_congr rfl
  intro u _
  exact M.conditional_coordinate_residual s ξ u (f u) c

/-- The local first-layer source is bounded by the beta second moment;
no independence is required of the outer law. -/
theorem local_source_bound (s : ℝ) (f : U → C → ℝ) (c : C) {A B b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 ≤ b)
    (hf : ∀ u t, |f u t| ≤ A) (hp : ∀ ξ u, (M.cavity ξ u).w c ≤ B)
    (hβ : ∀ u, expectReal M.shell (fun ξ => M.beta s u c ξ ^ 2) ≤ b ^ 2) :
    |expectReal M.shell (fun ξ => covariance (CI2ZF.productLaw (M.cavity ξ))
      (fun σ => ∑ u, f u (σ u)) (M.residual s c))| ≤
        2 * (Fintype.card U : ℝ) * A * B * b := by
  simp_rw [M.conditional_local_residual]
  rw [expectReal_sum]
  calc
    _ ≤ ∑ u, |expectReal M.shell (fun ξ => M.beta s u c ξ * covariance (M.cavity ξ u) (f u) (colourIndicator c))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u : U, 2 * A * B * b := by
      apply Finset.sum_le_sum
      intro u _
      calc
        _ ≤ expectReal M.shell (fun ξ => |M.beta s u c ξ * covariance (M.cavity ξ u) (f u) (colourIndicator c)|) := abs_expectReal_le _ _
        _ ≤ expectReal M.shell (fun ξ => (2 * A * B) * |M.beta s u c ξ|) := by
          apply expectReal_mono
          intro ξ
          rw [abs_mul]
          have hh := (covariance_indicator_abs (M.cavity ξ u) (f u) c (hf u)).trans
            (mul_le_mul_of_nonneg_left (hp ξ u) (by positivity : 0 ≤ 2 * A))
          nlinarith [abs_nonneg (M.beta s u c ξ)]
        _ = (2 * A * B) * expectReal M.shell (fun ξ => |M.beta s u c ξ|) := expectReal_const_mul _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (expect_abs_le_of_second_moment _ _ hb (hβ u)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end InsertionModel
end
end CI2ZF.Appendix.Girth
