import CI2ZF.Appendix.Girth.Covariance.Insertion.GraphCoordinates

/-! Poincaré for the true graph law controls the covariance matrix of
the insertion residual under its actual shell marginal. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
open CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq S] [DecidableEq O] [DecidableEq C] [Nonempty C]

namespace InsertionGraph
variable (I : PinningData (Vertex U S O) C) (x : ℝ) (hx : 0 < x)

theorem expect_model_shell (c₀ : C) (hZ : 0 < I.partition x) (f : (S → C) → ℝ) :
    expectReal (model I x hx c₀ hZ).shell f =
      expectReal (I.gibbs x hx.le hZ) (fun σ => f (shell σ)) := by
  change expectReal (InsertionBalance.shellLaw (law I x hx hZ)) f = _
  rw [InsertionBalance.expect_shellLaw, law, CI2ZF.expectReal_mapLaw]
  rfl

theorem variance_model_shell (c₀ : C) (hZ : 0 < I.partition x) (f : (S → C) → ℝ) :
    variance (model I x hx c₀ hZ).shell f =
      variance (I.gibbs x hx.le hZ) (fun σ => f (shell σ)) := by
  unfold variance
  rw [expect_model_shell, expect_model_shell]

theorem localVariance_shell_inside (u : U) (f : (S → C) → ℝ) (σ : Vertex U S O → C) :
    GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
      (Sum.inl u) (fun τ => f (shell τ)) σ = 0 := by
  unfold GraphHeatBath.localVariance
  simp only [shell_update_inside]
  simp [variance, expectReal_const]

theorem localVariance_shell_outside (o : O) (f : (S → C) → ℝ) (σ : Vertex U S O → C) :
    GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
      (Sum.inr (Sum.inr o)) (fun τ => f (shell τ)) σ = 0 := by
  unfold GraphHeatBath.localVariance
  simp only [shell_update_outside]
  simp [variance, expectReal_const]

theorem shell_poincare (c₀ : C) (hZ : 0 < I.partition x) {γ : ℝ}
    (hP : ∀ f, γ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ)
        (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx) v f))
    (f : (S → C) → ℝ) :
    γ * variance (model I x hx c₀ hZ).shell f ≤
      ∑ w : S, expectReal (I.gibbs x hx.le hZ)
        (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
          (Sum.inr (Sum.inl w)) (fun σ => f (shell σ))) := by
  rw [variance_model_shell]
  have h := hP (fun σ => f (shell σ))
  have hi (u : U) : expectReal (I.gibbs x hx.le hZ)
      (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
        (Sum.inl u) (fun σ => f (shell σ))) = 0 := by
    change expectReal _ (fun σ => GraphHeatBath.localVariance I x hx _ _ _ σ) = _
    simp_rw [localVariance_shell_inside]
    exact expectReal_const _ _
  have ho (o : O) : expectReal (I.gibbs x hx.le hZ)
      (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
        (Sum.inr (Sum.inr o)) (fun σ => f (shell σ))) = 0 := by
    change expectReal _ (fun σ => GraphHeatBath.localVariance I x hx _ _ _ σ) = _
    simp_rw [localVariance_shell_outside]
    exact expectReal_const _ _
  simpa only [Fintype.sum_sum_type, hi, ho, Finset.sum_const_zero, zero_add, add_zero] using h

/-- Every input on the right is an actual moment under the Gibbs shell
marginal.  The result is its full colour covariance quadratic form. -/
theorem residual_colour_covariance (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    {m γ b : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (hγ : 0 < γ) (hsize : (Fintype.card S : ℝ) ≤ (Δ : ℝ) ^ 2)
    (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (hP : ∀ f, γ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ)
        (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx) v f))
    (hβ : ∀ u c, expectReal (model I x hx c₀ hZ).shell
      (fun ξ => (model I x hx c₀ hZ).beta (1-x) u c ξ ^ 2) ≤ b ^ 2) :
    ColourCovarianceBound (model I x hx c₀ hZ).shell ((model I x hx c₀ hZ).G (1-x))
      ((Δ : ℝ) ^ 2 * (1/m) *
        ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m) ^ 2 / γ * b ^ 2) := by
  intro z
  let M := model I x hx c₀ hZ
  let L := (1 + Real.sqrt ((Fintype.card C : ℝ) / (m+1))) / m
  have hpoint (w : S) : expectReal (I.gibbs x hx.le hZ)
      (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx)
        (Sum.inr (Sum.inl w)) (fun σ => ∑ c, z c * M.G (1-x) c (shell σ))) ≤
        (1/m) * L ^ 2 * b ^ 2 * ∑ c, z c ^ 2 := by
    calc
      _ ≤ expectReal (I.gibbs x hx.le hZ)
          (fun σ => (1/m) * L ^ 2 * ∑ c, z c ^ 2 * M.beta (1-x) (owner w) c (shell σ) ^ 2) :=
        expectReal_mono _ (fun σ => G_coordinate_variance I x hx hi hs c₀ hZ hx1 hd hm hq owner howner z σ w)
      _ = expectReal M.shell
          (fun ξ => (1/m) * L ^ 2 * ∑ c, z c ^ 2 * M.beta (1-x) (owner w) c ξ ^ 2) :=
        (expect_model_shell I x hx c₀ hZ
          (fun ξ => (1/m) * L ^ 2 * ∑ c, z c ^ 2 * M.beta (1-x) (owner w) c ξ ^ 2)).symm
      _ = (1/m) * L ^ 2 * ∑ c, z c ^ 2 * expectReal M.shell
          (fun ξ => M.beta (1-x) (owner w) c ξ ^ 2) := by
        rw [expectReal_const_mul, expectReal_sum]
        simp_rw [expectReal_const_mul]
      _ ≤ (1/m) * L ^ 2 * ∑ c, z c ^ 2 * b ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hβ (owner w) c) (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have h := (shell_poincare I x hx c₀ hZ hP (fun ξ => ∑ c, z c * M.G (1-x) c ξ)).trans
    (Finset.sum_le_sum fun w _ => hpoint w)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hh : γ * variance M.shell (fun ξ => ∑ c, z c * M.G (1-x) c ξ) ≤
      (Δ : ℝ) ^ 2 * ((1/m) * L ^ 2 * b ^ 2 * ∑ c, z c ^ 2) :=
    h.trans (mul_le_mul_of_nonneg_right hsize (by positivity))
  calc
    _ ≤ ((Δ : ℝ) ^ 2 * ((1/m) * L ^ 2 * b ^ 2 * ∑ c, z c ^ 2)) / γ :=
      (le_div_iff₀ hγ).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by dsimp [L]; ring

end InsertionGraph
end
end CI2ZF.Appendix.Girth
