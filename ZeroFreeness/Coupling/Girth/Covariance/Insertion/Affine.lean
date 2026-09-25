import ZeroFreeness.Coupling.Girth.Covariance.Insertion.Law
import ZeroFreeness.Coupling.Girth.Analysis.OneEdge

/-! The insertion residual is affine in each neighbour marginal. Its
coefficient is independent of that neighbour's entire second-layer block. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω C U O : Type*} [Fintype Ω] [Fintype C] [Fintype U] [Fintype O]
  [DecidableEq C] [DecidableEq U]

theorem variance_add_const (μ : FinDist Ω) (f : Ω → ℝ) (a : ℝ) :
    variance μ (fun ω => f ω + a) = variance μ f := by
  unfold variance
  rw [expectReal_add, expectReal_const]
  congr 1
  funext ω
  congr 1
  ring

namespace InsertionModel
variable (M : InsertionModel Ω U O C)

def affineRest (s : ℝ) (u : U) (c : C) (ξ : Ω) : ℝ :=
  (∏ j ∈ Finset.univ.erase u, (1 - s * M.pi j c ξ)) / M.T s c - 1 -
    M.alpha s u c * M.p u c +
    ∑ j ∈ Finset.univ.erase u, M.alpha s j c * (M.pi j c ξ - M.p j c)

theorem G_affine (s : ℝ) (u : U) (c : C) (ξ : Ω) :
    M.G s c ξ = M.beta s u c ξ * M.pi u c ξ + M.affineRest s u c ξ := by
  unfold G Y beta affineRest
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ u),
    ← Finset.sum_erase_add _ _ (Finset.mem_univ u)]
  ring

theorem beta_congr (s : ℝ) (u : U) (c : C) {ξ η : Ω}
    (hπ : ∀ j, j ≠ u → M.pi j c ξ = M.pi j c η) :
    M.beta s u c ξ = M.beta s u c η := by
  unfold beta
  congr 2
  apply Finset.prod_congr rfl
  intro j hj
  rw [hπ j (Finset.ne_of_mem_erase hj)]

theorem affineRest_congr (s : ℝ) (u : U) (c : C) {ξ η : Ω}
    (hπ : ∀ j, j ≠ u → M.pi j c ξ = M.pi j c η) :
    M.affineRest s u c ξ = M.affineRest s u c η := by
  have hprod : (∏ j ∈ Finset.univ.erase u, (1 - s * M.pi j c ξ)) =
      ∏ j ∈ Finset.univ.erase u, (1 - s * M.pi j c η) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [hπ j (Finset.ne_of_mem_erase hj)]
  unfold affineRest
  rw [hprod]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hπ j (Finset.ne_of_mem_erase hj)]

theorem G_difference (s : ℝ) (u : U) (c : C) {ξ η : Ω}
    (hπ : ∀ j, j ≠ u → M.pi j c ξ = M.pi j c η) :
    M.G s c ξ - M.G s c η = M.beta s u c η * (M.pi u c ξ - M.pi u c η) := by
  rw [M.G_affine s u c ξ, M.G_affine s u c η,
    M.beta_congr s u c hπ, M.affineRest_congr s u c hπ]
  ring

/-- Any single spin in the corresponding block acts through the actual
one-edge colour response; the affine coefficient may depend on all the
other spins. -/
theorem colour_direction_coordinate_variance (u : U) (ξ₀ : Ω) (ξ : C → Ω)
    {s m B : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hm : 0 < m) (hB : 0 ≤ B)
    (r ρ : FinDist C) (hr : ∀ c, r.w c ≤ 1 / (m + 1)) (hρ : ∀ c, ρ.w c ≤ B)
    (hother : ∀ t j, j ≠ u → ∀ c, M.pi j c (ξ t) = M.pi j c ξ₀)
    (hedge : ∀ t c, M.pi u c (ξ t) =
      r.w c * (1 - s * colourIndicator t c) / (1 - s * r.w t))
    (z : C → ℝ) :
    variance ρ (fun t => ∑ c, z c * M.G s c (ξ t)) ≤
      B * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m + 1))) / m) ^ 2 *
        ∑ c, z c ^ 2 * M.beta s u c ξ₀ ^ 2 := by
  let h : C → ℝ := fun c => z c * M.beta s u c ξ₀
  let a : ℝ := ∑ c, z c * M.affineRest s u c ξ₀
  have hf (t : C) : (∑ c, z c * M.G s c (ξ t)) = edgeResponse s r h t + a := by
    have he : (∑ c, z c * M.G s c (ξ t)) =
        (∑ c, h c * M.pi u c (ξ t)) + a := by
      simp_rw [M.G_affine s u]
      simp_rw [M.beta_congr s u _ (hother t · · _),
        M.affineRest_congr s u _ (hother t · · _)]
      simp only [mul_add, Finset.sum_add_distrib, h, a, mul_assoc]
    rw [he]
    congr 1
    simp_rw [hedge]
    unfold edgeResponse
    simp only [← mul_div_assoc]
    rw [← Finset.sum_div]
    congr 1
    calc
      _ = (∑ c, r.w c * h c) - s * r.w t * h t := by
        simp only [colourIndicator, mul_sub, mul_one, Finset.sum_sub_distrib,
          mul_ite, mul_zero, Finset.sum_ite_eq']
        simp only [Finset.mem_univ, ite_true]
        rw [Finset.sum_congr rfl (fun c _ => mul_comm (h c) (r.w c))]
        ring
      _ = _ := rfl
  simp_rw [hf]
  rw [variance_add_const]
  have hb := one_edge_variance_bound hs hs1 hm hB r ρ hr hρ h
  simpa only [h, mul_pow] using hb

end InsertionModel
end
end ZeroFreeness.Appendix.Girth
