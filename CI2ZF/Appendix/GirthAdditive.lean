import CI2ZF.Appendix.GirthSectorRepresentation

/-! Leaf-additive residuals and the exact cancellation forced by
orthogonality to the additive subspace. These are actual weighted
function identities used for the singleton-complement bound. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D]

theorem productLaw_singleton_pair (p : D → FinDist C) (i j : D)
    (f g : C → ℝ) (hf : expectReal (p i) f = 0) :
    expectReal (productLaw p) (fun σ => f (σ i) * g (σ j)) =
      if i = j then expectReal (p i) (fun t => f t * g t) else 0 := by
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    exact productLaw_coordinate_expectation p i (fun t => f t * g t)
  · simp only [hij, ite_false]
    have h := tensor_inner_zero_of_difference p {i} {j} (fun _ => f) (fun _ => g)
      (Finset.mem_singleton_self i) (by simpa using hij) hf
    simpa only [tensorFeature, Finset.prod_singleton] using h

namespace ConditionalStar

variable [DecidableEq C] (S : ConditionalStar C D)

def additiveResidual (i : D) (h : C → ℝ) (c t : C) : ℝ :=
  h t - expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) h

theorem additiveResidual_mean (i : D) (h : C → ℝ) (c : C) :
    expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c))
      (S.additiveResidual i h c) = 0 := expectation_centered _ h

theorem singleton_additive_inner (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c
      (S.edge_positive i c)) (g i c) = 0) (i : D) (h : C → ℝ) :
    expectReal S.jointLaw (fun σ => singletonFunction g σ * S.additiveResidual i h σ.1 (σ.2 i)) =
      ∑ t, (S.cavity i).w t * h t *
        (∑ c, S.centreLaw.w c * g i c t * edgeLikelihood S.s (S.cavity i) c t) := by
  rw [S.jointLaw_expectation]
  have he (c : C) : expectReal (S.leafChannel c) (fun σ =>
      singletonFunction g (c, σ) * S.additiveResidual i h c (σ i)) =
      expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c))
        (fun t => g i c t * h t) := by
    unfold singletonFunction leafChannel
    simp only [Finset.sum_mul, expectReal_finset_sum]
    have hp (j : D) := productLaw_singleton_pair
      (fun k => edgeChannel (S.cavity k) S.s S.s_le_one c (S.edge_positive k c))
      j i (g j c) (S.additiveResidual i h c) (hmean j c)
    simp_rw [hp]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    unfold additiveResidual expectReal
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hz : (∑ t, (edgeChannel (S.cavity i) S.s S.s_le_one c
        (S.edge_positive i c)).w t * g i c t) = 0 := hmean i c
    simp only [← mul_assoc]
    rw [← Finset.sum_mul]
    simp only [hz, zero_mul, sub_zero]
  simp_rw [he]
  unfold expectReal edgeChannel
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Orthogonality to every leaf-additive residual gives the Bayes
cancellation needed by the singleton Hoeffding expansion. Values outside
cavity support are required to be the canonical zero extension. -/
theorem singleton_cancellation_of_orthogonal (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c
      (S.edge_positive i c)) (g i c) = 0)
    (hzero : ∀ i c t, (S.cavity i).w t = 0 → g i c t = 0)
    (horth : ∀ i h, expectReal S.jointLaw (fun σ => singletonFunction g σ *
      S.additiveResidual i h σ.1 (σ.2 i)) = 0) (i : D) (t : C) :
    ∑ c, S.centreLaw.w c * g i c t * edgeLikelihood S.s (S.cavity i) c t = 0 := by
  by_cases ht : (S.cavity i).w t = 0
  · simp only [hzero i _ t ht, mul_zero, zero_mul, Finset.sum_const_zero]
  · have h := horth i (fun u => if u = t then 1 else 0)
    rw [S.singleton_additive_inner g hmean] at h
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    exact (mul_eq_zero.mp h).resolve_left ht

end ConditionalStar
end
end CI2ZF.Appendix.Girth
