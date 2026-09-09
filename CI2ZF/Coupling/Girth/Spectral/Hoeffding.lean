import CI2ZF.Coupling.Girth.Spectral.Star

/-!
# Finite product Hoeffding orthogonality

Exact factorization and orthogonality of centred product sectors under
the actual cavity product law. No strictly positive atom hypothesis or
Hilbert decomposition is assumed.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D I : Type*} [Fintype C] [Fintype D]

def tensorFeature (J : Finset D) (f : D → C → ℝ) (σ : D → C) : ℝ := ∏ i ∈ J, f i (σ i)

omit [Fintype C] in
theorem tensorFeature_eq_full (J : Finset D) (f : D → C → ℝ) (σ : D → C) :
    tensorFeature J f σ = ∏ i, if i ∈ J then f i (σ i) else 1 := by
  simp only [tensorFeature, Finset.prod_ite_mem, Finset.univ_inter]

theorem productLaw_expect_tensor (p : D → FinDist C) (J : Finset D) (f : D → C → ℝ) :
    expectReal (productLaw p) (tensorFeature J f) = ∏ i ∈ J, expectReal (p i) (f i) := by
  change expectReal (productLaw p) (fun σ => tensorFeature J f σ) = _
  simp_rw [tensorFeature_eq_full]
  rw [productLaw_expect_product p (fun i c => if i ∈ J then f i c else 1)]
  have he (i : D) : expectReal (p i) (fun c => if i ∈ J then f i c else 1) =
      if i ∈ J then expectReal (p i) (f i) else 1 := by
    by_cases hi : i ∈ J <;> simp only [hi, ite_true, ite_false, expectReal_const]
  simp only [he, Finset.prod_ite_mem, Finset.univ_inter]

theorem tensor_inner_factorization (p : D → FinDist C) (J K : Finset D)
    (f g : D → C → ℝ) :
    expectReal (productLaw p) (fun σ => tensorFeature J f σ * tensorFeature K g σ) =
      ∏ i, expectReal (p i) (fun c => (if i ∈ J then f i c else 1) *
        (if i ∈ K then g i c else 1)) := by
  simp_rw [tensorFeature_eq_full, ← Finset.prod_mul_distrib]
  exact productLaw_expect_product p (fun i c => (if i ∈ J then f i c else 1) *
    (if i ∈ K then g i c else 1))

theorem tensor_inner_zero_of_difference (p : D → FinDist C) (J K : Finset D)
    (f g : D → C → ℝ) {i : D} (hi : i ∈ J) (hiK : i ∉ K)
    (hmean : expectReal (p i) (f i) = 0) :
    expectReal (productLaw p) (fun σ => tensorFeature J f σ * tensorFeature K g σ) = 0 := by
  rw [tensor_inner_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simpa only [hi, hiK, ite_true, ite_false, mul_one] using hmean

/-- Distinct centred product sectors are orthogonal, even when cavity
laws are supported on proper subsets of the colour set. -/
theorem tensor_sectors_orthogonal (p : D → FinDist C) (J K : Finset D)
    (f g : D → C → ℝ) (hJK : J ≠ K)
    (hf : ∀ i ∈ J, expectReal (p i) (f i) = 0)
    (hg : ∀ i ∈ K, expectReal (p i) (g i) = 0) :
    expectReal (productLaw p) (fun σ => tensorFeature J f σ * tensorFeature K g σ) = 0 := by
  by_cases hsub : J ⊆ K
  · have hnot : ¬ K ⊆ J := fun h => hJK (Finset.Subset.antisymm hsub h)
    obtain ⟨i, hi, hiJ⟩ := Finset.not_subset.mp hnot
    simpa only [mul_comm] using tensor_inner_zero_of_difference p K J g f hi hiJ (hg i hi)
  · obtain ⟨i, hi, hiK⟩ := Finset.not_subset.mp hsub
    exact tensor_inner_zero_of_difference p J K f g hi hiK (hf i hi)

omit [Fintype D] in
theorem expectReal_finset_sum (p : FinDist C) (J : Finset I) (f : I → C → ℝ) :
    expectReal p (fun c => ∑ i ∈ J, f i c) = ∑ i ∈ J, expectReal p (f i) := by
  simp only [expectReal, Finset.mul_sum]
  exact Finset.sum_comm

omit [Fintype D] in
theorem expectReal_const_mul (p : FinDist C) (a : ℝ) (f : C → ℝ) :
    expectReal p (fun c => a * f c) = a * expectReal p f := by
  simp only [expectReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

omit [Fintype D] in
/-- The finite Pythagorean identity for any family of pairwise orthogonal
observables. This is the exact summation used for Hoeffding sectors. -/
theorem orthogonal_sum_squared (p : FinDist C) (J : Finset I) (f : I → C → ℝ)
    (horth : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → expectReal p (fun c => f i c * f j c) = 0) :
    expectReal p (fun c => (∑ i ∈ J, f i c) ^ 2) =
      ∑ i ∈ J, expectReal p (fun c => f i c ^ 2) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, expectReal_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_eq_single i
  · intro j hj hji
    exact horth j hj i hi hji
  · exact fun h => (h hi).elim

variable {L : Type*}

/-- Arbitrary finite linear combinations within distinct centred
product sectors remain orthogonal. -/
theorem mixed_tensor_sectors_orthogonal (p : D → FinDist C) (J K : Finset D)
    (A : Finset I) (B : Finset L) (a : I → ℝ) (b : L → ℝ)
    (f : I → D → C → ℝ) (g : L → D → C → ℝ) (hJK : J ≠ K)
    (hf : ∀ t ∈ A, ∀ i ∈ J, expectReal (p i) (f t i) = 0)
    (hg : ∀ t ∈ B, ∀ i ∈ K, expectReal (p i) (g t i) = 0) :
    expectReal (productLaw p) (fun σ => (∑ t ∈ A, a t * tensorFeature J (f t) σ) *
      (∑ t ∈ B, b t * tensorFeature K (g t) σ)) = 0 := by
  simp only [Finset.sum_mul, Finset.mul_sum, expectReal_finset_sum]
  apply Finset.sum_eq_zero
  intro t ht
  apply Finset.sum_eq_zero
  intro u hu
  have he : (fun σ => (a u * tensorFeature J (f u) σ) * (b t * tensorFeature K (g t) σ)) =
      (fun σ => (a u * b t) * (tensorFeature J (f u) σ * tensorFeature K (g t) σ)) := by
    funext σ
    ring
  rw [he, expectReal_const_mul, tensor_sectors_orthogonal p J K (f u) (g t) hJK (hf u hu) (hg t ht), mul_zero]

variable [Fintype I]

/-- Exact tensor-mixture energy as the Schur product of its coordinate
Gram kernels. Coefficients and one-site features are arbitrary. -/
theorem mixed_tensor_energy (p : D → FinDist C) (J : Finset D)
    (a : I → ℝ) (f : I → D → C → ℝ) :
    expectReal (productLaw p) (fun σ => (∑ c, a c * tensorFeature J (f c) σ) ^ 2) =
      kernelEnergy (fun c d => ∏ j ∈ J, featureGram (p j) (fun c => f c j) c d) a := by
  have hprod (c d : I) : expectReal (productLaw p)
      (fun σ => tensorFeature J (f c) σ * tensorFeature J (f d) σ) =
      ∏ j ∈ J, featureGram (p j) (fun c => f c j) c d := by
    simp only [tensorFeature, ← Finset.prod_mul_distrib]
    exact productLaw_expect_tensor p J (fun i t => f c i t * f d i t)
  simp only [kernelEnergy, pow_two, Finset.sum_mul, Finset.mul_sum, expectReal_finset_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  have he : (fun σ => (a d * tensorFeature J (f d) σ) * (a c * tensorFeature J (f c) σ)) =
      (fun σ => (a c * a d) * (tensorFeature J (f c) σ * tensorFeature J (f d) σ)) := by
    funext σ
    ring
  rw [he, expectReal_const_mul, hprod]

theorem productLaw_coordinate_expectation (p : D → FinDist C) (i : D) (h : C → ℝ) :
    expectReal (productLaw p) (fun σ => h (σ i)) = expectReal (p i) h := by
  have he : tensorFeature {i} (fun _ : D => h) = (fun σ => h (σ i)) := by
    funext σ
    simp only [tensorFeature, Finset.prod_singleton]
  simpa only [he, Finset.prod_singleton] using productLaw_expect_tensor p {i} (fun _ => h)

theorem productLaw_centered_additive_energy (p : D → FinDist C) (f : D → C → ℝ)
    (hmean : ∀ i, expectReal (p i) (f i) = 0) :
    expectReal (productLaw p) (fun σ => (∑ i, f i (σ i)) ^ 2) =
      ∑ i, expectReal (p i) (fun c => f i c ^ 2) := by
  have horth : ∀ i ∈ (Finset.univ : Finset D), ∀ j ∈ (Finset.univ : Finset D), i ≠ j →
      expectReal (productLaw p) (fun σ => f i (σ i) * f j (σ j)) = 0 := by
    intro i _ j _ hij
    have hset : ({i} : Finset D) ≠ {j} := fun h => hij (Finset.singleton_injective h)
    have h := tensor_sectors_orthogonal p {i} {j} f f hset
      (fun k _ => hmean k) (fun k _ => hmean k)
    simpa only [tensorFeature, Finset.prod_singleton] using h
  rw [orthogonal_sum_squared _ _ _ horth]
  apply Finset.sum_congr rfl
  intro i _
  exact productLaw_coordinate_expectation p i (fun c => f i c ^ 2)

end

end CI2ZF.Appendix.Girth
