import ZeroFreeness.Coupling.Girth.Spectral.Singleton

/-! Exact orthogonal expansion of the centre heat-bath image of the
singleton complement. The cancellation condition is the conditional
expectation identity forced by orthogonality to leaf-additive residuals. -/

namespace ZeroFreeness.Appendix.Girth.ConditionalStar

open scoped BigOperators
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

def singletonFunction (g : D → C → C → ℝ) (σ : C × (D → C)) : ℝ := ∑ i, g i σ.1 (σ.2 i)

theorem singletonComponent_eq (g : D → C → C → ℝ) (i : D) (J : Finset D)
    (hi : i ∈ J) (σ : D → C) :
    S.singletonComponent g i J σ = ∑ c, S.centreLaw.w c *
      (g i c (σ i) * edgeLikelihood S.s (S.cavity i) c (σ i)) *
      ∏ j ∈ J.erase i, edgeFluctuation S.s (S.cavity j) c (σ j) := by
  unfold singletonComponent tensorFeature
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.mul_prod_erase J _ hi]
  rw [S.markedFeature_self]
  have he : (∏ j ∈ J.erase i, S.markedFeature g i c j (σ j)) =
      ∏ j ∈ J.erase i, edgeFluctuation S.s (S.cavity j) c (σ j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [S.markedFeature_of_ne g i j c (Finset.mem_erase.mp hj).1]
  rw [he]
  ring

theorem singletonNumerator_expansion (g : D → C → C → ℝ) (σ : D → C) :
    S.centreNumerator (singletonFunction g) σ =
      ∑ J ∈ (Finset.univ : Finset D).powerset, S.singletonSector g J σ := by
  have he (c : C) : (∏ i, edgeLikelihood S.s (S.cavity i) c (σ i)) * (∑ i, g i c (σ i)) =
      ∑ J ∈ (Finset.univ : Finset D).powerset, ∑ i ∈ J,
        (g i c (σ i) * edgeLikelihood S.s (S.cavity i) c (σ i)) *
          ∏ j ∈ J.erase i, edgeFluctuation S.s (S.cavity j) c (σ j) := by
    rw [← marked_product_expansion]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hprod : (∏ j ∈ (Finset.univ : Finset D).erase i,
        (1 + edgeFluctuation S.s (S.cavity j) c (σ j))) =
        ∏ j ∈ (Finset.univ : Finset D).erase i, edgeLikelihood S.s (S.cavity j) c (σ j) := by
      apply Finset.prod_congr rfl
      intro j _
      unfold edgeFluctuation
      ring
    rw [hprod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    ring
  unfold centreNumerator singletonFunction
  simp only [mul_assoc]
  simp_rw [he]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.sum_comm]
  unfold singletonSector
  apply Finset.sum_congr rfl
  intro i hi
  rw [S.singletonComponent_eq g i J hi]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem singletonSector_small (g : D → C → C → ℝ)
    (hcancel : ∀ i t, (∑ c, S.centreLaw.w c * g i c t * edgeLikelihood S.s (S.cavity i) c t) = 0)
    (J : Finset D) (hJ : J.card ≤ 1) (σ : D → C) : S.singletonSector g J σ = 0 := by
  by_cases he : J = ∅
  · subst J
    simp only [singletonSector, Finset.sum_empty]
  · have hcard : J.card = 1 := by have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    simp only [singletonSector, Finset.sum_singleton]
    rw [S.singletonComponent_eq g i {i} (Finset.mem_singleton_self i)]
    simpa only [Finset.erase_singleton, Finset.prod_empty, mul_one, ← mul_assoc] using hcancel i (σ i)

theorem singletonNumerator_energy (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal
      (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) = 0) :
    expectReal (productLaw S.cavity) (fun σ => S.centreNumerator (singletonFunction g) σ ^ 2) =
      ∑ J ∈ (Finset.univ : Finset D).powerset,
        expectReal (productLaw S.cavity) (fun σ => S.singletonSector g J σ ^ 2) := by
  simp_rw [S.singletonNumerator_expansion]
  exact orthogonal_sum_squared _ _ _ (fun _ _ _ _ hJK => S.singletonSector_orthogonal g hmean hJK)

theorem singletonSector_energy_le (g : D → C → C → ℝ) (J : Finset D) :
    expectReal (productLaw S.cavity) (fun σ => S.singletonSector g J σ ^ 2) ≤
      (J.card : ℝ) * ∑ i ∈ J,
        expectReal (productLaw S.cavity) (fun σ => S.singletonComponent g i J σ ^ 2) := by
  have hp (σ : D → C) : S.singletonSector g J σ ^ 2 ≤
      (J.card : ℝ) * ∑ i ∈ J, S.singletonComponent g i J σ ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul J
      (r := fun i => S.singletonComponent g i J σ) (f := fun _ => (1 : ℝ))
      (g := fun i => S.singletonComponent g i J σ ^ 2)
      (fun _ _ => zero_le_one) (fun _ _ => sq_nonneg _) (fun _ _ => by simp only [one_mul, le_refl])
    simpa only [singletonSector, Finset.sum_const, nsmul_eq_mul, mul_one] using h
  calc
    _ ≤ expectReal (productLaw S.cavity) (fun σ => (J.card : ℝ) * ∑ i ∈ J, S.singletonComponent g i J σ ^ 2) :=
      expectReal_mono _ hp
    _ = _ := by rw [expectReal_const_mul, expectReal_finset_sum]

/-- The singleton-complement heat-bath estimate, after summing every
orthogonal Hoeffding sector and every marked leaf. -/
theorem singleton_projection_bound (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal
      (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) = 0)
    (hcancel : ∀ i t, (∑ c, S.centreLaw.w c * g i c t * edgeLikelihood S.s (S.cavity i) c t) = 0)
    {B c₀ : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) (hc : 0 < c₀)
    (hp : ∀ i c, S.s * (S.cavity i).w c ≤ B) (hν : ∀ c, S.s * S.centreLaw.w c ≤ B)
    (hR : ∀ σ, c₀ ≤ S.leafDensity σ) :
    expectReal S.jointLaw (fun σ => S.centreProjection (singletonFunction g) σ ^ 2) ≤
      (2 * ((Fintype.card D - 1 : ℕ) : ℝ) * (B ^ 2 / (1 - B) ^ 2) *
        (1 + S.s * B / (1 - B) ^ 2) ^ (Fintype.card D - 2) / (c₀ * (1 - B))) *
        ∑ i, S.leafResidualEnergy g i := by
  let κ := B ^ 2 / (1 - B) ^ 2
  let ω := S.s * B / (1 - B) ^ 2
  have hκ : 0 ≤ κ / (1 - B) := div_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith)
  have hω : 0 ≤ ω := div_nonneg (mul_nonneg S.s_nonneg hB) (sq_nonneg _)
  have hsum : expectReal (productLaw S.cavity) (fun σ => S.centreNumerator (singletonFunction g) σ ^ 2) ≤
      (κ / (1 - B)) *
        ((2 * ((Fintype.card D - 1 : ℕ) : ℝ) * (1 + ω) ^ (Fintype.card D - 2)) *
          ∑ i, S.leafResidualEnergy g i) := by
    rw [S.singletonNumerator_energy g hmean]
    calc
      _ ≤ (κ / (1 - B)) * ∑ J ∈ (Finset.univ : Finset D).powerset,
          (if 2 ≤ J.card then (J.card : ℝ) * ω ^ (J.card - 2) * ∑ i ∈ J, S.leafResidualEnergy g i else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro J _
        by_cases hJ : 2 ≤ J.card
        · rw [if_pos hJ]
          have hb := (S.singletonSector_energy_le g J).trans
            (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi =>
              S.singletonComponent_energy_bound g i J hi hJ hB hB1 hp hν) (Nat.cast_nonneg _))
          calc
            _ ≤ (J.card : ℝ) * ∑ i ∈ J, ((κ * ω ^ (J.card - 2) / (1 - B)) * S.leafResidualEnergy g i) := hb
            _ = _ := by rw [← Finset.mul_sum]; ring
        · have hz (σ : D → C) := S.singletonSector_small g hcancel J (by omega) σ
          simp only [hz, zero_pow (by norm_num : 2 ≠ 0), expectReal_const, if_neg hJ, mul_zero, le_refl]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hκ
        simpa only [Finset.card_univ] using weighted_marked_subset_sum_le
          (Finset.univ : Finset D) hω (S.leafResidualEnergy g) (fun i _ => S.leafResidualEnergy_nonneg g i)
  have hb := (S.centreProjection_energy_le (singletonFunction g) hc hR).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 / c₀))
  change _ ≤ (2 * ((Fintype.card D - 1 : ℕ) : ℝ) * κ * (1 + ω) ^ (Fintype.card D - 2) /
    (c₀ * (1 - B))) * ∑ i, S.leafResidualEnergy g i
  calc
    _ ≤ (1 / c₀) * ((κ / (1 - B)) *
        ((2 * ((Fintype.card D - 1 : ℕ) : ℝ) * (1 + ω) ^ (Fintype.card D - 2)) *
          ∑ i, S.leafResidualEnergy g i)) := hb
    _ = _ := by
      field_simp [hc.ne', (sub_pos.mpr hB1).ne']

end

end ZeroFreeness.Appendix.Girth.ConditionalStar
