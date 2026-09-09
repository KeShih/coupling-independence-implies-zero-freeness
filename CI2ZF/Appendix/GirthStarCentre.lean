import CI2ZF.Appendix.GirthHoeffding
import CI2ZF.Appendix.GirthSubsetSums

/-!
# Centre-to-leaf Hoeffding estimates

The exact conditional-star centre numerator is expanded in orthogonal
product sectors. Each nonempty sector is bounded using the proved
weighted Potts Schur-product estimate.
-/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

def centreSector (h : C → ℝ) (J : Finset D) (σ : D → C) : ℝ :=
  ∑ c, S.centreLaw.w c * h c * tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) c) σ

theorem centreSector_empty (h : C → ℝ) (σ : D → C) :
    S.centreSector h ∅ σ = expectReal S.centreLaw h := by
  simp only [centreSector, tensorFeature, Finset.prod_empty, mul_one, expectReal]

theorem centreSector_energy (h : C → ℝ) (J : Finset D) :
    expectReal (productLaw S.cavity) (fun σ => S.centreSector h J σ ^ 2) =
      kernelEnergy (fun c d => ∏ j ∈ J, featureGram (S.cavity j) (edgeFluctuation S.s (S.cavity j)) c d)
        (fun c => S.centreLaw.w c * h c) := by
  have hprod (c d : C) : expectReal (productLaw S.cavity)
      (fun σ => tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) c) σ *
        tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) d) σ) =
      ∏ j ∈ J, featureGram (S.cavity j) (edgeFluctuation S.s (S.cavity j)) c d := by
    simp only [tensorFeature, ← Finset.prod_mul_distrib]
    exact productLaw_expect_tensor S.cavity J (fun i t =>
      edgeFluctuation S.s (S.cavity i) c t * edgeFluctuation S.s (S.cavity i) d t)
  simp only [centreSector, kernelEnergy, pow_two, Finset.sum_mul, Finset.mul_sum, expectReal_finset_sum]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  have he : (fun σ => (S.centreLaw.w d * h d * tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) d) σ) *
      (S.centreLaw.w c * h c * tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) c) σ)) =
      (fun σ => (S.centreLaw.w c * h c) * (S.centreLaw.w d * h d) *
        (tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) c) σ *
          tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) d) σ)) := by
    funext σ
    ring
  rw [he, expectReal_const_mul, hprod]

theorem centreSector_orthogonal (h : C → ℝ) {J K : Finset D} (hJK : J ≠ K) :
    expectReal (productLaw S.cavity) (fun σ => S.centreSector h J σ * S.centreSector h K σ) = 0 := by
  simp only [centreSector, Finset.sum_mul, Finset.mul_sum, expectReal_finset_sum]
  apply Finset.sum_eq_zero
  intro c _
  apply Finset.sum_eq_zero
  intro d _
  have he : (fun σ => (S.centreLaw.w d * h d * tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) d) σ) *
      (S.centreLaw.w c * h c * tensorFeature K (fun i => edgeFluctuation S.s (S.cavity i) c) σ)) =
      (fun σ => (S.centreLaw.w d * h d) * (S.centreLaw.w c * h c) *
        (tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) d) σ *
          tensorFeature K (fun i => edgeFluctuation S.s (S.cavity i) c) σ)) := by
    funext σ
    ring
  rw [he, expectReal_const_mul]
  have hz := tensor_sectors_orthogonal S.cavity J K
    (fun i => edgeFluctuation S.s (S.cavity i) d) (fun i => edgeFluctuation S.s (S.cavity i) c)
    hJK (fun i _ => edgeFluctuation_mean (S.cavity i) d (S.edge_positive i d).ne')
    (fun i _ => edgeFluctuation_mean (S.cavity i) c (S.edge_positive i c).ne')
  rw [hz, mul_zero]

theorem centreNumerator_expansion (h : C → ℝ) (σ : D → C) :
    S.centreNumerator (fun τ => h τ.1) σ =
      ∑ J ∈ (Finset.univ : Finset D).powerset, S.centreSector h J σ := by
  have he (c : C) : (∏ i, edgeLikelihood S.s (S.cavity i) c (σ i)) =
      ∑ J ∈ (Finset.univ : Finset D).powerset,
        tensorFeature J (fun i => edgeFluctuation S.s (S.cavity i) c) σ := by
    unfold tensorFeature
    rw [← Finset.prod_one_add]
    apply Finset.prod_congr rfl
    intro i _
    unfold edgeFluctuation
    ring
  unfold centreNumerator centreSector
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [he, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro J _
  ring

theorem centreNumerator_energy (h : C → ℝ) :
    expectReal (productLaw S.cavity) (fun σ => S.centreNumerator (fun τ => h τ.1) σ ^ 2) =
      ∑ J ∈ (Finset.univ : Finset D).powerset,
        expectReal (productLaw S.cavity) (fun σ => S.centreSector h J σ ^ 2) := by
  simp_rw [S.centreNumerator_expansion]
  exact orthogonal_sum_squared _ _ _ (fun _ _ _ _ hJK => S.centreSector_orthogonal h hJK)

theorem centreSector_energy_bound (h : C → ℝ) (J : Finset D) (hJ : J.Nonempty)
    {B : ℝ} (hB : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (hν : ∀ c, S.s * S.centreLaw.w c ≤ B) :
    expectReal (productLaw S.cavity) (fun σ => S.centreSector h J σ ^ 2) ≤
      ((B ^ 2 / (1 - B) ^ 2) * (S.s * B / (1 - B) ^ 2) ^ (J.card - 1)) *
        expectReal S.centreLaw (fun c => h c ^ 2) := by
  have hb := weighted_edge_schur_product_bound S.cavity S.centreLaw S.s_nonneg hB hB1 hp hν J hJ
    (fun c => Real.sqrt (S.centreLaw.w c) * h c)
  have he : kernelEnergy (fun c d => Real.sqrt (S.centreLaw.w c) * Real.sqrt (S.centreLaw.w d) *
      ∏ j ∈ J, featureGram (S.cavity j) (edgeFluctuation S.s (S.cavity j)) c d)
      (fun c => Real.sqrt (S.centreLaw.w c) * h c) =
      kernelEnergy (fun c d => ∏ j ∈ J, featureGram (S.cavity j) (edgeFluctuation S.s (S.cavity j)) c d)
        (fun c => S.centreLaw.w c * h c) := by
    unfold kernelEnergy
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    have hc := Real.sq_sqrt (S.centreLaw.nonneg c)
    have hd := Real.sq_sqrt (S.centreLaw.nonneg d)
    calc
      _ = Real.sqrt (S.centreLaw.w c) ^ 2 * Real.sqrt (S.centreLaw.w d) ^ 2 * h c * h d *
          (∏ j ∈ J, featureGram (S.cavity j) (edgeFluctuation S.s (S.cavity j)) c d) := by ring
      _ = _ := by rw [hc, hd]; ring
  have hn : (∑ c, (Real.sqrt (S.centreLaw.w c) * h c) ^ 2) =
      expectReal S.centreLaw (fun c => h c ^ 2) := by
    simp only [mul_pow, Real.sq_sqrt (S.centreLaw.nonneg _), expectReal]
  rw [he, hn] at hb
  rw [S.centreSector_energy]
  exact hb

/-- The full centre block estimate. The sole assumptions are the actual
star's raw marginal caps and its leaf-density lower bound. -/
theorem centre_projection_bound (h : C → ℝ) (hmean : expectReal S.centreLaw h = 0)
    {B c₀ : ℝ} (hB : 0 ≤ B) (hB1 : B < 1) (hc : 0 < c₀)
    (hp : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (hν : ∀ c, S.s * S.centreLaw.w c ≤ B)
    (hR : ∀ σ, c₀ ≤ S.leafDensity σ) :
    expectReal S.jointLaw (fun σ => S.centreProjection (fun τ => h τ.1) σ ^ 2) ≤
      ((Fintype.card D : ℝ) * (B ^ 2 / (1 - B) ^ 2) *
        (1 + S.s * B / (1 - B) ^ 2) ^ (Fintype.card D - 1) / c₀) *
        expectReal S.centreLaw (fun c => h c ^ 2) := by
  let κ := B ^ 2 / (1 - B) ^ 2
  let ω := S.s * B / (1 - B) ^ 2
  let E := expectReal S.centreLaw (fun c => h c ^ 2)
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hω : 0 ≤ ω := div_nonneg (mul_nonneg S.s_nonneg hB) (sq_nonneg _)
  have hE : 0 ≤ E := Finset.sum_nonneg fun c _ => mul_nonneg (S.centreLaw.nonneg c) (sq_nonneg _)
  have hsum : expectReal (productLaw S.cavity) (fun σ => S.centreNumerator (fun τ => h τ.1) σ ^ 2) ≤
      κ * E * ((Fintype.card D : ℝ) * (1 + ω) ^ (Fintype.card D - 1)) := by
    rw [S.centreNumerator_energy]
    calc
      _ ≤ ∑ J ∈ (Finset.univ : Finset D).powerset, κ * E * (if J.Nonempty then ω ^ (J.card - 1) else 0) := by
        apply Finset.sum_le_sum
        intro J _
        by_cases hJ : J.Nonempty
        · rw [if_pos hJ]
          have hb := S.centreSector_energy_bound h J hJ hB hB1 hp hν
          change _ ≤ (κ * ω ^ (J.card - 1)) * E at hb
          nlinarith
        · have he : J = ∅ := Finset.not_nonempty_iff_eq_empty.mp hJ
          subst J
          simp only [S.centreSector_empty, hmean, zero_pow (by norm_num : 2 ≠ 0), expectReal_const,
            Finset.not_nonempty_empty, ite_false, mul_zero, le_refl]
      _ = κ * E * ∑ J ∈ (Finset.univ : Finset D).powerset, (if J.Nonempty then ω ^ (J.card - 1) else 0) :=
        (Finset.mul_sum ..).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hκ hE)
        simpa only [Finset.card_univ] using nonempty_subset_sum_le (Finset.univ : Finset D) hω
  have hb := (S.centreProjection_energy_le (fun τ => h τ.1) hc hR).trans
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 / c₀))
  change _ ≤ ((Fintype.card D : ℝ) * κ * (1 + ω) ^ (Fintype.card D - 1) / c₀) * E
  calc
    _ ≤ (1 / c₀) * (κ * E * ((Fintype.card D : ℝ) * (1 + ω) ^ (Fintype.card D - 1))) := hb
    _ = _ := by ring

end

end CI2ZF.Appendix.Girth.ConditionalStar
