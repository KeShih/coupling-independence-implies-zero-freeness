import CI2ZF.Appendix.GirthChannel
import CI2ZF.Appendix.GirthStarCentre

/-! Marked Hoeffding components for the singleton complement of a
conditional star. The distinguished leaf carries its actual conditional
residual; all other leaves carry centred edge likelihoods. -/

namespace CI2ZF.Appendix.Girth.ConditionalStar

open scoped BigOperators
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

def markedFeature (g : D → C → C → ℝ) (i : D) (c : C) (j : D) (t : C) : ℝ :=
  if j = i then g i c t * edgeLikelihood S.s (S.cavity i) c t
  else edgeFluctuation S.s (S.cavity j) c t

theorem markedFeature_self (g : D → C → C → ℝ) (i : D) (c : C) :
    S.markedFeature g i c i = (fun t => g i c t * edgeLikelihood S.s (S.cavity i) c t) := by
  funext t
  simp only [markedFeature, ite_true]

theorem markedFeature_of_ne (g : D → C → C → ℝ) (i j : D) (c : C) (hji : j ≠ i) :
    S.markedFeature g i c j = edgeFluctuation S.s (S.cavity j) c := by
  funext t
  simp only [markedFeature, if_neg hji]

def singletonComponent (g : D → C → C → ℝ) (i : D) (J : Finset D) (σ : D → C) : ℝ :=
  ∑ c, S.centreLaw.w c * tensorFeature J (S.markedFeature g i c) σ

def singletonSector (g : D → C → C → ℝ) (J : Finset D) (σ : D → C) : ℝ :=
  ∑ i ∈ J, S.singletonComponent g i J σ

def leafResidualEnergy (g : D → C → C → ℝ) (i : D) : ℝ :=
  expectReal S.centreLaw (fun c => expectReal
    (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (fun t => g i c t ^ 2))

theorem leafResidualEnergy_nonneg (g : D → C → C → ℝ) (i : D) : 0 ≤ S.leafResidualEnergy g i := by
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (S.centreLaw.nonneg c)
  exact Finset.sum_nonneg fun t _ => mul_nonneg
    ((edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)).nonneg t) (sq_nonneg _)

theorem markedFeature_mean_zero (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal
      (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) = 0)
    (i j : D) (c : C) : expectReal (S.cavity j) (S.markedFeature g i c j) = 0 := by
  by_cases hji : j = i
  · subst j
    have he : expectReal (S.cavity i) (fun t => g i c t * edgeLikelihood S.s (S.cavity i) c t) =
        expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) := by
      simp only [expectReal, edgeChannel]
      apply Finset.sum_congr rfl
      intro t _
      ring
    simpa only [S.markedFeature_self] using he.trans (hmean i c)
  · simpa only [S.markedFeature_of_ne g i j c hji] using
      edgeFluctuation_mean (S.cavity j) c (S.edge_positive j c).ne'

theorem singletonComponent_orthogonal (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal
      (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) = 0)
    (i j : D) {J K : Finset D} (hJK : J ≠ K) :
    expectReal (productLaw S.cavity)
      (fun σ => S.singletonComponent g i J σ * S.singletonComponent g j K σ) = 0 :=
  mixed_tensor_sectors_orthogonal S.cavity J K Finset.univ Finset.univ S.centreLaw.w S.centreLaw.w
    (S.markedFeature g i) (S.markedFeature g j) hJK
    (fun c _ k _ => S.markedFeature_mean_zero g hmean i k c)
    (fun c _ k _ => S.markedFeature_mean_zero g hmean j k c)

theorem singletonSector_orthogonal (g : D → C → C → ℝ)
    (hmean : ∀ i c, expectReal
      (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (g i c) = 0)
    {J K : Finset D} (hJK : J ≠ K) :
    expectReal (productLaw S.cavity) (fun σ => S.singletonSector g J σ * S.singletonSector g K σ) = 0 := by
  simp only [singletonSector, Finset.sum_mul, Finset.mul_sum, expectReal_finset_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact S.singletonComponent_orthogonal g hmean j i hJK

/-- Equation (sg-component-bound): a marked leaf costs one conditional
leaf energy and `(1-B)⁻¹`, while the remaining nonempty Gram product gives
κ ω^(|J|-2). -/
theorem singletonComponent_energy_bound (g : D → C → C → ℝ) (i : D)
    (J : Finset D) (hi : i ∈ J) (hJ : 2 ≤ J.card) {B : ℝ}
    (hB : 0 ≤ B) (hB1 : B < 1) (hp : ∀ j c, S.s * (S.cavity j).w c ≤ B)
    (hν : ∀ c, S.s * S.centreLaw.w c ≤ B) :
    expectReal (productLaw S.cavity) (fun σ => S.singletonComponent g i J σ ^ 2) ≤
      ((B ^ 2 / (1 - B) ^ 2) * (S.s * B / (1 - B) ^ 2) ^ (J.card - 2) / (1 - B)) *
        S.leafResidualEnergy g i := by
  let κ := B ^ 2 / (1 - B) ^ 2
  let ω := S.s * B / (1 - B) ^ 2
  let K : C → C → ℝ := fun c d => Real.sqrt (S.centreLaw.w c) * Real.sqrt (S.centreLaw.w d) *
    ∏ j ∈ J.erase i, featureGram (S.cavity j) (edgeFluctuation S.s (S.cavity j)) c d
  let f : C → C → ℝ := fun c t => g i c t * edgeLikelihood S.s (S.cavity i) c t
  have hrest : (J.erase i).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hi]
    omega
  have hK (z : C → ℝ) : kernelEnergy K z ≤ (κ * ω ^ (J.card - 2)) * ∑ c, z c ^ 2 := by
    have h := weighted_edge_schur_product_bound S.cavity S.centreLaw S.s_nonneg hB hB1 hp hν
      (J.erase i) hrest z
    have he : (J.erase i).card - 1 = J.card - 2 := by rw [Finset.card_erase_of_mem hi]; omega
    simpa only [he] using h
  have hb := schur_feature_energy_bound K (S.cavity i) f hK (fun c => Real.sqrt (S.centreLaw.w c))
  have he : (fun c d => K c d * featureGram (S.cavity i) f c d) =
      (fun c d => Real.sqrt (S.centreLaw.w c) * Real.sqrt (S.centreLaw.w d) *
        ∏ j ∈ J, featureGram (S.cavity j) (fun c => S.markedFeature g i c j) c d) := by
    funext c d
    rw [← Finset.mul_prod_erase J _ hi]
    have hiF : featureGram (S.cavity i) (fun c => S.markedFeature g i c i) c d =
        featureGram (S.cavity i) f c d := by simp only [S.markedFeature_self, f]
    rw [hiF]
    have hpF : (∏ j ∈ J.erase i, featureGram (S.cavity j) (fun c => S.markedFeature g i c j) c d) =
        ∏ j ∈ J.erase i, featureGram (S.cavity j) (edgeFluctuation S.s (S.cavity j)) c d := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [S.markedFeature_of_ne g i j _ (Finset.mem_erase.mp hj).1]
    rw [hpF]
    dsimp [K]
    ring
  have heE : kernelEnergy (fun c d => K c d * featureGram (S.cavity i) f c d)
      (fun c => Real.sqrt (S.centreLaw.w c)) =
      expectReal (productLaw S.cavity) (fun σ => S.singletonComponent g i J σ ^ 2) := by
    rw [he]
    unfold singletonComponent
    rw [mixed_tensor_energy]
    unfold kernelEnergy
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    calc
      _ = Real.sqrt (S.centreLaw.w c) ^ 2 * Real.sqrt (S.centreLaw.w d) ^ 2 *
          (∏ j ∈ J, featureGram (S.cavity j) (fun c => S.markedFeature g i c j) c d) := by ring
      _ = _ := by rw [Real.sq_sqrt (S.centreLaw.nonneg c), Real.sq_sqrt (S.centreLaw.nonneg d)]
  rw [heE] at hb
  simp only [Real.sq_sqrt (S.centreLaw.nonneg _)] at hb
  have hleaf : (∑ c, S.centreLaw.w c * expectReal (S.cavity i) (fun t => f c t ^ 2)) ≤
      (1 / (1 - B)) * S.leafResidualEnergy g i := by
    unfold leafResidualEnergy
    rw [expectReal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c _
    have h := mul_le_mul_of_nonneg_left
      (marked_leaf_energy_bound (S.cavity i) S.s_nonneg S.s_le_one hB1 (hp i) c (g i c)) (S.centreLaw.nonneg c)
    change _ ≤ S.centreLaw.w c * ((1 / (1 - B)) * _) at h
    calc
      _ ≤ S.centreLaw.w c * ((1 / (1 - B)) * _) := h
      _ = _ := by ring
  have hcoef : 0 ≤ κ * ω ^ (J.card - 2) := by
    apply mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    exact pow_nonneg (div_nonneg (mul_nonneg S.s_nonneg hB) (sq_nonneg _)) _
  have hfinal := hb.trans (mul_le_mul_of_nonneg_left hleaf hcoef)
  change _ ≤ (κ * ω ^ (J.card - 2) / (1 - B)) * S.leafResidualEnergy g i
  calc
    _ ≤ (κ * ω ^ (J.card - 2)) * ((1 / (1 - B)) * S.leafResidualEnergy g i) := hfinal
    _ = _ := by ring

end

end CI2ZF.Appendix.Girth.ConditionalStar
