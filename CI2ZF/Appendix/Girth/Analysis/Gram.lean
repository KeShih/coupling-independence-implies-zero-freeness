import CI2ZF.Appendix.Girth.Analysis.Covariance

/-!
# Weighted Potts Gram bounds and Schur products

The colour-matrix estimates are proved as quadratic-form bounds directly
from the actual one-leaf channel. The Schur-product step uses the channel's
Gram representation and finite averaging, so no matrix norm theorem is
assumed. Zero atoms of either colour law are allowed throughout.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI Finset

noncomputable section

variable {C T : Type*} [Fintype C] [Fintype T]

def kernelEnergy (K : C → C → ℝ) (z : C → ℝ) : ℝ :=
  ∑ c, ∑ d, z c * z d * K c d

def featureGram (p : FinDist T) (f : C → T → ℝ) (c d : C) : ℝ :=
  expectReal p (fun t => f c t * f d t)

theorem kernelEnergy_featureGram (p : FinDist T) (f : C → T → ℝ) (z : C → ℝ) :
    kernelEnergy (featureGram p f) z = expectReal p (fun t => (∑ c, z c * f c t) ^ 2) := by
  simp only [kernelEnergy, featureGram, expectReal, pow_two, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ c, ∑ t, ∑ d, z c * z d * (p.w t * (f c t * f d t)) := by
      apply Finset.sum_congr rfl
      intro c _
      exact Finset.sum_comm
    _ = ∑ t, ∑ c, ∑ d, z c * z d * (p.w t * (f c t * f d t)) := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring

/-- Schur multiplication by a Gram kernel costs at most its largest
diagonal entry. This is proved by applying the old bound separately to
each feature direction and then averaging. -/
theorem schur_feature_energy_bound (K : C → C → ℝ) (p : FinDist T) (f : C → T → ℝ)
    {κ : ℝ}
    (hK : ∀ z, kernelEnergy K z ≤ κ * ∑ c, z c ^ 2)
    (z : C → ℝ) :
    kernelEnergy (fun c d => K c d * featureGram p f c d) z ≤
      κ * ∑ c, z c ^ 2 * expectReal p (fun t => f c t ^ 2) := by
  have he : kernelEnergy (fun c d => K c d * featureGram p f c d) z =
      expectReal p (fun t => kernelEnergy K (fun c => z c * f c t)) := by
    simp only [kernelEnergy, featureGram, expectReal, Finset.mul_sum]
    calc
      _ = ∑ c, ∑ t, ∑ d, z c * z d * (K c d * (p.w t * (f c t * f d t))) := by
        apply Finset.sum_congr rfl
        intro c _
        exact Finset.sum_comm
      _ = ∑ t, ∑ c, ∑ d, z c * z d * (K c d * (p.w t * (f c t * f d t))) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro d _
        ring
  rw [he]
  calc
    _ ≤ expectReal p (fun t => κ * ∑ c, (z c * f c t) ^ 2) := expectReal_mono p fun t => hK _
    _ = κ * ∑ c, z c ^ 2 * expectReal p (fun t => f c t ^ 2) := by
      simp only [expectReal, Finset.mul_sum, mul_pow]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro t _
      ring

theorem schur_feature_bound (K : C → C → ℝ) (p : FinDist T) (f : C → T → ℝ)
    {κ ω : ℝ} (hκ : 0 ≤ κ)
    (hK : ∀ z, kernelEnergy K z ≤ κ * ∑ c, z c ^ 2)
    (hdiag : ∀ c, expectReal p (fun t => f c t ^ 2) ≤ ω) (z : C → ℝ) :
    kernelEnergy (fun c d => K c d * featureGram p f c d) z ≤ κ * ω * ∑ c, z c ^ 2 := by
  calc
    _ ≤ κ * ∑ c, z c ^ 2 * expectReal p (fun t => f c t ^ 2) := schur_feature_energy_bound K p f hK z
    _ ≤ κ * ∑ c, z c ^ 2 * ω := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left (hdiag c) (sq_nonneg _)) hκ
    _ = _ := by rw [← Finset.sum_mul]; ring

variable [DecidableEq C]

/-- The full one-channel quadratic form is a categorical variance. -/
theorem edge_gram_energy (p : FinDist C) {s : ℝ}
    (hden : ∀ c, 1 - s * p.w c ≠ 0) (z : C → ℝ) :
    kernelEnergy (featureGram p (edgeFluctuation s p)) z =
      variance p (fun c => s * z c / (1 - s * p.w c)) := by
  rw [kernelEnergy_featureGram]
  unfold variance
  congr 1
  funext t
  have he : (∑ c, z c * edgeFluctuation s p c t) =
      -(s * z t / (1 - s * p.w t) - expectReal p (fun c => s * z c / (1 - s * p.w c))) := by
    simp_rw [edgeFluctuation_eq p _ _ (hden _)]
    simp only [mul_sub, Finset.sum_sub_distrib, colourIndicator, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    unfold expectReal
    have hs : (∑ c, z c * ((-s / (1 - s * p.w c)) * p.w c)) =
        -(∑ c, p.w c * (s * z c / (1 - s * p.w c))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hs]
    ring
  rw [he, neg_sq]

/-- The weighted one-leaf Gram operator has norm at most B²/(1-B)²,
expressed as its exact Euclidean quadratic-form estimate. -/
theorem weighted_edge_gram_bound (p ν : FinDist C) {s B : ℝ}
    (hs : 0 ≤ s) (hB : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ c, s * p.w c ≤ B) (hν : ∀ c, s * ν.w c ≤ B) (z : C → ℝ) :
    kernelEnergy (fun c d => Real.sqrt (ν.w c) * Real.sqrt (ν.w d) *
      featureGram p (edgeFluctuation s p) c d) z ≤
      (B ^ 2 / (1 - B) ^ 2) * ∑ c, z c ^ 2 := by
  have hd (c : C) : 0 < 1 - s * p.w c := by linarith [hp c]
  have he : kernelEnergy (fun c d => Real.sqrt (ν.w c) * Real.sqrt (ν.w d) *
      featureGram p (edgeFluctuation s p) c d) z =
      kernelEnergy (featureGram p (edgeFluctuation s p)) (fun c => Real.sqrt (ν.w c) * z c) := by
    unfold kernelEnergy
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro d _
    ring
  rw [he, edge_gram_energy p (fun c => (hd c).ne')]
  calc
    _ ≤ expectReal p (fun c => (s * (Real.sqrt (ν.w c) * z c) / (1 - s * p.w c)) ^ 2) := by
      simpa only [sub_zero] using variance_le_error p
        (fun c => s * (Real.sqrt (ν.w c) * z c) / (1 - s * p.w c)) 0
    _ ≤ ∑ c, (B ^ 2 / (1 - B) ^ 2) * z c ^ 2 := by
      apply Finset.sum_le_sum
      intro c _
      have hnum : s ^ 2 * p.w c * ν.w c ≤ B ^ 2 := by
        have h := mul_le_mul (hp c) (hν c) (mul_nonneg hs (ν.nonneg c)) hB
        nlinarith
      have hden : (1 - B) ^ 2 ≤ (1 - s * p.w c) ^ 2 := by nlinarith [hp c]
      have hc := div_le_div₀ (sq_nonneg B)
        hnum (by positivity : 0 < (1 - B) ^ 2) hden
      have heq : p.w c * (s * (Real.sqrt (ν.w c) * z c) / (1 - s * p.w c)) ^ 2 =
          (s ^ 2 * p.w c * ν.w c / (1 - s * p.w c) ^ 2) * z c ^ 2 := by
        rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (ν.nonneg c)]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := (Finset.mul_sum ..).symm

theorem edge_gram_diagonal_bound (p : FinDist C) {s B : ℝ}
    (hs : 0 ≤ s) (hB : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ c, s * p.w c ≤ B) (c : C) :
    expectReal p (fun t => edgeFluctuation s p c t ^ 2) ≤ s * B / (1 - B) ^ 2 := by
  have hd : 0 < 1 - s * p.w c := by linarith [hp c]
  have he : expectReal p (fun t => edgeFluctuation s p c t ^ 2) =
      s ^ 2 * (p.w c - p.w c ^ 2) / (1 - s * p.w c) ^ 2 := by
    simpa only [pow_two, ite_true, eq_self] using edge_gram_formula p c c hd.ne' hd.ne'
  rw [he]
  have hnum : s ^ 2 * (p.w c - p.w c ^ 2) ≤ s * B := by
    have h := mul_le_mul_of_nonneg_left (hp c) hs
    nlinarith [sq_nonneg (s * p.w c)]
  have hden : (1 - B) ^ 2 ≤ (1 - s * p.w c) ^ 2 := by nlinarith [hp c]
  exact div_le_div₀ (mul_nonneg hs hB) hnum (by positivity) hden

variable {D : Type*} [Fintype D]

omit [DecidableEq C] [Fintype D] in
theorem schur_feature_product_bound (K : C → C → ℝ) (p : D → FinDist T)
    (f : D → C → T → ℝ) {κ ω : ℝ} (hκ : 0 ≤ κ) (hω : 0 ≤ ω)
    (hK : ∀ z, kernelEnergy K z ≤ κ * ∑ c, z c ^ 2)
    (hdiag : ∀ i c, expectReal (p i) (fun t => f i c t ^ 2) ≤ ω)
    (J : Finset D) (z : C → ℝ) :
    kernelEnergy (fun c d => K c d * ∏ j ∈ J, featureGram (p j) (f j) c d) z ≤
      (κ * ω ^ J.card) * ∑ c, z c ^ 2 := by
  classical
  induction J using Finset.induction_on generalizing z with
  | empty => simpa only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero] using hK z
  | @insert i J hi ih =>
    have hb := schur_feature_bound (fun c d => K c d * ∏ j ∈ J, featureGram (p j) (f j) c d)
      (p i) (f i) (mul_nonneg hκ (pow_nonneg hω _)) (fun z => ih z) (hdiag i) z
    have he : (fun c d => K c d * ∏ j ∈ insert i J, featureGram (p j) (f j) c d) =
        (fun c d => (K c d * ∏ j ∈ J, featureGram (p j) (f j) c d) * featureGram (p i) (f i) c d) := by
      funext c d
      rw [Finset.prod_insert hi]
      ring
    rw [he]
    simpa only [Finset.card_insert_of_notMem hi, pow_succ, mul_assoc] using hb

omit [Fintype D] in
/-- Equation (sg-schur-product), for every nonempty collection of actual
Potts leaf channels, including supported laws with zero atoms. -/
theorem weighted_edge_schur_product_bound (p : D → FinDist C) (ν : FinDist C)
    {s B : ℝ} (hs : 0 ≤ s) (hB : 0 ≤ B) (hB1 : B < 1)
    (hp : ∀ i c, s * (p i).w c ≤ B) (hν : ∀ c, s * ν.w c ≤ B)
    (J : Finset D) (hJ : J.Nonempty) (z : C → ℝ) :
    kernelEnergy (fun c d => Real.sqrt (ν.w c) * Real.sqrt (ν.w d) *
      ∏ j ∈ J, featureGram (p j) (edgeFluctuation s (p j)) c d) z ≤
      ((B ^ 2 / (1 - B) ^ 2) * (s * B / (1 - B) ^ 2) ^ (J.card - 1)) * ∑ c, z c ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := hJ
  have hb := schur_feature_product_bound
    (fun c d => Real.sqrt (ν.w c) * Real.sqrt (ν.w d) * featureGram (p i) (edgeFluctuation s (p i)) c d)
    p (fun j => edgeFluctuation s (p j)) (by positivity : 0 ≤ B ^ 2 / (1 - B) ^ 2)
    (by positivity : 0 ≤ s * B / (1 - B) ^ 2)
    (weighted_edge_gram_bound (p i) ν hs hB hB1 (hp i) hν)
    (fun j c => edge_gram_diagonal_bound (p j) hs hB hB1 (hp j) c) (J.erase i) z
  have he : (fun c d => Real.sqrt (ν.w c) * Real.sqrt (ν.w d) *
      ∏ j ∈ J, featureGram (p j) (edgeFluctuation s (p j)) c d) =
      (fun c d => (Real.sqrt (ν.w c) * Real.sqrt (ν.w d) * featureGram (p i) (edgeFluctuation s (p i)) c d) *
        ∏ j ∈ J.erase i, featureGram (p j) (edgeFluctuation s (p j)) c d) := by
    funext c d
    rw [← Finset.mul_prod_erase J _ hi]
    ring
  rw [he]
  simpa only [Finset.card_erase_of_mem hi] using hb

end

end CI2ZF.Appendix.Girth
