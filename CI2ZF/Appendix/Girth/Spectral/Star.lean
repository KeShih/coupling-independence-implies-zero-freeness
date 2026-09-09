import CI2ZF.Appendix.Girth.Analysis.Gram
import CI2ZF.Appendix.Girth.Analysis.Messages

/-!
# Supported conditional stars

Actual product cavity laws, edge channels, centre marginal, joint star
law, and leaf density. All formulas are valid at activity zero and permit
zero atoms. Positivity comes from the explicit local palette slack.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI Finset

noncomputable section

attribute [local instance] Classical.propDecidable

variable {C D : Type*} [Fintype C] [Fintype D]

def productLaw (p : D → FinDist C) : FinDist (D → C) where
  w σ := ∏ i, (p i).w (σ i)
  nonneg σ := Finset.prod_nonneg fun i _ => (p i).nonneg (σ i)
  sum_one := by
    rw [← Fintype.prod_sum (fun (i : D) (c : C) => (p i).w c)]
    simp only [FinDist.sum_one, Finset.prod_const_one]

theorem productLaw_expect_product (p : D → FinDist C) (f : D → C → ℝ) :
    expectReal (productLaw p) (fun σ => ∏ i, f i (σ i)) = ∏ i, expectReal (p i) (f i) := by
  simp only [expectReal, productLaw, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : D) (c : C) => (p i).w c * f i c)).symm

variable [DecidableEq C]

theorem edgeLikelihood_nonneg (p : FinDist C) {s : ℝ} (hs : s ≤ 1)
    (c t : C) (hd : 0 < 1 - s * p.w c) : 0 ≤ edgeLikelihood s p c t := by
  unfold edgeLikelihood colourIndicator
  split_ifs <;> simp only [mul_one, mul_zero, sub_zero]
  · exact div_nonneg (sub_nonneg.mpr hs) hd.le
  · positivity

def edgeChannel (p : FinDist C) (s : ℝ) (hs : s ≤ 1) (c : C)
    (hd : 0 < 1 - s * p.w c) : FinDist C where
  w t := p.w t * edgeLikelihood s p c t
  nonneg t := mul_nonneg (p.nonneg t) (edgeLikelihood_nonneg p hs c t hd)
  sum_one := edgeLikelihood_mean p c hd.ne'

/-- Only raw local data and an explicit palette budget occur in this
structure. It assumes no spectral, covariance, or mixing conclusion. -/
structure ConditionalStar (C D : Type*) [Fintype C] [Fintype D] [DecidableEq C] where
  s : ℝ
  s_nonneg : 0 ≤ s
  s_le_one : s ≤ 1
  unary : C → ℝ
  unary_nonneg : ∀ c, 0 ≤ unary c
  unary_le_one : ∀ c, unary c ≤ 1
  cavity : D → FinDist C
  edge_positive : ∀ i c, 0 < 1 - s * (cavity i).w c
  palette_slack : 0 < (∑ c, unary c) - (Fintype.card D : ℝ) * s

namespace ConditionalStar

variable (S : ConditionalStar C D)

def palette : ℝ := ∑ c, S.unary c
def normalizer : ℝ := messagePartition S.unary (fun i c => S.s * (S.cavity i).w c)

theorem normalizer_lower : S.palette - (Fintype.card D : ℝ) * S.s ≤ S.normalizer := by
  apply messagePartition_lower (fun c => ⟨S.unary_nonneg c, S.unary_le_one c⟩)
    (fun i c => ⟨mul_nonneg S.s_nonneg ((S.cavity i).nonneg c), by linarith [S.edge_positive i c]⟩)
  intro i
  simp only [← Finset.mul_sum, FinDist.sum_one, mul_one, le_refl]

theorem normalizer_pos : 0 < S.normalizer := S.palette_slack.trans_le S.normalizer_lower

theorem palette_pos : 0 < S.palette := by
  have h := S.palette_slack
  have hn : 0 ≤ (Fintype.card D : ℝ) * S.s := mul_nonneg (Nat.cast_nonneg _) S.s_nonneg
  change 0 < S.palette - (Fintype.card D : ℝ) * S.s at h
  linarith

theorem normalizer_le_palette : S.normalizer ≤ S.palette := by
  apply Finset.sum_le_sum
  intro c _
  have hp : (∏ i, (1 - S.s * (S.cavity i).w c)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => (S.edge_positive i c).le)
      (fun i _ => by linarith [mul_nonneg S.s_nonneg ((S.cavity i).nonneg c)])
  simpa only [mul_one, messageWeight] using mul_le_mul_of_nonneg_left hp (S.unary_nonneg c)

def centreLaw : FinDist C := messageLaw S.unary (fun i c => S.s * (S.cavity i).w c)
  (messageWeight_nonneg S.unary_nonneg (fun i c => by linarith [S.edge_positive i c])) S.normalizer_pos

def leafChannel (c : C) : FinDist (D → C) :=
  productLaw fun i => edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)

def jointLaw : FinDist (C × (D → C)) where
  w σ := S.centreLaw.w σ.1 * (S.leafChannel σ.1).w σ.2
  nonneg σ := mul_nonneg (S.centreLaw.nonneg _) ((S.leafChannel _).nonneg _)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, FinDist.sum_one, mul_one]

def leafDensity (σ : D → C) : ℝ :=
  ∑ c, S.centreLaw.w c * ∏ i, edgeLikelihood S.s (S.cavity i) c (σ i)

theorem jointLaw_weight (c : C) (σ : D → C) :
    S.jointLaw.w (c, σ) = (S.unary c / S.normalizer) *
      ∏ i, (S.cavity i).w (σ i) * (1 - S.s * colourIndicator c (σ i)) := by
  change messageMarginal S.unary (fun i c => S.s * (S.cavity i).w c) c *
    (∏ i, (S.cavity i).w (σ i) * edgeLikelihood S.s (S.cavity i) c (σ i)) = _
  unfold messageMarginal messageWeight edgeLikelihood
  change (S.unary c * (∏ i, (1 - S.s * (S.cavity i).w c)) / S.normalizer) *
    (∏ i, (S.cavity i).w (σ i) * ((1 - S.s * colourIndicator c (σ i)) /
      (1 - S.s * (S.cavity i).w c))) = _
  have hp : (∏ i, (1 - S.s * (S.cavity i).w c)) ≠ 0 :=
    (Finset.prod_pos fun i _ => S.edge_positive i c).ne'
  have he : (∏ i, (S.cavity i).w (σ i) * ((1 - S.s * colourIndicator c (σ i)) /
      (1 - S.s * (S.cavity i).w c))) =
      (∏ i, (S.cavity i).w (σ i) * (1 - S.s * colourIndicator c (σ i))) /
        (∏ i, (1 - S.s * (S.cavity i).w c)) := by
    simp only [← mul_div_assoc, Finset.prod_div_distrib]
  rw [he]
  field_simp [hp, S.normalizer_pos.ne']

theorem leaf_marginal_density (σ : D → C) :
    (∑ c, S.jointLaw.w (c, σ)) = (productLaw S.cavity).w σ * S.leafDensity σ := by
  simp only [jointLaw, leafChannel, productLaw, edgeChannel, leafDensity, Finset.prod_mul_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem leafDensity_eq (σ : D → C) :
    S.leafDensity σ =
      messagePartition S.unary (fun i c => S.s * colourIndicator c (σ i)) / S.normalizer := by
  unfold leafDensity messagePartition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  change (S.unary c * (∏ i, (1 - S.s * (S.cavity i).w c)) / S.normalizer) *
    (∏ i, edgeLikelihood S.s (S.cavity i) c (σ i)) = _
  unfold edgeLikelihood messageWeight
  have hp : (∏ i, (1 - S.s * (S.cavity i).w c)) ≠ 0 :=
    (Finset.prod_pos fun i _ => S.edge_positive i c).ne'
  rw [Finset.prod_div_distrib]
  field_simp [hp, S.normalizer_pos.ne']

/-- The exact density lower bound before substituting the degree budget. -/
theorem leafDensity_lower (σ : D → C) :
    (S.palette - (Fintype.card D : ℝ) * S.s) / S.palette ≤ S.leafDensity σ := by
  have hweight (i : D) (c : C) : 0 ≤ S.s * colourIndicator c (σ i) ∧
      S.s * colourIndicator c (σ i) ≤ 1 := by
    unfold colourIndicator
    split_ifs <;> simp only [mul_one, mul_zero]
    · exact ⟨S.s_nonneg, S.s_le_one⟩
    · norm_num
  have hmass (i : D) : (∑ c, S.s * colourIndicator c (σ i)) ≤ S.s := by
    simp [colourIndicator]
  have hn := messagePartition_lower (fun c => ⟨S.unary_nonneg c, S.unary_le_one c⟩)
    hweight hmass
  rw [S.leafDensity_eq]
  calc
    _ ≤ (S.palette - (Fintype.card D : ℝ) * S.s) / S.normalizer :=
      div_le_div_of_nonneg_left S.palette_slack.le S.normalizer_pos S.normalizer_le_palette
    _ ≤ _ := div_le_div_of_nonneg_right hn S.normalizer_pos.le

theorem leafDensity_pos (σ : D → C) : 0 < S.leafDensity σ :=
  (div_pos S.palette_slack S.palette_pos).trans_le (S.leafDensity_lower σ)

/-- The degree-budget specialization of the lower density estimate. -/
theorem leafDensity_budget {δ Δ : ℝ} (hδ : 0 < δ)
    (hd : (Fintype.card D : ℝ) ≤ Δ)
    (hA : S.s * ((Fintype.card D : ℝ) + δ * Δ) ≤ S.palette) (σ : D → C) :
    δ / (1 + δ) ≤ S.leafDensity σ := by
  apply le_trans _ (S.leafDensity_lower σ)
  apply (div_le_div_iff₀ (by linarith : 0 < 1 + δ) S.palette_pos).mpr
  have hm := mul_le_mul_of_nonneg_left hd (mul_nonneg S.s_nonneg hδ.le)
  nlinarith

def centreNumerator (f : C × (D → C) → ℝ) (σ : D → C) : ℝ :=
  ∑ c, S.centreLaw.w c * (∏ i, edgeLikelihood S.s (S.cavity i) c (σ i)) * f (c, σ)

def centreAverage (f : C × (D → C) → ℝ) (σ : D → C) : ℝ :=
  S.centreNumerator f σ / S.leafDensity σ

def centreProjection (f : C × (D → C) → ℝ) (σ : C × (D → C)) : ℝ :=
  S.centreAverage f σ.2

theorem centreProjection_energy (f : C × (D → C) → ℝ) :
    expectReal S.jointLaw (fun σ => S.centreProjection f σ ^ 2) =
      expectReal (productLaw S.cavity) (fun σ => S.centreNumerator f σ ^ 2 / S.leafDensity σ) := by
  unfold expectReal centreProjection centreAverage
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.sum_mul]
  simp_rw [S.leaf_marginal_density]
  apply Finset.sum_congr rfl
  intro σ _
  field_simp [S.leafDensity_pos σ |>.ne']

/-- Density comparison on supported L²; no positive atom is divided by. -/
theorem centreProjection_energy_le (f : C × (D → C) → ℝ) {c₀ : ℝ}
    (hc : 0 < c₀) (hR : ∀ σ, c₀ ≤ S.leafDensity σ) :
    expectReal S.jointLaw (fun σ => S.centreProjection f σ ^ 2) ≤
      (1 / c₀) * expectReal (productLaw S.cavity) (fun σ => S.centreNumerator f σ ^ 2) := by
  rw [S.centreProjection_energy]
  calc
    _ ≤ expectReal (productLaw S.cavity) (fun σ => S.centreNumerator f σ ^ 2 / c₀) :=
      expectReal_mono _ fun σ => div_le_div_of_nonneg_left (sq_nonneg _) hc (hR σ)
    _ = _ := by
      simp only [expectReal, ← mul_div_assoc, ← Finset.sum_div, one_div]
      ring

theorem jointLaw_centre_expectation (f : C → ℝ) :
    expectReal S.jointLaw (fun σ => f σ.1) = expectReal S.centreLaw f := by
  simp only [expectReal, jointLaw, Fintype.sum_prod_type]
  calc
    _ = ∑ c, S.centreLaw.w c * f c * ∑ σ, (S.leafChannel c).w σ := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = _ := by simp only [FinDist.sum_one, mul_one]

end ConditionalStar

end

end CI2ZF.Appendix.Girth
