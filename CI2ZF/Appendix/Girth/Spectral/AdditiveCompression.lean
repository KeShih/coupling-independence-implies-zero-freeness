import CI2ZF.Appendix.Girth.Spectral.Additive
import CI2ZF.Appendix.Girth.Spectral.Occupancy

/-! The additive-compression estimate from the actual leaf channels,
weighted Cauchy--Schwarz, and the sharp star occupancy bound. -/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators InnerProductSpace
open PottsCI Finset

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I]

theorem weighted_sum_square (w f : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * f i)
  have he (i : I) : Real.sqrt (w i) * (Real.sqrt (w i) * f i) = w i * f i := by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  simpa only [he, mul_pow, Real.sq_sqrt (hw _)] using h

namespace ConditionalStar

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]
variable (S : ConditionalStar C D)

def additiveMean (h : D → C → ℝ) (c : C) : ℝ :=
  ∑ i, expectReal (edgeChannel (S.cavity i) S.s S.s_le_one c (S.edge_positive i c)) (h i)

def additiveResidualSum (h : D → C → ℝ) : C × (D → C) → ℝ :=
  singletonFunction (fun i => S.additiveResidual i (h i))

theorem additiveMean_formula (h : D → C → ℝ)
    (hmean : ∀ i, expectReal (S.cavity i) (h i) = 0) (c : C) :
    S.additiveMean h c = -S.s * ∑ i, (S.cavity i).w c * (h i c / (1 - S.s * (S.cavity i).w c)) := by
  unfold additiveMean
  simp_rw [edgeChannel_expect, hmean, zero_sub]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem additiveMean_square_bound {B : ℝ} (hB : B < 1)
    (hcap : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (h : D → C → ℝ) (hmean : ∀ i, expectReal (S.cavity i) (h i) = 0) (c : C) :
    S.additiveMean h c ^ 2 ≤ (S.s ^ 2 / (1 - B) ^ 2) *
      (∑ i, (S.cavity i).w c) * ∑ i, (S.cavity i).w c * h i c ^ 2 := by
  rw [S.additiveMean_formula h hmean c, mul_pow, neg_sq]
  have hcs := weighted_sum_square (fun i => (S.cavity i).w c)
    (fun i => h i c / (1 - S.s * (S.cavity i).w c)) (fun i => (S.cavity i).nonneg c)
  have hnorm : (∑ i, (S.cavity i).w c * (h i c / (1 - S.s * (S.cavity i).w c)) ^ 2) ≤
      (∑ i, (S.cavity i).w c * h i c ^ 2) / (1 - B) ^ 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    have hden : (1 - B) ^ 2 ≤ (1 - S.s * (S.cavity i).w c) ^ 2 := by nlinarith [hcap i c]
    have ht := div_le_div_of_nonneg_left (sq_nonneg (h i c)) (by positivity : 0 < (1 - B) ^ 2) hden
    simpa only [div_pow, mul_div_assoc] using mul_le_mul_of_nonneg_left ht ((S.cavity i).nonneg c)
  calc
    _ ≤ S.s ^ 2 * ((∑ i, (S.cavity i).w c) *
        ∑ i, (S.cavity i).w c * (h i c / (1 - S.s * (S.cavity i).w c)) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ ≤ S.s ^ 2 * ((∑ i, (S.cavity i).w c) *
        ((∑ i, (S.cavity i).w c * h i c ^ 2) / (1 - B) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm
        (Finset.sum_nonneg fun i _ => (S.cavity i).nonneg c)) (sq_nonneg _)
    _ = _ := by ring

theorem additiveMean_energy_bound {B θ : ℝ} (hB : B < 1)
    (hcap : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (hocc : ∀ c, ((Fintype.card D : ℝ) * S.s ^ 2 / (1 - B) ^ 2) *
      (S.centreLaw.w c * ∑ i, (S.cavity i).w c) ≤ θ)
    (h : D → C → ℝ) (hmean : ∀ i, expectReal (S.cavity i) (h i) = 0) :
    (Fintype.card D : ℝ) * expectReal S.centreLaw (fun c => S.additiveMean h c ^ 2) ≤
      θ * ∑ i, expectReal (S.cavity i) (fun c => h i c ^ 2) := by
  have hc (c : C) : (Fintype.card D : ℝ) * S.centreLaw.w c * S.additiveMean h c ^ 2 ≤
      θ * ∑ i, (S.cavity i).w c * h i c ^ 2 := by
    have hb := mul_le_mul_of_nonneg_left (S.additiveMean_square_bound hB hcap h hmean c)
      (mul_nonneg (Nat.cast_nonneg (Fintype.card D)) (S.centreLaw.nonneg c))
    have hsum : 0 ≤ ∑ i, (S.cavity i).w c * h i c ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg ((S.cavity i).nonneg c) (sq_nonneg (h i c))
    have hh := mul_le_mul_of_nonneg_right (hocc c) hsum
    calc
      _ ≤ ((Fintype.card D : ℝ) * S.centreLaw.w c) *
          ((S.s ^ 2 / (1 - B) ^ 2) * (∑ i, (S.cavity i).w c) *
          (∑ i, (S.cavity i).w c * h i c ^ 2)) := hb
      _ = ((Fintype.card D : ℝ) * S.s ^ 2 / (1 - B) ^ 2) *
          (S.centreLaw.w c * ∑ i, (S.cavity i).w c) *
          (∑ i, (S.cavity i).w c * h i c ^ 2) := by ring
      _ ≤ _ := hh
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hc c)
  simp only [expectReal, Finset.mul_sum, mul_assoc] at hh ⊢
  rw [Finset.sum_comm] at hh
  exact hh

theorem additiveResidualSum_energy (h : D → C → ℝ) :
    expectReal S.jointLaw (fun σ => S.additiveResidualSum h σ ^ 2) =
      ∑ i, channelVariance S.centreLaw (S.cavity i) S.s S.s_le_one (S.edge_positive i) (h i) := by
  rw [additiveResidualSum, S.singletonFunction_energy _ (fun i c => S.additiveResidual_mean i (h i) c)]
  rfl

/-- The functional form of the exact additive-compression estimate,
with the displayed margin `(1+δ/2)⁻¹`. -/
theorem additive_compression_energy {δ Δ B : ℝ} (hδ : 0 < δ) (hB0 : 0 ≤ B)
    (hB : B ≤ δ / (8 * (1 + δ)))
    (hd : (Fintype.card D : ℝ) ≤ Δ)
    (hA : S.s * ((Fintype.card D : ℝ) + δ * Δ) ≤ S.palette)
    (hcap : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (hν : ∀ c, S.s * S.centreLaw.w c ≤ B)
    (h : D → C → ℝ) (hmean : ∀ i, expectReal (S.cavity i) (h i) = 0) :
    (Fintype.card D : ℝ) * expectReal S.jointLaw (fun σ =>
      (S.additiveMean h σ.1 - S.centreProjection (fun τ => S.additiveMean h τ.1) σ) ^ 2) ≤
      (1 / (1 + δ / 2)) * expectReal S.jointLaw (fun σ => S.additiveResidualSum h σ ^ 2) := by
  have hb := (le_div_iff₀ (by positivity : 0 < 8 * (1 + δ))).mp hB
  have hB1 : B < 1 := by nlinarith
  let E : ℝ := ∑ i, expectReal (S.cavity i) (fun c => h i c ^ 2)
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun c _ => mul_nonneg ((S.cavity i).nonneg c) (sq_nonneg _)
  have hmeanbound := S.additiveMean_energy_bound hB1 hcap
    (S.star_occupancy_le hδ hB0 hB hd hA hcap) h hmean
  have hcomp := mul_le_mul_of_nonneg_left
    (S.centreComplement_energy_le (fun σ => S.additiveMean h σ.1)) (Nat.cast_nonneg (Fintype.card D) (α := ℝ))
  rw [S.jointLaw_centre_expectation (fun c => S.additiveMean h c ^ 2)] at hcomp
  have hvar : (1 - B / (1 - B) ^ 2) * E ≤
      expectReal S.jointLaw (fun σ => S.additiveResidualSum h σ ^ 2) := by
    rw [S.additiveResidualSum_energy]
    dsimp [E]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact channelVariance_lower S.centreLaw (S.cavity i) S.s_nonneg S.s_le_one hB0 hB1
      (hcap i) hν (h i) (hmean i)
  have hfac := (channel_variance_factor_lower hδ hB0 hB).2
  have hmargin := mul_le_mul_of_nonneg_right hfac hE
  have hvar' := mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ 1 + 3 * δ / 4)
  have hden : 0 < 1 + 3 * δ / 4 := by positivity
  have hmean' := (le_div_iff₀ hden).mp (by simpa only [one_div_mul_eq_div] using hmeanbound)
  have hlast : (1 + δ / 2) * ((Fintype.card D : ℝ) *
      expectReal S.centreLaw (fun c => S.additiveMean h c ^ 2)) ≤
        expectReal S.jointLaw (fun σ => S.additiveResidualSum h σ ^ 2) := by
    have he := mul_le_mul_of_nonneg_left hmean' (by positivity : 0 ≤ 1 + δ / 2)
    nlinarith
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ (by positivity : 0 < 1 + δ / 2)).mpr
  have hh := mul_le_mul_of_nonneg_right hcomp (by positivity : 0 ≤ 1 + δ / 2)
  simpa only [one_div_mul_eq_div] using hh.trans (by nlinarith [hlast])

omit [DecidableEq C] in
theorem expectation_sub_constant (p : FinDist C) (f : C → ℝ) (a : ℝ) :
    expectReal p (fun c => f c - a) = expectReal p f - a := by
  simp only [expectReal, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    FinDist.sum_one, one_mul]

theorem additiveResidual_shift (i : D) (h : C → ℝ) (a : ℝ) (c t : C) :
    S.additiveResidual i (fun u => h u - a) c t = S.additiveResidual i h c t := by
  unfold additiveResidual
  rw [expectation_sub_constant]
  ring

theorem additiveMean_shift (h : D → C → ℝ) (a : D → ℝ) (c : C) :
    S.additiveMean (fun i t => h i t - a i) c = S.additiveMean h c - ∑ i, a i := by
  unfold additiveMean
  simp_rw [expectation_sub_constant]
  rw [Finset.sum_sub_distrib]

theorem additiveResidualSum_shift (h : D → C → ℝ) (a : D → ℝ) :
    S.additiveResidualSum (fun i t => h i t - a i) = S.additiveResidualSum h := by
  funext σ
  unfold additiveResidualSum singletonFunction
  simp only [S.additiveResidual_shift]

theorem centreProjection_shift (f : C × (D → C) → ℝ) (a : ℝ) (σ : C × (D → C)) :
    S.centreProjection (fun τ => f τ - a) σ = S.centreProjection f σ - a := by
  unfold centreProjection
  rw [S.centreAverage_expectation, S.centreAverage_expectation, expectation_sub_constant]

/-- The final estimate needs no normalization of the chosen additive
functions: subtracting their cavity means leaves all residuals and the
centre complement unchanged. -/
theorem additive_compression_energy_all {δ Δ B : ℝ} (hδ : 0 < δ) (hB0 : 0 ≤ B)
    (hB : B ≤ δ / (8 * (1 + δ)))
    (hd : (Fintype.card D : ℝ) ≤ Δ)
    (hA : S.s * ((Fintype.card D : ℝ) + δ * Δ) ≤ S.palette)
    (hcap : ∀ i c, S.s * (S.cavity i).w c ≤ B)
    (hν : ∀ c, S.s * S.centreLaw.w c ≤ B) (h : D → C → ℝ) :
    (Fintype.card D : ℝ) * expectReal S.jointLaw (fun σ =>
      (S.additiveMean h σ.1 - S.centreProjection (fun τ => S.additiveMean h τ.1) σ) ^ 2) ≤
      (1 / (1 + δ / 2)) * expectReal S.jointLaw (fun σ => S.additiveResidualSum h σ ^ 2) := by
  let a : D → ℝ := fun i => expectReal (S.cavity i) (h i)
  have hh := S.additive_compression_energy hδ hB0 hB hd hA hcap hν
    (fun i t => h i t - a i) (fun i => expectation_centered (S.cavity i) (h i))
  rw [S.additiveResidualSum_shift h a] at hh
  have he : (fun σ : C × (D → C) => S.additiveMean (fun i t => h i t - a i) σ.1 -
      S.centreProjection (fun τ => S.additiveMean (fun i t => h i t - a i) τ.1) σ) =
      (fun σ => S.additiveMean h σ.1 - S.centreProjection (fun τ => S.additiveMean h τ.1) σ) := by
    funext σ
    simp_rw [S.additiveMean_shift h a]
    rw [S.centreProjection_shift]
    ring
  change (Fintype.card D : ℝ) * expectReal S.jointLaw (fun σ =>
    ((fun σ => S.additiveMean (fun i t => h i t - a i) σ.1 -
      S.centreProjection (fun τ => S.additiveMean (fun i t => h i t - a i) τ.1) σ) σ) ^ 2) ≤ _ at hh
  rw [he] at hh
  exact hh

end ConditionalStar
end
end CI2ZF.Appendix.Girth
