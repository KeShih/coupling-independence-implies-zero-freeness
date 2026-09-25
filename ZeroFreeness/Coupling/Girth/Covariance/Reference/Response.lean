import ZeroFreeness.Coupling.Girth.Covariance.Reference.Marginal
import ZeroFreeness.Coupling.Girth.Covariance.Response.BlockBound

/-! Substitution of the reference occupancy estimate into the actual
response matrix, retaining the single exponential insertion loss. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
set_option linter.unusedSectionVars false
variable {C U : Type*} [Fintype C] [Fintype U] [DecidableEq C] [Nonempty C]

theorem exists_occupancy_max (p : FinDist C) (r : U → FinDist C) :
    ∃ c, ∀ b, p.w b * (∑ u, (r u).w b) ≤ p.w c * (∑ u, (r u).w c) := by
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ
    (fun c => p.w c * ∑ u, (r u).w c) Finset.univ_nonempty
  exact ⟨c, fun b => hc b (Finset.mem_univ b)⟩

theorem responseCoefficient_le {s d Λ K B : ℝ}
    (hs : 0 ≤ s) (hd : 0 ≤ d) (hΛ : 0 ≤ Λ) (hK : 0 ≤ K) (hB : B < 1)
    (hocc : s ^ 2 * d * Λ ≤ K) :
    s * Real.sqrt (d * Λ) / (1 - B) ≤ Real.sqrt K / (1 - B) := by
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hB).le
  apply (sq_le_sq₀ (mul_nonneg hs (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hd hΛ), Real.sq_sqrt hK]
  nlinarith only [hocc]

theorem responseBlock_both_of_occupancy (s : ℝ) (p : FinDist C) (r : U → FinDist C)
    (h : U → C → ℝ) {B K H₂ Hinf : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hB0 : 0 ≤ B) (hB : B < 1) (hp : ∀ c, p.w c ≤ B) (hK : 0 ≤ K)
    (hocc : ∀ c, s ^ 2 * (Fintype.card U : ℝ) * p.w c * (∑ u, (r u).w c) ≤ K)
    (hH₂ : 0 ≤ H₂) (hHinf : 0 ≤ Hinf)
    (hh₂ : ∀ u, colourNorm (h u) ≤ H₂) (hhinf : ∀ u c, |h u c| ≤ Hinf) :
    colourNorm (responseBlockAction s p r h) ≤ Real.sqrt K / (1 - B) * H₂ ∧
    ∀ c, |responseBlockAction s p r h c| ≤
      Real.sqrt K / (1 - B) * (Hinf + Real.sqrt B * H₂) := by
  obtain ⟨b, hb⟩ := exists_occupancy_max p r
  let Λ := p.w b * (∑ u, (r u).w b)
  have hΛ : 0 ≤ Λ := mul_nonneg (p.nonneg b) (Finset.sum_nonneg fun u _ => (r u).nonneg b)
  have hco := responseCoefficient_le hs0 (Nat.cast_nonneg (Fintype.card U)) hΛ hK hB
    (show s ^ 2 * (Fintype.card U : ℝ) * Λ ≤ K by simpa only [Λ, mul_assoc] using hocc b)
  constructor
  · exact (responseBlock_norm s p r h hs0 hs1 hB hp hΛ hb hH₂ hh₂).trans
      (mul_le_mul_of_nonneg_right hco hH₂)
  · intro c
    exact (responseBlock_infty s p r h hs0 hs1 hB0 hB hp hΛ hb hH₂ hHinf hh₂ hhinf c).trans
      (mul_le_mul_of_nonneg_right hco (add_nonneg hHinf (mul_nonneg (Real.sqrt_nonneg _) hH₂)))

theorem referenceResponseCoefficient_eq {E B t : ℝ} (_ht : 0 ≤ t) :
    referenceResponseCoefficient E B t =
      Real.sqrt (Real.exp (2 * E) * (t * Real.exp (t * logChord B - 1))) / (1 - B) := by
  unfold referenceResponseCoefficient
  rw [Real.sqrt_mul (Real.exp_pos _).le]
  have he : Real.sqrt (Real.exp (2 * E)) = Real.exp E := by
    have he2 : Real.exp (2 * E) = Real.exp E ^ 2 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he2, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos E)]
  rw [he]

/-- Both displayed contraction bounds, for actual root and cavity laws.
The only insertion input is the already quantified density comparison. -/
theorem reference_response_both (a : C → ℝ) (r : U → FinDist C) (p : FinDist C)
    (h : U → C → ℝ) {s A B t E H₂ Hinf : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA0 : 0 < A) (hA : A ≤ ∑ c, a c)
    (hB0 : 0 < B) (hB1 : B < 1) (hr : ∀ i c, s * (r i).w c ≤ B)
    (ht : (Fintype.card U : ℝ) / A ≤ t) (hroot : ∀ c, p.w c ≤ B)
    (hp : ∀ c, p.w c ≤ Real.exp (2 * E) * messageMarginal a (fun i c => s * (r i).w c) c)
    (hH₂ : 0 ≤ H₂) (hHinf : 0 ≤ Hinf)
    (hh₂ : ∀ u, colourNorm (h u) ≤ H₂) (hhinf : ∀ u c, |h u c| ≤ Hinf) :
    colourNorm (responseBlockAction s p r h) ≤ referenceResponseCoefficient E B t * H₂ ∧
    ∀ c, |responseBlockAction s p r h c| ≤
      referenceResponseCoefficient E B t * (Hinf + Real.sqrt B * H₂) := by
  have ht0 : 0 ≤ t := (div_nonneg (Nat.cast_nonneg _) hA0.le).trans ht
  rw [referenceResponseCoefficient_eq ht0]
  apply responseBlock_both_of_occupancy s p r h hs0 hs1 hB0.le hB1 hroot
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg ht0 (Real.exp_pos _).le))
    (fun c => tilted_reference_occupancy a r p hs0 hs1 ha hA0 hA hB0 hB1 hr ht hp c)
    hH₂ hHinf hh₂ hhinf

end
end ZeroFreeness.Appendix.Girth
