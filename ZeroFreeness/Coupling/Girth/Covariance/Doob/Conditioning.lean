import ZeroFreeness.Coupling.Girth.Covariance.Response.Score
import ZeroFreeness.Coupling.Edge.Finite.Conditioning

/-! Exact finite conditioning and the variance decomposition behind sequential revelation. -/
namespace ZeroFreeness.Appendix.Girth.Doob
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω A C : Type*} [Fintype Ω] [Fintype A] [Fintype C]

abbrev observed (μ : FinDist Ω) (k : Ω → A) : FinDist A := Edge.FiniteLaw.marginal μ k
abbrev given (μ : FinDist Ω) (k : Ω → A) (a : A) : FinDist Ω :=
  Edge.FiniteLaw.conditional μ (fun ω => k ω = a)

theorem observed_mul_given (μ : FinDist Ω) (k : Ω → A) (a : A) (ω : Ω) :
    (observed μ k).w a * (given μ k a).w ω = if k ω = a then μ.w ω else 0 :=
  Edge.FiniteLaw.mass_mul_conditional μ _ ω

/-- This family form keeps track of observables that depend on the revealed colour. -/
theorem family_expectation (μ : FinDist Ω) (k : Ω → A) (f : A → Ω → ℝ) :
    expectReal μ (fun ω => f (k ω) ω) =
      expectReal (observed μ k) (fun a => expectReal (given μ k a) (f a)) := by
  unfold expectReal
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp_rw [observed_mul_given]
  simp [ite_mul, eq_comm]

theorem expectation_disintegration (μ : FinDist Ω) (k : Ω → A) (f : Ω → ℝ) :
    expectReal μ f = expectReal (observed μ k) (fun a => expectReal (given μ k a) f) :=
  family_expectation μ k (fun _ => f)

theorem variance_moment (μ : FinDist Ω) (f : Ω → ℝ) :
    variance μ f = expectReal μ (fun ω => f ω ^ 2) - expectReal μ f ^ 2 := by
  rw [← covariance_self, covariance_eq_moment]
  simp only [pow_two]

/-- The exact conditional variance identity, retaining the possibly dependent base law. -/
theorem family_variance (μ : FinDist Ω) (k : Ω → A) (f : A → Ω → ℝ) :
    variance μ (fun ω => f (k ω) ω) =
      expectReal (observed μ k) (fun a => variance (given μ k a) (f a)) +
      variance (observed μ k) (fun a => expectReal (given μ k a) (f a)) := by
  simp_rw [variance_moment]
  rw [family_expectation μ k f, family_expectation μ k (fun a ω => f a ω ^ 2)]
  rw [expectReal_sub]
  ring

def observedMean (μ : FinDist Ω) (k : Ω → A) (f : Ω → ℝ) (a : A) : ℝ :=
  expectReal (given μ k a) f

theorem observedMean_mean (μ : FinDist Ω) (k : Ω → A) (f : Ω → ℝ) :
    expectReal (observed μ k) (observedMean μ k f) = expectReal μ f :=
  (expectation_disintegration μ k f).symm

variable [DecidableEq C]

theorem observed_eq_coordinateMarginal (μ : FinDist Ω) (k : Ω → C) :
    observed μ k = coordinateMarginal μ k := by
  apply FinDist.ext
  funext c
  unfold observed Edge.FiniteLaw.marginal Edge.FiniteLaw.eventMass coordinateMarginal mapLaw FinDist.bind FinDist.pure
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hc : k ω = c
  · simp [hc]
  · have hc' : c ≠ k ω := Ne.symm hc
    simp [hc, hc']

theorem observedMean_eq_coordinateMean (μ : FinDist Ω) (k : Ω → C) (f : Ω → ℝ) (c : C)
    (hc : 0 < (observed μ k).w c) :
    observedMean μ k f c = coordinateMean μ k f c := by
  unfold observedMean expectReal
  simp_rw [given, Edge.FiniteLaw.conditional_w μ (fun ω => k ω = c) hc]
  unfold coordinateMean expectReal
  rw [← observed_eq_coordinateMarginal]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : k ω = c <;> simp [colourIndicator, h]

/-- The transformed-score comparison is also valid at zero marginal atoms. -/
theorem observed_variance_le_score (s : ℝ) (μ : FinDist Ω) (k : Ω → C) (f : Ω → ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hden : ∀ c, 1 - s * (coordinateMarginal μ k).w c ≠ 0) :
    variance (observed μ k) (observedMean μ k f) ≤ ∑ c, responseScore s μ k f c ^ 2 := by
  unfold variance expectReal
  change (∑ c, (observed μ k).w c *
    (observedMean μ k f c - expectReal (observed μ k) (observedMean μ k f)) ^ 2) ≤ _
  rw [observedMean_mean]
  apply Finset.sum_le_sum
  intro c _
  by_cases hc : 0 < (observed μ k).w c
  · rw [observedMean_eq_coordinateMean μ k f c hc, observed_eq_coordinateMarginal]
    have hp : 0 < (coordinateMarginal μ k).w c := by simpa only [observed_eq_coordinateMarginal] using hc
    rw [responseScore_eq s μ k f c hp, mul_pow, scoreDiagonal, div_pow, Real.sq_sqrt hp.le]
    have hp1 := probability_atom_le_one (coordinateMarginal μ k) c
    have hd0 : 0 ≤ 1 - s * (coordinateMarginal μ k).w c := by nlinarith
    have hd1 : 1 - s * (coordinateMarginal μ k).w c ≤ 1 := by nlinarith
    have hd : (1 - s * (coordinateMarginal μ k).w c) ^ 2 ≤ 1 := by nlinarith
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply (le_div_iff₀ (sq_pos_of_ne_zero (hden c))).mpr
    exact mul_le_of_le_one_right hp.le hd
  · have hz : (observed μ k).w c = 0 := le_antisymm (le_of_not_gt hc) ((observed μ k).nonneg c)
    rw [hz, zero_mul]
    exact sq_nonneg _

end
end ZeroFreeness.Appendix.Girth.Doob
