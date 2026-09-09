import CI2ZF.Appendix.Girth.Covariance.Response.Score

/-! Exact response recursion obtained directly from finite expectations.
The formula includes the complete remaining source, including exterior
terms, before any estimate or induction is applied. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω U C : Type*} [Fintype Ω] [Fintype U] [Fintype C] [DecidableEq C]

namespace RootInsertion
variable (μ : FinDist Ω) (k : U → Ω → C) (s : ℝ)

def likelihood (c : C) (ω : Ω) : ℝ := ∏ u, (1 - s * colourIndicator c (k u ω))

def normalizer (c : C) : ℝ := expectReal μ (likelihood k s c)

def alpha (u : U) (c : C) : ℝ := s / (1 - s * (coordinateMarginal μ (k u)).w c)

def residual (c : C) (ω : Ω) : ℝ :=
  likelihood k s c ω / normalizer μ k s c - 1 +
    ∑ u, alpha μ k s u c * (colourIndicator c (k u ω) - (coordinateMarginal μ (k u)).w c)

/-- Mean of the full remaining source under the genuine insertion
reweighting. It will be identified with the graph child law. -/
def insertionMean (f : Ω → ℝ) (c : C) : ℝ :=
  expectReal μ (fun ω => f ω * likelihood k s c ω) / normalizer μ k s c

def defect (f : Ω → ℝ) (c : C) : ℝ := covariance μ f (residual μ k s c)

theorem residual_covariance (f : Ω → ℝ) (c : C) :
    defect μ k s f c = covariance μ f (likelihood k s c) / normalizer μ k s c +
      ∑ u, alpha μ k s u c * covariance μ f (fun ω => colourIndicator c (k u ω)) := by
  change covariance μ f (fun ω => likelihood k s c ω / normalizer μ k s c - 1 +
    ∑ u, alpha μ k s u c * (colourIndicator c (k u ω) - (coordinateMarginal μ (k u)).w c)) = _
  rw [covariance_add_right, covariance_sub_right, covariance_const_right,
    sub_zero, covariance_sum_right]
  have hd : (fun ω => likelihood k s c ω / normalizer μ k s c) =
      fun ω => (normalizer μ k s c)⁻¹ * likelihood k s c ω := by funext ω; ring
  rw [hd, covariance_const_mul_right]
  simp_rw [covariance_const_mul_right, covariance_sub_right, covariance_const_right, sub_zero]
  ring

theorem insertionMean_expansion (f : Ω → ℝ) (c : C) (hT : normalizer μ k s c ≠ 0) :
    insertionMean μ k s f c = expectReal μ f + defect μ k s f c -
      ∑ u, alpha μ k s u c * covariance μ f (fun ω => colourIndicator c (k u ω)) := by
  rw [residual_covariance, covariance_eq_moment]
  change expectReal μ (fun ω => f ω * likelihood k s c ω) / normalizer μ k s c =
    expectReal μ f + ((expectReal μ (fun ω => f ω * likelihood k s c ω) -
      expectReal μ f * normalizer μ k s c) / normalizer μ k s c + _) - _
  field_simp
  ring

theorem alpha_covariance_score (f : Ω → ℝ) (u : U) (c : C)
    (hc : 0 < (coordinateMarginal μ (k u)).w c)
    (hd : 1 - s * (coordinateMarginal μ (k u)).w c ≠ 0) :
    alpha μ k s u c * covariance μ f (fun ω => colourIndicator c (k u ω)) =
      s * Real.sqrt ((coordinateMarginal μ (k u)).w c) * responseScore s μ (k u) f c := by
  unfold alpha responseScore
  field_simp [(Real.sqrt_pos.mpr hc).ne', hd]

/-- The exact colour-coordinate recursion before projection at the root.
Taking two colour differences here never divides by a root marginal. -/
theorem insertionMean_score (f : Ω → ℝ) (c : C) (hT : normalizer μ k s c ≠ 0)
    (hp : ∀ u, 0 < (coordinateMarginal μ (k u)).w c)
    (hd : ∀ u, 1 - s * (coordinateMarginal μ (k u)).w c ≠ 0) :
    insertionMean μ k s f c = expectReal μ f + defect μ k s f c -
      s * ∑ u, Real.sqrt ((coordinateMarginal μ (k u)).w c) * responseScore s μ (k u) f c := by
  rw [insertionMean_expansion μ k s f c hT]
  simp_rw [alpha_covariance_score μ k s f _ c (hp _) (hd _)]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  ring

end RootInsertion

def responseBlockAction {U : Type*} [Fintype U] (s : ℝ) (p : FinDist C)
    (r : U → FinDist C) (h : U → C → ℝ) (c : C) : ℝ :=
  -s * scoreDiagonal s p c *
    ((∑ u, Real.sqrt ((r u).w c) * h u c) -
      expectReal p (fun d => ∑ u, Real.sqrt ((r u).w d) * h u d))

/-- The actual finite response identity, with the insertion covariance
retained exactly. The only hypotheses concern denominators of normalized
finite laws. -/
theorem response_recursion (μ : FinDist Ω) (k : U → Ω → C) (s : ℝ)
    (p : FinDist C) (fv : C → ℝ) (f : Ω → ℝ)
    (hT : ∀ c, RootInsertion.normalizer μ k s c ≠ 0)
    (hp : ∀ u c, 0 < (coordinateMarginal μ (k u)).w c)
    (hd : ∀ u c, 1 - s * (coordinateMarginal μ (k u)).w c ≠ 0) :
    scoreSource s p (fun c => fv c + RootInsertion.insertionMean μ k s f c) =
      fun c => responseBlockAction s p (fun u => coordinateMarginal μ (k u))
        (fun u => responseScore s μ (k u) f) c +
        scoreSource s p (fun c => fv c + RootInsertion.defect μ k s f c) c := by
  funext c
  have hm (d : C) := RootInsertion.insertionMean_score μ k s f d (hT d)
    (fun u => hp u d) (fun u => hd u d)
  simp only [scoreSource, responseBlockAction, hm, expectReal_add, expectReal_sub,
    expectReal_const, expectReal_const_mul]
  ring

end
end CI2ZF.Appendix.Girth
