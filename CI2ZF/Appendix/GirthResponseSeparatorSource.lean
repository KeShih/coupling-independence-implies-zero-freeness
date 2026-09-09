import CI2ZF.Appendix.GirthResponseInstance
import CI2ZF.Appendix.GirthInsertionActualEstimates
import CI2ZF.Appendix.GirthInsertionFullSource
import CI2ZF.Appendix.GirthDoobKernel

/-! Full additive sources in the actual two-layer coordinates. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq S] [DecidableEq O] [DecidableEq C] [Nonempty C]

namespace WeightedSource
variable {I : PinningData (Vertex U S O) C} {χ : ℝ} (F : WeightedSource I χ)

def firstTerms (u : U) : C → ℝ := F.term (Sum.inl u)
def shellTerms (ξ : S → C) : ℝ := ∑ w, F.term (Sum.inr (Sum.inl w)) (ξ w)
def exteriorTerms (o : O → C) : ℝ := ∑ w, F.term (Sum.inr (Sum.inr w)) (o w)
def splitSource : ((S → C) × ((U → C) × (O → C))) → ℝ :=
  InsertionModel.additiveSource F.firstTerms F.shellTerms F.exteriorTerms

theorem observable_join (α : U → C) (ξ : S → C) (o : O → C) :
    F.observable (join α ξ o) = F.splitSource (ξ,(α,o)) := by
  simp only [observable, splitSource, InsertionModel.additiveSource, firstTerms, shellTerms,
    exteriorTerms, Fintype.sum_sum_type, join, Sum.elim_inl, Sum.elim_inr]
  ring

theorem splitSource_coloringEquiv (σ : Vertex U S O → C) :
    F.splitSource (coloringEquiv σ) = F.observable σ := by
  rw [← F.observable_join]
  change F.observable (coloringEquiv.symm (coloringEquiv σ)) = F.observable σ
  rw [Equiv.symm_apply_apply]

def shellSource (M : InsertionModel (S → C) U (O → C) C) : (S → C) → ℝ :=
  M.shellSource F.firstTerms F.shellTerms F.exteriorTerms

def localDefect (M : InsertionModel (S → C) U (O → C) C) (s : ℝ) (c : C) : ℝ :=
  expectReal M.shell (fun ξ => covariance (CI2ZF.productLaw (M.cavity ξ))
    (fun α => ∑ u, F.firstTerms u (α u)) (M.residual s c))

theorem full_defect_decomposition (M : InsertionModel (S → C) U (O → C) C) (s : ℝ) (c : C) :
    covariance M.law F.splitSource (fun σ => M.residual s c σ.2.1) =
      F.localDefect M s c + covariance M.shell (F.shellSource M) (M.G s c) :=
  M.full_source_decomposition s c F.firstTerms F.shellTerms F.exteriorTerms

theorem localDefect_bound (M : InsertionModel (S → C) U (O → C) C) (s : ℝ) (p : CovarianceScale)
    (he : M.CovarianceEstimates s p) (hdeg : (Fintype.card U : ℝ) ≤ p.Δ)
    {A : ℝ} (hA : 0 ≤ A) (hχ : 0 ≤ χ)
    (hfirst : ∀ u, F.weight (Sum.inl u) ≤ χ * A) (c : C) :
    |F.localDefect M s c| ≤ p.ell * χ * A := by
  have h := M.local_source_bound s F.firstTerms c (mul_nonneg hχ hA) p.B_pos.le p.b_nonneg
    (fun u t => (F.term_bound _ t).trans (hfirst u))
    (fun ξ u => he.atom u c ξ) (fun u => he.beta_second u c)
  apply h.trans
  calc
    _ ≤ 2 * p.Δ * (χ * A) * p.B * p.b := by
      have hb := p.b_nonneg
      have hB := p.B_pos.le
      gcongr
    _ = _ := by unfold CovarianceScale.ell; ring

theorem localSource_bound (M : InsertionModel (S → C) U (O → C) C) (s : ℝ) (p : CovarianceScale)
    (he : M.CovarianceEstimates s p) (hdeg : (Fintype.card U : ℝ) ≤ p.Δ)
    {A : ℝ} (hA : 0 ≤ A) (hχ : 0 ≤ χ)
    (hfirst : ∀ u, F.weight (Sum.inl u) ≤ χ * A)
    (fv : C → ℝ) (hfv : ∀ c, |fv c| ≤ A) (c : C) :
    |fv c + F.localDefect M s c| ≤ (1 + p.ell * χ) * A := by
  calc
    _ ≤ |fv c| + |F.localDefect M s c| := abs_add_le _ _
    _ ≤ A + p.ell * χ * A := add_le_add (hfv c) (F.localDefect_bound M s p he hdeg hA hχ hfirst c)
    _ = _ := by ring

end WeightedSource
end
end CI2ZF.Appendix.Girth
