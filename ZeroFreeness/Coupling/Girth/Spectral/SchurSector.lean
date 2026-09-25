import ZeroFreeness.Coupling.Girth.Spectral.SchurFull

/-! The degree-sector scalar estimates used to instantiate StarData for
literal unequal incidence weights. -/
namespace ZeroFreeness.Appendix.Girth.Schur
open scoped BigOperators
noncomputable section

theorem higher_sector_bounds {n : ℕ} (hn : 2 ≤ n) {w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 2 * n) :
    (2 : ℝ) ≤ (n : ℝ) * (n - 1) ∧
    w ^ 2 ≤ 8 * (n : ℝ) * (n - 1) ∧
    (w - 1) ^ 2 ≤ (9 / 2 : ℝ) * n * (n - 1) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg (w - 2 * n), mul_nonneg hw0 (sub_nonneg.mpr hw)]
  · have hupper : (w - 1) ^ 2 ≤ (2 * (n : ℝ) - 1) ^ 2 := by
      have hprod : 0 ≤ (2 * (n : ℝ) - w) * (2 * (n : ℝ) + w - 2) :=
        mul_nonneg (sub_nonneg.mpr hw) (by linarith)
      nlinarith
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (show 0 ≤ (n : ℝ) + 1 by linarith)]

theorem incidence_sector_bounds {I : Type*} [DecidableEq I] (J : Finset I) (β : I → ℝ)
    (hβ : ∀ i ∈ J, β i ∈ Set.Ioo (0 : ℝ) 2) (hJ : 2 ≤ J.card) :
    (2 : ℝ) ≤ (J.card : ℝ) * (J.card - 1) ∧
    (∑ i ∈ J, β i) ^ 2 ≤ 8 * (J.card : ℝ) * (J.card - 1) ∧
    ((∑ i ∈ J, β i) - 1) ^ 2 ≤ (9 / 2 : ℝ) * J.card * (J.card - 1) := by
  apply higher_sector_bounds hJ
  · exact Finset.sum_nonneg fun i hi => (hβ i hi).1.le
  · have h := Finset.sum_le_sum (s := J) (fun i hi => (hβ i hi).2.le)
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using h

end
end ZeroFreeness.Appendix.Girth.Schur
