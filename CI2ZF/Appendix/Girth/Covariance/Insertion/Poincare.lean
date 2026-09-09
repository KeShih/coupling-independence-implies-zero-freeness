import CI2ZF.Appendix.Girth.Covariance.Insertion.Edge

/-! The actual conditional-variance Dirichlet form and palette atom
bounds used by every residual insertion instance. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [Nonempty C]

namespace GraphHeatBath
variable (I : PinningData V C) (x : ℝ) (hx : 0 < x)
  (hlocal : ∀ σ v, 0 < sitePartition I x σ v) (hZ : 0 < I.partition x)

def localVariance (v : V) (f : (V → C) → ℝ) (σ : V → C) : ℝ :=
  variance (siteLaw I x hx.le hlocal σ v) (fun c => f (Function.update σ v c))

theorem projection_stationary (v : V) (f : (V → C) → ℝ) :
    expectReal (I.gibbs x hx.le hZ) (projection I x hx.le hlocal v f) =
      expectReal (I.gibbs x hx.le hZ) f := by
  have h := projection_selfAdjoint I x hx.le hlocal hZ v f (fun _ => 1)
  rw [projection_const] at h
  simpa only [mul_one] using h

theorem localVariance_projection (v : V) (f : (V → C) → ℝ) (σ : V → C) :
    localVariance I x hx hlocal v f σ =
      projection I x hx.le hlocal v (fun τ => (f τ - projection I x hx.le hlocal v f τ) ^ 2) σ := by
  change expectReal (siteLaw I x hx.le hlocal σ v)
    (fun c => (f (Function.update σ v c) - projection I x hx.le hlocal v f σ) ^ 2) = _
  unfold projection
  apply congrArg (expectReal _)
  funext c
  congr 2
  exact (projection_update I x hx hlocal v f σ c).symm

theorem expect_localVariance (v : V) (f : (V → C) → ℝ) :
    expectReal (I.gibbs x hx.le hZ) (localVariance I x hx hlocal v f) =
      expectReal (I.gibbs x hx.le hZ) (fun σ => (f σ - projection I x hx.le hlocal v f σ) ^ 2) := by
  change expectReal (I.gibbs x hx.le hZ) (fun σ => localVariance I x hx hlocal v f σ) = _
  simp_rw [localVariance_projection]
  exact projection_stationary I x hx hlocal hZ v _

theorem dirichlet_eq_localVariances (f : (V → C) → ℝ) :
    dirichlet I x hx hlocal hZ f = ∑ v, expectReal (I.gibbs x hx.le hZ) (localVariance I x hx hlocal v f) := by
  unfold dirichlet
  apply Finset.sum_congr rfl
  intro v _
  exact (expect_localVariance I x hx hlocal hZ v f).symm

theorem positive_poincare_localVariance {δ : ℝ} (hδ : 0 < δ) (hg : 5 ≤ I.graph.egirth)
    (hstar : (system I x hx.le hlocal hZ).LocalStarBound (Schur.StarData.theta δ))
    (f : (V → C) → ℝ) :
    GraphProjections.spectralGap δ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ) (localVariance I x hx hlocal v f) := by
  rw [← dirichlet_eq_localVariances]
  exact positive_poincare I x hx hlocal hZ hδ hg hstar f

theorem siteLaw_atom_le (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ) {m : ℝ}
    (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ) (σ : V → C) (v : V) (c : C) :
    (siteLaw I x hx.le hlocal σ v).w c ≤ 1 / m := by
  have hl := sitePartition_lower I hx.le σ v
  have hv : (I.constraintDegree v : ℝ) ≤ Δ := by exact_mod_cast hd v
  have hn : (0 : ℝ) ≤ I.constraintDegree v := Nat.cast_nonneg _
  have hmZ : m ≤ sitePartition I x σ v := by nlinarith
  have hnum : siteWeight I x σ v c ≤ 1 := pow_le_one₀ hx.le hx1
  change siteWeight I x σ v c / sitePartition I x σ v ≤ 1 / m
  apply (div_le_div_iff₀ (hlocal σ v) hm).mpr
  nlinarith

end GraphHeatBath

namespace InsertionBalance
variable {Ω U O : Type*} [Fintype Ω] [Fintype U] [Fintype O] [DecidableEq U]
  (μ : FinDist (Ω × ((U → C) × O)))

theorem expect_shellLaw (f : Ω → ℝ) :
    expectReal (shellLaw μ) f = expectReal μ (fun z => f z.1) := by
  simp only [expectReal, shellLaw, Fintype.sum_prod_type, Finset.sum_mul]

theorem variance_shellLaw (f : Ω → ℝ) :
    variance (shellLaw μ) f = variance μ (fun z => f z.1) := by
  unfold variance
  rw [expect_shellLaw, expect_shellLaw]

end InsertionBalance
end
end CI2ZF.Appendix.Girth
