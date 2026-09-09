import CI2ZF.Coupling.Girth.Spectral.SupportedSpace
import CI2ZF.Coupling.Girth.Covariance.Insertion.Law

namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

def finiteL2 (μ : FinDist Ω) (f : Ω → ℝ) : ℝ := ‖supportedEmbed μ f‖

theorem finiteL2_nonneg (μ : FinDist Ω) (f : Ω → ℝ) : 0 ≤ finiteL2 μ f := norm_nonneg _

theorem finiteL2_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    finiteL2 μ f ^ 2 = expectReal μ (fun ω => f ω ^ 2) := supportedEmbed_norm_sq μ f

theorem finiteL2_add_le (μ : FinDist Ω) (f g : Ω → ℝ) :
    finiteL2 μ (fun ω => f ω + g ω) ≤ finiteL2 μ f + finiteL2 μ g := by
  change ‖supportedEmbed μ (f + g)‖ ≤ _
  rw [map_add]
  exact norm_add_le _ _

theorem finiteL2_const (μ : FinDist Ω) (a : ℝ) : finiteL2 μ (fun _ => a) = |a| := by
  have hh := finiteL2_sq μ (fun _ => a)
  rw [expectReal_const] at hh
  nlinarith [finiteL2_nonneg μ (fun _ => a), abs_nonneg a, sq_abs a]

theorem finiteL2_le_of_sq (μ : FinDist Ω) (f : Ω → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hh : expectReal μ (fun ω => f ω ^ 2) ≤ a ^ 2) : finiteL2 μ f ≤ a := by
  rw [← finiteL2_sq] at hh
  nlinarith [finiteL2_nonneg μ f]

theorem finiteL2_pointwise (μ : FinDist Ω) (f g : Ω → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hh : ∀ ω, |f ω| ≤ a * |g ω|) :
    finiteL2 μ f ≤ a * finiteL2 μ g := by
  apply finiteL2_le_of_sq μ f (mul_nonneg ha (finiteL2_nonneg μ g))
  calc
    _ ≤ expectReal μ (fun ω => a ^ 2 * g ω ^ 2) := expectReal_mono μ fun ω => by
      have hs := pow_le_pow_left₀ (abs_nonneg (f ω)) (hh ω) 2
      simpa only [mul_pow, sq_abs] using hs
    _ = _ := by rw [expectReal_const_mul, ← finiteL2_sq]; ring

theorem finiteL2_le_const (μ : FinDist Ω) (f : Ω → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hh : ∀ ω, |f ω| ≤ a) : finiteL2 μ f ≤ a := by
  simpa only [finiteL2_const, abs_one, mul_one] using
    finiteL2_pointwise μ f (fun _ => 1) ha (by simpa only [abs_one, mul_one] using hh)

theorem finiteL2_centered (μ : FinDist Ω) (f : Ω → ℝ) :
    finiteL2 μ (fun ω => f ω - expectReal μ f) = Real.sqrt (variance μ f) := by
  have hh := finiteL2_sq μ (fun ω => f ω - expectReal μ f)
  change finiteL2 μ (fun ω => f ω - expectReal μ f) ^ 2 = variance μ f at hh
  nlinarith [finiteL2_nonneg μ (fun ω => f ω - expectReal μ f),
    Real.sqrt_nonneg (variance μ f), Real.sq_sqrt (variance_nonneg μ f)]

theorem sqrt_variance_le_error (μ : FinDist Ω) (f : Ω → ℝ) (a : ℝ) :
    Real.sqrt (variance μ f) ≤ finiteL2 μ (fun ω => f ω - a) := by
  have hh := variance_le_error μ f a
  rw [← finiteL2_sq] at hh
  nlinarith [finiteL2_nonneg μ (fun ω => f ω - a), Real.sqrt_nonneg (variance μ f),
    Real.sq_sqrt (variance_nonneg μ f)]

theorem sqrt_variance_add_error (μ : FinDist Ω) (f g : Ω → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hh : ∀ ω, |f ω - g ω| ≤ a) :
    Real.sqrt (variance μ f) ≤ Real.sqrt (variance μ g) + a := by
  calc
    _ ≤ finiteL2 μ (fun ω => f ω - expectReal μ g) := sqrt_variance_le_error μ f _
    _ = finiteL2 μ (fun ω => (g ω - expectReal μ g) + (f ω - g ω)) := by congr 1; funext ω; ring
    _ ≤ finiteL2 μ (fun ω => g ω - expectReal μ g) + finiteL2 μ (fun ω => f ω - g ω) := finiteL2_add_le μ _ _
    _ ≤ _ := by rw [finiteL2_centered]; exact add_le_add le_rfl (finiteL2_le_const μ _ ha hh)

end
end CI2ZF.Appendix.Girth
