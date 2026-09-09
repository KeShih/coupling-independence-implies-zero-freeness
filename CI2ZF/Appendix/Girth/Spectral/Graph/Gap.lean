import CI2ZF.Appendix.Girth.Spectral.Graph.Decomposition
import CI2ZF.Appendix.Girth.Spectral.SchurEstimate

/-! Summing local conditional-star inequalities with the actual directed
incidence weights yields the uniform rate-one Glauber spectral gap. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators InnerProductSpace
open Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace GraphProjections
variable {G : SimpleGraph V} (P : GraphProjections G E)

/-- The incidence correction is zero for isolated vertices, without a
separate choice of a division convention. -/
def correction (v : V) (f : E) : ℝ :=
  ∑ u, if G.Adj v u then P.beta v u ^ 2 / (G.degree v : ℝ) * energy (P.Q u) f else 0

theorem correction_sum_le (f : E) : (∑ v, P.correction v f) ≤ energy P.laplacian f := by
  unfold correction
  rw [Finset.sum_comm, P.laplacian_sum_energy]
  apply Finset.sum_le_sum
  intro u _
  have hcoef : (∑ v, if G.Adj v u then P.beta v u ^ 2 / (G.degree v : ℝ) else 0) ≤ 1 := by
    have h := sum_incoming_incidence_le_one G u
    simpa only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter,
      G.adj_comm u, beta] using h
  have hfactor : (∑ v, if G.Adj v u then P.beta v u ^ 2 / (G.degree v : ℝ) * energy (P.Q u) f else 0) =
      (∑ v, if G.Adj v u then P.beta v u ^ 2 / (G.degree v : ℝ) else 0) * energy (P.Q u) f := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v _
    split_ifs <;> simp
  rw [hfactor]
  have hpos : 0 ≤ energy (P.Q u) f := by rw [energy, (P.projection u).inner_self]; exact sq_nonneg _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef hpos

/-- This is the single local inequality that the internally proved
conditional-star theorem supplies after disintegration. It concerns the
actual supported operators, with no graph gap or mixing assumption. -/
def LocalStarBound (θ : ℝ) : Prop := ∀ v f,
  energy (P.Q v) f / 2 - θ / 2 * P.correction v f ≤ energy (P.starOperator v) f

theorem global_square_gap {θ : ℝ} (hθ : 0 ≤ θ) (hg : 5 ≤ G.egirth)
    (hlocal : P.LocalStarBound θ) (f : E) :
    (1 - θ) / 2 * energy P.laplacian f ≤ energy (P.laplacian.comp P.laplacian) f := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun v _ => hlocal v f)
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← P.laplacian_sum_energy] at hs
  have hc := mul_le_mul_of_nonneg_left (P.correction_sum_le f) (div_nonneg hθ (by norm_num : (0 : ℝ) ≤ 2))
  have hglobal := P.global_decomposition hg f
  have hdistant := P.distant_energy_nonneg f
  rw [P.square_laplacian_energy]
  nlinarith

def spectralGap (δ : ℝ) : ℝ := δ / (4 * (2 + δ))

theorem spectralGap_pos {δ : ℝ} (hδ : 0 < δ) : 0 < spectralGap δ := by
  unfold spectralGap
  positivity

theorem spectralGap_eq_theta {δ : ℝ} (hδ : 0 < δ) :
    spectralGap δ = (1 - StarData.theta δ) / 2 := by
  unfold spectralGap StarData.theta
  have hden : 1 + δ / 2 ≠ 0 := by positivity
  have hden' : 2 + δ ≠ 0 := by positivity
  field_simp
  ring

/-- The exact appendix constant δ/[4(2+δ)] for the unnormalized,
rate-one Glauber generator on every finite graph of girth at least five. -/
theorem girth_five_square_gap {δ : ℝ} (hδ : 0 < δ) (hg : 5 ≤ G.egirth)
    (hlocal : P.LocalStarBound (StarData.theta δ)) (f : E) :
    spectralGap δ * energy P.laplacian f ≤ energy (P.laplacian.comp P.laplacian) f := by
  rw [spectralGap_eq_theta hδ]
  exact P.global_square_gap (StarData.theta_mem hδ).1.le hg hlocal f

end GraphProjections
end
end CI2ZF.Appendix.Girth
