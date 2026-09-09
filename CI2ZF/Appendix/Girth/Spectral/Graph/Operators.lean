import CI2ZF.Appendix.Girth.Spectral.SchurLinear
import CI2ZF.Appendix.Girth.Geometry

/-! Rate-one Glauber operator algebra on a finite graph. The maps here
are intended to be the actual supported-L² heat-bath complements; the
probability construction supplies precisely the projection and local
commutation fields. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators InnerProductSpace
open Schur
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure GraphProjections (G : SimpleGraph V) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  Q : V → E →ₗ[ℝ] E
  projection : ∀ v, Schur.Projection (Q v)
  nonadjacent_commute : ∀ v u, ¬ G.Adj v u → Commute (Q v) (Q u)

namespace GraphProjections
variable {G : SimpleGraph V} (P : GraphProjections G E)

def laplacian : E →ₗ[ℝ] E := ∑ v, P.Q v

def beta (_P : GraphProjections G E) (v u : V) : ℝ := incidenceWeight (G.degree v) (G.degree u)

def neighbourSum (v : V) : E →ₗ[ℝ] E := ∑ u, if G.Adj v u then P.Q u else 0

def incidenceSum (v : V) : E →ₗ[ℝ] E := ∑ u, if G.Adj v u then P.beta v u • P.Q u else 0

def starOperator (v : V) : E →ₗ[ℝ] E :=
  P.Q v + (1 / 2 : ℝ) • ((P.Q v).comp (P.incidenceSum v) + (P.incidenceSum v).comp (P.Q v)) +
    (P.neighbourSum v).comp (P.neighbourSum v) - P.neighbourSum v

theorem laplacian_symmetric : Schur.Symmetric P.laplacian := by
  intro f g
  simp only [laplacian, LinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun v _ => (P.projection v).symmetric f g

theorem laplacian_energy (f : E) : energy P.laplacian f = ∑ v, ‖P.Q v f‖ ^ 2 := by
  simp only [energy, laplacian, LinearMap.sum_apply, inner_sum]
  exact Finset.sum_congr rfl fun v _ => (P.projection v).inner_self f

theorem laplacian_positive : Positive P.laplacian := by
  intro f
  rw [P.laplacian_energy]
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem incidenceSum_symmetric (v : V) : Schur.Symmetric (P.incidenceSum v) := by
  intro f g
  simp only [incidenceSum, LinearMap.sum_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs
  · simp only [LinearMap.smul_apply, real_inner_smul_left, real_inner_smul_right,
      (P.projection u).symmetric f g]
  · simp

theorem neighbourSum_symmetric (v : V) : Schur.Symmetric (P.neighbourSum v) := by
  intro f g
  simp only [neighbourSum, LinearMap.sum_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro u _
  split_ifs
  · exact (P.projection u).symmetric f g
  · simp

theorem commuting_pair_energy (v u : V) (hvu : ¬ G.Adj v u) (f : E) :
    ⟪P.Q v f, P.Q u f⟫_ℝ = ‖P.Q v (P.Q u f)‖ ^ 2 := by
  have hc (x : E) : P.Q v (P.Q u x) = P.Q u (P.Q v x) :=
    LinearMap.congr_fun (P.nonadjacent_commute v u hvu).eq x
  rw [← (P.projection v).inner_self (P.Q u f)]
  rw [(P.projection u).symmetric, ← hc, (P.projection u).idem]
  exact (P.projection v).symmetric f (P.Q u f)

/-- Every distant cross term is nonnegative, including hard-activity
supports, because two commuting orthogonal projections have PSD product. -/
theorem nonadjacent_pair_nonneg (v u : V) (hvu : ¬ G.Adj v u) (f : E) :
    0 ≤ ⟪P.Q v f, P.Q u f⟫_ℝ := by
  rw [P.commuting_pair_energy v u hvu f]
  exact sq_nonneg _

theorem starOperator_energy (v : V) (f : E) :
    energy (P.starOperator v) f = energy (P.Q v) f +
      ⟪P.Q v f, P.incidenceSum v f⟫_ℝ + ‖P.neighbourSum v f‖ ^ 2 -
      energy (P.neighbourSum v) f := by
  simp only [starOperator, energy, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, inner_sub_right, inner_add_right,
    real_inner_smul_right]
  have h1 : ⟪f, P.Q v (P.incidenceSum v f)⟫_ℝ = ⟪P.Q v f, P.incidenceSum v f⟫_ℝ :=
    ((P.projection v).symmetric _ _).symm
  have h2 : ⟪f, P.incidenceSum v (P.Q v f)⟫_ℝ = ⟪P.Q v f, P.incidenceSum v f⟫_ℝ := by
    rw [← P.incidenceSum_symmetric v f (P.Q v f), real_inner_comm]
  have h3 : ⟪f, P.neighbourSum v (P.neighbourSum v f)⟫_ℝ = ‖P.neighbourSum v f‖ ^ 2 := by
    rw [← P.neighbourSum_symmetric v f (P.neighbourSum v f), real_inner_self_eq_norm_sq]
  rw [h1, h2, h3]
  ring

end GraphProjections
end
end CI2ZF.Appendix.Girth
