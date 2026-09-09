import CI2ZF.Appendix.GirthDoobReveal
import CI2ZF.Appendix.EdgeSlotConditioning

/-! Deterministic transport and constant-source invariance for the exact
scores and successive conditional laws in the finite Doob argument. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω Λ C : Type*} [Fintype Ω] [Fintype Λ] [Fintype C] [DecidableEq C]

theorem coordinateMarginal_map (μ : FinDist Ω) (e : Ω → Λ) (k : Λ → C) :
    coordinateMarginal (mapLaw μ e) k = coordinateMarginal μ (fun ω => k (e ω)) := by
  exact mapLaw_comp μ e k

theorem covariance_map (μ : FinDist Ω) (e : Ω → Λ) (f g : Λ → ℝ) :
    covariance (mapLaw μ e) f g = covariance μ (fun ω => f (e ω)) (fun ω => g (e ω)) := by
  simp only [covariance_eq_moment, expectReal_mapLaw]

theorem responseScore_map (μ : FinDist Ω) (e : Ω → Λ) (s : ℝ) (k : Λ → C)
    (f : Λ → ℝ) (c : C) :
    responseScore s (mapLaw μ e) k f c = responseScore s μ (fun ω => k (e ω)) (fun ω => f (e ω)) c := by
  rw [responseScore, coordinateMarginal_map, covariance_map]
  rfl

theorem covariance_add_const_left (μ : FinDist Ω) (f g : Ω → ℝ) (a : ℝ) :
    covariance μ (fun ω => f ω + a) g = covariance μ f g := by
  rw [covariance_comm, covariance_add_right, covariance_const_right, add_zero, covariance_comm]

theorem responseScore_add_const (μ : FinDist Ω) (s : ℝ) (k : Ω → C)
    (f : Ω → ℝ) (a : ℝ) (c : C) :
    responseScore s μ k (fun ω => f ω + a) c = responseScore s μ k f c := by
  rw [responseScore, covariance_add_const_left]
  rfl

namespace Doob

theorem given_map (μ : FinDist Ω) (e : Ω → Λ) (k : Λ → C) (c : C) :
    given (mapLaw μ e) k c = mapLaw (given μ (fun ω => k (e ω)) c) e :=
  (Edge.FiniteLaw.conditional_mapLaw μ e (fun ω => k ω = c)).symm

theorem observed_map (μ : FinDist Ω) (e : Ω → Λ) (k : Λ → C) :
    observed (mapLaw μ e) k = observed μ (fun ω => k (e ω)) := by
  rw [observed_eq_coordinateMarginal, observed_eq_coordinateMarginal, coordinateMarginal_map]

def pullScores (e : Ω → Λ) (ks : List ((Λ → C) × ℝ)) : List ((Ω → C) × ℝ) :=
  ks.map (fun z => ((fun ω => z.1 (e ω)), z.2))

theorem squareBudget_pull (e : Ω → Λ) (ks : List ((Λ → C) × ℝ)) :
    squareBudget (pullScores e ks) = squareBudget ks := by
  simp only [squareBudget, pullScores, List.map_map, Function.comp_def]

theorem boundedScores_map (e : Ω → Λ) (ks : List ((Λ → C) × ℝ)) (s K : ℝ) (f : Λ → ℝ)
    (μ : FinDist Ω) :
    BoundedScores s K f ks (mapLaw μ e) ↔ BoundedScores s K (fun ω => f (e ω)) (pullScores e ks) μ := by
  induction ks generalizing μ with
  | nil => simp only [pullScores, List.map_nil, BoundedScores]
  | cons z ks ih =>
    obtain ⟨k,a⟩ := z
    simp only [pullScores, List.map_cons, BoundedScores]
    simp_rw [coordinateMarginal_map, responseScore_map, observed_map, given_map]
    exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun c => imp_congr_right fun _ => ih _))

theorem boundedScores_add_const (ks : List ((Ω → C) × ℝ)) (s K : ℝ) (f : Ω → ℝ) (a : ℝ)
    (μ : FinDist Ω) :
    BoundedScores s K (fun ω => f ω + a) ks μ ↔ BoundedScores s K f ks μ := by
  induction ks generalizing μ with
  | nil => exact Iff.rfl
  | cons z ks ih =>
    obtain ⟨k,b⟩ := z
    simp only [BoundedScores]
    simp_rw [responseScore_add_const]
    exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun c => imp_congr_right fun _ => ih _))

theorem boundedScores_map_add_const (e : Ω → Λ) (ks : List ((Λ → C) × ℝ)) (s K : ℝ)
    (f : Λ → ℝ) (g : Ω → ℝ) (a : ℝ) (hf : ∀ ω, f (e ω) = g ω + a) (μ : FinDist Ω) :
    BoundedScores s K f ks (mapLaw μ e) ↔ BoundedScores s K g (pullScores e ks) μ := by
  rw [boundedScores_map]
  simp_rw [hf]
  exact boundedScores_add_const _ _ _ _ _ _

end Doob
end
end CI2ZF.Appendix.Girth
