import CI2ZF.HolantUniformResponse
import CI2ZF.HolantStrongInduction
import CI2ZF.HolantTubeTheorem

/-! Uniform zero-freeness for the actual log-concave Boolean Holant model.
The parameters are chosen before the graph and the activity path. Every
smaller-instance input is discharged by simultaneous strong induction. -/
namespace CI2ZF.Holant
open Metric Set
universe u
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No coupling, logarithm, separator, or smaller-instance hypothesis remains
in this theorem. The same numerical budgets apply to all finite graphs. -/
theorem uniform_path_nonzero_and_response (F : Finset Signature) (Δ : ℕ)
    {R : ℝ} (hR : 0 ≤ R)
    (pars : TransferParameters (2 * (Δ - 1)) (residualGrowthBound F) R
      (2 * ((1 + (HolantCoupling.residualCouplingA F) ^ 2 * R) ^ Δ - 1)))
    (G : SimpleGraph V) (hΔ : ∀ v, G.degree v ≤ Δ)
    (H : NormalizedInstance V (Sym2 V)) (hinc : H.incidence = graphIncidence)
    (hE : H.edges ⊆ G.edgeFinset) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (p : ActivityPath H.edges R pars.epsilon) :
    (∀ t ∈ ball (0 : ℂ) p.radius, H.toInstance.complexPartition (p.activity t) ≠ 0) ∧
    (∀ e (he : e ∈ H.edges) (hs : H.OneSurvives e), ResponseBound H e he hs p pars.alpha) :=
  path_simultaneous_of_response_step G F pars.alpha_small pars.parent_small
    (uniform_response_step G F Δ hΔ hR pars) H hinc hE hF p

/-- The manuscript's Holant polytube theorem. The radius is chosen before
the vertex type, graph, signature assignment, real anchors and independent
complex activities. Only genuine graph-edge coordinates are constrained.
The proof also covers degree bounds zero and one and a degenerate box. -/
theorem exists_uniform_holant_polytube (F : Finset Signature) (Δ : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V), (∀ v, G.degree v ≤ Δ) →
      ∀ f : V → Signature, (∀ v, f v ∈ F) →
      (∀ v, (f v).arity = G.degree v) → ∀ z : Sym2 V → ℂ,
      (∀ e ∈ G.edgeFinset, ∃ x : ℝ, x ∈ Icc 0 R ∧ ‖z e - (x : ℂ)‖ < ε) →
      graphPartition G (complexValues f) z ≠ 0 := by
  obtain ⟨pars⟩ := exists_transferParameters (C :=
    2 * ((1 + (HolantCoupling.residualCouplingA F) ^ 2 * R) ^ Δ - 1))
    (2 * (Δ - 1)) (residualGrowthBound_nonneg F) hR
  refine ⟨pars.epsilon, pars.epsilon_pos, ?_⟩
  intro V _ _ G hΔ f hF harity z hz
  have hpath : GraphFamilyPathNonzero (V := V) F Δ R pars.epsilon := by
    intro G hΔ H hinc hE hF p
    exact (uniform_path_nonzero_and_response F Δ hR pars G hΔ H hinc hE hF p).1
  let x : Sym2 V → ℝ := fun e =>
    if he : e ∈ G.edgeFinset then Classical.choose (hz e he) else 0
  have hx (e : Sym2 V) (he : e ∈ G.edgeFinset) :
      x e ∈ Icc 0 R ∧ ‖z e - (x e : ℂ)‖ < pars.epsilon := by
    simpa only [x, dif_pos he] using Classical.choose_spec (hz e he)
  exact graphPartition_ne_zero_of_paths F Δ pars.epsilon_pos hpath G hΔ f hF harity x z
    (fun e he => (hx e he).1) (fun e he => (hx e he).2)

end
end CI2ZF.Holant
