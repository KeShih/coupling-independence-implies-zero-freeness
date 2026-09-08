import CI2ZF.HolantPathParent
import CI2ZF.HolantCoefficientBounds

/-!
# Simultaneous strong induction on the number of free Holant edges

The response-step argument is isolated as a callback so that the separator
construction can be supplied independently. Strong induction then derives
both actual path nonvanishing and the continued response property. All
smaller-instance hypotheses passed to the callback are proved recursively;
the parent nonvanishing step uses actual normalized child instances and
handles empty instances and structurally dead one-children.
-/
namespace CI2ZF.Holant
open Metric
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A response step supplied with both genuine strong-induction hypotheses
closes the entire nonvanishing/response induction.  The only numerical inputs
needed here are the response cap and the parent perturbation budget. -/
theorem path_simultaneous_of_response_step (G : SimpleGraph V) (F : Finset Signature)
    {R ε α : ℝ} (hα : α ≤ 1 / 4)
    (hparent : (residualGrowthBound F) ^ 2 * ε * (4 / 3) < 1)
    (responseStep : ∀ H : NormalizedInstance V (Sym2 V),
      H.incidence = graphIncidence → H.edges ⊆ G.edgeFinset →
      (∀ v, H.signature v ∈ residualFamily F) →
      ∀ p : ActivityPath H.edges R ε,
      (∀ K : NormalizedInstance V (Sym2 V), K.incidence = H.incidence →
        K.edges ⊆ H.edges → K.edges.card < H.edges.card →
        (∀ v, K.signature v ∈ residualFamily F) →
        ∀ t ∈ ball (0 : ℂ) p.radius, K.toInstance.complexPartition (p.activity t) ≠ 0) →
      (∀ K : NormalizedInstance V (Sym2 V), K.incidence = H.incidence →
        ∀ hK : K.edges ⊆ H.edges, K.edges.card < H.edges.card →
        (∀ v, K.signature v ∈ residualFamily F) →
        ∀ a (ha : a ∈ K.edges) (hs : K.OneSurvives a),
          ResponseBound K a ha hs (p.restrict hK) α) →
      ∀ e (he : e ∈ H.edges) (hs : H.OneSurvives e), ResponseBound H e he hs p α) :
    ∀ H : NormalizedInstance V (Sym2 V), H.incidence = graphIncidence →
      H.edges ⊆ G.edgeFinset → (∀ v, H.signature v ∈ residualFamily F) →
      ∀ p : ActivityPath H.edges R ε,
        (∀ t ∈ ball (0 : ℂ) p.radius, H.toInstance.complexPartition (p.activity t) ≠ 0) ∧
        (∀ e (he : e ∈ H.edges) (hs : H.OneSurvives e), ResponseBound H e he hs p α) := by
  have main : ∀ n : ℕ, ∀ H : NormalizedInstance V (Sym2 V),
      H.incidence = graphIncidence → H.edges ⊆ G.edgeFinset →
      (∀ v, H.signature v ∈ residualFamily F) → H.edges.card = n →
      ∀ p : ActivityPath H.edges R ε,
        (∀ t ∈ ball (0 : ℂ) p.radius, H.toInstance.complexPartition (p.activity t) ≠ 0) ∧
        (∀ e (he : e ∈ H.edges) (hs : H.OneSurvives e), ResponseBound H e he hs p α) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro H hinc hE hF hcard p
      have hsmallNZ : ∀ K : NormalizedInstance V (Sym2 V), K.incidence = H.incidence →
          K.edges ⊆ H.edges → K.edges.card < H.edges.card →
          (∀ v, K.signature v ∈ residualFamily F) →
          ∀ t ∈ ball (0 : ℂ) p.radius, K.toInstance.complexPartition (p.activity t) ≠ 0 := by
        intro K hKinc hKH hKcard hKF
        have hK := ih K.edges.card (by omega) K (hKinc.trans hinc) (hKH.trans hE)
          hKF rfl (p.restrict hKH)
        exact hK.1
      have hsmallResponse : ∀ K : NormalizedInstance V (Sym2 V), K.incidence = H.incidence →
          ∀ hK : K.edges ⊆ H.edges, K.edges.card < H.edges.card →
          (∀ v, K.signature v ∈ residualFamily F) →
          ∀ a (ha : a ∈ K.edges) (hs : K.OneSurvives a),
            ResponseBound K a ha hs (p.restrict hK) α := by
        intro K hKinc hKH hKcard hKF
        have hK := ih K.edges.card (by omega) K (hKinc.trans hinc) (hKH.trans hE)
          hKF rfl (p.restrict hKH)
        exact hK.2
      have hresponse := responseStep H hinc hE hF p hsmallNZ hsmallResponse
      have htwo : ∀ e ∈ H.edges, (Finset.univ.filter (H.incidence e)).card = 2 := by
        intro e he
        rw [hinc]
        exact graph_edge_two_endpoints G e (hE he)
      have hzero : ∀ e, ∀ _he : e ∈ H.edges, ∀ t ∈ ball (0 : ℂ) p.radius,
          (H.zeroChild e).toInstance.complexPartition (p.activity t) ≠ 0 := by
        intro e he
        exact hsmallNZ (H.zeroChild e) rfl (Finset.erase_subset e H.edges)
          (H.zeroChild_card_lt e he) (H.zeroChild_family F hF e)
      have hone : ∀ e, ∀ he : e ∈ H.edges, ∀ hs : H.OneSurvives e,
          ∀ t ∈ ball (0 : ℂ) p.radius,
            (H.oneChild e he hs).toInstance.complexPartition (p.activity t) ≠ 0 := by
        intro e he hs
        exact hsmallNZ (H.oneChild e he hs) rfl (Finset.erase_subset e H.edges)
          (H.zeroChild_card_lt e he) (H.oneChild_family F hF e he hs)
      exact ⟨H.path_ne_zero_of_children F hF htwo p hα hparent hzero hone hresponse,
        hresponse⟩
  intro H hinc hE hF p
  exact main H.edges.card H hinc hE hF rfl p

end
end CI2ZF.Holant
