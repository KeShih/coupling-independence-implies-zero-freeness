import CI2ZF.Appendix.Girth.Covariance.Response.Instance
import CI2ZF.Appendix.Girth.Covariance.Graph.ResponseRoot
import CI2ZF.Appendix.Girth.Transfer.SphereCoupling

/-! The full-root oscillation theorem implies the additive-source
interface used for finite sign duality. The root source is set to zero;
all source terms on the remaining graph are retained. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]

def UniformChildOscillation (C : Type v) [Fintype C] [Nonempty C]
    (Δ g : ℕ) (x χ M : ℝ) : Prop :=
  ∀ (V : Type u) [Fintype V] [DecidableEq V] (I : PinningData (Option V) C),
    I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (hx : 0 < x)
    (F : WeightedSource I χ) (a b : C),
    |(F.term none a + expectReal (GraphResponseRoot.childLaw I x hx a) F.deleted.observable) -
      (F.term none b + expectReal (GraphResponseRoot.childLaw I x hx b) F.deleted.observable)| ≤
      M * F.weight none

theorem uniformWeightedSource_of_child_oscillation {Δ g : ℕ} {x χ M : ℝ}
    (hchild : UniformChildOscillation.{u,v} C Δ g x χ M) :
    UniformWeightedSource.{u,v} C Δ g x χ M := by
  intro V _ I hd hg a b hx ha hb w hw hwl f hf
  let : DecidableEq C := fun _ _ => Classical.propDecidable _
  let : DecidableEq V := fun _ _ => Classical.propDecidable _
  let F : WeightedSource I χ :=
    { weight := w
      positive := hw
      edge_le := fun u v huv => hwl v u huv.symm
      term := Option.elim' (fun _ => 0) f
      term_bound := by
        intro v c
        cases v with
        | none => exact (by simpa using (hw none).le)
        | some v => exact hf v c }
  have h := hchild V I hd hg hx F a b
  change |(0 + expectReal (GraphResponseRoot.childLaw I x hx a) (fun σ => ∑ v, f v (σ v))) -
      (0 + expectReal (GraphResponseRoot.childLaw I x hx b) (fun σ => ∑ v, f v (σ v)))| ≤ M * w none at h
  simpa only [zero_add, GraphResponseRoot.childLaw] using h

end
end CI2ZF.Appendix.Girth
