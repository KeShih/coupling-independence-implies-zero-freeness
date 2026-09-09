import CI2ZF.Potts.Model.OptionPinning
import CI2ZF.Potts.Model.PottsModel
import CI2ZF.Potts.Model.PinningRestriction
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! CLMM sphere influence uses a fixed ambient graph throughout all
further pinnings. In particular, pinning a vertex never recomputes the
sphere in the remaining free graph. -/
namespace CI2ZF.Appendix.CLMM
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C]

def singleSiteMass {O : Type u} [Fintype O] (μ : FinDist (O → C)) (o : O) (c : C) : ℝ :=
  ∑ σ, if σ o = c then μ.w σ else 0

/-- Influence on a sphere in the current residual graph. This useful
quantity alone is not the all-pinnings hypothesis of CLMM Lemma 5.13. -/
def sphereInfluence {O : Type u} [Fintype O] (I : PinningData (Option O) C)
    (R : ℕ) (μ ν : FinDist (O → C)) : ℝ :=
  ∑ o, if I.graph.edist none (some o) = (R : ℕ∞) then
    (1 / 2 : ℝ) * ∑ c, |singleSiteMass μ o c - singleSiteMass ν o c| else 0

/-- The current free coordinates are embedded in the fixed graph `G`.
The distance appearing here remains the distance in `G` after pinning. -/
def ambientSphereInfluence {A O : Type u} [Fintype O] (G : SimpleGraph A)
    (e : Option O ↪ A) (R : ℕ) (μ ν : FinDist (O → C)) : ℝ :=
  ∑ o, if G.edist (e none) (e (some o)) = (R : ℕ∞) then
    (1 / 2 : ℝ) * ∑ c, |singleSiteMass μ o c - singleSiteMass ν o c| else 0

/-- Uniform current-residual sphere influence, retained only for
intermediate estimates. The literature interfaces use the stronger
fixed-ambient, all-pinnings condition below. -/
def SphereDecay (C : Type v) [Fintype C] (Δ g R : ℕ) (x ε : ℝ) : Prop :=
  ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
    I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
    (hx : 0 ≤ x) (ha : 0 < (optionChildData I a).partition x)
    (hb : 0 < (optionChildData I b).partition x),
    sphereInfluence I R ((optionChildData I a).gibbs x hx ha)
      ((optionChildData I b).gibbs x hx hb) ≤ ε

/-- CLMM Condition 5.12 for every base system and every further pinning.
`pin` colours exactly the complement of the embedded free set, and the
restricted model retains both the base unary counts and every new pinned
neighbour. The ambient graph and its metric are fixed before `pin` is
chosen. Positive activities make all these pinnings feasible. -/
def FixedAmbientSphereDecay (C : Type v) [Fintype C] (Δ g R : ℕ) (x ε : ℝ) : Prop :=
  ∀ {A : Type u} [Fintype A] (J : PinningData A C),
    J.DegreeBound Δ → (g : ℕ∞) ≤ J.graph.egirth →
    ∀ {O : Type u} [Fintype O] (e : Option O ↪ A) (pin : A → Option C),
    (∀ a, pin a = none ↔ a ∈ Set.range e) →
    let I := restrictPinningData J e pin
    ∀ (a b : C) (hx : 0 ≤ x) (ha : 0 < (optionChildData I a).partition x)
      (hb : 0 < (optionChildData I b).partition x),
      ambientSphereInfluence J.graph e R ((optionChildData I a).gibbs x hx ha)
        ((optionChildData I b).gibbs x hx hb) ≤ ε

theorem fixedAmbientSphereDecay_mono {Δ g R : ℕ} {x ε η : ℝ}
    (h : FixedAmbientSphereDecay.{u,v} C Δ g R x ε) (he : ε ≤ η) :
    FixedAmbientSphereDecay.{u,v} C Δ g R x η := by
  intro A _ J hd hg O _ e pin hpin
  dsimp only
  intro a b hx ha hb
  exact (h J hd hg e pin hpin a b hx ha hb).trans he

end
end CI2ZF.Appendix.CLMM
