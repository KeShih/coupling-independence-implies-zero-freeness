import ZeroFreeness.Coupling.CLMM.SphereEstimate

/-! The CLMM eventual-depth transfer with the proved sphere estimate
(Equation (10)) supplied: `eventual_transfer` without its `Literature`
argument. -/
namespace ZeroFreeness.Appendix.CLMM
open scoped BigOperators
open PottsCI PottsCI.FinDist ZeroFreeness.Potts Filter Set
open ZeroFreeness.Appendix.Girth
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u v
variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]

/-- The eventual-depth transfer: tree TID and relative SSM beyond a fixed
depth give one girth and one coupling constant for a whole activity set. -/
theorem eventual_transfer_unconditional (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (A B ρ : ℝ) (hA : 0 < A) (hB : 0 < B) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (K₀ : ℕ) (J : Set ℝ)
    (hJ : ∀ x ∈ J, 0 < x ∧ x ≤ 1)
    (htree : ∀ (x : ℝ) (hxJ : x ∈ J),
      TreeTID (C := C) Δ x (hJ x hxJ).1 A ρ ∧ TreeRelative (C := C) Δ x B ρ K₀) :
    ∃ (g : ℕ) (cost : ℝ), 3 ≤ g ∧ 0 ≤ cost ∧
      ∀ (x : ℝ) (hxJ : x ∈ J), ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
        I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
        (ha : 0 < (optionChildData I a).partition x)
        (hb : 0 < (optionChildData I b).partition x),
        W ham ((optionChildData I a).gibbs x (hJ x hxJ).1.le ha)
          ((optionChildData I b).gibbs x (hJ x hxJ).1.le hb) ≤ cost :=
  eventual_transfer (literature.{u,v} C) Δ hΔ A B ρ hA hB hρ hρ1 K₀ J hJ htree

end
end ZeroFreeness.Appendix.CLMM
