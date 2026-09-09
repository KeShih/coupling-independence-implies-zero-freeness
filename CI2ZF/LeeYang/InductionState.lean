import CI2ZF.LeeYang.Analytic
import CI2ZF.Potts.Model.PinningRestrictionInstances

/-! The field-direction induction is uniform over actual members of the
operation-closed graph family and over all bounded field directions. -/
namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts
noncomputable section
universe u v
variable {C : Type v} [Fintype C]

def SmallerCurvesNonzero (F : PinningFamily.{u, v} C) (Δ n : ℕ) (r : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
    I.DegreeBound Δ → Fintype.card V < n →
    ∀ d : V → C → ℂ, DirectionBound d → CurveNonzeroOn I d r

def SmallerCurveResponses (F : PinningFamily.{u, v} C) (Δ n : ℕ) (r α : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C), F.contains I →
    I.DegreeBound Δ → Fintype.card (Option V) < n →
    ∀ d : Option V → C → ℂ, DirectionBound d → CurveRootResponses I d r α

end
end CI2ZF.LeeYang
