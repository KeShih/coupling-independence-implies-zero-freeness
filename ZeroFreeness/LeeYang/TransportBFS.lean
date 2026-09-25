import ZeroFreeness.LeeYang.TransportRelabel
import ZeroFreeness.LeeYang.Analytic
import ZeroFreeness.LeeYang.Separator
import ZeroFreeness.Potts.Transfer.FamilyBFSResponseSteps

/-! Field directions follow the actual parent vertices through BFS
splitting and one-coordinate unpinning. -/
namespace ZeroFreeness.LeeYang
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Separator ZeroFreeness.Potts.OptionBFS
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] optionBFSMarginalInsideEq optionBFSMarginalShellEq
  optionBFSMarginalOutsideEq optionBFSMarginalInsideFintype optionBFSMarginalOutsideFintype
set_option linter.unusedSectionVars false
universe u v
variable {O : Type u} {C : Type v} [Fintype O] [Fintype C]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _

theorem fieldPull_childEquiv_symm (I : PinningData (Option O) C) (k : ℕ)
    (ℓ : Option O → C → ℂ) :
    fieldPull (childEquiv I.graph k).symm (fieldPull some ℓ) =
      fieldPull (parentValue I.graph k) ℓ := by
  funext w c
  change ℓ (some ((childEquiv I.graph k).symm w)) c = _
  rw [some_childEquiv_symm, unsplit_parentEmbedding]
  rfl

theorem fieldPartition_childSplit (I : PinningData (Option O) C) (a : C) (k : ℕ)
    (ℓ : Option O → C → ℂ) :
    fieldPartition (childSplit I a k) (fieldPull (parentValue I.graph k) ℓ) =
      fieldPartition (optionChildData I a) (fieldPull some ℓ) := by
  rw [← fieldPull_childEquiv_symm]
  exact fieldPartition_relabel (optionChildData I a) (childEquiv I.graph k) _

theorem fieldCurve_childSplit (I : PinningData (Option O) C) (a : C) (k : ℕ)
    (d : Option O → C → ℂ) (z : ℂ) :
    fieldCurve (childSplit I a k) (fieldPull (parentValue I.graph k) d) z =
      fieldCurve (optionChildData I a) (fieldPull some d) z :=
  fieldPartition_childSplit I a k (fieldLine d z)

@[simp] theorem exteriorField_fieldLine {U S : Type*} [Fintype U] [Fintype S]
    (d : Separator.Vertex U S O → C → ℂ) (z : ℂ) :
    exteriorField (fieldLine d z) = fieldLine (exteriorField d) z := rfl

theorem exteriorField_childSplit_pull (I : PinningData (Option O) C) (k : ℕ)
    (ℓ : Option O → C → ℂ) :
    exteriorField (fieldPull (parentValue I.graph k) ℓ) = fieldPull Subtype.val ℓ := rfl

theorem DirectionBound.exterior {U S : Type*} [Fintype U] [Fintype S]
    {d : Separator.Vertex U S O → C → ℂ} (hd : DirectionBound d) :
    DirectionBound (exteriorField d) := hd.pull _

theorem fieldCurve_unpinnedExterior {U S : Type*} [Fintype U] [Fintype S]
    (I : PinningData (Separator.Vertex U S O) C) (d : Separator.Vertex U S O → C → ℂ)
    (ξ : S → C) (s : S) (a : C) (z : ℂ) :
    fieldCurve (optionChildData (unpinnedExteriorData I ξ s) a)
        (fieldPull some (fieldPull (unpinShellEmbedding s) d)) z =
      fieldCurve (exteriorData I (Function.update ξ s a)) (exteriorField d) z := by
  rw [optionChildData_unpinnedExterior]
  rfl

end
end ZeroFreeness.LeeYang
