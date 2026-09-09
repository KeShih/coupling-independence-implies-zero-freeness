import CI2ZF.LeeYang.GeometryFields
import CI2ZF.Potts.Geometry.GenericGibbsRelabel
import CI2ZF.Potts.Model.PinningRestrictionComposition
import CI2ZF.Potts.Model.PinningRestrictionInstances
import CI2ZF.Potts.Geometry.RootOptionRelabel

/-! Exact transport of the actual field partition under vertex
relabeling and successive normalized pinnings. -/
namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
universe u v
variable {V W T : Type u} {C : Type v} [Fintype V] [Fintype W] [Fintype T] [Fintype C]

theorem fieldWeight_relabel (I : PinningData V C) (e : V ≃ W)
    (ℓ : V → C → ℂ) (τ : W → C) :
    fieldWeight (relabelData I e) (fieldPull e.symm ℓ) τ = fieldWeight I ℓ (τ ∘ e) := by
  rw [fieldWeight_eq_hardWeight_mul, fieldWeight_eq_hardWeight_mul, weight_relabel]
  congr 1
  exact Fintype.prod_equiv e.symm _ _ (fun w => by simp [fieldPull])

theorem fieldPartition_relabel (I : PinningData V C) (e : V ≃ W) (ℓ : V → C → ℂ) :
    fieldPartition (relabelData I e) (fieldPull e.symm ℓ) = fieldPartition I ℓ := by
  unfold fieldPartition
  apply Fintype.sum_equiv (relabelColouring (C := C) e).symm
  intro τ
  exact fieldWeight_relabel I e ℓ τ

theorem fieldPartition_relabel_any (I : PinningData V C) (e : V ≃ W) (ℓ : W → C → ℂ) :
    fieldPartition (relabelData I e) ℓ = fieldPartition I (fieldPull e ℓ) := by
  have he : fieldPull e.symm (fieldPull e ℓ) = ℓ := by
    funext w c
    simp [fieldPull]
  simpa only [he] using fieldPartition_relabel I e (fieldPull e ℓ)

theorem fieldPartition_relabel_line (I : PinningData V C) (e : V ≃ W)
    (d : V → C → ℂ) (z : ℂ) :
    fieldPartition (relabelData I e) (fieldLine (fieldPull e.symm d) z) =
      fieldPartition I (fieldLine d z) := fieldPartition_relabel I e (fieldLine d z)

theorem fieldPartition_restrict_restrict (I : PinningData V C)
    (e : W ↪ V) (pin : V → Option C) (f : T ↪ W) (newPin : W → Option C)
    (hpin : ∀ w, pin (e w) = none) (ℓ : V → C → ℂ) :
    fieldPartition (restrictPinningData (restrictPinningData I e pin) f newPin)
      (fieldPull f (fieldPull e ℓ)) =
    fieldPartition (restrictPinningData I (f.trans e) (composePinning e pin newPin))
      (fieldPull (f.trans e) ℓ) := by
  rw [restrictPinningData_restrict I e pin f newPin hpin]
  rfl

theorem fieldPartition_optionChild_restrict (I : PinningData (Option V) C)
    (a : C) (ℓ : Option V → C → ℂ) :
    fieldPartition (optionChildData I a) (fieldPull Option.some ℓ) =
      fieldPartition (restrictPinningData I someEmbedding (rootOnlyPinning a))
        (fieldPull someEmbedding ℓ) := by
  rw [optionChildData_eq_restrictPinningData]
  rfl

theorem fieldPartition_rootOption (I : PinningData V C) (v : V) (ℓ : V → C → ℂ) :
    fieldPartition (rootOptionData I v) (fieldPull (rootOptionEquiv v).symm ℓ) =
      fieldPartition I ℓ := fieldPartition_relabel I (rootOptionEquiv v) ℓ

end
end CI2ZF.LeeYang
