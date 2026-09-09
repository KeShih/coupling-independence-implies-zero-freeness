import CI2ZF.LeeYang.Pinning
import CI2ZF.LeeYang.ModelRoot
import CI2ZF.LeeYang.TransportRelabel
import CI2ZF.RootLawRelabel

/-! The original graph root recursion uses the literal enlarged partial
colouring, including blocked root colours whose parent coefficient is zero. -/

namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts CI2ZF.Potts.Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u v
variable {V O : Type u} {C : Type v} [Fintype V] [Fintype O] [Fintype C]

theorem fieldPartition_rootChildData (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (ℓ : V → C → ℂ) :
    fieldPartition (rootChildData tau G r a) (fun v => ℓ v.val) =
      normalizedFieldPartition (pinVertex tau r a) G ℓ := by
  rw [normalizedFieldPartition_eq]
  unfold rootChildData
  congr 2

theorem fieldPartition_optionChild_original (tau : PartialColouring V C)
    (G : SimpleGraph V) (e : Option O ≃ tau.FreeVertex) (a : C) (ℓ : V → C → ℂ) :
    fieldPartition (optionChildData (relabelData (tau.toPinningData G) e.symm) a)
        (fun o => ℓ (e (some o)).val) =
      normalizedFieldPartition (pinVertex tau (e none) a) G ℓ := by
  rw [← rootChildData_relabel_of_parent tau G e _ rfl a, fieldPartition_relabel_any]
  have hf : fieldPull (optionRootRemainingEquiv tau e).symm
      (fun o => ℓ (e (some o)).val) = fun v => ℓ v.val := by
    funext v c
    change ℓ (e (some ((optionRootRemainingEquiv tau e).symm v))).val c = ℓ v.val c
    rw [← optionRootRemainingEquiv_val, Equiv.apply_symm_apply]
  rw [hf]
  exact fieldPartition_rootChildData tau G (e none) a ℓ

theorem normalizedFieldPartition_pinVertex_recursion (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (ℓ : V → C → ℂ) :
    normalizedFieldPartition tau G ℓ =
      ∑ a : C, (if tau.boundaryCount G r a = 0 then ℓ r.val a else 0) *
        normalizedFieldPartition (pinVertex tau r a) G ℓ := by
  let e : Option {v : tau.FreeVertex // v ≠ r} ≃ tau.FreeVertex := (rootOptionEquiv r).symm
  have he : e none = r := rfl
  rw [normalizedFieldPartition_eq,
    ← fieldPartition_relabel (tau.toPinningData G) e.symm (fun v => ℓ v.val),
    option_parent_fieldPartition]
  apply Finset.sum_congr rfl
  intro a _
  have hc := fieldPartition_optionChild_original tau G e a ℓ
  simp only [he] at hc
  change (if tau.boundaryCount G r a = 0 then ℓ r.val a else 0) *
      fieldPartition (optionChildData (relabelData (tau.toPinningData G) e.symm) a)
        (fun o => ℓ (e (some o)).val) = _
  rw [hc]

theorem normalizedFieldPartition_pinVertex_recursion_allowed (tau : PartialColouring V C)
    (G : SimpleGraph V) (r : tau.FreeVertex) (ℓ : V → C → ℂ) :
    normalizedFieldPartition tau G ℓ =
      ∑ a ∈ Finset.univ.filter (fun a => tau.boundaryCount G r a = 0),
        ℓ r.val a * normalizedFieldPartition (pinVertex tau r a) G ℓ := by
  rw [normalizedFieldPartition_pinVertex_recursion tau G r ℓ, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

end
end CI2ZF.LeeYang
