import CI2ZF.LeeYang.Model
import CI2ZF.Potts.Model.OptionPinning

/-! Exact conditioning on a root colour. A blocked root colour has zero
parent coefficient; its normalized child is still the actual pinned model. -/

namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {O C : Type*} [Fintype O] [Fintype C]

def optionJoin (a : C) (σ : O → C) : Option O → C := Option.elim' a σ

def optionColouringEquiv : (Option O → C) ≃ C × (O → C) where
  toFun σ := (σ none, fun o => σ (some o))
  invFun p := optionJoin p.1 p.2
  left_inv σ := by funext o; cases o <;> rfl
  right_inv _ := rfl

theorem hardAdmissible_optionJoin (I : PinningData (Option O) C) (a : C) (σ : O → C) :
    I.HardAdmissible (optionJoin a σ) ↔
      I.boundaryCount none a = 0 ∧ (optionChildData I a).HardAdmissible σ := by
  constructor
  · intro h
    refine ⟨h.2 none, ⟨?_, ?_⟩⟩
    · intro u v huv
      exact h.1 (some u) (some v) huv
    · intro o
      rw [optionChildData_count]
      have hb := h.2 (some o)
      change I.boundaryCount (some o) (σ o) = 0 at hb
      rw [hb, zero_add]
      exact if_neg (fun hh => (h.1 none (some o) hh.1) hh.2.symm)
  · rintro ⟨hroot, hchild⟩
    have hb (o : O) : I.boundaryCount (some o) (σ o) = 0 := by
      have h := hchild.2 o
      rw [optionChildData_count] at h
      omega
    have hc (o : O) (hadj : I.graph.Adj none (some o)) : a ≠ σ o := by
      intro he
      have h := hchild.2 o
      rw [optionChildData_count, if_pos ⟨hadj, he.symm⟩] at h
      omega
    refine ⟨?_, ?_⟩
    · intro u v huv
      cases u with
      | none =>
        cases v with
        | none => exact (I.graph.loopless.irrefl none huv).elim
        | some v => exact hc v huv
      | some u =>
        cases v with
        | none => exact (hc u huv.symm).symm
        | some v => exact hchild.1 u v huv
    · intro o
      cases o with
      | none => exact hroot
      | some o => exact hb o

theorem option_fieldWeight (I : PinningData (Option O) C)
    (ℓ : Option O → C → ℂ) (a : C) (σ : O → C) :
    fieldWeight I ℓ (optionJoin a σ) =
      (if I.boundaryCount none a = 0 then ℓ none a else 0) *
        fieldWeight (optionChildData I a) (fun o => ℓ (some o)) σ := by
  unfold fieldWeight
  rw [hardAdmissible_optionJoin]
  by_cases hr : I.boundaryCount none a = 0 <;>
    by_cases hc : (optionChildData I a).HardAdmissible σ <;>
    simp [hr, hc, Fintype.prod_option, optionJoin]

theorem option_parent_fieldPartition (I : PinningData (Option O) C)
    (ℓ : Option O → C → ℂ) :
    fieldPartition I ℓ =
      ∑ a : C, (if I.boundaryCount none a = 0 then ℓ none a else 0) *
        fieldPartition (optionChildData I a) (fun o => ℓ (some o)) := by
  unfold fieldPartition
  have he : (∑ σ : Option O → C, fieldWeight I ℓ σ) =
      ∑ p : C × (O → C), fieldWeight I ℓ (optionJoin p.1 p.2) := by
    exact Fintype.sum_equiv (optionColouringEquiv (O := O) (C := C))
      (fun σ => fieldWeight I ℓ σ)
      (fun p => fieldWeight I ℓ (optionJoin p.1 p.2))
      (fun σ => by congr 1; exact (optionColouringEquiv.left_inv σ).symm)
  have hp : (∑ p : C × (O → C), fieldWeight I ℓ (optionJoin p.1 p.2)) =
      ∑ a : C, (if I.boundaryCount none a = 0 then ℓ none a else 0) *
        ∑ σ : O → C, fieldWeight (optionChildData I a) (fun o => ℓ (some o)) σ := by
    rw [Fintype.sum_prod_type]
    simp_rw [option_fieldWeight, Finset.mul_sum]
  convert he.trans hp using 1
  congr 2
  exact Subsingleton.elim _ _

theorem option_parent_fieldPartition_allowed (I : PinningData (Option O) C)
    (ℓ : Option O → C → ℂ) :
    fieldPartition I ℓ =
      ∑ a ∈ Finset.univ.filter (fun a => I.boundaryCount none a = 0),
        ℓ none a * fieldPartition (optionChildData I a) (fun o => ℓ (some o)) := by
  rw [option_parent_fieldPartition, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

theorem option_child_fieldPartition_one_ne_zero [Nonempty C]
    (I : PinningData (Option O) C) {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (a : C) :
    fieldPartition (optionChildData I a) oneField ≠ 0 :=
  fieldPartition_one_ne_zero _ (optionChildData_degreeBound I hdegree a) hq

end
end CI2ZF.LeeYang
