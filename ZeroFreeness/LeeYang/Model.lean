import ZeroFreeness.Potts.Model.PottsModel

/-! Actual hard-colouring partition functions with independent complex
vertex-colour fields. Pinned-only constraints have already been omitted
by `PinningData`; no properness assumption is made on their origin. -/

namespace ZeroFreeness.LeeYang

open PottsCI ZeroFreeness.Potts
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]

def oneField : V → C → ℂ := fun _ _ => 1

def fieldWeight (I : PinningData V C) (ℓ : V → C → ℂ) (σ : V → C) : ℂ :=
  if I.HardAdmissible σ then ∏ v, ℓ v (σ v) else 0

def fieldPartition (I : PinningData V C) (ℓ : V → C → ℂ) : ℂ :=
  ∑ σ : V → C, fieldWeight I ℓ σ

@[simp] theorem oneField_apply (v : V) (c : C) : oneField v c = 1 := rfl

theorem fieldWeight_eq_hardWeight_mul (I : PinningData V C)
    (ℓ : V → C → ℂ) (σ : V → C) :
    fieldWeight I ℓ σ = (I.weight 0 σ : ℂ) * ∏ v, ℓ v (σ v) := by
  rw [I.weight_zero_eq]
  by_cases h : I.HardAdmissible σ <;> simp [fieldWeight, h]

@[simp] theorem fieldWeight_one (I : PinningData V C) (σ : V → C) :
    fieldWeight I oneField σ = (I.weight 0 σ : ℂ) := by
  simp [fieldWeight_eq_hardWeight_mul]

@[simp] theorem fieldPartition_one (I : PinningData V C) :
    fieldPartition I oneField = (I.partition 0 : ℂ) := by
  simp [fieldPartition, PinningData.partition]

theorem fieldPartition_one_re_pos [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) :
    0 < (fieldPartition I oneField).re := by
  simpa using partition_zero_pos_of_succ_le I hdegree hq

theorem fieldPartition_one_ne_zero [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) :
    fieldPartition I oneField ≠ 0 := by
  rw [fieldPartition_one]
  exact_mod_cast (partition_zero_pos_of_succ_le I hdegree hq).ne'

theorem fieldPartition_eq_sum (I : PinningData V C) (ℓ : V → C → ℂ) :
    fieldPartition I ℓ =
      ∑ σ : V → C, if I.HardAdmissible σ then ∏ v, ℓ v (σ v) else 0 := rfl

theorem continuous_fieldWeight (I : PinningData V C) (σ : V → C) :
    Continuous (fun ℓ : V → C → ℂ => fieldWeight I ℓ σ) := by
  unfold fieldWeight
  split_ifs
  · exact continuous_finsetProd _ fun v _ => (continuous_apply (σ v)).comp (continuous_apply v)
  · exact continuous_const

theorem continuous_fieldPartition (I : PinningData V C) :
    Continuous (fieldPartition I) := by
  exact continuous_finsetSum _ fun σ _ => continuous_fieldWeight I σ

end
end ZeroFreeness.LeeYang
