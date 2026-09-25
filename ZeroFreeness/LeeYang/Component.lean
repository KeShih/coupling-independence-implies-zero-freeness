import ZeroFreeness.LeeYang.TransportRelabel
import ZeroFreeness.LeeYang.InductionState
import ZeroFreeness.LeeYang.Local
import ZeroFreeness.Potts.Transfer.FamilyInduction

/-! Field partitions factor exactly over connected components. Only the
root component contributes to its normalized child-response quotient. -/
namespace ZeroFreeness.LeeYang
open PottsCI ZeroFreeness.Potts ZeroFreeness.Potts.Component
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false
universe u v
variable {U O : Type u} {C : Type v} [Fintype U] [Fintype O] [Fintype C]

theorem hardAdmissible_sum (I : PinningData (U ⊕ O) C) (hsep : Separated I)
    (σ : U → C) (τ : O → C) :
    I.HardAdmissible (Sum.elim σ τ) ↔
      (leftData I).HardAdmissible σ ∧ (rightData I).HardAdmissible τ := by
  constructor
  · intro h
    exact ⟨⟨fun u v huv => h.1 (.inl u) (.inl v) huv, fun u => h.2 (.inl u)⟩,
      ⟨fun u v huv => h.1 (.inr u) (.inr v) huv, fun u => h.2 (.inr u)⟩⟩
  · rintro ⟨hσ, hτ⟩
    refine ⟨?_, ?_⟩
    · intro u v huv
      rcases u with u | u <;> rcases v with v | v
      · exact hσ.1 u v huv
      · exact (hsep u v huv).elim
      · exact (hsep v u huv.symm).elim
      · exact hτ.1 u v huv
    · intro u
      rcases u with u | u
      · exact hσ.2 u
      · exact hτ.2 u

theorem sum_fieldWeight (I : PinningData (U ⊕ O) C) (hsep : Separated I)
    (ℓ : U ⊕ O → C → ℂ) (σ : U → C) (τ : O → C) :
    fieldWeight I ℓ (Sum.elim σ τ) =
      fieldWeight (leftData I) (fieldPull Sum.inl ℓ) σ *
        fieldWeight (rightData I) (fieldPull Sum.inr ℓ) τ := by
  unfold fieldWeight
  rw [hardAdmissible_sum I hsep]
  by_cases hσ : (leftData I).HardAdmissible σ <;>
    by_cases hτ : (rightData I).HardAdmissible τ <;>
    simp [hσ, hτ, Fintype.prod_sum_type, fieldPull]

theorem sum_fieldPartition (I : PinningData (U ⊕ O) C) (hsep : Separated I)
    (ℓ : U ⊕ O → C → ℂ) :
    fieldPartition I ℓ = fieldPartition (leftData I) (fieldPull Sum.inl ℓ) *
      fieldPartition (rightData I) (fieldPull Sum.inr ℓ) := by
  unfold fieldPartition
  trans ∑ p : (U → C) × (O → C), fieldWeight I ℓ (Sum.elim p.1 p.2)
  · exact Fintype.sum_equiv colouringEquiv _ _
      (fun σ => by congr 1; exact (colouringEquiv.left_inv σ).symm)
  simp only [Fintype.sum_prod_type, sum_fieldWeight I hsep]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem cut_fieldPartition {V : Type u} [Fintype V]
    (I : PinningData V C) (p : V → Prop)
    (hclosed : ∀ u, p u → ∀ w, I.graph.Adj u w → p w) (ℓ : V → C → ℂ) :
    fieldPartition I ℓ = fieldPartition (restrictData I p) (fieldPull Subtype.val ℓ) *
      fieldPartition (restrictData I (fun v => ¬ p v)) (fieldPull Subtype.val ℓ) := by
  rw [← fieldPartition_relabel I (cutEquiv p)]
  apply sum_fieldPartition
  intro u o hadj
  exact o.property (hclosed u.val u.property o.val hadj)

theorem optionChild_field_factorization (I : PinningData (Option O) C) (a : C)
    (ℓ : O → C → ℂ) :
    fieldPartition (optionChildData I a) ℓ =
      fieldPartition (optionComponentChildData I a) (fieldPull Subtype.val ℓ) *
        fieldPartition (optionCommonRemainderData I) (fieldPull Subtype.val ℓ) := by
  rw [cut_fieldPartition _ _ (optionInRootComponent_closed I a),
    optionChild_remainder_eq_common]
  rfl

theorem optionChild_curve_factorization (I : PinningData (Option O) C) (a : C)
    (d : O → C → ℂ) (z : ℂ) :
    fieldCurve (optionChildData I a) d z =
      fieldCurve (optionComponentChildData I a) (fieldPull Subtype.val d) z *
        fieldCurve (optionCommonRemainderData I) (fieldPull Subtype.val d) z :=
  optionChild_field_factorization I a (fieldLine d z)

theorem small_component_curve_response [Nonempty C]
    (F : PinningFamily.{u, v} C) (I : PinningData (Option O) C) (hI : F.contains I)
    {Δ B : ℕ} (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C)
    (hB : Fintype.card (Component.RootComponent I.graph none) ≤ B)
    {α r : ℝ} (hα : 0 < α) (hr : 0 < r) (hrB : r ≤ localFieldRadius B α)
    (hNZ : SmallerCurvesNonzero F Δ (Fintype.card (Option O)) r)
    (d : Option O → C → ℂ) (hdir : DirectionBound d) : CurveRootResponses I d r α := by
  let d' := fieldPull some d
  have hE : CurveNonzeroOn (optionCommonRemainderData I) (fieldPull Subtype.val d') r :=
    hNZ _ (F.commonRemainder_mem hI) (optionCommonRemainderData_degreeBound I hd)
      (optionCommonRemainder_card_lt_parent I) _ ((hdir.pull some).pull _)
  have hlocal (a : C) := bounded_fieldCurve_log_control (optionComponentChildData I a)
    (fieldPartition_one_ne_zero _ (optionComponentChildData_degreeBound I hd a) hq)
    ((optionComponentChild_card_le I).trans hB) hα hrB
    (fieldPull Subtype.val d') ((hdir.pull some).pull _)
  let L (a : C) := principalResponseLog
    (fieldCurve (optionComponentChildData I a) (fieldPull Subtype.val d')) 0
  intro a b
  refine ⟨fun z => L a z - L b z, ?_, (hlocal a).2.1.sub (hlocal b).2.1, ?_, ?_⟩
  · simp only [L, (hlocal a).1, (hlocal b).1, sub_self]
  · intro z hz
    rw [Complex.exp_sub, (hlocal a).2.2.1 z hz, (hlocal b).2.2.1 z hz]
    simp only [optionChild_curve_factorization]
    rw [mul_div_mul_comm, mul_div_mul_comm]
    exact (mul_div_mul_right _ _ (div_ne_zero (hE z hz) (hE 0 (Metric.mem_ball_self hr)))).symm
  · intro z hz
    exact (norm_sub_le _ _).trans (by linarith [(hlocal a).2.2.2 z hz, (hlocal b).2.2.2 z hz])

end
end ZeroFreeness.LeeYang
