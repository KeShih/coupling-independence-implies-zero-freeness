import CI2ZF.LeeYang.Model

/-! Original-graph semantics of the normalized and full hard field
partition functions, including arbitrary improper partial colourings. -/

namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]

/-- The actual free-field sum omits all pinned-only constraints. -/
def normalizedFieldPartition (tau : PartialColouring V C) (G : SimpleGraph V)
    (ℓ : V → C → ℂ) : ℂ :=
  ∑ σ : tau.FreeVertex → C,
    if tau.boundaryConflictCount G σ + tau.freeConflictCount G σ = 0
    then ∏ v : tau.FreeVertex, ℓ v.val (σ v) else 0

/-- The ordinary pinned field sum counts exactly proper full extensions. -/
def fullFieldPartition (tau : PartialColouring V C) (G : SimpleGraph V)
    (ℓ : V → C → ℂ) : ℂ :=
  ∑ σ : tau.FreeVertex → C,
    if tau.fullConflictCount G σ = 0 then ∏ v : V, ℓ v (tau.extend σ v) else 0

def pinnedFieldProduct (tau : PartialColouring V C) (ℓ : V → C → ℂ) : ℂ :=
  ∏ v : tau.domain, ℓ v.val (tau.colour v)

def ProperPinning (tau : PartialColouring V C) (G : SimpleGraph V) : Prop :=
  tau.pinnedConflictCount G = 0

theorem hardAdmissible_toPinningData_iff (tau : PartialColouring V C)
    (G : SimpleGraph V) (σ : tau.FreeVertex → C) :
    (tau.toPinningData G).HardAdmissible σ ↔
      tau.boundaryConflictCount G σ + tau.freeConflictCount G σ = 0 := by
  have h := tau.childWeight_eq_pow G (0 : ℝ) σ
  rw [(tau.toPinningData G).weight_zero_eq, ← pow_add] at h
  by_cases ha : (tau.toPinningData G).HardAdmissible σ <;>
    by_cases hz : tau.boundaryConflictCount G σ + tau.freeConflictCount G σ = 0 <;>
    simp_all

theorem normalizedFieldPartition_eq (tau : PartialColouring V C) (G : SimpleGraph V)
    (ℓ : V → C → ℂ) :
    normalizedFieldPartition tau G ℓ =
      fieldPartition (tau.toPinningData G) (fun v => ℓ v.val) := by
  unfold normalizedFieldPartition fieldPartition fieldWeight
  simp_rw [hardAdmissible_toPinningData_iff]
  congr 2
  exact Subsingleton.elim _ _

@[simp] theorem normalizedFieldPartition_one (tau : PartialColouring V C)
    (G : SimpleGraph V) :
    normalizedFieldPartition tau G oneField = normalizedPartition tau G 0 := by
  rw [normalizedPartition_eq_sum]
  unfold normalizedFieldPartition
  apply Finset.sum_congr (by ext; simp)
  intro σ _
  by_cases h : tau.boundaryConflictCount G σ + tau.freeConflictCount G σ = 0
  · rw [if_pos h, h, pow_zero]
    simp [oneField]
  · rw [if_neg h, zero_pow h]

theorem normalizedFieldPartition_one_ne_zero [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : Δ + 1 ≤ Fintype.card C) :
    normalizedFieldPartition tau G oneField ≠ 0 := by
  rw [normalizedFieldPartition_one]
  exact normalizedPartition_zero_ne_zero tau G hdegree hq

theorem properPinning_iff (tau : PartialColouring V C) (G : SimpleGraph V) :
    ProperPinning tau G ↔
      ∀ u v : tau.domain, G.Adj u.val v.val → tau.colour u ≠ tau.colour v := by
  unfold ProperPinning PartialColouring.pinnedConflictCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h u v huv heq
    apply h s(u.val, v.val)
    simp only [PartialColouring.pinnedConflictEdges, Finset.mem_filter,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      PartialColouring.pinnedSameColour_mk]
    exact ⟨huv, u.property, v.property, heq⟩
  · intro h e he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [PartialColouring.pinnedConflictEdges, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        PartialColouring.pinnedSameColour_mk] at he
      obtain ⟨huv, hu, hv, hc⟩ := he
      exact h ⟨u, hu⟩ ⟨v, hv⟩ huv hc

theorem fullConflictCount_zero_iff (tau : PartialColouring V C) (G : SimpleGraph V)
    (σ : tau.FreeVertex → C) :
    tau.fullConflictCount G σ = 0 ↔
      ∀ u v, G.Adj u v → tau.extend σ u ≠ tau.extend σ v := by
  unfold PartialColouring.fullConflictCount
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h u v huv heq
    apply h s(u, v)
    simp [PartialColouring.fullConflictEdges, huv, heq]
  · intro h e he
    induction e using Sym2.ind with
    | _ u v =>
      simp only [PartialColouring.fullConflictEdges, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
        PartialColouring.fullSameColour_mk] at he
      exact h u v he.1 he.2

theorem fullFieldPartition_eq_proper_extensions (tau : PartialColouring V C)
    (G : SimpleGraph V) (ℓ : V → C → ℂ) :
    fullFieldPartition tau G ℓ =
      ∑ σ : {σ : V → C // tau.Extends σ},
        if (∀ u v, G.Adj u v → σ.val u ≠ σ.val v)
        then ∏ v, ℓ v (σ.val v) else 0 := by
  unfold fullFieldPartition
  simp_rw [fullConflictCount_zero_iff]
  exact Fintype.sum_equiv tau.extensionEquiv _ _ (fun _ => rfl)

theorem fieldProduct_extend (tau : PartialColouring V C) (ℓ : V → C → ℂ)
    (σ : tau.FreeVertex → C) :
    (∏ v : V, ℓ v (tau.extend σ v)) =
      pinnedFieldProduct tau ℓ * ∏ v : tau.FreeVertex, ℓ v.val (σ v) := by
  let e : tau.domain ⊕ tau.FreeVertex ≃ V := Equiv.sumCompl (fun v => v ∈ tau.domain)
  have h : (∏ v : V, ℓ v (tau.extend σ v)) =
      ∏ v : tau.domain ⊕ tau.FreeVertex,
        Sum.elim (fun u => ℓ u.val (tau.colour u)) (fun u => ℓ u.val (σ u)) v := by
    symm
    apply Fintype.prod_equiv e
    intro v
    cases v with
    | inl v => exact (congrArg (ℓ v.val) (tau.extend_of_mem σ v.property)).symm
    | inr v => exact (congrArg (ℓ v.val) (tau.extend_of_not_mem σ v.property)).symm
  rw [Fintype.prod_sum_type] at h
  convert h using 1
  congr 2

theorem fullFieldPartition_eq (tau : PartialColouring V C) (G : SimpleGraph V)
    (ℓ : V → C → ℂ) :
    fullFieldPartition tau G ℓ =
      if ProperPinning tau G then pinnedFieldProduct tau ℓ *
        normalizedFieldPartition tau G ℓ else 0 := by
  unfold fullFieldPartition normalizedFieldPartition
  by_cases hp : ProperPinning tau G
  · rw [if_pos hp, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [tau.fullConflictCount_add]
    have hpin : tau.pinnedConflictCount G = 0 := hp
    rw [hpin, zero_add, fieldProduct_extend]
    split_ifs <;> simp
  · rw [if_neg hp]
    apply Finset.sum_eq_zero
    intro σ _
    have hn : tau.fullConflictCount G σ ≠ 0 := by
      rw [tau.fullConflictCount_add]
      unfold ProperPinning at hp
      omega
    exact if_neg hn

theorem fullFieldPartition_of_proper (tau : PartialColouring V C) (G : SimpleGraph V)
    (ℓ : V → C → ℂ) (hp : ProperPinning tau G) :
    fullFieldPartition tau G ℓ =
      pinnedFieldProduct tau ℓ * normalizedFieldPartition tau G ℓ := by
  rw [fullFieldPartition_eq, if_pos hp]

theorem fullFieldPartition_of_improper (tau : PartialColouring V C) (G : SimpleGraph V)
    (ℓ : V → C → ℂ) (hp : ¬ ProperPinning tau G) :
    fullFieldPartition tau G ℓ = 0 := by
  rw [fullFieldPartition_eq, if_neg hp]

theorem fullFieldPartition_ne_zero_of_proper (tau : PartialColouring V C)
    (G : SimpleGraph V) (ℓ : V → C → ℂ) (hp : ProperPinning tau G)
    (hpin : ∀ v : tau.domain, ℓ v.val (tau.colour v) ≠ 0)
    (hn : normalizedFieldPartition tau G ℓ ≠ 0) :
    fullFieldPartition tau G ℓ ≠ 0 := by
  rw [fullFieldPartition_of_proper tau G ℓ hp]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun v _ => hpin v) hn

end
end CI2ZF.LeeYang
