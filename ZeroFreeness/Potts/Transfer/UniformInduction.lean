import ZeroFreeness.Potts.Transfer.InductionState
import ZeroFreeness.Potts.Geometry.RootOptionRelabel

/-! A simultaneous strong induction over the number of actual free
vertices. At each size, root responses are proved before parent
nonvanishing. Both response hypotheses concern strictly smaller data. -/
namespace ZeroFreeness.Potts
open PottsCI Separator
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem pinningProductPartition_of_isEmpty {V : Type u} {C : Type v}
    [Fintype V] [Fintype C] [IsEmpty V] (I : PinningData V C) (z : ℂ) :
    pinningProductPartition I z = 1 := by
  have he : I.graph.edgeFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e _
    induction e using Sym2.ind with
    | _ a b => exact isEmptyElim a
  simp [pinningProductPartition, pinningProductWeight, he]

theorem partitionNonzeroOn_of_isEmpty {V : Type u} {C : Type v}
    [Fintype V] [Fintype C] [IsEmpty V] (I : PinningData V C)
    (x : ℂ) (r : ℝ) : PartitionNonzeroOn I x r := by
  intro z _
  rw [pinningProductPartition_of_isEmpty]
  exact one_ne_zero

/-- The induction engine. `response_step` uses only smaller partition
and response statements. `parent_step` receives the already established
current root responses and the smaller actual children. -/
theorem uniform_induction (C : Type v) [Fintype C] (Delta : ℕ)
    (x : ℂ) (r alpha : ℝ)
    (response_step : ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      I.DegreeBound Delta →
      SmallerPartitionsNonzero.{u, v} C Delta (Fintype.card (Option V)) x r →
      SmallerRootResponses.{u, v} C Delta (Fintype.card (Option V)) x r alpha →
      OptionRootResponses I x r alpha)
    (parent_step : ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      I.DegreeBound Delta →
      (∀ a : C, PartitionNonzeroOn (optionChildData I a) x r) →
      OptionRootResponses I x r alpha → PartitionNonzeroOn I x r) :
    (∀ {V : Type u} [Fintype V] (I : PinningData V C),
      I.DegreeBound Delta → PartitionNonzeroOn I x r) ∧
    ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      I.DegreeBound Delta → OptionRootResponses I x r alpha := by
  have hlevel : ∀ n : ℕ,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C),
        I.DegreeBound Delta → Fintype.card V = n → PartitionNonzeroOn I x r) ∧
      (∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
        I.DegreeBound Delta → Fintype.card (Option V) = n →
          OptionRootResponses I x r alpha) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hsmallNZ : SmallerPartitionsNonzero.{u, v} C Delta n x r := by
        intro V _ I hd hn
        exact (ih (Fintype.card V) hn).1 I hd rfl
      have hsmallResponse : SmallerRootResponses.{u, v} C Delta n x r alpha := by
        intro V _ I hd hn
        exact (ih (Fintype.card (Option V)) hn).2 I hd rfl
      have hcurrentResponse {V : Type u} [Fintype V]
          (I : PinningData (Option V) C) (hd : I.DegreeBound Delta)
          (hn : Fintype.card (Option V) = n) : OptionRootResponses I x r alpha := by
        apply response_step I hd
        · intro W _ J hdJ hJ
          exact hsmallNZ J hdJ (hJ.trans_eq hn)
        · intro W _ J hdJ hJ
          exact hsmallResponse J hdJ (hJ.trans_eq hn)
      refine ⟨?_, fun I hd hn => hcurrentResponse I hd hn⟩
      intro V _ I hd hn
      cases isEmpty_or_nonempty V with
      | inl hEmpty =>
        let := hEmpty
        exact partitionNonzeroOn_of_isEmpty I x r
      | inr hNonempty =>
        let := hNonempty
        let v : V := Classical.arbitrary V
        have hdOption := rootOptionData_degreeBound I v hd
        have hcard : Fintype.card (Option {w : V // w ≠ v}) = n :=
          (rootOptionData_card v).trans hn
        have hchild (a : C) :
            PartitionNonzeroOn (optionChildData (rootOptionData I v) a) x r := by
          apply hsmallNZ _ (optionChildData_degreeBound _ hdOption a)
          exact (rootDeletedData_card_lt v).trans_eq hn
        have hparent := parent_step (rootOptionData I v) hdOption hchild
          (hcurrentResponse _ hdOption hcard)
        intro z hz
        have hp := hparent z hz
        rwa [rootOptionData_partition] at hp
  exact ⟨fun I hd => (hlevel _).1 I hd rfl,
    fun I hd => (hlevel _).2 I hd rfl⟩

end
end ZeroFreeness.Potts
