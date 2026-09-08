import CI2ZF.PinningRestrictionInstances
import CI2ZF.InductionComponentSteps
import CI2ZF.UniformInduction

/-! The simultaneous induction predicates restricted to actual members
of a pinning family. They do not quantify over unrelated instances. -/
namespace CI2ZF.Potts.PinningFamily
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C]

def SmallerPartitionsNonzero (F : PinningFamily.{u, v} C) (Δ n : ℕ)
    (x : ℂ) (r : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
    I.DegreeBound Δ → Fintype.card V < n → PartitionNonzeroOn I x r

def SmallerRootResponses (F : PinningFamily.{u, v} C) (Δ n : ℕ)
    (x : ℂ) (r α : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C), F.contains I →
    I.DegreeBound Δ → Fintype.card (Option V) < n → OptionRootResponses I x r α

theorem commonRemainder_mem (F : PinningFamily.{u, v} C)
    {O : Type u} [Fintype O] {I : PinningData (Option O) C} (hI : F.contains I) :
    F.contains (Component.optionCommonRemainderData I) := by
  convert F.cut_mem (F.optionMiddle_mem hI) (fun o => ¬ Component.optionInRootComponent I o) using 1
  congr 1

theorem positive_small_component_response_step
    (F : PinningFamily.{u, v} C) {O : Type u} [Fintype O]
    {Δ B : ℕ} {K : Set ℂ} {x : ℂ} {r α : ℝ}
    (hlocal : PositiveLocalControls.{u, v} C Δ B K r α)
    (ha : 0 ≤ α) (hx : x ∈ K) (I : PinningData (Option O) C) (hI : F.contains I)
    (hd : I.DegreeBound Δ) (hB : Fintype.card (Component.RootComponent I.graph none) ≤ B)
    (hNZ : F.SmallerPartitionsNonzero Δ (Fintype.card (Option O)) x r) :
    OptionRootResponses I x r α := by
  have hE : PartitionNonzeroOn (Component.optionCommonRemainderData I) x r :=
    hNZ _ (F.commonRemainder_mem hI) (Component.optionCommonRemainderData_degreeBound I hd)
      (Component.optionCommonRemainder_card_lt_parent I)
  intro a b
  exact HasSmallResponseLog.mono_bound (hlocal.component I hd hB x hx hE a b) (by linarith)

theorem hard_small_component_response_step
    (F : PinningFamily.{u, v} C) {O : Type u} [Fintype O]
    {Δ B : ℕ} {r α : ℝ} (hlocal : HardLocalControls.{u, v} C Δ B r α)
    (ha : 0 ≤ α) (I : PinningData (Option O) C) (hI : F.contains I)
    (hd : I.DegreeBound Δ) (hB : Fintype.card (Component.RootComponent I.graph none) ≤ B)
    (hNZ : F.SmallerPartitionsNonzero Δ (Fintype.card (Option O)) 0 r) :
    OptionRootResponses I 0 r α := by
  have hE : PartitionNonzeroOn (Component.optionCommonRemainderData I) 0 r :=
    hNZ _ (F.commonRemainder_mem hI) (Component.optionCommonRemainderData_degreeBound I hd)
      (Component.optionCommonRemainder_card_lt_parent I)
  intro a b
  exact HasSmallResponseLog.mono_bound (hlocal.component I hd hB hE a b) (by linarith)

/-- Strong induction first proves the current root response, then the
current nonvanishing statement. Every use of the induction hypotheses
carries an actual family-membership proof. -/
theorem uniform_induction (F : PinningFamily.{u, v} C) (Δ : ℕ)
    (x : ℂ) (r α : ℝ)
    (response_step : ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      F.contains I → I.DegreeBound Δ →
      F.SmallerPartitionsNonzero Δ (Fintype.card (Option V)) x r →
      F.SmallerRootResponses Δ (Fintype.card (Option V)) x r α → OptionRootResponses I x r α)
    (parent_step : ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      F.contains I → I.DegreeBound Δ →
      (∀ a : C, PartitionNonzeroOn (optionChildData I a) x r) →
      OptionRootResponses I x r α → PartitionNonzeroOn I x r) :
    (∀ {V : Type u} [Fintype V] (I : PinningData V C),
      F.contains I → I.DegreeBound Δ → PartitionNonzeroOn I x r) ∧
    ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      F.contains I → I.DegreeBound Δ → OptionRootResponses I x r α := by
  have hlevel : ∀ n : ℕ,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
        I.DegreeBound Δ → Fintype.card V = n → PartitionNonzeroOn I x r) ∧
      (∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C), F.contains I →
        I.DegreeBound Δ → Fintype.card (Option V) = n → OptionRootResponses I x r α) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hsmallNZ : F.SmallerPartitionsNonzero Δ n x r := by
        intro V _ I hI hd hn
        exact (ih (Fintype.card V) hn).1 I hI hd rfl
      have hsmallResponse : F.SmallerRootResponses Δ n x r α := by
        intro V _ I hI hd hn
        exact (ih (Fintype.card (Option V)) hn).2 I hI hd rfl
      have hcurrentResponse {V : Type u} [Fintype V]
          (I : PinningData (Option V) C) (hI : F.contains I) (hd : I.DegreeBound Δ)
          (hn : Fintype.card (Option V) = n) : OptionRootResponses I x r α := by
        apply response_step I hI hd
        · intro W _ J hmJ hdJ hJ
          exact hsmallNZ J hmJ hdJ (hJ.trans_eq hn)
        · intro W _ J hmJ hdJ hJ
          exact hsmallResponse J hmJ hdJ (hJ.trans_eq hn)
      refine ⟨?_, fun I hI hd hn => hcurrentResponse I hI hd hn⟩
      intro V _ I hI hd hn
      cases isEmpty_or_nonempty V with
      | inl hEmpty =>
        let := hEmpty
        exact partitionNonzeroOn_of_isEmpty I x r
      | inr hNonempty =>
        let := hNonempty
        let w : V := Classical.arbitrary V
        have hmOption : F.contains (rootOptionData I w) := F.relabel_mem hI (rootOptionEquiv w)
        have hdOption := rootOptionData_degreeBound I w hd
        have hcard : Fintype.card (Option {v : V // v ≠ w}) = n :=
          (rootOptionData_card w).trans hn
        have hchild (a : C) :
            PartitionNonzeroOn (optionChildData (rootOptionData I w) a) x r := by
          apply hsmallNZ _ (F.optionChild_mem hmOption a) (optionChildData_degreeBound _ hdOption a)
          exact (rootDeletedData_card_lt w).trans_eq hn
        have hparent := parent_step (rootOptionData I w) hmOption hdOption hchild
          (hcurrentResponse _ hmOption hdOption hcard)
        intro z hz
        have hp := hparent z hz
        rwa [rootOptionData_partition] at hp
  exact ⟨fun I hI hd => (hlevel _).1 I hI hd rfl,
    fun I hI hd => (hlevel _).2 I hI hd rfl⟩

end
end CI2ZF.Potts.PinningFamily
