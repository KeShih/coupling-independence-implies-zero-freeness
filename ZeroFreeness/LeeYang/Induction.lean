import ZeroFreeness.LeeYang.InductionState
import ZeroFreeness.LeeYang.TransportRelabel

/-! Strong induction on the number of free vertices, simultaneously for
nonvanishing and normalized root responses in every field direction. -/
namespace ZeroFreeness.LeeYang
open PottsCI ZeroFreeness.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C]

theorem uniform_curve_induction (F : PinningFamily.{u, v} C) (Δ : ℕ) (r α : ℝ)
    (response_step : ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      F.contains I → I.DegreeBound Δ →
      SmallerCurvesNonzero F Δ (Fintype.card (Option V)) r →
      SmallerCurveResponses F Δ (Fintype.card (Option V)) r α →
      ∀ d, DirectionBound d → CurveRootResponses I d r α)
    (parent_step : ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      F.contains I → I.DegreeBound Δ → ∀ d, DirectionBound d →
      (∀ a : C, CurveNonzeroOn (optionChildData I a) (fieldPull some d) r) →
      CurveRootResponses I d r α → CurveNonzeroOn I d r) :
    (∀ {V : Type u} [Fintype V] (I : PinningData V C),
      F.contains I → I.DegreeBound Δ → ∀ d, DirectionBound d → CurveNonzeroOn I d r) ∧
    ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
      F.contains I → I.DegreeBound Δ → ∀ d, DirectionBound d → CurveRootResponses I d r α := by
  have hlevel : ∀ n : ℕ,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
        I.DegreeBound Δ → Fintype.card V = n →
        ∀ d, DirectionBound d → CurveNonzeroOn I d r) ∧
      (∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C), F.contains I →
        I.DegreeBound Δ → Fintype.card (Option V) = n →
        ∀ d, DirectionBound d → CurveRootResponses I d r α) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have hsmallNZ : SmallerCurvesNonzero F Δ n r := by
        intro V _ I hI hd hn
        exact (ih (Fintype.card V) hn).1 I hI hd rfl
      have hsmallResponse : SmallerCurveResponses F Δ n r α := by
        intro V _ I hI hd hn
        exact (ih (Fintype.card (Option V)) hn).2 I hI hd rfl
      have hcurrentResponse {V : Type u} [Fintype V]
          (I : PinningData (Option V) C) (hI : F.contains I) (hd : I.DegreeBound Δ)
          (hn : Fintype.card (Option V) = n) :
          ∀ d, DirectionBound d → CurveRootResponses I d r α := by
        apply response_step I hI hd
        · intro W _ J hmJ hdJ hJ
          exact hsmallNZ J hmJ hdJ (hJ.trans_eq hn)
        · intro W _ J hmJ hdJ hJ
          exact hsmallResponse J hmJ hdJ (hJ.trans_eq hn)
      refine ⟨?_, fun I hI hd hn => hcurrentResponse I hI hd hn⟩
      intro V _ I hI hd hn d hdir
      cases isEmpty_or_nonempty V with
      | inl hEmpty =>
        let := hEmpty
        exact curveNonzeroOn_of_isEmpty I d r
      | inr hNonempty =>
        let := hNonempty
        let w : V := Classical.arbitrary V
        let d' := fieldPull (rootOptionEquiv w).symm d
        have hdir' : DirectionBound d' := hdir.pull _
        have hmOption : F.contains (rootOptionData I w) := F.relabel_mem hI (rootOptionEquiv w)
        have hdOption := rootOptionData_degreeBound I w hd
        have hcard : Fintype.card (Option {v : V // v ≠ w}) = n :=
          (rootOptionData_card w).trans hn
        have hchild (a : C) :
            CurveNonzeroOn (optionChildData (rootOptionData I w) a) (fieldPull some d') r := by
          exact hsmallNZ _ (F.optionChild_mem hmOption a) (optionChildData_degreeBound _ hdOption a)
            ((rootDeletedData_card_lt w).trans_eq hn) _ (hdir'.pull _)
        have hparent := parent_step (rootOptionData I w) hmOption hdOption d' hdir' hchild
          (hcurrentResponse _ hmOption hdOption hcard d' hdir')
        intro z hz
        have hp := hparent z hz
        change fieldPartition (rootOptionData I w)
          (fieldLine (fieldPull (rootOptionEquiv w).symm d) z) ≠ 0 at hp
        simpa only [← fieldPull_fieldLine, fieldPartition_rootOption, fieldCurve] using hp
  exact ⟨fun I hI hd => (hlevel _).1 I hI hd rfl,
    fun I hI hd => (hlevel _).2 I hI hd rfl⟩

end
end ZeroFreeness.LeeYang
