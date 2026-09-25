import ZeroFreeness.Potts.Transfer.PositiveFamilyTransfer
import ZeroFreeness.Potts.Geometry.GraphClassInputs
import ZeroFreeness.Potts.Geometry.RootLawRelabel
import ZeroFreeness.Potts.Geometry.GraphClassCoupling

/-! The positive-base response induction in the original graph and
partial-colouring notation, without a hard colour-slack assumption. -/
namespace ZeroFreeness.Potts
open PottsCI PottsCI.FinDist Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {A : Type u} {C : Type v} [Fintype A] [Fintype C]

/-- Reindexing the chosen original root as `none` does not alter either
actual normalized child partition function. -/
theorem option_root_partition_eq_pinVertex (tau : PartialColouring A C) (G : SimpleGraph A)
    (s : tau.FreeVertex) (a : C) (z : ℂ) :
    pinningProductPartition (optionChildData (rootOptionData (tau.toPinningData G) s) a) z =
      normalizedPartition (pinVertex tau s a) G z := by
  let e := (rootOptionEquiv s).symm
  have he := rootChildData_relabel_of_parent tau G e
    (rootOptionData (tau.toPinningData G) s) rfl a
  rw [← he, pinningProductPartition_relabel]
  exact pinningProductPartition_toPinningData (pinVertex tau s a) G z

end
end ZeroFreeness.Potts

namespace ZeroFreeness.Potts.GraphClass
open PottsCI PottsCI.FinDist Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

/-- Return to every original graph and arbitrary pinning, including the
actual normalized one-root response logarithms. The radius is chosen
before all graphs, vertex sets, pinnings and base points. -/
theorem positive_zero_free_and_responses_of_family_ci (F : GraphClass.{u})
    (Δ : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Ioi 0) (cost : ℝ)
    (hCI : ∀ (x : ℝ) (hx : 0 < x), (x : ℂ) ∈ K →
      (F.pinningFamily C).PositiveRootCouplingBound Δ x hx cost) :
    ∃ ε > 0, ∃ α > 0, ∀ {A : Type u} [Fintype A] (G : SimpleGraph A), F.contains G →
      (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring A C,
      (∀ x ∈ K, ∀ z ∈ ball x ε, normalizedPartition tau G z ≠ 0) ∧
      ∀ (s : tau.FreeVertex) (a b : C), ∀ x ∈ K,
        HasSmallResponseLog (fun z => normalizedPartition (pinVertex tau s a) G z)
          (fun z => normalizedPartition (pinVertex tau s b) G z) x ε α := by
  obtain ⟨ε, hε, α, hα, hnz, hresp⟩ :=
    (F.pinningFamily C).positive_uniform_transfer_of_positive_ci Δ K hK hreal cost hCI
  refine ⟨ε, hε, α, hα, ?_⟩
  intro A _ G hG hd tau
  have hmem := F.original_pinning_mem C G hG tau
  have hdegree := tau.degreeBound_of_original G hd
  constructor
  · intro x hx z hz
    have hn := hnz (tau.toPinningData G) hmem hdegree x hx z hz
    rwa [pinningProductPartition_toPinningData] at hn
  · intro s a b x hx
    have hrootmem : (F.pinningFamily C).contains (rootOptionData (tau.toPinningData G) s) :=
      (F.pinningFamily C).relabel_mem hmem (rootOptionEquiv s)
    have hdOption := rootOptionData_degreeBound (tau.toPinningData G) s hdegree
    have hresponse : OptionRootResponses
        (rootOptionData (tau.toPinningData G) s) x ε α := by
      apply hresp _ hrootmem _ x hx
      convert hdOption using 1
    obtain ⟨ℓ, hzero, hdiff, hexp, hbound⟩ :=
      hresponse a b
    refine ⟨ℓ, hzero, hdiff, ?_, hbound⟩
    intro z hz
    simpa only [option_root_partition_eq_pinVertex] using hexp z hz

/-- Original graph-class CI supplies exactly the positive Gibbs-law
input required by the family induction. No hard feasibility bound is used. -/
theorem positive_root_coupling_to_pinningFamily (F : GraphClass.{u}) (Δ : ℕ)
    {x : ℝ} (hx : 0 < x) {cost : ℝ}
    (hci : GraphClassRootCouplingBound F C ⟨x, hx.le⟩ cost) :
    (F.pinningFamily C).PositiveRootCouplingBound Δ x hx cost := by
  intro O _ I hI _ a b
  obtain ⟨A, hA, G, hG, ⟨R⟩⟩ := hI
  let : Fintype A := hA
  exact R.root_W_le_of_graphClass_ci F hG ⟨x, hx.le⟩ hci a b _ _

/-- The positive-base response lemma with CI stated on the original
induced-subgraph-closed class, uniformly on an arbitrary positive compact set. -/
theorem positive_zero_free_and_responses (F : GraphClass.{u})
    (Δ : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Ioi 0) (cost : ℝ)
    (hCI : ∀ (x : ℝ) (hx : 0 < x), (x : ℂ) ∈ K →
      GraphClassRootCouplingBound F C ⟨x, hx.le⟩ cost) :
    ∃ ε > 0, ∃ α > 0, ∀ {A : Type u} [Fintype A] (G : SimpleGraph A), F.contains G →
      (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring A C,
      (∀ x ∈ K, ∀ z ∈ ball x ε, normalizedPartition tau G z ≠ 0) ∧
      ∀ (s : tau.FreeVertex) (a b : C), ∀ x ∈ K,
        HasSmallResponseLog (fun z => normalizedPartition (pinVertex tau s a) G z)
          (fun z => normalizedPartition (pinVertex tau s b) G z) x ε α :=
  F.positive_zero_free_and_responses_of_family_ci Δ K hK hreal cost
    (fun x hx hxK => F.positive_root_coupling_to_pinningFamily Δ hx (hCI x hx hxK))

/-- The paper's standalone positive-base response conclusion on `[δ,1]`,
including every original pinning and root. The number of colours is only
assumed nonzero, without a hard-colouring extension threshold. -/
theorem positive_interval_zero_free_and_responses (F : GraphClass.{u})
    (Δ : ℕ) {δ : ℝ} (hδ : 0 < δ) (cost : ℝ)
    (hCI : ∀ (x : ℝ) (hx : 0 < x), x ∈ Icc δ 1 →
      GraphClassRootCouplingBound F C ⟨x, hx.le⟩ cost) :
    ∃ ε > 0, ∃ α > 0, ∀ {A : Type u} [Fintype A] (G : SimpleGraph A), F.contains G →
      (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring A C,
      (∀ x ∈ Icc δ 1, ∀ z ∈ ball (x : ℂ) ε, normalizedPartition tau G z ≠ 0) ∧
      ∀ (s : tau.FreeVertex) (a b : C), ∀ x ∈ Icc δ 1,
        HasSmallResponseLog (fun z => normalizedPartition (pinVertex tau s a) G z)
          (fun z => normalizedPartition (pinVertex tau s b) G z) (x : ℂ) ε α := by
  let K : Set ℂ := Complex.ofReal '' Icc δ 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hreal : K ⊆ Complex.ofReal '' Ioi 0 := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, hδ.trans_le ht.1, rfl⟩
  obtain ⟨ε, hε, α, hα, h⟩ := F.positive_zero_free_and_responses (C := C) Δ K hK hreal cost
    (fun x hx hxK => by
      obtain ⟨t, ht, htx⟩ := hxK
      have htx' : t = x := Complex.ofReal_injective htx
      subst t
      intro V _ G hG tau s a b ha hb
      exact hCI x hx ht G hG tau s a b ha hb)
  refine ⟨ε, hε, α, hα, ?_⟩
  intro A _ G hG hd tau
  obtain ⟨hn, hr⟩ := h G hG hd tau
  exact ⟨fun x hx => hn (x : ℂ) ⟨x, hx, rfl⟩,
    fun s a b x hx => hr s a b (x : ℂ) ⟨x, hx, rfl⟩⟩

end
end ZeroFreeness.Potts.GraphClass
