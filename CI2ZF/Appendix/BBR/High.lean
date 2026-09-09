import CI2ZF.Appendix.BBR.TotalInfluence
import CI2ZF.Appendix.BBR.Relative
import CI2ZF.Appendix.Girth.Transfer.Family
import CI2ZF.PositiveGraphClassTransfer

/-! The complete BBR interval: one girth and one coupling constant for
all activities, followed by the proved positive-base zero-free transfer.
The only literature parameters are the precise BBR local results, the
CLMM influence identity, and the two general CLMM graph-transfer inputs. -/
namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts CI2ZF.Potts.Separator Set Metric
open CI2ZF.Appendix.Girth
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

/-- Uniform coupling for the actual root-pinned Gibbs laws on the whole
closed BBR interval. In particular, the constant is chosen before x. -/
theorem high_girth_coupling
    (external : Literature C) (identity : InfluenceIdentity C) (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C) :
    ∃ (g : ℕ) (K : ℝ), 3 ≤ g ∧ 0 ≤ K ∧
      ∀ (x : ℝ) (hx : 0 < x), x ∈ Icc (start (Fintype.card C) Δ) 1 →
        (largeGirthFamily.{u,v} C g).PositiveRootCouplingBound Δ x hx K := by
  let x₀ := start (Fintype.card C) Δ
  let ρ := contractionRate Δ
  let A := totalInfluenceConstant (Fintype.card C) Δ x₀ / ρ
  let B := relativeConstant (Fintype.card C) Δ x₀
  have hx₀ := start_mem hq hr
  have hdq := degree_gt_colours (Nat.cast_pos.mpr Fintype.card_pos) hr
  have hdqn : Fintype.card C < Δ := by exact_mod_cast hdq
  have hΔ : 3 ≤ Δ := by omega
  have hρ := contractionRate_mem (show 2 ≤ Δ by omega)
  have hA : 0 < A := div_pos (totalInfluenceConstant_pos Fintype.card_pos (by omega) hx₀.1 hx₀.2) hρ.1
  have hB : 0 < B := by
    dsimp [B, relativeConstant]
    have hd : (0 : ℝ) < Δ := Nat.cast_pos.mpr (by omega)
    have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
    have hκ := (contractionSquare_mem (show 2 ≤ Δ by omega)).1
    have hx0 : 0 < x₀ := hx₀.1
    positivity
  have htree : ∀ (x : ℝ) (hx : x ∈ Icc x₀ 1),
      CLMM.TreeTID (C := C) Δ x (hx₀.1.trans_le hx.1) A ρ ∧
      CLMM.TreeRelative (C := C) Δ x B ρ 2 := by
    intro x hx
    constructor
    · intro d b t hd ht k a z
      have he : A * ρ ^ (k + 1) = totalInfluenceConstant (Fintype.card C) Δ x₀ * ρ ^ k := by
        dsimp [A]
        rw [pow_succ]
        have hr0 : ρ ≠ 0 := hρ.1.ne'
        field_simp [hr0]
      rw [he]
      exact total_influence_decay external identity hq hr hx d b t hd ht k a z
    · intro k _ d b t t' hdom hag hd ht ht' c
      exact root_relative_ssm external hq hr hx k d b t t' hd ht ht' hdom hag c
  obtain ⟨g, K, hg, hK, hc⟩ := CLMM.eventual_transfer transfer Δ hΔ A B ρ hA hB hρ.1 hρ.2
    2 (Icc x₀ 1) (fun _ hx => ⟨hx₀.1.trans_le hx.1, hx.2⟩) htree
  refine ⟨g, K, hg, hK, ?_⟩
  intro x hx hxI O _ I hI hd a b
  exact hc x hxI I hd hI a b _ _

/-- The BBR zero-free neighbourhood for every finite residual graph and
arbitrary nonnegative boundary counts obeying the degree budget. -/
theorem high_girth_zero_free
    (external : Literature C) (identity : InfluenceIdentity C) (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C) :
    ∃ g : ℕ, 3 ≤ g ∧ ∃ ε > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening ε (Complex.ofReal '' Icc (start (Fintype.card C) Δ) 1),
        pinningProductPartition I z ≠ 0 := by
  obtain ⟨g, K, hg, _, hci⟩ := high_girth_coupling external identity transfer Δ hq hr
  obtain ⟨ε, hε, hn⟩ := (largeGirthFamily.{u,v} C g).positive_interval_uniform_transfer_of_positive_ci
    Δ (start_mem hq hr).1 K hci
  refine ⟨g, hg, ε, hε, ?_⟩
  intro V _ I hgI hd z hz
  obtain ⟨w, ⟨x, hx, rfl⟩, hdw⟩ := mem_thickening_iff.mp hz
  exact hn I hgI hd x hx z hdw

/-- Original graph and pinning semantics, plus the actual one-root
response logarithms from the positive-base induction. -/
theorem high_girth_original_zero_free_and_responses
    (external : Literature C) (identity : InfluenceIdentity C) (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C) :
    ∃ g : ℕ, 3 ≤ g ∧ ∃ ε > 0, ∃ α > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (g : ℕ∞) ≤ G.egirth → (∀ v, G.degree v ≤ Δ) → ∀ tau : PartialColouring V C,
      (∀ z ∈ thickening ε (Complex.ofReal '' Icc (start (Fintype.card C) Δ) 1),
        normalizedPartition tau G z ≠ 0) ∧
      (∀ z ∈ thickening ε (Complex.ofReal '' Icc (start (Fintype.card C) Δ) 1),
        fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
      ∀ (r : tau.FreeVertex) (a b : C) (x : ℝ), x ∈ Icc (start (Fintype.card C) Δ) 1 →
        HasSmallResponseLog (fun z => normalizedPartition (pinVertex tau r a) G z)
          (fun z => normalizedPartition (pinVertex tau r b) G z) (x : ℂ) ε α := by
  obtain ⟨g, K, hg, _, hci⟩ := high_girth_coupling external identity transfer Δ hq hr
  let J : Set ℂ := Complex.ofReal '' Icc (start (Fintype.card C) Δ) 1
  have hJ : IsCompact J := isCompact_Icc.image Complex.continuous_ofReal
  have hreal : J ⊆ Complex.ofReal '' Ioi 0 := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, (start_mem hq hr).1.trans_le ht.1, rfl⟩
  obtain ⟨ε, hε, α, hα, hn, hresp⟩ :=
    (largeGirthFamily.{u,v} C g).positive_uniform_transfer_of_positive_ci Δ J hJ hreal K
      (fun x hx hxJ => by
        obtain ⟨t, ht, heq⟩ := hxJ
        have he := Complex.ofReal_injective heq
        subst t
        intro O _ I hI hd a b
        exact hci x hx ht I hI hd a b)
  refine ⟨g, hg, ε, hε, α, hα, ?_⟩
  intro V _ G hG hd tau
  have hfree : (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth :=
    hG.trans (SimpleGraph.Embedding.comap
      (⟨Subtype.val, Subtype.val_injective⟩ : tau.FreeVertex ↪ V) G).isContained.egirth_le
  have hdegree := tau.degreeBound_of_original G hd
  have hnorm : ∀ z ∈ thickening ε J, normalizedPartition tau G z ≠ 0 := by
    intro z hz
    obtain ⟨w, hw, hdw⟩ := mem_thickening_iff.mp hz
    have h := hn (tau.toPinningData G) hfree hdegree w hw z hdw
    rwa [pinningProductPartition_toPinningData] at h
  refine ⟨hnorm, fun z hz => fullPartition_eq_zero_iff_of_normalized_ne_zero tau G z (hnorm z hz), ?_⟩
  intro r a b x hx
  have hrootmem : (largeGirthFamily.{u,v} C g).contains (rootOptionData (tau.toPinningData G) r) :=
    (largeGirthFamily.{u,v} C g).relabel_mem hfree (rootOptionEquiv r)
  have hdOption := rootOptionData_degreeBound (tau.toPinningData G) r hdegree
  have hrsp : OptionRootResponses (rootOptionData (tau.toPinningData G) r) (x : ℂ) ε α := by
    apply hresp _ hrootmem _ (x : ℂ) ⟨x, hx, rfl⟩
    convert hdOption using 1
  obtain ⟨ℓ, hzero, hdiff, hexp, hbound⟩ := hrsp a b
  refine ⟨ℓ, hzero, hdiff, ?_, hbound⟩
  intro z hz
  simpa only [option_root_partition_eq_pinVertex] using hexp z hz

end
end CI2ZF.Appendix.BBR
