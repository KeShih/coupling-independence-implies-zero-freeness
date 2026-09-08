import CI2ZF.Appendix.GirthRatioMixing
import CI2ZF.Appendix.GirthFamily
import CI2ZF.Appendix.CLMMTransfer

/-!
# The large-girth Potts theorem at q ≥ Δ + 3

All Potts recursion, differential, norm, finite-difference, spatial-mixing,
and parameter-uniformity estimates are proved in the imported `Girth`
modules. The only external parameters are the explicitly cited general
CLMM influence identity (Lemma 8.7), sphere estimate (Equation (10)), and
sphere-to-coupling theorem (Lemma 5.13). The uniform burn-in, graph CI,
both real endpoints, and zero-free transfer are then proved here.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts CI2ZF.Potts.Separator Set Metric
open CavityTree

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

theorem high_girth_soft_coupling
    (identity : CLMMInfluenceIdentity C) (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ (g : ℕ) (K : ℝ), 3 ≤ g ∧ 0 ≤ K ∧ SoftLargeGirthCoupling.{u,v} C Δ g K := by
  let q : ℝ := Fintype.card C
  let ρ := decayRate q
  let A := totalInfluenceConstant Δ q / ρ
  let B := 2 * relativeMixingConstant Δ q / ρ ^ 2
  have hq0 : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hd0 : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hr : 0 < ρ := decayRate_pos q
  have hr1 : ρ < 1 := decayRate_lt_one hq0
  have hA : 0 < A := by
    dsimp [A, totalInfluenceConstant]
    positivity
  have hB : 0 < B := by
    dsimp [B, relativeMixingConstant]
    have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
    positivity
  obtain ⟨k₀, hk₀⟩ := eventual_ratio_spatial_mixing (C := C) hq
  have htree : ∀ (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1),
      CLMM.TreeTID (C := C) Δ x hx.1 A ρ ∧
      CLMM.TreeRelative (C := C) Δ x B ρ (k₀ + 2) := by
    intro x hx
    constructor
    · intro d b t hd ht k a z
      have he : A * ρ ^ (k + 1) = totalInfluenceConstant Δ q * ρ ^ k := by
        dsimp [A]
        rw [pow_succ]
        field_simp
      rw [he]
      exact total_influence_decay identity x hx.1 hx.2 hq d b t hd ht k a z
    · intro k hk d b t t' _ hs hd ht ht' c
      have he : B * ρ ^ (k + 2) = 2 * relativeMixingConstant Δ q * ρ ^ k := by
        dsimp [B]
        rw [pow_add]
        field_simp
      rw [he]
      exact hk₀ k (by omega) d b t t' hs x hx.1 hx.2 hd ht ht' c
  obtain ⟨g, K, hg, hK, hcouple⟩ := CLMM.eventual_transfer transfer Δ hΔ A B ρ hA hB hr hr1
    (k₀ + 2) (Ioo 0 1) (fun _ hx => ⟨hx.1, hx.2.le⟩) htree
  refine ⟨g, K, hg, hK, ?_⟩
  intro O _ I hd hgI a b x hx hx1
  exact hcouple x ⟨hx, hx1⟩ I hd hgI a b
    ((optionChildData I a).partition_pos_of_parameter_pos hx)
    ((optionChildData I b).partition_pos_of_parameter_pos hx)

/-- The appendix's graph- and activity-uniform coupling theorem, including
proper-colouring activity zero and the common product law at activity one. -/
theorem high_girth_coupling
    (identity : CLMMInfluenceIdentity C) (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ (g : ℕ) (K : ℝ), 3 ≤ g ∧ 0 ≤ K ∧
      ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ≤ 1 →
        (largeGirthFamily.{u,v} C g).RootCouplingBound Δ (by omega) x K := by
  obtain ⟨g, K, hg, hK, hsoft⟩ := high_girth_soft_coupling identity transfer Δ hΔ hq
  exact ⟨g, K, hg, hK, fun x hx => closed_root_coupling_of_soft (by omega) hK hsoft x hx⟩

/-- A single complex neighbourhood works for all graph sizes, pinnings,
and activities in `[0,1]` when q ≥ Δ+3 and the residual girth is large. -/
theorem high_girth_zero_free
    (identity : CLMMInfluenceIdentity C) (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ (g : ℕ), 3 ≤ g ∧ ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0 := by
  obtain ⟨g, K, hg, hK, hsoft⟩ := high_girth_soft_coupling identity transfer Δ hΔ hq
  exact ⟨g, hg, large_girth_zero_free_of_soft_ci (by omega) hK hsoft⟩

/-- Original-graph semantics, including arbitrary improper pinnings: the
normalized partition has no zero in the uniform neighbourhood, and the
full partition retains exactly its forced pinned-conflict zero. -/
theorem high_girth_original_zero_free
    (identity : CLMMInfluenceIdentity C) (transfer : CLMM.Literature.{u,v} C)
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ (g : ℕ), 3 ≤ g ∧ ∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (g : ℕ∞) ≤ G.egirth → (∀ v, G.degree v ≤ Δ) → ∀ tau : PartialColouring V C,
      (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
      (∀ z ∈ thickening eps pottsInterval,
        fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
      (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G := by
  obtain ⟨g, hg, eps, heps, hnz⟩ := high_girth_zero_free identity transfer Δ hΔ hq
  have hzero : (0 : ℂ) ∈ thickening eps pottsInterval := by
    apply mem_thickening_iff.mpr
    exact ⟨0, ⟨0, by simp, rfl⟩, by simpa using heps⟩
  refine ⟨g, hg, eps, heps, ?_⟩
  intro V _ G hG hd tau
  have hfree : (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth :=
    hG.trans (SimpleGraph.Embedding.comap
      (⟨Subtype.val, Subtype.val_injective⟩ : tau.FreeVertex ↪ V) G).isContained.egirth_le
  have hnorm : ∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0 := by
    intro z hz
    have h := hnz (tau.toPinningData G) hfree (tau.degreeBound_of_original G hd) z hz
    rwa [pinningProductPartition_toPinningData] at h
  exact ⟨hnorm, fun z hz => fullPartition_eq_zero_iff_of_normalized_ne_zero tau G z (hnorm z hz),
    fullPolynomial_rootMultiplicity_zero_of_normalized_ne_zero tau G (hnorm 0 hzero)⟩

end

end CI2ZF.Appendix.Girth
