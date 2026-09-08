import CI2ZF.FamilyBFSResponseSteps
import CI2ZF.FamilyCouplingInputs
import CI2ZF.InductionParentSteps

/-! Uniform Potts transfer restricted to an actual pinning family.
Only CI for members of that family is assumed; all smaller instances
are justified by the family's restriction and repinning closure. -/
namespace CI2ZF.Potts.PinningFamily
open PottsCI Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

theorem positive_uniform_transfer (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (K : Set ℂ)
    (hK : IsCompact K) (hreal : K ⊆ Complex.ofReal '' Ioi 0)
    (cost : ℝ)
    (hCI : ∀ (x : ℝ) (hx : 0 < x), (x : ℂ) ∈ K →
      F.RootCouplingBound Δ hq ⟨x, hx.le⟩ cost) :
    ∃ r > 0, ∃ alpha > 0,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
        I.DegreeBound Δ → ∀ x ∈ K, PartitionNonzeroOn I x r) ∧
      ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C), F.contains I →
        I.DegreeBound Δ → ∀ x ∈ K, OptionRootResponses I x r alpha := by
  obtain ⟨L, B, hL, hcost, hB, alpha, ha, ha1, haB⟩ :=
    exists_geometric_transfer_scales Δ cost
  obtain ⟨r, hr, hcontrols⟩ := exists_positive_local_controls.{u, v} C Δ B K hK hreal ha
  have hlocal := hcontrols r hr le_rfl
  have hbase (x : ℝ) (hx : 0 < x) (hxK : (x : ℂ) ∈ K) := by
    apply F.uniform_induction Δ (x : ℂ) r alpha
    · intro O _ I hI hd hNZ hRoot
      by_cases hsmall : Fintype.card (Component.RootComponent I.graph none) ≤ B
      · exact F.positive_small_component_response_step hlocal ha.le hxK I hI hd hsmall hNZ
      · intro a b
        apply F.positive_bfs_response_step I hI a b hd hL hB
          (Nat.lt_of_not_ge hsmall) hx hr ha.le (by linarith) (by linarith) hcost
        · exact hCI x hx hxK I hI hd a b
        · exact hNZ
        · exact hRoot
        · intro U S E _ _ _ J hdJ hcard ξ
          exact hlocal.inside J hdJ hcard ξ (x : ℂ) hxK
    · intro O _ I _ hd hchildren hresponses
      exact positive_parent_step_of_local_controls hlocal (by linarith) hx hxK
        I hd hchildren hresponses
  refine ⟨r, hr, alpha, ha, ?_, ?_⟩
  · intro V _ I hI hd x hx
    obtain ⟨t, ht, rfl⟩ := hreal hx
    exact (hbase t ht hx).1 I hI hd
  · intro V _ I hI hd x hx
    obtain ⟨t, ht, rfl⟩ := hreal hx
    exact (hbase t ht hx).2 I hI hd

theorem positive_interval_uniform_transfer (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) {δ : ℝ} (hδ : 0 < δ)
    (cost : ℝ)
    (hCI : ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ∈ Icc δ 1 →
      F.RootCouplingBound Δ hq x cost) :
    ∃ r > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
      I.DegreeBound Δ → ∀ x ∈ Icc δ 1, PartitionNonzeroOn I (x : ℂ) r := by
  let K : Set ℂ := Complex.ofReal '' Icc δ 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hreal : K ⊆ Complex.ofReal '' Ioi 0 := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, hδ.trans_le ht.1, rfl⟩
  obtain ⟨r, hr, _, _, hn, _⟩ := F.positive_uniform_transfer Δ hq K hK hreal cost
    (fun x hx hxK => by
      obtain ⟨t, ht, htx⟩ := hxK
      have htx' : t = x := Complex.ofReal_injective htx
      subst t
      intro O _ I hI hd a b
      exact hCI ⟨x, hx.le⟩ ht I hI hd a b)
  exact ⟨r, hr, fun I hI hd x hx => hn I hI hd (x : ℂ) ⟨x, hx, rfl⟩⟩

theorem hard_uniform_transfer (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : F.RootCouplingBound Δ hq PinningData.hardParameter cost) :
    ∃ r > 0, ∃ alpha > 0,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
        I.DegreeBound Δ → PartitionNonzeroOn I 0 r) ∧
      ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C), F.contains I →
        I.DegreeBound Δ → OptionRootResponses I 0 r alpha := by
  obtain ⟨L, B, hL, hcost, hB, alpha, ha, ha1, haB⟩ :=
    exists_geometric_transfer_scales Δ cost
  obtain ⟨eps, heps, hcontrols⟩ := exists_hard_local_controls.{u, v} C Δ B hq ha
  obtain ⟨r, hr, hre, hr1, hdefect, hparent⟩ :=
    exists_hard_transfer_radius (Fintype.card C) Δ B ha heps
  have hlocal := hcontrols r hr hre
  refine ⟨r, hr, alpha, ha, ?_⟩
  apply F.uniform_induction Δ 0 r alpha
  · intro O _ I hI hd hNZ hRoot
    by_cases hsmall : Fintype.card (Component.RootComponent I.graph none) ≤ B
    · exact F.hard_small_component_response_step hlocal ha.le I hI hd hsmall hNZ
    · intro a b
      apply F.hard_bfs_response_step I hI a b hd hq hL hB
        (Nat.lt_of_not_ge hsmall) hr hr1 ha.le ha1 haB hcost
      · exact hCI I hI hd a b
      · exact hNZ
      · exact hRoot
      · exact hdefect
  · intro O _ I _ hd hchildren hresponses
    exact hard_parent_step hq (by linarith) hr1 hparent.le I hd hchildren hresponses

/-- The endpoint and positive intervals are patched with one radius
chosen before all family members, graph sizes and pinnings. -/
theorem uniform_transfer_zero_free (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (hCI : F.TransferCouplingInputs Δ hq) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
      I.DegreeBound Δ → ∀ z ∈ thickening eps pottsInterval,
        pinningProductPartition I z ≠ 0 := by
  obtain ⟨cost, hc⟩ := hCI.hard
  obtain ⟨rho, hrho, _, _, hzero, _⟩ := F.hard_uniform_transfer Δ hq cost hc
  let δ : ℝ := min (1 / 2) (rho / 4)
  have hd : 0 < δ := lt_min (by norm_num) (by positivity)
  have hdhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hdrho : δ ≤ rho / 4 := min_le_right _ _
  obtain ⟨cp, hcp⟩ := hCI.positive δ hd (by linarith)
  obtain ⟨ep, hep, hp⟩ := F.positive_interval_uniform_transfer Δ hq hd cp hcp
  refine ⟨min ep δ, lt_min hep hd, ?_⟩
  intro V _ I hI hdegree z hz
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
  obtain ⟨x, hx, rfl⟩ := hw
  by_cases hxd : x ≤ δ
  · apply hzero I hI hdegree z
    have hdist : dist z (x : ℂ) < δ := lt_of_lt_of_le hzw (min_le_right _ _)
    have hnorm : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    have htri : ‖z‖ ≤ dist z (x : ℂ) + ‖(x : ℂ)‖ := by
      simpa only [dist_zero_right] using dist_triangle z (x : ℂ) 0
    rw [hnorm] at htri
    rw [mem_ball, dist_zero_right]
    linarith
  · exact hp I hI hdegree x ⟨le_of_not_ge hxd, hx.2⟩ z
      (lt_of_lt_of_le hzw (min_le_left _ _))

end
end CI2ZF.Potts.PinningFamily
