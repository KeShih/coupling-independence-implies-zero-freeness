import CI2ZF.Potts.Transfer.PositiveBFSResponseStep
import CI2ZF.Potts.Transfer.InductionComponentSteps
import CI2ZF.Potts.Transfer.InductionParentSteps
import CI2ZF.Potts.Transfer.UniformInduction
import CI2ZF.Potts.Transfer.TransferCouplingInputs

/-! Positive-base uniform Potts induction. The coupling bound is the
only probabilistic input; the actual BFS separator, local analytic
controls, and parent recursion are all derived internally. -/
namespace CI2ZF.Potts
open PottsCI
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

/-- One disk radius works for every datum and every base in a compact
positive real set. It is selected before quantifying graph size. -/
theorem positive_uniform_transfer (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (K : Set ℂ)
    (hK : IsCompact K) (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0)
    (cost : ℝ)
    (hCI : ∀ (x : ℝ) (hx : 0 < x), (x : ℂ) ∈ K →
      RootCouplingBound.{u, v} C Δ hq ⟨x, hx.le⟩ cost) :
    ∃ r > 0, ∃ alpha > 0,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C),
        I.DegreeBound Δ → ∀ x ∈ K, PartitionNonzeroOn I x r) ∧
      ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
        I.DegreeBound Δ → ∀ x ∈ K, OptionRootResponses I x r alpha := by
  obtain ⟨L, B, hL, hcost, hB, alpha, ha, ha1, haB⟩ :=
    exists_geometric_transfer_scales Δ cost
  obtain ⟨r, hr, hcontrols⟩ := exists_positive_local_controls.{u, v} C Δ B K hK hreal ha
  have hlocal := hcontrols r hr le_rfl
  have hbase (x : ℝ) (hx : 0 < x) (hxK : (x : ℂ) ∈ K) := by
    apply uniform_induction.{u, v} C Δ (x : ℂ) r alpha
    · intro O _ I hd hNZ hRoot
      by_cases hsmall : Fintype.card (Component.RootComponent I.graph none) ≤ B
      · exact positive_small_component_response_step hlocal ha.le hxK I hd hsmall hNZ
      · intro a b
        apply OptionBFS.positive_bfs_response_step I a b hd hL hB
          (Nat.lt_of_not_ge hsmall) hx hr ha.le (by linarith) (by linarith) hcost
        · exact hCI x hx hxK I hd a b
        · exact hNZ
        · exact hRoot
        · intro U S E _ _ _ J hdJ hcard ξ
          exact hlocal.inside J hdJ hcard ξ (x : ℂ) hxK
    · intro O _ I hd hchildren hresponses
      exact positive_parent_step_of_local_controls hlocal (by linarith) hx hxK
        I hd hchildren hresponses
  refine ⟨r, hr, alpha, ha, ?_, ?_⟩
  · intro V _ I hd x hx
    obtain ⟨t, ht, rfl⟩ := hreal hx
    exact (hbase t ht hx).1 I hd
  · intro V _ I hd x hx
    obtain ⟨t, ht, rfl⟩ := hreal hx
    exact (hbase t ht hx).2 I hd

/-- The positive half of the transfer hypotheses supplies a radius
uniform on each `[δ,1]`, including both endpoints of that interval. -/
theorem positive_interval_uniform_transfer (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) {δ : ℝ} (hδ : 0 < δ)
    (cost : ℝ)
    (hCI : ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ∈ Set.Icc δ 1 →
      RootCouplingBound.{u, v} C Δ hq x cost) :
    ∃ r > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      I.DegreeBound Δ → ∀ x ∈ Set.Icc δ 1, PartitionNonzeroOn I (x : ℂ) r := by
  let K : Set ℂ := Complex.ofReal '' Set.Icc δ 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hreal : K ⊆ Complex.ofReal '' Set.Ioi 0 := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, hδ.trans_le ht.1, rfl⟩
  obtain ⟨r, hr, _, _, hn, _⟩ := positive_uniform_transfer.{u, v} C Δ hq K hK hreal cost
    (fun x hx hxK => by
      obtain ⟨t, ht, htx⟩ := hxK
      have htx' : t = x := Complex.ofReal_injective htx
      subst t
      intro O _ I hd a b
      exact hCI ⟨x, hx.le⟩ ht I hd a b)
  exact ⟨r, hr, fun I hd x hx => hn I hd (x : ℂ) ⟨x, hx, rfl⟩⟩

end
end CI2ZF.Potts
