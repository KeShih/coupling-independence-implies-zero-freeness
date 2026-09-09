import CI2ZF.Potts.Transfer.FamilyUniformTransfer

/-! The standalone positive-base induction needs no hard colour slack.
Its only probabilistic input concerns actual positive-activity Gibbs laws. -/
namespace CI2ZF.Potts.PinningFamily
open PottsCI PottsCI.FinDist Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

/-- Positive activity supplies positivity directly, independently of
any hard-colouring extension threshold. -/
def PositiveRootCouplingBound (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (x : ℝ) (hx : 0 < x) (cost : ℝ) : Prop :=
  ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C), F.contains I →
    I.DegreeBound Δ → ∀ a b : C,
    W ham
      ((optionChildData I a).gibbs x hx.le
        ((optionChildData I a).partition_pos_of_parameter_pos hx))
      ((optionChildData I b).gibbs x hx.le
        ((optionChildData I b).partition_pos_of_parameter_pos hx)) ≤ cost

/-- The standalone positive-base response lemma for an operation-closed
family, with no lower bound on the number of colours. -/
theorem positive_uniform_transfer_of_positive_ci (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (K : Set ℂ)
    (hK : IsCompact K) (hreal : K ⊆ Complex.ofReal '' Ioi 0)
    (cost : ℝ)
    (hCI : ∀ (x : ℝ) (hx : 0 < x), (x : ℂ) ∈ K →
      F.PositiveRootCouplingBound Δ x hx cost) :
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

theorem positive_interval_uniform_transfer_of_positive_ci (F : PinningFamily.{u, v} C)
    (Δ : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (cost : ℝ)
    (hCI : ∀ (x : ℝ) (hx : 0 < x), x ∈ Icc δ 1 →
      F.PositiveRootCouplingBound Δ x hx cost) :
    ∃ r > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C), F.contains I →
      I.DegreeBound Δ → ∀ x ∈ Icc δ 1, PartitionNonzeroOn I (x : ℂ) r := by
  let K : Set ℂ := Complex.ofReal '' Icc δ 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hreal : K ⊆ Complex.ofReal '' Ioi 0 := by
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, hδ.trans_le ht.1, rfl⟩
  obtain ⟨r, hr, _, _, hn, _⟩ := F.positive_uniform_transfer_of_positive_ci Δ K hK hreal cost
    (fun x hx hxK => by
      obtain ⟨t, ht, htx⟩ := hxK
      have htx' : t = x := Complex.ofReal_injective htx
      subst t
      intro O _ I hI hd a b
      exact hCI x hx ht I hI hd a b)
  exact ⟨r, hr, fun I hI hd x hx => hn I hI hd (x : ℂ) ⟨x, hx, rfl⟩⟩

end
end CI2ZF.Potts.PinningFamily
