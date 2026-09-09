import CI2ZF.Appendix.CV.Kernel
import CI2ZF.HardMoveMass

/-! The aggregate component mass and holding reserve of the actual CV kernel. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

lemma proposal_mass_of_component_member (F : HardListInstance V C) (X : V → C)
    (u : V) (c : C) (hc : c ≠ X u)
    (ha : flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c))
    (v : V) (hv : v ∈ flipSet F.graph X u c) :
    let Y := flipConfiguration X (flipSet F.graph X u c) (X u) c
    (proposalDistribution F X v (Y v)).w Y =
      mass (flipSet F.graph X u c).card / (flipSet F.graph X u c).card := by
  let Y := flipConfiguration X (flipSet F.graph X u c) (X u) c
  change (proposalDistribution F X v (Y v)).w Y = _
  have hne : Y v ≠ X v := (flipConfiguration_ne_iff hc v).mpr hv
  have hYX : Y ≠ X := fun h => hne (congrFun h v)
  obtain ⟨hset, hconf⟩ := component_move_from_member F.graph X u c hc v hv
  change flipSet F.graph X v (Y v) = flipSet F.graph X u c at hset
  change flipConfiguration X (flipSet F.graph X v (Y v)) (X v) (Y v) = Y at hconf
  have hprob : acceptanceProbability F X v (Y v) =
      mass (flipSet F.graph X u c).card / (flipSet F.graph X u c).card := by
    unfold acceptanceProbability
    rw [hconf, hset, if_pos ha]
  unfold proposalDistribution
  rw [if_neg hne, twoPoint_w, hprob, hconf]
  simp [hYX]

/-- Exactly one colour proposal per vertex of a component produces this
move; hence its total transition mass is `p_s/(|V| q)`. -/
theorem hardStep_component_mass [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (u : V) (c : C) (hc : c ≠ X u)
    (ha : flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)) :
    (hardStep F X).w (flipConfiguration X (flipSet F.graph X u c) (X u) c) =
      mass (flipSet F.graph X u c).card /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  let S := flipSet F.graph X u c
  let Y := flipConfiguration X S (X u) c
  let mass := mass S.card / (S.card : ℝ)
  let k := (Fintype.card (V × C) : ℝ)⁻¹
  have hYX : Y ≠ X := by
    intro h
    have hn := (flipConfiguration_ne_iff (G := F.graph) hc u).mpr self_mem_flipSet
    exact hn (congrFun h u)
  have hinner (v : V) : (∑ d : C, k * (proposalDistribution F X v d).w Y) =
      if v ∈ S then k * mass else 0 := by
    rw [Finset.sum_eq_single (Y v)]
    · by_cases hv : v ∈ S
      · rw [if_pos hv, proposal_mass_of_component_member F X u c hc ha v hv]
      · have hyv : Y v = X v := flipConfiguration_of_not_mem hv
        rw [if_neg hv, hyv]
        simp [proposalDistribution, FinDist.pure, hYX]
    · intro d _ hd
      rw [proposalDistribution_eq_zero hYX.symm v d hd, mul_zero]
    · simp
  change (hardStep F X).w Y = _
  rw [hardStep_w, Fintype.sum_prod_type]
  change (∑ v : V, ∑ d : C, k * (proposalDistribution F X v d).w Y) = _
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hs : (S.card : ℝ) ≠ 0 := by exact_mod_cast (flipSet_card_pos (G := F.graph)
    (X := X) (u := u) (c := c)).ne'
  dsimp [k, mass]
  rw [Fintype.card_prod, Nat.cast_mul]
  field_simp
  rfl

/-- The proposals that retain their current colour reserve holding mass
`1/q`; this pays for the root-colour moves paired with holding. -/
theorem hardStep_holding_mass [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) :
    1 / (Fintype.card C : ℝ) ≤ (hardStep F X).w X := by
  let k := (Fintype.card (V × C) : ℝ)⁻¹
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hsingle (u : V) : k ≤ ∑ c : C, k * (proposalDistribution F X u c).w X := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun c => k * (proposalDistribution F X u c).w X)
      (fun c _ => mul_nonneg hk ((proposalDistribution F X u c).nonneg X))
      (Finset.mem_univ (X u))
    simpa [proposalDistribution, FinDist.pure] using h
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hsingle u)
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := V)
  have hid : (∑ _u : V, k) = 1 / (Fintype.card C : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, k,
      Fintype.card_prod, Nat.cast_mul]
    field_simp
  rw [hid] at hsum
  rw [hardStep_w, Fintype.sum_prod_type]
  exact hsum

end
end CI2ZF.Appendix.CV
