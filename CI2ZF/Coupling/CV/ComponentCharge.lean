import CI2ZF.Coupling.CV.IncidenceRates

/-! Canonical graph-component charges for the CV profile. All capacity,
positivity, and profile hypotheses are derived from the graph and lists. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def canonicalOffRootCharge {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (u w : V) : ℝ :=
  (∑ S : RootPiece FX X v c, (S.val.card : ℝ) * componentResidual FX X v c u S) +
  (∑ S : RootPiece FY Y v c, (S.val.card : ℝ) * componentResidual FY Y v c w S) -
  ∑ i, CanonicalMatching.atIncidence (componentOf FX X v c) (oppositeComponentOf h hca hcb)
    (fun S => componentResidual FX X v c u S) (fun S => componentResidual FY Y v c w S) i

def canonicalColourCharge {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (u w : V) : ℝ :=
  if (rootNeighbours FX X v c).Nonempty then
    rootCharge FX X v c u + rootCharge FY Y v c w + canonicalOffRootCharge h hca hcb u w
  else -(if c ∈ FX.list v then 1 else 0)

lemma canonical_component_share_le (F : HardListInstance V C) (X : V → C) (v : V)
    (c : C) (u : V) (i : RootIncidence F X v c) :
    CanonicalMatching.share (componentOf F X v c)
      (fun S => componentResidual F X v c u S) i ≤ mass (componentOf F X v c i).val.card := by
  unfold CanonicalMatching.share
  split_ifs
  · exact componentResidual_le_mass F X v c u _
  · exact mass_nonneg _

lemma canonical_opposite_share_le {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (w : V) (i : RootIncidence FX X v c) :
    CanonicalMatching.share (oppositeComponentOf h hca hcb)
      (fun S => componentResidual FY Y v c w S) i ≤ mass (oppositeComponentOf h hca hcb i).val.card := by
  unfold CanonicalMatching.share
  split_ifs
  · exact componentResidual_le_mass FY Y v c w _
  · exact mass_nonneg _

/-- Every physical incidence costs at most 1.324, including repeated and
blocked components; the canonical sharing identity counts each component once. -/
theorem canonicalOffRootCharge_le {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (u w : V) :
    canonicalOffRootCharge h hca hcb u w ≤
      (1 + 81 / 250 : ℝ) * (rootNeighbours FX X v c).card := by
  unfold canonicalOffRootCharge
  rw [CanonicalMatching.charge_as_incidence_sum _ _ (componentOf_surjective FX X v c)
    (oppositeComponentOf_surjective h hca hcb)]
  calc
    _ ≤ ∑ _i : RootIncidence FX X v c, (1 + 81 / 250 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact pair_charge_le _ _
        (Finset.card_pos.mpr (rootFamily_nonempty_component (componentOf FX X v c i).property))
        (Finset.card_pos.mpr (rootFamily_nonempty_component (oppositeComponentOf h hca hcb i).property))
        (canonical_component_share_le FX X v c u i) (canonical_opposite_share_le h hca hcb w i)
    _ = _ := by simp [RootIncidence, mul_comm]; ring

lemma rootCharge_le (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (u : V) (hu : u ∈ rootNeighbours F X v c) : rootCharge F X v c u ≤ 22 / 125 := by
  have hS : offRootComponent F X v (X v) c u ∈ rootFamily F X v c :=
    Finset.mem_image.mpr ⟨u, hu, rfl⟩
  have hpos : 1 ≤ (offRootComponent F X v (X v) c u).card :=
    Finset.card_pos.mpr (rootFamily_nonempty_component hS)
  have hposR : (1 : ℝ) ≤ (offRootComponent F X v (X v) c u).card := by exact_mod_cast hpos
  unfold rootCharge rootRate
  split_ifs
  · have hp := mass_nonneg (flipSet F.graph X v c).card
    have hb := sub_two_size_mass_le (flipSet F.graph X v c).card
    nlinarith
  · norm_num

theorem canonicalColourCharge_le_of_three_le {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (u w : V)
    (hu : u ∈ rootNeighbours FX X v c) (hw : w ∈ rootNeighbours FY Y v c)
    (hm : 3 ≤ (rootNeighbours FX X v c).card) :
    canonicalColourCharge h hca hcb u w ≤ -1 + bulk * (rootNeighbours FX X v c).card := by
  rw [canonicalColourCharge, if_pos ⟨u, hu⟩]
  have hX := rootCharge_le FX X v c u hu
  have hY := rootCharge_le FY Y v c w hw
  have hO := canonicalOffRootCharge_le h hca hcb u w
  have hnum := high_multiplicity_arithmetic (by exact_mod_cast hm : (3 : ℝ) ≤
    (rootNeighbours FX X v c).card)
  linarith

theorem canonicalColourCharge_le_of_unavailable {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (u w : V) (hc : c ∉ FX.list v) :
    canonicalColourCharge h hca hcb u w ≤
      (1 + 81 / 250 : ℝ) * (rootNeighbours FX X v c).card := by
  have hcY : c ∉ FY.list v := fun hcY => hc ((h.root_list_regular_iff c hca hcb).mpr hcY)
  unfold canonicalColourCharge
  split_ifs
  · simpa [rootCharge, rootRate_zero_of_unavailable FX X v c hc,
      rootRate_zero_of_unavailable FY Y v c hcY] using canonicalOffRootCharge_le h hca hcb u w
  · simp
    positivity

end
end CI2ZF.Appendix.CV
