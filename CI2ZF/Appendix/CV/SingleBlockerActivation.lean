import CI2ZF.Appendix.CV.SafetyActivation

/-! Every actual N₁₂ record lies in a unique active physical free-blocker
event. Its probability is bounded by the fresh-gain resource. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
variable {V C : Type*} [Fintype V] [Fintype C]

lemma rootNeighbours_empty_of_flipSet_card_one (F : HardListInstance V C) (X : V → C)
    (u : V) (c : C) (hc : c ≠ X u) (hs : (flipSet F.graph X u c).card = 1) :
    rootNeighbours F X u c = ∅ := by
  have hh := rootFlip_card_ge_neighbours F X u c hc
  apply Finset.card_eq_zero.mp
  omega

lemma rootNeighbours_card_one_of_flipSet_card_two (F : HardListInstance V C) (X : V → C)
    (u : V) (c : C) (hc : c ≠ X u) (hs : (flipSet F.graph X u c).card = 2) :
    (rootNeighbours F X u c).card = 1 := by
  have hh := rootFlip_card_ge_neighbours F X u c hc
  have hn : rootNeighbours F X u c ≠ ∅ := by
    intro he
    have hsing := root_flipSet_singleton_of_no_neighbours F X u c hc he
    rw [hsing, Finset.card_singleton] at hs
    contradiction
  have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
  omega

lemma componentSafe12_neighbour_shapes
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hu : u ∈ rootNeighbours FX X v c)
    (hsafe : componentSafe12 FX FY X Y v u c = 1) :
    ∃ w, ((rootNeighbours FY Y u a = {w} ∧ rootNeighbours FX X u b = ∅) ∨
      (rootNeighbours FY Y u a = ∅ ∧ rootNeighbours FX X u b = {w})) ∧
      a ∈ FY.list u ∧ b ∈ FX.list u := by
  have huv := rootNeighbour_ne_root hu
  have huY : u ∈ rootNeighbours FY Y v c := h.rootNeighbours_eq hca hcb ▸ hu
  have huc := (mem_rootNeighbours.mp hu).2
  have hucY := (mem_rootNeighbours.mp huY).2
  have hsca : a ≠ Y u := by rw [hucY]; exact hca.symm
  have hscb : b ≠ X u := by rw [huc]; exact hcb.symm
  have hSX := h.offRootComponent_eq_opposite_flipSet hcb hu
  have hSY := h.symm.offRootComponent_eq_opposite_flipSet hca huY
  unfold componentSafe12 at hsafe
  split_ifs at hsafe with hh
  have ha : a ∈ FY.list u := by
    rw [← h.offRoot_list_eq u huv, ← h.X_root]
    exact hh.2.1
  have hb : b ∈ FX.list u := by
    rw [h.offRoot_list_eq u huv, ← h.Y_root]
    exact hh.2.2
  have hshape := hh.1
  rw [h.X_root, h.Y_root, hSX, hSY] at hshape
  rcases hshape with ⟨h1, h2⟩ | ⟨h2, h1⟩
  · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp
      (rootNeighbours_card_one_of_flipSet_card_two FX X u b hscb h2)
    exact ⟨w, Or.inr ⟨rootNeighbours_empty_of_flipSet_card_one FY Y u a hsca h1, hw⟩, ha, hb⟩
  · obtain ⟨w, hw⟩ := Finset.card_eq_one.mp
      (rootNeighbours_card_one_of_flipSet_card_two FY Y u a hsca h2)
    exact ⟨w, Or.inl ⟨hw, rootNeighbours_empty_of_flipSet_card_one FX X u b hscb h1⟩, ha, hb⟩

def blockerFreeConstraint (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (w : freeBlockers I X Y v u.val) : I.Constraint :=
  rootFreeConstraint I u.val ⟨w.val, by
    change I.graph.Adj u.val w.val
    simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp w.property).1⟩

lemma blockerFreeConstraint_mem_targets (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (w : freeBlockers I X Y v u.val) :
    blockerFreeConstraint I X Y v u w ∈ targetConstraints I X Y v u.val := by
  exact (mem_targetConstraints I X Y v u.val _).mpr
    ⟨w.val, rfl, (Finset.mem_filter.mp w.property).2.2⟩

lemma blockerFreeConstraint_ne_root (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (w : freeBlockers I X Y v u.val) :
    blockerFreeConstraint I X Y v u w ≠ rootFreeConstraint I v u := by
  apply rootFreeConstraint_edge_ne I v u _ w.val rfl
  exact (Finset.mem_filter.mp w.property).2.1

def singleBlockerActivation (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (w : freeBlockers I X Y v u.val) (ω : I.Constraint → Bool) : Prop :=
  coinPattern {rootFreeConstraint I v u, blockerFreeConstraint I X Y v u w}
    ((targetConstraints I X Y v u.val) \ {rootFreeConstraint I v u, blockerFreeConstraint I X Y v u w}) ω

theorem singleBlockerActivation_probability (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (w : freeBlockers I X Y v u.val)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx)
      (fun ω => if singleBlockerActivation I X Y v u w ω then (1 : ℝ) else 0) =
      (1 - x)^2 * x^(blockerCount I X Y v u.val - 1) := by
  let A : Finset I.Constraint := {rootFreeConstraint I v u, blockerFreeConstraint I X Y v u w}
  let D := targetConstraints I X Y v u.val
  have hA : A.card = 2 := by
    simp [A, (blockerFreeConstraint_ne_root I X Y v u w).symm]
  have hsub : A ⊆ D := by
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact targetConstraints_root_edge_mem I X Y v u
    · rw [Finset.mem_singleton] at hk
      exact hk ▸ blockerFreeConstraint_mem_targets I X Y v u w
  have hD : (D \ A).card = blockerCount I X Y v u.val - 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hA]
    have he := targetConstraints_erase_root_card I X Y v u
    rw [Finset.card_erase_of_mem (targetConstraints_root_edge_mem I X Y v u)] at he
    change D.card - 1 = blockerCount I X Y v u.val at he
    omega
  have hp := coinPatternProbability_eq_inactive x hx A (D \ A) Finset.disjoint_sdiff
  change expectReal (activityCoins I x hx) _ = _ at hp
  change expectReal (activityCoins I x hx) (fun ω => if coinPattern A (D \ A) ω then (1 : ℝ) else 0) = _
  simpa only [hA, hD] using hp

lemma active_target_other_eq_blocker (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hu : regularAt X Y v u.val) (hagree : ∀ t, t ≠ v → X t = Y t)
    (w : V) (hw : I.graph.Adj u.val w)
    (hNX : ∀ t, t ∈ rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X u.val (Y v) → t = w)
    (hNY : ∀ t, t ∈ rootNeighbours (activeHardListInstance I (activatedSet I Y ω)) Y u.val (X v) → t = w)
    (ha : X v ∈ (activeHardListInstance I (activatedSet I Y ω)).list u.val)
    (hb : Y v ∈ (activeHardListInstance I (activatedSet I X ω)).list u.val)
    (k : I.Constraint) (hk : k ∈ targetConstraints I X Y v u.val)
    (hne : k ≠ rootFreeConstraint I v u) (hcoin : ω k = true) :
    k = rootFreeConstraint I u.val ⟨w, hw⟩ := by
  have hsat := targetConstraints_satisfied I X Y v u.val hu hagree k hk
  rw [mem_targetConstraints] at hk
  cases k with
  | inl e =>
    obtain ⟨t, he, ht⟩ := hk
    have htv : t ≠ v := by
      intro hh
      apply hne
      apply congrArg Sum.inl
      apply Subtype.ext
      exact he.trans ((congrArg (fun z => s(u.val, z)) hh).trans Sym2.eq_swap)
    have hcol : X t = X v ∨ X t = Y v := by
      change X t = X v ∨ X t = Y v ∨ Y t = X v ∨ Y t = Y v at ht
      rw [← hagree t htv] at ht
      tauto
    have hax : (activeGraph I (activatedSet I X ω)).Adj u.val t :=
      ⟨e, (mem_activatedSet I X ω _).mpr ⟨hcoin, hsat.1⟩, he⟩
    have hay : (activeGraph I (activatedSet I Y ω)).Adj u.val t :=
      ⟨e, (mem_activatedSet I Y ω _).mpr ⟨hcoin, hsat.2⟩, he⟩
    have htw : t = w := hcol.elim
      (fun hh => hNY t (mem_rootNeighbours.mpr ⟨hay, (hagree t htv).symm.trans hh⟩))
      (fun hh => hNX t (mem_rootNeighbours.mpr ⟨hax, hh⟩))
    apply congrArg Sum.inl
    apply Subtype.ext
    exact he.trans (congrArg (fun t => s(u.val, t)) htw)
  | inr i =>
    obtain ⟨t, c, i⟩ := i
    obtain ⟨rfl, hc⟩ := hk
    rcases hc with rfl | rfl
    · have hlist := (Potts.mem_activeList_activated I Y ω u.val (X v)).mp ha
      exact (hlist ⟨⟨i, hcoin⟩, hsat.2⟩).elim
    · have hlist := (Potts.mem_activeList_activated I X ω u.val (Y v)).mp hb
      exact (hlist ⟨⟨i, hcoin⟩, hsat.1⟩).elim

/-- The graph record itself identifies one physical blocker; every other
collected target bit must be false. -/
theorem componentSafe12_implies_singleBlocker (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hroot : X v ≠ Y v) (hu : regularAt X Y v u.val)
    (hagree : ∀ t, t ≠ v → X t = Y t) (hcoin : ω (rootFreeConstraint I v u) = true)
    (hsafe : componentSafe12 (activeHardListInstance I (activatedSet I X ω))
      (activeHardListInstance I (activatedSet I Y ω)) X Y v u.val (X u.val) = 1) :
    ∃ w : freeBlockers I X Y v u.val, singleBlockerActivation I X Y v u w ω := by
  let FX := activeHardListInstance I (activatedSet I X ω)
  let FY := activeHardListInstance I (activatedSet I Y ω)
  let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
  have hmem : u.val ∈ rootNeighbours FX X v (X u.val) :=
    (activeRootIncidence_iff_coin I X v (X u.val) hu.2.1 ω u).mpr ⟨rfl, hcoin⟩
  obtain ⟨w, hshape, ha, hb⟩ := componentSafe12_neighbour_shapes h hu.2.1 hu.2.2 hmem hsafe
  change (rootNeighbours FY Y u.val (X v) = {w} ∧ rootNeighbours FX X u.val (Y v) = ∅) ∨
    (rootNeighbours FY Y u.val (X v) = ∅ ∧ rootNeighbours FX X u.val (Y v) = {w}) at hshape
  have hNX : ∀ t, t ∈ rootNeighbours FX X u.val (Y v) → t = w := by
    intro t ht
    rcases hshape with ⟨_, he⟩ | ⟨_, he⟩
    · rw [he] at ht
      exact (Finset.notMem_empty t ht).elim
    · simpa only [he, Finset.mem_singleton] using ht
  have hNY : ∀ t, t ∈ rootNeighbours FY Y u.val (X v) → t = w := by
    intro t ht
    rcases hshape with ⟨he, _⟩ | ⟨he, _⟩
    · simpa only [he, Finset.mem_singleton] using ht
    · rw [he] at ht
      exact (Finset.notMem_empty t ht).elim
  have hwmem : w ∈ rootNeighbours FX X u.val (Y v) ∨ w ∈ rootNeighbours FY Y u.val (X v) := by
    rcases hshape with ⟨he, _⟩ | ⟨_, he⟩
    · exact Or.inr (by simp only [he, Finset.mem_singleton])
    · exact Or.inl (by simp only [he, Finset.mem_singleton])
  have hwphysical : I.graph.Adj u.val w := by
    rcases hwmem with hw | hw
    · exact activeGraph_le_original I _ (mem_rootNeighbours.mp hw).1
    · exact activeGraph_le_original I _ (mem_rootNeighbours.mp hw).1
  have hwv : w ≠ v := by
    intro hh
    rcases hwmem with hw | hw
    · exact hroot (hh ▸ (mem_rootNeighbours.mp hw).2)
    · exact hroot ((hh ▸ (mem_rootNeighbours.mp hw).2).symm)
  have hwtarget : targetAt X Y v w := by
    rcases hwmem with hw | hw
    · exact Or.inr (Or.inl (mem_rootNeighbours.mp hw).2)
    · exact Or.inr (Or.inr (Or.inl (mem_rootNeighbours.mp hw).2))
  let wi : freeBlockers I X Y v u.val :=
    ⟨w, Finset.mem_filter.mpr ⟨by simpa only [SimpleGraph.mem_neighborFinset] using hwphysical, hwv, hwtarget⟩⟩
  have hwcoin : ω (blockerFreeConstraint I X Y v u wi) = true := by
    rcases hwmem with hw | hw
    · have hed := (mem_rootNeighbours.mp hw).1
      change (activeGraph I (activatedSet I X ω)).Adj u.val w at hed
      rw [activeGraph_root_adj_iff I _ u.val ⟨w, hwphysical⟩] at hed
      exact ((mem_activatedSet I X ω _).mp hed).1
    · have hed := (mem_rootNeighbours.mp hw).1
      change (activeGraph I (activatedSet I Y ω)).Adj u.val w at hed
      rw [activeGraph_root_adj_iff I _ u.val ⟨w, hwphysical⟩] at hed
      exact ((mem_activatedSet I Y ω _).mp hed).1
  refine ⟨wi, ?_⟩
  unfold singleBlockerActivation coinPattern
  constructor
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hcoin
    · rw [Finset.mem_singleton] at hk
      exact hk ▸ hwcoin
  · intro k hk
    obtain ⟨hkt, hkne⟩ := Finset.mem_sdiff.mp hk
    apply Bool.eq_false_iff.mpr
    intro hktrue
    have hkr : k ≠ rootFreeConstraint I v u := fun hh => hkne (by simp [hh])
    have heq := active_target_other_eq_blocker I X Y v u ω hu hagree w hwphysical hNX hNY ha hb k hkt hkr hktrue
    apply hkne
    exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr heq)

theorem activatedGainAt_le_singleBlocker_events (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hroot : X v ≠ Y v) (hagree : ∀ t, t ≠ v → X t = Y t) :
    activatedGainAt I X Y v ω u ≤
      ∑ w : freeBlockers I X Y v u.val,
        if singleBlockerActivation I X Y v u w ω then (1 : ℝ) else 0 := by
  have hnonneg : 0 ≤ ∑ w : freeBlockers I X Y v u.val,
      if singleBlockerActivation I X Y v u w ω then (1 : ℝ) else 0 := by
    apply Finset.sum_nonneg
    intro w _
    split_ifs <;> norm_num
  unfold activatedGainAt
  split_ifs with hu hav
  · by_cases hs : componentSafe12 (activeHardListInstance I (activatedSet I X ω))
        (activeHardListInstance I (activatedSet I Y ω)) X Y v u.val (X u.val) = 1
    · rw [hs, Nat.cast_one]
      obtain ⟨w, hw⟩ := componentSafe12_implies_singleBlocker I X Y v u ω hroot hu.1 hagree hu.2 hs
      calc
        _ = if singleBlockerActivation I X Y v u w ω then (1 : ℝ) else 0 := by rw [if_pos hw]
        _ ≤ _ := by
          apply Finset.single_le_sum _ (Finset.mem_univ w)
          intro t _
          split_ifs <;> norm_num
    · have hh := componentSafety_sum_le_one (activeHardListInstance I (activatedSet I X ω))
        (activeHardListInstance I (activatedSet I Y ω)) X Y v u.val (X u.val)
      have hz : componentSafe12 (activeHardListInstance I (activatedSet I X ω))
          (activeHardListInstance I (activatedSet I Y ω)) X Y v u.val (X u.val) = 0 := by omega
      rw [hz, Nat.cast_zero]
      exact hnonneg
  · exact hnonneg
  · exact hnonneg

theorem expected_activatedGainAt_le (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (hroot : X v ≠ Y v)
    (hagree : ∀ t, t ≠ v → X t = Y t) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx) (fun ω => activatedGainAt I X Y v ω u) ≤
      if regularAt X Y v u.val then
        (freeBlockers I X Y v u.val).card * (1 - x)^2 * x^(blockerCount I X Y v u.val - 1) else 0 := by
  by_cases hu : regularAt X Y v u.val
  · rw [if_pos hu]
    have hp := expectReal_mono (activityCoins I x hx)
      (fun ω => activatedGainAt_le_singleBlocker_events I X Y v u ω hroot hagree)
    rw [expectReal_sum] at hp
    simp only [singleBlockerActivation_probability I X Y v u _ x hx,
      Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hp
    exact hp.trans_eq (by ring)
  · rw [if_neg hu]
    have hz (ω : I.Constraint → Bool) : activatedGainAt I X Y v ω u = 0 :=
      if_neg (fun hh => hu hh.1)
    simp_rw [hz]
    rw [expectReal_const]

/-- No N₁₂ credit exceeds the actual physical single-blocker probability.
The availability restriction can only discard events. -/
theorem expected_colourGain_le_singleBlockerTotal (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ t, t ≠ v → X t = Y t)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx)
      (fun ω => ∑ c, colourGainCount
        (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) c) ≤
      singleBlockerTotal I x X Y v := by
  have he (ω : I.Constraint → Bool) := sum_colourGainCount_eq I X Y v hroot hagree ω
  simp_rw [he]
  rw [expectReal_sum]
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun u _ => expected_activatedGainAt_le I X Y v u hroot hagree x hx)
  apply hs.trans_eq
  unfold singleBlockerTotal
  exact (Finset.sum_subtype (I.graph.neighborFinset v) (p := fun u => I.graph.Adj v u)
    (by simp) (fun u => if regularAt X Y v u then
      (freeBlockers I X Y v u).card * (1 - x)^2 * x^(blockerCount I X Y v u - 1) else 0)).symm

end
end CI2ZF.Appendix.CV
