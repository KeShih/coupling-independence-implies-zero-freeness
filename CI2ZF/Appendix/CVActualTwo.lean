import CI2ZF.Appendix.CVMaxChoice
import CI2ZF.Appendix.CVTwoIncidence
import CI2ZF.Appendix.CVActualOne

/-! The two-incidence certificate applied to actual canonical graph records,
including repeated-component markers and synchronized maximum choices. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

structure TwoGraphRecord where
  a₀ : Branch
  a₁ : Branch
  b₀ : Branch
  b₁ : Branch

def twoGraphRecord {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (iu iw : RootIncidence FX X v c) : TwoGraphRecord :=
  { a₀ := componentBranch FX X v c (by rwa [h.X_root]) iu.val iu.property
    a₁ := secondComponentBranch FX X v c (by rwa [h.X_root]) iu.val iw.val iw.property
    b₀ := componentBranch FY Y v c (by rwa [h.Y_root]) iu.val
      ((h.rootNeighbours_eq hca hcb) ▸ iu.property)
    b₁ := secondComponentBranch FY Y v c (by rwa [h.Y_root]) iu.val iw.val
      ((h.rootNeighbours_eq hca hcb) ▸ iw.property) }

lemma twoGraphRecord_pos {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (iu iw : RootIncidence FX X v c) :
    0 < branchSize (twoGraphRecord h hca hcb iu iw).a₀ ∧
      0 < branchSize (twoGraphRecord h hca hcb iu iw).b₀ :=
  ⟨componentBranch_pos FX X v c (by rwa [h.X_root]) iu.val iu.property,
    componentBranch_pos FY Y v c (by rwa [h.Y_root]) iu.val ((h.rootNeighbours_eq hca hcb) ▸ iu.property)⟩

lemma twoGraphRecord_choice_valid {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (iu iw : RootIncidence FX X v c) (i j : Bool)
    (hp : let R := twoGraphRecord h hca hcb iu iw; permitted R.a₀ R.a₁ R.b₀ R.b₁ i j = true) :
    (i = true → offRootComponent FX X v (X v) c iu.val ≠ offRootComponent FX X v (X v) c iw.val) ∧
    (j = true → offRootComponent FY Y v (Y v) c iu.val ≠ offRootComponent FY Y v (Y v) c iw.val) := by
  have hpos := twoGraphRecord_pos h hca hcb iu iw
  constructor
  · intro hi heq
    have hz : branchSize (twoGraphRecord h hca hcb iu iw).a₁ = 0 := by
      simp [twoGraphRecord, secondComponentBranch, heq, branchSize]
    exact permitted_left_not_zero hp hpos.1 hi hz
  · intro hj heq
    have hz : branchSize (twoGraphRecord h hca hcb iu iw).b₁ = 0 := by
      simp [twoGraphRecord, secondComponentBranch, heq, branchSize]
    exact permitted_right_not_zero hp hpos.2 hj hz

lemma canonicalOffRootCharge_two_neighbours {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (iu iw : RootIncidence FX X v c)
    (hN : rootNeighbours FX X v c = {iu.val, iw.val})
    (horder : CanonicalMatching.index iu < CanonicalMatching.index iw) (uStar wStar : V) :
    canonicalOffRootCharge h hca hcb uStar wStar =
      let A₀ := offRootComponent FX X v (X v) c iu.val
      let A₁ := offRootComponent FX X v (X v) c iw.val
      let B₀ := offRootComponent FY Y v (Y v) c iu.val
      let B₁ := offRootComponent FY Y v (Y v) c iw.val
      let r := componentResidual FX X v c uStar
      let s := componentResidual FY Y v c wStar
      A₀.card * r A₀ + (if A₀ = A₁ then 0 else A₁.card * r A₁) +
      B₀.card * s B₀ + (if B₀ = B₁ then 0 else B₁.card * s B₁) -
      min (r A₀) (s B₀) - min (if A₀ = A₁ then 0 else r A₁) (if B₀ = B₁ then 0 else s B₁) := by
  have hall (i : RootIncidence FX X v c) : i = iu ∨ i = iw := by
    have hm : i.val = iu.val ∨ i.val = iw.val := by simpa [hN] using i.property
    exact hm.imp (fun hi => Subtype.ext hi) (fun hi => Subtype.ext hi)
  have hs := CanonicalMatching.charge_two (componentOf FX X v c) (oppositeComponentOf h hca hcb)
    (componentOf_surjective FX X v c) (oppositeComponentOf_surjective h hca hcb)
    (fun S => componentResidual FX X v c uStar S) (fun S => (S.val.card : ℝ))
    (fun S => componentResidual FY Y v c wStar S) (fun S => (S.val.card : ℝ))
    iu iw hall horder
  have hfa : componentOf FX X v c iu = componentOf FX X v c iw ↔
      offRootComponent FX X v (X v) c iu.val = offRootComponent FX X v (X v) c iw.val :=
    Subtype.ext_iff
  have hfb : oppositeComponentOf h hca hcb iu = oppositeComponentOf h hca hcb iw ↔
      offRootComponent FY Y v (Y v) c iu.val = offRootComponent FY Y v (Y v) c iw.val :=
    Subtype.ext_iff
  simp only [hfa, hfb] at hs
  simpa [canonicalOffRootCharge, componentOf, oppositeComponentOf, rootIncidenceEquiv] using hs

lemma recordTwo_fullFamily (a₀ a₁ b₀ b₁ : Branch) (i j : Bool) :
    recordTwo a₀ a₁ b₀ b₁ i j =
      let A := fullFamily a₀ a₁ i
      let B := fullFamily b₀ b₁ j
      A.rootCost + B.rootCost + A.cost₀ + A.cost₁ + B.cost₀ + B.cost₁ -
        min A.residual₀ B.residual₀ - min A.residual₁ B.residual₁ := by
  rfl

/-- Exact graph-to-record identity for the two-neighbour canonical charge. -/
theorem canonicalColourCharge_eq_recordTwo {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v) (iu iw : RootIncidence FX X v c)
    (hN : rootNeighbours FX X v c = {iu.val, iw.val})
    (horder : CanonicalMatching.index iu < CanonicalMatching.index iw) (i j : Bool)
    (hp : let R := twoGraphRecord h hca hcb iu iw; permitted R.a₀ R.a₁ R.b₀ R.b₁ i j = true) :
    canonicalColourCharge h hca hcb (if i then iw.val else iu.val) (if j then iw.val else iu.val) =
      let R := twoGraphRecord h hca hcb iu iw
      recordTwo R.a₀ R.a₁ R.b₀ R.b₁ i j := by
  have hNY : rootNeighbours FY Y v c = {iu.val, iw.val} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hcX : c ≠ X v := by rwa [h.X_root]
  have hcY : c ≠ Y v := by rwa [h.Y_root]
  have havY := (h.root_list_regular_iff c hca hcb).mp hav
  obtain ⟨hi, hj⟩ := twoGraphRecord_choice_valid h hca hcb iu iw i j hp
  change _ = recordTwo _ _ _ _ _ _
  rw [recordTwo_fullFamily]
  dsimp only [twoGraphRecord]
  rw [fullFamily_eq_componentFamily, fullFamily_eq_componentFamily,
    componentFamily_eq_actual FX X v c hcX hav iu.val iw.val hN i hi,
    componentFamily_eq_actual FY Y v c hcY havY iu.val iw.val hNY j hj]
  dsimp only
  rw [canonicalColourCharge, if_pos ⟨iu.val, iu.property⟩,
    canonicalOffRootCharge_two_neighbours h hca hcb iu iw hN horder]
  dsimp only
  ring

lemma shared_second_card_ge_three (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u w : V) (hu : u ∈ rootNeighbours F X v c)
    (hw : w ∈ rootNeighbours F X v c) (huw : u ≠ w)
    (heq : offRootComponent F X v (X v) c u = offRootComponent F X v (X v) c w) :
    3 ≤ (offRootComponent F X v (X v) c w).card := by
  rw [← heq]
  apply shared_component_card_ge_three hc.symm (mem_rootNeighbours.mp hu).2
    (mem_rootNeighbours.mp hw).2 huw
  rw [heq]
  exact self_mem_offRootComponent F X v w (X v) c

lemma twoGraphRecord_safe_first {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (iu iw : RootIncidence FX X v c) :
    let R := twoGraphRecord h hca hcb iu iw
    safe11 R.a₀ R.b₀ = componentSafe11 FX FY X Y v iu.val c ∧
      safe12 R.a₀ R.b₀ = componentSafe12 FX FY X Y v iu.val c := by
  exact ⟨componentBranch_safe11 FX FY X Y v iu.val c (by rwa [h.X_root]) (by rwa [h.Y_root]) iu.property
      ((h.rootNeighbours_eq hca hcb) ▸ iu.property),
    componentBranch_safe12 FX FY X Y v iu.val c (by rwa [h.X_root]) (by rwa [h.Y_root]) iu.property
      ((h.rootNeighbours_eq hca hcb) ▸ iu.property)⟩

lemma twoGraphRecord_safe_second {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (iu iw : RootIncidence FX X v c) (huw : iu.val ≠ iw.val) :
    let R := twoGraphRecord h hca hcb iu iw
    safe11 R.a₁ R.b₁ = componentSafe11 FX FY X Y v iw.val c ∧
      safe12 R.a₁ R.b₁ = componentSafe12 FX FY X Y v iw.val c := by
  have hcX : c ≠ X v := by rwa [h.X_root]
  have hcY : c ≠ Y v := by rwa [h.Y_root]
  have huY : iu.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ iu.property
  have hwY : iw.val ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ iw.property
  by_cases hX : offRootComponent FX X v (X v) c iu.val = offRootComponent FX X v (X v) c iw.val
  · have hsize := shared_second_card_ge_three FX X v c hcX iu.val iw.val iu.property iw.property huw hX
    have hs1 : (offRootComponent FX X v (X v) c iw.val).card ≠ 1 := by omega
    have hs2 : (offRootComponent FX X v (X v) c iw.val).card ≠ 2 := by omega
    simp [twoGraphRecord, secondComponentBranch, hX, safe11, safe12, branchSize,
      componentSafe11, componentSafe12, hs1, hs2]
  · by_cases hY : offRootComponent FY Y v (Y v) c iu.val = offRootComponent FY Y v (Y v) c iw.val
    · have hsize := shared_second_card_ge_three FY Y v c hcY iu.val iw.val huY hwY huw hY
      have hs1 : (offRootComponent FY Y v (Y v) c iw.val).card ≠ 1 := by omega
      have hs2 : (offRootComponent FY Y v (Y v) c iw.val).card ≠ 2 := by omega
      simp [twoGraphRecord, secondComponentBranch, hY, safe11, safe12, branchSize,
        componentSafe11, componentSafe12, hs1, hs2]
    · simp only [twoGraphRecord, secondComponentBranch, if_neg hX, if_neg hY]
      exact ⟨componentBranch_safe11 FX FY X Y v iw.val c hcX hcY iw.property hwY,
        componentBranch_safe12 FX FY X Y v iw.val c hcX hcY iw.property hwY⟩

/-- The corrected bound for a physical two-incidence record. Shared components
cannot be singletons or pairs, so the zero-marker convention preserves the
actual safety counts at both neighbouring vertices. -/
theorem canonicalColourCharge_two_corrected {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v) (iu iw : RootIncidence FX X v c)
    (hN : rootNeighbours FX X v c = {iu.val, iw.val})
    (horder : CanonicalMatching.index iu < CanonicalMatching.index iw) (i j : Bool)
    (hp : let R := twoGraphRecord h hca hcb iu iw; permitted R.a₀ R.a₁ R.b₀ R.b₁ i j = true)
    (gain loss : ℝ) :
    canonicalColourCharge h hca hcb (if i then iw.val else iu.val) (if j then iw.val else iu.val) +
      loss * (componentSafe11 FX FY X Y v iu.val c + componentSafe11 FX FY X Y v iw.val c) -
      gain * (componentSafe12 FX FY X Y v iu.val c + componentSafe12 FX FY X Y v iw.val c) ≤
      -1 + 2 * low gain loss := by
  have huw : iu.val ≠ iw.val := by
    intro heq
    have hi : iu = iw := Subtype.ext heq
    rw [hi] at horder
    exact lt_irrefl _ horder
  let R := twoGraphRecord h hca hcb iu iw
  have hpos := twoGraphRecord_pos h hca hcb iu iw
  have hs0 := twoGraphRecord_safe_first h hca hcb iu iw
  have hs1 := twoGraphRecord_safe_second h hca hcb iu iw huw
  have hbound := recordTwo_corrected R.a₀ R.a₁ R.b₀ R.b₁ i j
    (by dsimp [R]; omega) (by dsimp [R]; omega) hp gain loss
  rw [canonicalColourCharge_eq_recordTwo h hca hcb hav iu iw hN horder i j hp]
  simpa only [R, hs0.1, hs0.2, hs1.1, hs1.2] using hbound

lemma ordered_two_incidence_exists (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hm : (rootNeighbours F X v c).card = 2) :
    ∃ iu iw : RootIncidence F X v c, rootNeighbours F X v c = {iu.val, iw.val} ∧
      CanonicalMatching.index iu < CanonicalMatching.index iw := by
  obtain ⟨u, w, huw, hN⟩ := Finset.card_eq_two.mp hm
  let iu : RootIncidence F X v c := ⟨u, by simp [hN]⟩
  let iw : RootIncidence F X v c := ⟨w, by simp [hN]⟩
  have hidx : CanonicalMatching.index iu ≠ CanonicalMatching.index iw := by
    intro hi
    exact huw (congrArg Subtype.val (CanonicalMatching.index_injective hi))
  rcases lt_or_gt_of_ne hidx with hlt | hlt
  · exact ⟨iu, iw, hN, hlt⟩
  · exact ⟨iw, iu, hN.trans (Finset.pair_comm u w), hlt⟩

/-- Legal actual representatives satisfying the corrected bound exist for
every two-neighbour colour. Synchronization is constructed, not assumed,
and the same representatives work for every real coefficient pair. -/
theorem exists_two_corrected_selectors {FX FY : HardListInstance V C} {X Y : V → C}
    {v : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v)
    (hm : (rootNeighbours FX X v c).card = 2) :
    ∃ u w : V, u ∈ rootNeighbours FX X v c ∧ w ∈ rootNeighbours FY Y v c ∧
      ∀ gain loss : ℝ,
        canonicalColourCharge h hca hcb u w +
          loss * (∑ i : RootIncidence FX X v c, componentSafe11 FX FY X Y v i.val c) -
          gain * (∑ i : RootIncidence FX X v c, componentSafe12 FX FY X Y v i.val c) ≤
          -1 + 2 * low gain loss := by
  obtain ⟨iu, iw, hN, horder⟩ := ordered_two_incidence_exists FX X v c hm
  let R := twoGraphRecord h hca hcb iu iw
  obtain ⟨i, j, hp⟩ := permitted_exists R.a₀ R.a₁ R.b₀ R.b₁
  refine ⟨if i then iw.val else iu.val, if j then iw.val else iu.val, ?_, ?_, ?_⟩
  · cases i <;> first | exact iu.property | exact iw.property
  · rw [← h.rootNeighbours_eq hca hcb]
    cases j <;> first | exact iu.property | exact iw.property
  · have hall (k : RootIncidence FX X v c) : k = iu ∨ k = iw := by
      have hk : k.val = iu.val ∨ k.val = iw.val := by simpa [hN] using k.property
      exact hk.imp (fun hk => Subtype.ext hk) (fun hk => Subtype.ext hk)
    have hne : iu ≠ iw := by intro heq; rw [heq] at horder; exact lt_irrefl _ horder
    intro gain loss
    rw [CanonicalMatching.sum_two iu iw hne hall, CanonicalMatching.sum_two iu iw hne hall]
    simpa only [Nat.cast_add] using
      canonicalColourCharge_two_corrected h hca hcb hav iu iw hN horder i j hp gain loss

end
end CI2ZF.Appendix.CV
