import ZeroFreeness.Coupling.Vigoda.IncidenceMatching

/-!
# Root components and their actual off-root pieces

The component family is an image of the active root neighbours, so repeated
neighbours of the same component do not create repeated component records.
All properties below follow from graph paths and the concrete flip sets.
-/

namespace ZeroFreeness.RootComponentGeometry

open Finset PottsCI PottsCI.Vigoda
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V]

@[simp] lemma mem_offRootComponent {F : HardListInstance V C} {X : V → C}
    {v u w : V} {a c : C} :
    w ∈ offRootComponent F X v a c u ↔
      Relation.ReflTransGen (offRootAlternatingAdj F X v a c) u w := by
  simp [offRootComponent]

lemma self_mem_offRootComponent (F : HardListInstance V C) (X : V → C)
    (v u : V) (a c : C) : u ∈ offRootComponent F X v a c u :=
  mem_offRootComponent.mpr .refl

lemma ne_root_of_mem_offRootComponent {F : HardListInstance V C} {X : V → C}
    {v u w : V} {a c : C} (hu : u ≠ v)
    (hw : w ∈ offRootComponent F X v a c u) : w ≠ v := by
  rw [mem_offRootComponent] at hw
  induction hw with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2.1

lemma offRoot_path_symm [Fintype C] {F : HardListInstance V C} {X : V → C}
    {v u w : V} {a c : C}
    (h : Relation.ReflTransGen (offRootAlternatingAdj F X v a c) u w) :
    Relation.ReflTransGen (offRootAlternatingAdj F X v a c) w u := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    exact ih.head ⟨hstep.2.1, hstep.1, alternatingAdj_symm hstep.2.2⟩

lemma offRootComponent_eq_of_mem [Fintype C] {F : HardListInstance V C} {X : V → C}
    {v u w : V} {a c : C} (hw : w ∈ offRootComponent F X v a c u) :
    offRootComponent F X v a c w = offRootComponent F X v a c u := by
  ext z
  simp only [mem_offRootComponent] at hw ⊢
  exact ⟨fun hz => hw.trans hz, fun hz => (offRoot_path_symm hw).trans hz⟩

lemma offRootComponent_disjoint_or_eq [Fintype C] (F : HardListInstance V C) (X : V → C)
    (v u w : V) (a c : C) :
    Disjoint (offRootComponent F X v a c u) (offRootComponent F X v a c w) ∨
      offRootComponent F X v a c u = offRootComponent F X v a c w := by
  by_cases h : Disjoint (offRootComponent F X v a c u) (offRootComponent F X v a c w)
  · exact Or.inl h
  · right
    obtain ⟨z, hzu, hzw⟩ := Finset.not_disjoint_iff.mp h
    exact (offRootComponent_eq_of_mem hzu).symm.trans (offRootComponent_eq_of_mem hzw)

def rootNeighbours (F : HardListInstance V C) (X : V → C) (v : V) (c : C) : Finset V :=
  univ.filter fun u => F.graph.Adj v u ∧ X u = c

@[simp] lemma mem_rootNeighbours {F : HardListInstance V C} {X : V → C}
    {v u : V} {c : C} : u ∈ rootNeighbours F X v c ↔ F.graph.Adj v u ∧ X u = c := by
  simp [rootNeighbours]

lemma rootNeighbour_ne_root {F : HardListInstance V C} {X : V → C}
    {v u : V} {c : C} (hu : u ∈ rootNeighbours F X v c) : u ≠ v :=
  (mem_rootNeighbours.mp hu).1.ne.symm

/-- Delete the root and take each distinct component meeting a root neighbour. -/
def rootFamily (F : HardListInstance V C) (X : V → C) (v : V) (c : C) :
    Finset (Finset V) :=
  (rootNeighbours F X v c).image (offRootComponent F X v (X v) c)

theorem mem_root_flipSet_iff [Fintype C] {F : HardListInstance V C} {X : V → C}
    {v w : V} {c : C} (hc : c ≠ X v) :
    w ∈ flipSet F.graph X v c ↔ w = v ∨
      ∃ u ∈ rootNeighbours F X v c, w ∈ offRootComponent F X v (X v) c u := by
  constructor
  · intro hw
    rw [mem_flipSet] at hw
    induction hw with
    | refl => exact Or.inl rfl
    | @tail y z _ hstep ih =>
      by_cases hz : z = v
      · exact Or.inl hz
      · right
        by_cases hy : y = v
        · subst y
          have hzc : X z = c := by
            rcases hstep.2 with h | h
            · exact h.2
            · exact (hc h.1.symm).elim
          exact ⟨z, mem_rootNeighbours.mpr ⟨hstep.1, hzc⟩,
            self_mem_offRootComponent F X v z (X v) c⟩
        · rcases ih with hroot | ⟨u, hu, hpath⟩
          · exact (hy hroot).elim
          · exact ⟨u, hu, mem_offRootComponent.mpr
              ((mem_offRootComponent.mp hpath).tail ⟨hy, hz, hstep⟩)⟩
  · rintro (rfl | ⟨u, hu, hw⟩)
    · exact self_mem_flipSet
    · rw [mem_flipSet]
      have hpath : Relation.ReflTransGen (alternatingAdj F.graph X (X v) c) u w := by
        rw [mem_offRootComponent] at hw
        induction hw with
        | refl => exact .refl
        | tail _ hstep ih => exact ih.tail hstep.2.2
      exact hpath.head ⟨(mem_rootNeighbours.mp hu).1,
        Or.inl ⟨rfl, (mem_rootNeighbours.mp hu).2⟩⟩

/-- The full root component is the root plus the union of its distinct
off-root components; no component decomposition is assumed. -/
theorem root_flipSet_eq [Fintype C] (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) :
    flipSet F.graph X v c = insert v ((rootFamily F X v c).biUnion id) := by
  ext w
  simp only [mem_root_flipSet_iff hc, mem_insert, mem_biUnion, rootFamily, mem_image]
  constructor
  · rintro (h | ⟨u, hu, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, ⟨u, hu, rfl⟩, hw⟩
  · rintro (h | ⟨S, ⟨u, hu, rfl⟩, hw⟩)
    · exact Or.inl h
    · exact Or.inr ⟨u, hu, hw⟩

lemma rootFamily_nonempty_component {F : HardListInstance V C} {X : V → C}
    {v : V} {c : C} {S : Finset V} (hS : S ∈ rootFamily F X v c) : S.Nonempty := by
  obtain ⟨u, _, rfl⟩ := mem_image.mp hS
  exact ⟨u, self_mem_offRootComponent F X v u (X v) c⟩

lemma rootFamily_avoids_root {F : HardListInstance V C} {X : V → C}
    {v : V} {c : C} {S : Finset V} (hS : S ∈ rootFamily F X v c) : v ∉ S := by
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hS
  intro hv
  exact ne_root_of_mem_offRootComponent (rootNeighbour_ne_root hu) hv rfl

lemma rootFamily_pairwise_disjoint [Fintype C] (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) : (rootFamily F X v c : Set (Finset V)).Pairwise Disjoint := by
  intro S hS T hT hne
  obtain ⟨u, _, rfl⟩ := mem_image.mp hS
  obtain ⟨w, _, rfl⟩ := mem_image.mp hT
  exact (offRootComponent_disjoint_or_eq F X v u w (X v) c).resolve_right hne

abbrev RootIncidence (F : HardListInstance V C) (X : V → C) (v : V) (c : C) :=
  {u : V // u ∈ rootNeighbours F X v c}

abbrev RootPiece (F : HardListInstance V C) (X : V → C) (v : V) (c : C) :=
  {S : Finset V // S ∈ rootFamily F X v c}

def componentOf (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (u : RootIncidence F X v c) : RootPiece F X v c :=
  ⟨offRootComponent F X v (X v) c u, mem_image.mpr ⟨u, u.property, rfl⟩⟩

lemma componentOf_surjective (F : HardListInstance V C) (X : V → C) (v : V) (c : C) :
    Function.Surjective (componentOf F X v c) := by
  rintro ⟨S, hS⟩
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hS
  exact ⟨⟨u, hu⟩, rfl⟩

lemma incidence_mem_component (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (u : RootIncidence F X v c) : u.val ∈ (componentOf F X v c u).val :=
  self_mem_offRootComponent F X v u (X v) c

lemma component_incidence_count_pos (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (S : RootPiece F X v c) : 0 < IncidenceMatching.count (componentOf F X v c) S :=
  IncidenceMatching.count_pos_of_surjective _ (componentOf_surjective F X v c) S

lemma component_incidence_count_le (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (S : RootPiece F X v c) : IncidenceMatching.count (componentOf F X v c) S ≤ S.val.card := by
  let toVertex : {u : RootIncidence F X v c // componentOf F X v c u = S} → S.val :=
    fun u => ⟨u.val.val, by
      have hmem := incidence_mem_component F X v c u.val
      rwa [u.property] at hmem⟩
  have hinj : Function.Injective toVertex := by
    intro u w huw
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : S.val => t.val) huw
  have h := Fintype.card_le_of_injective toVertex hinj
  rw [Fintype.card_coe] at h
  simpa only [Fintype.card_subtype, IncidenceMatching.count] using h

/-- Two distinct neighbours of the same root colour need an intermediate
vertex of the other colour if they lie in one alternating component. -/
theorem shared_component_card_ge_three {F : HardListInstance V C} {X : V → C}
    {v u w : V} {a c : C} (hac : a ≠ c) (hu : X u = c) (hw : X w = c)
    (huw : u ≠ w) (hmem : w ∈ offRootComponent F X v a c u) :
    3 ≤ (offRootComponent F X v a c u).card := by
  have hp := mem_offRootComponent.mp hmem
  obtain heq | ⟨z, huz, _⟩ := hp.cases_head
  · exact (huw heq).elim
  · have hza : X z = a := by
      rcases huz.2.2.2 with h | h
      · exact (hac (h.1.symm.trans hu)).elim
      · exact h.2
    have hzu : z ≠ u := fun h => hac (hza.symm.trans (h ▸ hu))
    have hzw : z ≠ w := fun h => hac (hza.symm.trans (h ▸ hw))
    have hzmem : z ∈ offRootComponent F X v a c u :=
      mem_offRootComponent.mpr (.single huz)
    have hsub : ({u, w, z} : Finset V) ⊆ offRootComponent F X v a c u := by
      intro t ht
      simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact self_mem_offRootComponent F X v _ a c
      · exact hmem
      · exact hzmem
    have h := card_le_card hsub
    simpa [huw, hzu, hzw, Ne.symm hzu, Ne.symm hzw] using h

theorem root_flipSet_card [Fintype C] (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) :
    (flipSet F.graph X v c).card = 1 + ∑ S ∈ rootFamily F X v c, S.card := by
  have hnot : v ∉ (rootFamily F X v c).biUnion id := by
    simp only [mem_biUnion]
    rintro ⟨S, hS, hv⟩
    exact rootFamily_avoids_root hS hv
  rw [root_flipSet_eq F X v c hc, card_insert_of_notMem hnot]
  change ((rootFamily F X v c).biUnion fun S => S).card + 1 = _
  rw [card_biUnion (rootFamily_pairwise_disjoint F X v c)]
  simp [Nat.add_comm]

lemma root_piece_subset_root [Fintype C] {F : HardListInstance V C} {X : V → C}
    {v : V} {c : C} (hc : c ≠ X v) {S : Finset V} (hS : S ∈ rootFamily F X v c) :
    S ⊆ flipSet F.graph X v c := by
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hS
  intro w hw
  exact (mem_root_flipSet_iff hc).mpr (Or.inr ⟨u, hu, hw⟩)

/-- Root feasibility is exactly root-list feasibility together with the
feasibility of every actual off-root piece. -/
theorem root_flipAllowed_iff [Fintype C] (F : HardListInstance V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) :
    flipAllowed F (flipSet F.graph X v c)
      (flipConfiguration X (flipSet F.graph X v c) (X v) c) ↔
    c ∈ F.list v ∧ ∀ S ∈ rootFamily F X v c,
      flipAllowed F S (flipConfiguration X S (X v) c) := by
  constructor
  · intro h
    constructor
    · simpa using h v self_mem_flipSet
    · intro S hS w hw
      have hwroot := root_piece_subset_root hc hS hw
      simpa only [flipConfiguration_of_mem hwroot, flipConfiguration_of_mem hw] using h w hwroot
  · rintro ⟨hv, hp⟩ w hw
    rcases (mem_root_flipSet_iff hc).mp hw with rfl | ⟨u, hu, hwu⟩
    · simpa using hv
    · have hS : offRootComponent F X v (X v) c u ∈ rootFamily F X v c :=
        mem_image.mpr ⟨u, hu, rfl⟩
      simpa only [flipConfiguration_of_mem hw, flipConfiguration_of_mem hwu] using
        hp _ hS w hwu

/-- In the opposite colouring the root has neither component colour, so
deleting it does not change this actual component. -/
theorem offRootComponent_eq_flipSet_of_root_colour [Fintype C]
    (F : HardListInstance V C) (X : V → C) (v u : V) (a c : C)
    (hu : X u = c) (hva : X v ≠ a) (hvc : X v ≠ c) :
    offRootComponent F X v a c u = flipSet F.graph X u a := by
  have hrel : offRootAlternatingAdj F X v a c = alternatingAdj F.graph X c a := by
    funext w z
    apply propext
    constructor
    · intro h
      exact alternatingAdj_comm_colours.mp h.2.2
    · intro h
      have h' := alternatingAdj_comm_colours.mp h
      have hw : w ≠ v := by
        intro heq
        subst w
        rcases h'.2 with hh | hh
        · exact hva hh.1
        · exact hvc hh.1
      have hz : z ≠ v := by
        intro heq
        subst z
        rcases h'.2 with hh | hh
        · exact hvc hh.2
        · exact hva hh.2
      exact ⟨hw, hz, h'⟩
  ext w
  simp only [mem_offRootComponent, mem_flipSet, hu, hrel]

theorem _root_.PottsCI.Vigoda.RootLocalPair.rootNeighbours_eq [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    rootNeighbours FX X v c = rootNeighbours FY Y v c := by
  ext u
  simp only [mem_rootNeighbours]
  constructor
  · rintro ⟨hu, hc⟩
    have huv : u ≠ v := hu.ne.symm
    exact ⟨(h.regular_root_edge_iff u c huv hc hca hcb).mp hu,
      (h.agree_off_root u huv).symm.trans hc⟩
  · rintro ⟨hu, hc⟩
    have huv : u ≠ v := hu.ne.symm
    have hXc := (h.agree_off_root u huv).trans hc
    exact ⟨(h.regular_root_edge_iff u c huv hXc hca hcb).mpr hu, hXc⟩

theorem _root_.PottsCI.Vigoda.RootLocalPair.offRootComponent_eq_opposite_flipSet [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hcb : c ≠ b)
    (hu : u ∈ rootNeighbours FX X v c) :
    offRootComponent FX X v a c u = flipSet FY.graph Y u a := by
  rw [h.offRootComponent_eq]
  apply offRootComponent_eq_flipSet_of_root_colour
  · exact (h.agree_off_root u (rootNeighbour_ne_root hu)).symm.trans
      (mem_rootNeighbours.mp hu).2
  · rw [h.Y_root]
    exact h.colours_ne.symm
  · rw [h.Y_root]
    exact hcb.symm

theorem _root_.PottsCI.Vigoda.RootLocalPair.offRoot_flipAllowed_iff [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v u : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (hu : u ∈ rootNeighbours FX X v c) :
    flipAllowed FX (offRootComponent FX X v a c u)
      (flipConfiguration X (offRootComponent FX X v a c u) a c) ↔
    flipAllowed FY (flipSet FY.graph Y u a)
      (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) := by
  have hset := h.offRootComponent_eq_opposite_flipSet hcb hu
  have huc : Y u = c := (h.agree_off_root u (rootNeighbour_ne_root hu)).symm.trans
    (mem_rootNeighbours.mp hu).2
  have hpoint (w : V) (hw : w ∈ offRootComponent FX X v a c u) :
      flipConfiguration X (offRootComponent FX X v a c u) a c w =
        flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a w := by
    have hw' : w ∈ flipSet FY.graph Y u a := hset ▸ hw
    have hwv := ne_root_of_mem_offRootComponent (rootNeighbour_ne_root hu) hw
    rw [flipConfiguration_of_mem hw, flipConfiguration_of_mem hw',
      h.agree_off_root w hwv, huc]
    rcases colour_eq_of_mem_flipSet hw' with hcol | hcol
    · rw [huc] at hcol
      simp [hcol, hca]
    · simp [hcol, hca.symm]
  constructor
  · intro hallowed w hw
    have hw' : w ∈ offRootComponent FX X v a c u := hset.symm ▸ hw
    have hwv := ne_root_of_mem_offRootComponent (rootNeighbour_ne_root hu) hw'
    rw [← h.offRoot_list_eq w hwv, ← hpoint w hw']
    exact hallowed w hw'
  · intro hallowed w hw
    have hwv := ne_root_of_mem_offRootComponent (rootNeighbour_ne_root hu) hw
    rw [h.offRoot_list_eq w hwv, hpoint w hw]
    exact hallowed w (hset ▸ hw)

/-- The root proposal's feasibility is determined by the root colour list
and the concrete opposite-side proposals meeting its root neighbours. -/
theorem _root_.PottsCI.Vigoda.RootLocalPair.root_flipAllowed_iff_opposite [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    flipAllowed FX (flipSet FX.graph X v c)
      (flipConfiguration X (flipSet FX.graph X v c) (X v) c) ↔
    c ∈ FX.list v ∧ ∀ u ∈ rootNeighbours FX X v c,
      flipAllowed FY (flipSet FY.graph Y u a)
        (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a) := by
  rw [root_flipAllowed_iff FX X v c (by rwa [h.X_root])]
  apply and_congr_right
  intro _
  constructor
  · intro hallowed u hu
    have hS : offRootComponent FX X v (X v) c u ∈ rootFamily FX X v c :=
      mem_image.mpr ⟨u, hu, rfl⟩
    have hp := hallowed _ hS
    rw [h.X_root] at hp
    exact (h.offRoot_flipAllowed_iff hca hcb hu).mp hp
  · intro hallowed S hS
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hS
    rw [h.X_root]
    exact (h.offRoot_flipAllowed_iff hca hcb hu).mpr (hallowed u hu)

omit [Fintype V] in
/-- Swapping the two actual instances gives the symmetric colour family. -/
theorem _root_.PottsCI.Vigoda.RootLocalPair.symm
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) : RootLocalPair FY FX Y X v b a where
  X_root := h.Y_root
  Y_root := h.X_root
  colours_ne := h.colours_ne.symm
  agree_off_root u hu := (h.agree_off_root u hu).symm
  properX := h.properY
  properY := h.properX
  offRoot_edge_iff u w hu hw := (h.offRoot_edge_iff u w hu hw).symm
  offRoot_list_eq u hu := (h.offRoot_list_eq u hu).symm
  regular_root_edge_iff u c hu huc hcb hca :=
    (h.regular_root_edge_iff u c hu ((h.agree_off_root u hu).trans huc) hca hcb).symm
  root_list_regular_iff c hcb hca := (h.root_list_regular_iff c hca hcb).symm

/-- The two colour families use the very same active regular neighbours. -/
def rootIncidenceEquiv [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    RootIncidence FX X v c ≃ RootIncidence FY Y v c :=
  Equiv.subtypeEquivRight fun u => by rw [h.rootNeighbours_eq hca hcb]

def oppositeComponentOf [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (u : RootIncidence FX X v c) : RootPiece FY Y v c :=
  componentOf FY Y v c (rootIncidenceEquiv h hca hcb u)

lemma oppositeComponentOf_surjective [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    Function.Surjective (oppositeComponentOf h hca hcb) :=
  (componentOf_surjective FY Y v c).comp (rootIncidenceEquiv h hca hcb).surjective

lemma opposite_component_incidence_count_le [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (S : RootPiece FY Y v c) :
    IncidenceMatching.count (oppositeComponentOf h hca hcb) S ≤ S.val.card := by
  change IncidenceMatching.count
    (fun u => componentOf FY Y v c (rootIncidenceEquiv h hca hcb u)) S ≤ _
  rw [IncidenceMatching.count_comp_equiv]
  exact component_incidence_count_le FY Y v c S

/-- The incidence estimate specialized to actual components of the two
root-local graphs. The incidence bounds are supplied by graph membership. -/
theorem actual_incidence_charge_le_four_thirds [Fintype C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b)
    (r : RootPiece FX X v c → ℝ) (s : RootPiece FY Y v c → ℝ)
    (hr : ∀ S, 0 ≤ r S) (hs : ∀ S, 0 ≤ s S)
    (hrp : ∀ S, r S ≤ vigodaMass S.val.card)
    (hsp : ∀ S, s S ≤ vigodaMass S.val.card) :
    (∑ S, (S.val.card : ℝ) * r S) + (∑ S, (S.val.card : ℝ) * s S) -
      (∑ i, IncidenceMatching.atIncidence (componentOf FX X v c)
        (oppositeComponentOf h hca hcb) r s i) ≤
      (4 / 3 : ℝ) * (rootNeighbours FX X v c).card := by
  have hb := IncidenceMatching.incidence_charge_le_four_thirds
    (componentOf FX X v c) (oppositeComponentOf h hca hcb)
    (componentOf_surjective FX X v c) (oppositeComponentOf_surjective h hca hcb)
    r s (fun S => S.val.card) (fun S => S.val.card) hr hs hrp hsp
    (component_incidence_count_le FX X v c) (opposite_component_incidence_count_le h hca hcb)
  simpa only [Fintype.card_coe] using hb

theorem root_flipSet_card_single_neighbour [Fintype C]
    (F : HardListInstance V C) (X : V → C) (v u : V) (c : C)
    (hc : c ≠ X v) (hN : rootNeighbours F X v c = {u}) :
    (flipSet F.graph X v c).card = 1 + (offRootComponent F X v (X v) c u).card := by
  rw [root_flipSet_card F X v c hc]
  simp [rootFamily, hN]

theorem root_flipSet_card_two_neighbours [Fintype C]
    (F : HardListInstance V C) (X : V → C) (v u w : V) (c : C)
    (hc : c ≠ X v) (hN : rootNeighbours F X v c = {u, w})
    (hpieces : offRootComponent F X v (X v) c u ≠ offRootComponent F X v (X v) c w) :
    (flipSet F.graph X v c).card =
      1 + (offRootComponent F X v (X v) c u).card +
        (offRootComponent F X v (X v) c w).card := by
  rw [root_flipSet_card F X v c hc]
  simp [rootFamily, hN, hpieces, Nat.add_assoc]

end
end ZeroFreeness.RootComponentGeometry
