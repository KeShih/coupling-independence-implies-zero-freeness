import ZeroFreeness.Coupling.Vigoda.HardMoveClassification

/-!
# Lemma `lem:cv-root-local-structure` (companion appendix CV, Lemma 5.6)

Fix two root-local active hard instances `FX, FY` (the formal version of the
coupled activation outcome of `lem:coupled-activation-root-local`), with
`X v = a`, `Y v = b`.  For a regular colour `c ∉ {a,b}` the set
`Γ_c = {u ∈ N(v) : X u = Y u = c, vu ∈ E_X ∩ E_Y}` is `gammaSet`.

* Part 1 (`cv_root_local_structure_part1`, and its mirror
  `cv_root_local_structure_part1_symm`): deleting `v` from the root-containing
  `{a,c}`-component in `F_X` gives exactly the `{a,c}`-components in `F_Y`
  meeting `Γ_c` (which avoid `v`), with the same post-swap assignments; the
  root move is feasible iff `c` is root-allowed (`c ∈ L_{X,v} ∩ L_{Y,v}`) and
  every corresponding off-root move is feasible.
* Part 2 (`cv_root_local_structure_part2`): for an off-root proposal vertex
  and a fixed colour pair, the two grown components have the same vertex set,
  the same post-swap assignments and the same feasibility whenever both avoid
  `v`; if they differ, one of them contains `v` and its flip recolours `v`.

`cv_root_local_structure` packages both parts in one statement.
-/

namespace ZeroFreeness.Appendix.CV

open Finset PottsCI PottsCI.Vigoda ZeroFreeness ZeroFreeness.RootComponentGeometry

attribute [local instance] Classical.propDecidable

noncomputable section
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]

/-- The paper's `Γ_c`: root neighbours of common colour `c` whose root edge is
active on both sides. -/
def gammaSet (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) : Finset V :=
  univ.filter fun u => FX.graph.Adj v u ∧ FY.graph.Adj v u ∧ X u = c ∧ Y u = c

lemma gammaSet_eq_left {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    gammaSet FX FY X Y v c = rootNeighbours FX X v c := by
  ext u
  simp only [gammaSet, mem_filter, mem_univ, true_and, mem_rootNeighbours]
  constructor
  · rintro ⟨hX, -, hc, -⟩
    exact ⟨hX, hc⟩
  · rintro ⟨hX, hc⟩
    have huv : u ≠ v := hX.ne.symm
    exact ⟨hX, (h.regular_root_edge_iff u c huv hc hca hcb).mp hX, hc,
      (h.agree_off_root u huv).symm.trans hc⟩

lemma gammaSet_eq_right {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    gammaSet FX FY X Y v c = rootNeighbours FY Y v c := by
  rw [gammaSet_eq_left h hca hcb, h.rootNeighbours_eq hca hcb]

lemma gammaSet_symm (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) :
    gammaSet FY FX Y X v c = gammaSet FX FY X Y v c := by
  ext u
  simp only [gammaSet, mem_filter, mem_univ, true_and]
  tauto

/-- `c` is root-allowed: it lies in both active root lists. -/
def RootAllowed (FX FY : HardListInstance V C) (v : V) (c : C) : Prop :=
  c ∈ FX.list v ∧ c ∈ FY.list v

/-- Part 1 of `lem:cv-root-local-structure`, for the `X`-side root move with
colour pair `{a,c}`. -/
theorem cv_root_local_structure_part1
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    -- the off-root `{a,c}`-components of `F_Y` meeting `Γ_c` avoid `v`
    (∀ u ∈ gammaSet FX FY X Y v c, v ∉ flipSet FY.graph Y u a) ∧
    -- deleting `v` from the root component gives exactly these components
    rootFamily FX X v c = (gammaSet FX FY X Y v c).image (fun u => flipSet FY.graph Y u a) ∧
    (flipSet FX.graph X v c).erase v =
      (gammaSet FX FY X Y v c).biUnion (fun u => flipSet FY.graph Y u a) ∧
    flipSet FX.graph X v c =
      insert v ((gammaSet FX FY X Y v c).biUnion (fun u => flipSet FY.graph Y u a)) ∧
    -- with the same post-swap assignments off the root, and colour `c` at `v`
    (∀ u ∈ gammaSet FX FY X Y v c, ∀ w ∈ flipSet FY.graph Y u a,
      flipConfiguration X (flipSet FX.graph X v c) (X v) c w =
        flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a w) ∧
    flipConfiguration X (flipSet FX.graph X v c) (X v) c v = c ∧
    -- feasibility of the root move
    (flipAllowed FX (flipSet FX.graph X v c)
        (flipConfiguration X (flipSet FX.graph X v c) (X v) c) ↔
      RootAllowed FX FY v c ∧ ∀ u ∈ gammaSet FX FY X Y v c,
        flipAllowed FY (flipSet FY.graph Y u a)
          (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a)) := by
  have hcX : c ≠ X v := by rw [h.X_root]; exact hca
  have hΓ := gammaSet_eq_left h hca hcb
  rw [hΓ]
  have hpiece (u : V) (hu : u ∈ rootNeighbours FX X v c) :
      offRootComponent FX X v (X v) c u = flipSet FY.graph Y u a := by
    rw [h.X_root]
    exact h.offRootComponent_eq_opposite_flipSet hcb hu
  have herase : (flipSet FX.graph X v c).erase v =
      (rootNeighbours FX X v c).biUnion (fun u => flipSet FY.graph Y u a) := by
    ext w
    simp only [mem_erase, mem_biUnion]
    constructor
    · rintro ⟨hwv, hw⟩
      rcases (mem_root_flipSet_iff hcX).mp hw with rfl | ⟨u, hu, hwu⟩
      · exact (hwv rfl).elim
      · exact ⟨u, hu, hpiece u hu ▸ hwu⟩
    · rintro ⟨u, hu, hwu⟩
      rw [← hpiece u hu] at hwu
      exact ⟨ne_root_of_mem_offRootComponent (rootNeighbour_ne_root hu) hwu,
        (mem_root_flipSet_iff hcX).mpr (Or.inr ⟨u, hu, hwu⟩)⟩
  refine ⟨fun u hu => regular_piece_no_root h hcb u hu, ?_, herase, ?_, ?_,
    flipConfiguration_at_start, ?_⟩
  · exact image_congr fun u hu => hpiece u hu
  · rw [← herase, insert_erase self_mem_flipSet]
  · intro u hu w hw
    have hwv : w ≠ v := by
      rw [← hpiece u hu] at hw
      exact ne_root_of_mem_offRootComponent (rootNeighbour_ne_root hu) hw
    have hwX : w ∈ flipSet FX.graph X v c := by
      have : w ∈ (flipSet FX.graph X v c).erase v := by
        rw [herase]; exact mem_biUnion.mpr ⟨u, hu, hw⟩
      exact mem_of_mem_erase this
    have huc : Y u = c :=
      (h.agree_off_root u (rootNeighbour_ne_root hu)).symm.trans (mem_rootNeighbours.mp hu).2
    rw [flipConfiguration_of_mem hwX, flipConfiguration_of_mem hw, h.agree_off_root w hwv,
      h.X_root, huc]
    rcases colour_eq_of_mem_flipSet hw with hcol | hcol
    · rw [huc] at hcol
      simp [hcol, hca]
    · simp [hcol, hca.symm]
  · rw [h.root_flipAllowed_iff_opposite hca hcb]
    unfold RootAllowed
    constructor
    · rintro ⟨hl, hp⟩
      exact ⟨⟨hl, (h.root_list_regular_iff c hca hcb).mp hl⟩, hp⟩
    · rintro ⟨⟨hl, _⟩, hp⟩
      exact ⟨hl, hp⟩

/-- The analogous statement with `a, X, Y` replaced by `b, Y, X`. -/
theorem cv_root_local_structure_part1_symm
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    (∀ u ∈ gammaSet FX FY X Y v c, v ∉ flipSet FX.graph X u b) ∧
    rootFamily FY Y v c = (gammaSet FX FY X Y v c).image (fun u => flipSet FX.graph X u b) ∧
    (flipSet FY.graph Y v c).erase v =
      (gammaSet FX FY X Y v c).biUnion (fun u => flipSet FX.graph X u b) ∧
    flipSet FY.graph Y v c =
      insert v ((gammaSet FX FY X Y v c).biUnion (fun u => flipSet FX.graph X u b)) ∧
    (∀ u ∈ gammaSet FX FY X Y v c, ∀ w ∈ flipSet FX.graph X u b,
      flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c w =
        flipConfiguration X (flipSet FX.graph X u b) (X u) b w) ∧
    flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c v = c ∧
    (flipAllowed FY (flipSet FY.graph Y v c)
        (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) ↔
      RootAllowed FX FY v c ∧ ∀ u ∈ gammaSet FX FY X Y v c,
        flipAllowed FX (flipSet FX.graph X u b)
          (flipConfiguration X (flipSet FX.graph X u b) (X u) b)) := by
  have hs := cv_root_local_structure_part1 h.symm hcb hca
  rw [gammaSet_symm] at hs
  have hr : RootAllowed FY FX v c ↔ RootAllowed FX FY v c := and_comm
  rw [hr] at hs
  exact hs

/-- Part 2 of `lem:cv-root-local-structure`: off-root proposals. -/
theorem cv_root_local_structure_part2
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (u : V) (huv : u ≠ v) (d : C) (hd : d ≠ X u) :
    (v ∉ flipSet FX.graph X u d → v ∉ flipSet FY.graph Y u d →
      flipSet FX.graph X u d = flipSet FY.graph Y u d ∧
      (∀ w ∈ flipSet FX.graph X u d,
        flipConfiguration X (flipSet FX.graph X u d) (X u) d w =
          flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d w) ∧
      (flipAllowed FX (flipSet FX.graph X u d)
          (flipConfiguration X (flipSet FX.graph X u d) (X u) d) ↔
        flipAllowed FY (flipSet FY.graph Y u d)
          (flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d))) ∧
    (flipSet FX.graph X u d ≠ flipSet FY.graph Y u d →
      (v ∈ flipSet FX.graph X u d ∧
          flipConfiguration X (flipSet FX.graph X u d) (X u) d v ≠ X v) ∨
        (v ∈ flipSet FY.graph Y u d ∧
          flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d v ≠ Y v)) := by
  have hxy := h.agree_off_root u huv
  have hdY : d ≠ Y u := by rw [← hxy]; exact hd
  constructor
  · intro hvX hvY
    have hset := common_component_sets h u d hvX hvY
    have hpoint (w : V) (hw : w ∈ flipSet FX.graph X u d) :
        flipConfiguration X (flipSet FX.graph X u d) (X u) d w =
          flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d w := by
      have hwv : w ≠ v := fun hh => hvX (hh ▸ hw)
      have hw' : w ∈ flipSet FY.graph Y u d := hset ▸ hw
      rw [flipConfiguration_of_mem hw, flipConfiguration_of_mem hw', h.agree_off_root w hwv, hxy]
    refine ⟨hset, hpoint, ?_⟩
    constructor
    · intro hA w hw
      have hwX : w ∈ flipSet FX.graph X u d := hset.symm ▸ hw
      have hwv : w ≠ v := fun hh => hvX (hh ▸ hwX)
      rw [← h.offRoot_list_eq w hwv, ← hpoint w hwX]
      exact hA w hwX
    · intro hA w hw
      have hwv : w ≠ v := fun hh => hvX (hh ▸ hw)
      rw [h.offRoot_list_eq w hwv, hpoint w hw]
      exact hA w (hset ▸ hw)
  · intro hne
    by_cases hvX : v ∈ flipSet FX.graph X u d
    · exact Or.inl ⟨hvX, (flipConfiguration_ne_iff hd v).mpr hvX⟩
    · by_cases hvY : v ∈ flipSet FY.graph Y u d
      · exact Or.inr ⟨hvY, (flipConfiguration_ne_iff hdY v).mpr hvY⟩
      · exact (hne (common_component_sets h u d hvX hvY)).elim

/-- `lem:cv-root-local-structure`, both parts in one statement. -/
theorem cv_root_local_structure
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    (∀ c, c ≠ a → c ≠ b →
      -- Part 1, `X`-side root `{a,c}`-move
      ((∀ u ∈ gammaSet FX FY X Y v c, v ∉ flipSet FY.graph Y u a) ∧
        rootFamily FX X v c =
          (gammaSet FX FY X Y v c).image (fun u => flipSet FY.graph Y u a) ∧
        (∀ u ∈ gammaSet FX FY X Y v c, ∀ w ∈ flipSet FY.graph Y u a,
          flipConfiguration X (flipSet FX.graph X v c) (X v) c w =
            flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a w) ∧
        (flipAllowed FX (flipSet FX.graph X v c)
            (flipConfiguration X (flipSet FX.graph X v c) (X v) c) ↔
          RootAllowed FX FY v c ∧ ∀ u ∈ gammaSet FX FY X Y v c,
            flipAllowed FY (flipSet FY.graph Y u a)
              (flipConfiguration Y (flipSet FY.graph Y u a) (Y u) a))) ∧
      -- Part 1, `Y`-side root `{b,c}`-move
      ((∀ u ∈ gammaSet FX FY X Y v c, v ∉ flipSet FX.graph X u b) ∧
        rootFamily FY Y v c =
          (gammaSet FX FY X Y v c).image (fun u => flipSet FX.graph X u b) ∧
        (∀ u ∈ gammaSet FX FY X Y v c, ∀ w ∈ flipSet FX.graph X u b,
          flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c w =
            flipConfiguration X (flipSet FX.graph X u b) (X u) b w) ∧
        (flipAllowed FY (flipSet FY.graph Y v c)
            (flipConfiguration Y (flipSet FY.graph Y v c) (Y v) c) ↔
          RootAllowed FX FY v c ∧ ∀ u ∈ gammaSet FX FY X Y v c,
            flipAllowed FX (flipSet FX.graph X u b)
              (flipConfiguration X (flipSet FX.graph X u b) (X u) b)))) ∧
    -- Part 2
    (∀ u, u ≠ v → ∀ d, d ≠ X u →
      (v ∉ flipSet FX.graph X u d → v ∉ flipSet FY.graph Y u d →
        flipSet FX.graph X u d = flipSet FY.graph Y u d ∧
        (∀ w ∈ flipSet FX.graph X u d,
          flipConfiguration X (flipSet FX.graph X u d) (X u) d w =
            flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d w) ∧
        (flipAllowed FX (flipSet FX.graph X u d)
            (flipConfiguration X (flipSet FX.graph X u d) (X u) d) ↔
          flipAllowed FY (flipSet FY.graph Y u d)
            (flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d))) ∧
      (flipSet FX.graph X u d ≠ flipSet FY.graph Y u d →
        (v ∈ flipSet FX.graph X u d ∧
            flipConfiguration X (flipSet FX.graph X u d) (X u) d v ≠ X v) ∨
          (v ∈ flipSet FY.graph Y u d ∧
            flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d v ≠ Y v))) := by
  refine ⟨fun c hca hcb => ?_, fun u huv d hd => cv_root_local_structure_part2 h u huv d hd⟩
  obtain ⟨h1, h2, -, -, h5, -, h7⟩ := cv_root_local_structure_part1 h hca hcb
  obtain ⟨k1, k2, -, -, k5, -, k7⟩ := cv_root_local_structure_part1_symm h hca hcb
  exact ⟨⟨h1, h2, h5, h7⟩, ⟨k1, k2, k5, k7⟩⟩

end

end ZeroFreeness.Appendix.CV
