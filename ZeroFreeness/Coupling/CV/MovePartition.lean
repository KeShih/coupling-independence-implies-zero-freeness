import ZeroFreeness.Coupling.CV.BaselinePartition

/-!
# Lemma `lem:cv-move-partition` (companion appendix CV, Lemma 5.7)

Setting: two root-local active hard instances (`RootLocalPair FX FY X Y v a b`,
`X v = a`, `Y v = b`) and the actual CV hard kernels `hardStep FX X`,
`hardStep FY Y` with the common off-root allocation
`hardCommonOffRootPartial` (the synchronous coupling of common off-root
moves).

* `xFamilyRows c` are the `X`-side rows of family `c`: the regular family
  (`regularMoveRows`) for `c ∉ {a,b}`, the `X`-off-root rows
  `rootColourOffRows FX FY X Y v` for `c = a`, and the `X`-root move for
  `c = b`.  The `Y`-side rows are `xFamilyRows FY FX Y X v`.  The families are
  pairwise disjoint (`xFamilyRows_disjoint`), and every nonidentity row with
  positive residual after the common coupling lies in exactly one of them
  (`xFamily_exists_unique`, `yFamily_exists_unique`), for every multiplicity.
* The common off-root `{a,b}`-components are `offRootComponent FX X v a b u`
  (equal to the `F_Y` ones).  `B_a` / `B_b` membership is `MeetsRoot FY Y v a`
  / `MeetsRoot FX X v b`.  `row_Ba_only`, `row_Bb_only`, `row_both`,
  `row_neither` are the four rows of the table, and
  `rootColourOffRows_eq_Ba_only` / `rootColourOffRows_symm_eq_Bb_only`
  identify the Lean root-colour families with the block classes
  `B_a \ B_b` and `B_b \ B_a`.
* `cv_move_partition` packages everything.
-/

namespace ZeroFreeness.Appendix.CV

open Finset PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry

attribute [local instance] Classical.propDecidable

noncomputable section
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]
local instance (priority := 2000) movePartitionConfigDecEq : DecidableEq (V → C) :=
  Classical.decEq _

/-! ## The four-row block classification -/

/-- `d` is the partner colour of `x` in the pair `{a,b}`. -/
def Partner (a b x d : C) : Prop := (x = a ∧ d = b) ∨ (x = b ∧ d = a)

lemma Partner.symm {a b x d : C} (hp : Partner a b x d) : Partner b a x d := Or.symm hp

lemma Partner.ne {a b x d : C} (hab : a ≠ b) (hp : Partner a b x d) : d ≠ x := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hab.symm
  · exact hab

lemma Partner.at_other_root {a b x d : C} (hab : a ≠ b) (hp : Partner a b x d) :
    (if b = x then d else x) = a := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [hab.symm]
  · simp

lemma Partner.at_self {a b x d : C} (hab : a ≠ b) (hp : Partner a b x d) :
    (if x = b then a else b) = d := by
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [hab]
  · simp

/-- A set of vertices meets the active root neighbours of colour `c` in `F`. -/
def MeetsRoot (F : HardListInstance V C) (Z : V → C) (v : V) (c : C) (S : Finset V) : Prop :=
  ∃ w ∈ S, w ∈ rootNeighbours F Z v c

/-- The common off-root `{a,b}`-components. -/
def abBlocks (FX : HardListInstance V C) (X : V → C) (v : V) (a b : C) : Finset (Finset V) :=
  (univ.filter fun u => u ≠ v ∧ (X u = a ∨ X u = b)).image (offRootComponent FX X v a b)

lemma offRoot_colour {F : HardListInstance V C} {X : V → C} {v u w : V} {a b : C}
    (hw : w ∈ offRootComponent F X v a b u) (hu : X u = a ∨ X u = b) :
    X w = a ∨ X w = b := by
  rw [mem_offRootComponent] at hw
  induction hw with
  | refl => exact hu
  | tail _ hstep _ =>
    rcases hstep.2.2.2 with hh | hh
    · exact Or.inr hh.2
    · exact Or.inl hh.2

/-- The off-root `{a,b}`-blocks are common to the two instances. -/
lemma block_common {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (u : V) :
    offRootComponent FX X v a b u = offRootComponent FY Y v b a u := by
  rw [h.offRootComponent_eq]
  exact offRootComponent_swap_colours FY Y v u a b

/-- The `Y`-side `{a,b}`-component of `u` reaches `v` iff its block is in `B_a`. -/
theorem reach_Y {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d) :
    v ∈ flipSet FY.graph Y u d ↔ MeetsRoot FY Y v a (offRootComponent FX X v a b u) := by
  have hab := h.colours_ne
  have hpY : Partner a b (Y u) d := h.agree_off_root u huv ▸ hp
  have hdY : d ≠ Y u := hpY.ne hab
  have haY : a ≠ Y v := by rw [h.Y_root]; exact hab
  rw [block_common h u]
  constructor
  · intro hv
    obtain ⟨hset, -⟩ := component_move_from_member FY.graph Y u d hdY v hv
    have hZ : flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d v = a := by
      rw [flipConfiguration_of_mem hv, h.Y_root]
      exact hpY.at_other_root hab
    rw [hZ] at hset
    have hu : u ∈ flipSet FY.graph Y v a := hset ▸ self_mem_flipSet
    rcases (mem_root_flipSet_iff haY).mp hu with huv' | ⟨w, hw, huw⟩
    · exact (huv huv').elim
    · refine ⟨w, ?_, hw⟩
      rw [h.Y_root] at huw
      rw [offRootComponent_eq_of_mem huw]
      exact self_mem_offRootComponent FY Y v w b a
  · rintro ⟨w, hwS, hw⟩
    have hu : u ∈ offRootComponent FY Y v b a w := by
      rw [offRootComponent_eq_of_mem hwS]
      exact self_mem_offRootComponent FY Y v u b a
    have hmem : u ∈ flipSet FY.graph Y v a :=
      (mem_root_flipSet_iff haY).mpr (Or.inr ⟨w, hw, by rw [h.Y_root]; exact hu⟩)
    obtain ⟨hset, -⟩ := component_move_from_member FY.graph Y v a haY u hmem
    have hZ : flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a u = d := by
      rw [flipConfiguration_of_mem hmem, h.Y_root]
      exact hpY.at_self hab
    rw [hZ] at hset
    rw [hset]
    exact self_mem_flipSet

/-- The `X`-side `{a,b}`-component of `u` reaches `v` iff its block is in `B_b`. -/
theorem reach_X {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d) :
    v ∈ flipSet FX.graph X u d ↔ MeetsRoot FX X v b (offRootComponent FX X v a b u) := by
  have hpY : Partner b a (Y u) d := h.agree_off_root u huv ▸ hp.symm
  have hr := reach_Y h.symm huv hpY
  rwa [← block_common h u] at hr

lemma contain_Y {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (u : V)
    (hA : MeetsRoot FY Y v a (offRootComponent FX X v a b u)) :
    offRootComponent FX X v a b u ⊆ flipSet FY.graph Y v a := by
  have haY : a ≠ Y v := by rw [h.Y_root]; exact h.colours_ne
  rw [block_common h u] at hA ⊢
  obtain ⟨w, hwS, hw⟩ := hA
  intro z hz
  apply (mem_root_flipSet_iff haY).mpr (Or.inr ⟨w, hw, ?_⟩)
  rw [h.Y_root, offRootComponent_eq_of_mem hwS]
  exact hz

lemma contain_X {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (u : V)
    (hB : MeetsRoot FX X v b (offRootComponent FX X v a b u)) :
    offRootComponent FX X v a b u ⊆ flipSet FX.graph X v b := by
  rw [block_common h u] at hB ⊢
  exact contain_Y h.symm u hB

lemma offroot_X {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d) (hB : ¬ MeetsRoot FX X v b (offRootComponent FX X v a b u)) :
    v ∉ flipSet FX.graph X u d ∧ flipSet FX.graph X u d = offRootComponent FX X v a b u := by
  have hv : v ∉ flipSet FX.graph X u d := fun hv => hB ((reach_X h huv hp).mp hv)
  refine ⟨hv, ?_⟩
  rw [flipSet_eq_offRootComponent_of_not_mem FX X v u d hv]
  rcases hp with ⟨hx, hd⟩ | ⟨hx, hd⟩
  · rw [hx, hd]
  · rw [hx, hd]
    exact offRootComponent_swap_colours FX X v u b a

lemma offroot_Y {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d) (hA : ¬ MeetsRoot FY Y v a (offRootComponent FX X v a b u)) :
    v ∉ flipSet FY.graph Y u d ∧ flipSet FY.graph Y u d = offRootComponent FX X v a b u := by
  have hpY : Partner b a (Y u) d := h.agree_off_root u huv ▸ hp.symm
  rw [block_common h u] at hA ⊢
  exact offroot_X h.symm huv hpY hA

lemma rootmove_X {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} {d : C}
    (hp : Partner a b (X u) d) (hv : v ∈ flipSet FX.graph X u d) :
    flipSet FX.graph X u d = flipSet FX.graph X v b ∧
      flipConfiguration X (flipSet FX.graph X u d) (X u) d =
        flipConfiguration X (flipSet FX.graph X v b) (X v) b := by
  have hab := h.colours_ne
  obtain ⟨hset, hmove⟩ := component_move_from_member FX.graph X u d (hp.ne hab) v hv
  have hZ : flipConfiguration X (flipSet FX.graph X u d) (X u) d v = b := by
    rw [flipConfiguration_of_mem hv, h.X_root]
    exact hp.symm.at_other_root hab.symm
  rw [hZ] at hset hmove
  exact ⟨hset.symm, hmove.symm⟩

lemma rootmove_Y {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d) (hv : v ∈ flipSet FY.graph Y u d) :
    flipSet FY.graph Y u d = flipSet FY.graph Y v a ∧
      flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d =
        flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a := by
  have hpY : Partner b a (Y u) d := h.agree_off_root u huv ▸ hp.symm
  exact rootmove_X h.symm hpY hv

lemma move_eq_ab {FX : HardListInstance V C} {X : V → C} {v u : V} {a b d : C}
    (hab : a ≠ b) (hp : Partner a b (X u) d) :
    flipConfiguration X (offRootComponent FX X v a b u) (X u) d =
      flipConfiguration X (offRootComponent FX X v a b u) a b := by
  have hu : X u = a ∨ X u = b := by rcases hp with ⟨hx, -⟩ | ⟨hx, -⟩ <;> tauto
  rcases hp with ⟨hx, hd⟩ | ⟨hx, hd⟩
  · rw [hx, hd]
  · rw [hx, hd]
    exact (flipConfiguration_swap_colours hab (fun w hw => offRoot_colour hw hu)).symm

/-- Row `B_a \ B_b`: the `a`-family.  The `X`-side move is off-root and is a
row of `rootColourOffRows` (the `X`-off-root rows of the `a`-family); the
`Y`-side move from the same vertex is the `Y`-root move. -/
theorem row_Ba_only {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d)
    (hA : MeetsRoot FY Y v a (offRootComponent FX X v a b u))
    (hB : ¬ MeetsRoot FX X v b (offRootComponent FX X v a b u)) :
    v ∉ offRootComponent FX X v a b u ∧
    flipSet FX.graph X u d = offRootComponent FX X v a b u ∧
    flipConfiguration X (flipSet FX.graph X u d) (X u) d =
      flipConfiguration X (offRootComponent FX X v a b u) a b ∧
    flipConfiguration X (offRootComponent FX X v a b u) a b ∈ rootColourOffRows FX FY X Y v ∧
    offRootComponent FX X v a b u ⊆ flipSet FY.graph Y v a ∧
    v ∈ flipSet FY.graph Y u d ∧
    flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d =
      flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a := by
  have hab := h.colours_ne
  have hvS : v ∉ offRootComponent FX X v a b u :=
    fun hh => ne_root_of_mem_offRootComponent huv hh rfl
  obtain ⟨-, hset⟩ := offroot_X h huv hp hB
  have hvY := (reach_Y h huv hp).mpr hA
  refine ⟨hvS, hset, by rw [hset]; exact move_eq_ab hab hp, ?_, contain_Y h u hA, hvY,
    (rootmove_Y h huv hp hvY).2⟩
  obtain ⟨w, hwS, hw⟩ := hA
  have hwv : w ≠ v := rootNeighbour_ne_root hw
  have hXw : X w = a := (h.agree_off_root w hwv).trans (mem_rootNeighbours.mp hw).2
  have hblock : offRootComponent FX X v a b w = offRootComponent FX X v a b u :=
    offRootComponent_eq_of_mem hwS
  have hpw : Partner a b (X w) b := Or.inl ⟨hXw, rfl⟩
  obtain ⟨-, hsetw⟩ := offroot_X h hwv hpw (by rwa [hblock])
  apply mem_filter.mpr
  constructor
  · apply mem_image.mpr
    refine ⟨w, by rwa [h.X_root], ?_⟩
    rw [h.Y_root, hsetw, hblock, hXw]
  · exact flipConfiguration_of_not_mem hvS

/-- Row `B_b \ B_a`: the `b`-family, mirror image of `row_Ba_only`. -/
theorem row_Bb_only {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d)
    (hA : ¬ MeetsRoot FY Y v a (offRootComponent FX X v a b u))
    (hB : MeetsRoot FX X v b (offRootComponent FX X v a b u)) :
    v ∉ offRootComponent FX X v a b u ∧
    flipSet FY.graph Y u d = offRootComponent FX X v a b u ∧
    flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d =
      flipConfiguration Y (offRootComponent FX X v a b u) b a ∧
    flipConfiguration Y (offRootComponent FX X v a b u) b a ∈ rootColourOffRows FY FX Y X v ∧
    offRootComponent FX X v a b u ⊆ flipSet FX.graph X v b ∧
    v ∈ flipSet FX.graph X u d ∧
    flipConfiguration X (flipSet FX.graph X u d) (X u) d =
      flipConfiguration X (flipSet FX.graph X v b) (X v) b := by
  have hpY : Partner b a (Y u) d := h.agree_off_root u huv ▸ hp.symm
  rw [block_common h u] at hA hB ⊢
  have hr := row_Ba_only h.symm huv hpY hB hA
  exact hr

/-- Row `B_a ∩ B_b`: the block lies in both root moves, and the moves grown
from it on either side are the root moves themselves, so it has no off-root
copy in either root-colour family. -/
theorem row_both {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d)
    (hA : MeetsRoot FY Y v a (offRootComponent FX X v a b u))
    (hB : MeetsRoot FX X v b (offRootComponent FX X v a b u)) :
    offRootComponent FX X v a b u ⊆ flipSet FX.graph X v b ∧
    offRootComponent FX X v a b u ⊆ flipSet FY.graph Y v a ∧
    v ∈ flipSet FX.graph X u d ∧ v ∈ flipSet FY.graph Y u d ∧
    flipConfiguration X (flipSet FX.graph X u d) (X u) d =
      flipConfiguration X (flipSet FX.graph X v b) (X v) b ∧
    flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d =
      flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a ∧
    flipConfiguration X (flipSet FX.graph X u d) (X u) d ∉ rootColourOffRows FX FY X Y v ∧
    flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d ∉ rootColourOffRows FY FX Y X v := by
  have hvX := (reach_X h huv hp).mpr hB
  have hvY := (reach_Y h huv hp).mpr hA
  have hmX := (rootmove_X h hp hvX).2
  have hmY := (rootmove_Y h huv hp hvY).2
  refine ⟨contain_X h u hB, contain_Y h u hA, hvX, hvY, hmX, hmY, ?_, ?_⟩
  · rw [hmX]
    simpa only [h.Y_root] using rootMove_not_rootColourOffRows h
  · rw [hmY]
    simpa only [h.X_root] using rootMove_not_rootColourOffRows h.symm

/-- Row "neither": the block is a common off-root move, with equal flipped
sets, equal feasibility, and (when feasible) its full true mass on the
common synchronous entry. -/
theorem row_neither
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {u : V} (huv : u ≠ v) {d : C}
    (hp : Partner a b (X u) d)
    (hA : ¬ MeetsRoot FY Y v a (offRootComponent FX X v a b u))
    (hB : ¬ MeetsRoot FX X v b (offRootComponent FX X v a b u)) :
    v ∉ offRootComponent FX X v a b u ∧
    flipSet FX.graph X u d = offRootComponent FX X v a b u ∧
    flipSet FY.graph Y u d = offRootComponent FX X v a b u ∧
    (flipAllowed FX (flipSet FX.graph X u d)
        (flipConfiguration X (flipSet FX.graph X u d) (X u) d) ↔
      flipAllowed FY (flipSet FY.graph Y u d)
        (flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d)) ∧
    (flipAllowed FX (flipSet FX.graph X u d)
        (flipConfiguration X (flipSet FX.graph X u d) (X u) d) →
      (hardCommonOffRootPartial FX FY X Y v).w
        (flipConfiguration X (flipSet FX.graph X u d) (X u) d)
        (flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d) =
          mass (flipSet FX.graph X u d).card / ((Fintype.card V : ℝ) * Fintype.card C)) := by
  have hab := h.colours_ne
  have hvS : v ∉ offRootComponent FX X v a b u :=
    fun hh => ne_root_of_mem_offRootComponent huv hh rfl
  obtain ⟨hvX, hsetX⟩ := offroot_X h huv hp hB
  obtain ⟨-, hsetY⟩ := offroot_Y h huv hp hA
  have hsets : flipSet FX.graph X u d = flipSet FY.graph Y u d := hsetX.trans hsetY.symm
  have hxy := h.agree_off_root u huv
  have hpoint (w : V) (hw : w ∈ flipSet FX.graph X u d) :
      flipConfiguration X (flipSet FX.graph X u d) (X u) d w =
        flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d w := by
    have hwv : w ≠ v := fun hh => hvX (hh ▸ hw)
    have hw' : w ∈ flipSet FY.graph Y u d := hsets ▸ hw
    rw [flipConfiguration_of_mem hw, flipConfiguration_of_mem hw', h.agree_off_root w hwv, hxy]
  refine ⟨hvS, hsetX, hsetY, ?_, fun ha =>
    hardCommonOffRoot_component_match h u d (hp.ne hab) hsets hvX ha⟩
  constructor
  · intro hA' w hw
    have hwX : w ∈ flipSet FX.graph X u d := hsets.symm ▸ hw
    have hwv : w ≠ v := fun hh => hvX (hh ▸ hwX)
    rw [← h.offRoot_list_eq w hwv, ← hpoint w hwX]
    exact hA' w hwX
  · intro hA' w hw
    have hwv : w ≠ v := fun hh => hvX (hh ▸ hw)
    rw [h.offRoot_list_eq w hwv, hpoint w hw]
    exact hA' w (hsets ▸ hw)

lemma mem_abBlocks {FX : HardListInstance V C} {X : V → C} {v : V} {a b : C}
    {S : Finset V} :
    S ∈ abBlocks FX X v a b ↔
      ∃ u, u ≠ v ∧ (X u = a ∨ X u = b) ∧ offRootComponent FX X v a b u = S := by
  simp only [abBlocks, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨huv, hu⟩, rfl⟩
    exact ⟨u, huv, hu, rfl⟩
  · rintro ⟨u, huv, hu, rfl⟩
    exact ⟨u, ⟨huv, hu⟩, rfl⟩

/-- The Lean `a`-family `X`-off-root rows are exactly the `X`-moves of the
blocks in `B_a \ B_b`. -/
theorem rootColourOffRows_eq_Ba_only
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    rootColourOffRows FX FY X Y v =
      ((abBlocks FX X v a b).filter
        (fun S => MeetsRoot FY Y v a S ∧ ¬ MeetsRoot FX X v b S)).image
        (fun S => flipConfiguration X S a b) := by
  ext U
  constructor
  · intro hU
    obtain ⟨hU1, hU2⟩ := mem_filter.mp hU
    obtain ⟨w, hw, rfl⟩ := mem_image.mp hU1
    rw [h.X_root] at hw
    have hwv : w ≠ v := rootNeighbour_ne_root hw
    have hXw : X w = a := (h.agree_off_root w hwv).trans (mem_rootNeighbours.mp hw).2
    have hpw : Partner a b (X w) b := Or.inl ⟨hXw, rfl⟩
    have hA : MeetsRoot FY Y v a (offRootComponent FX X v a b w) :=
      ⟨w, self_mem_offRootComponent FX X v w a b, hw⟩
    have hvX : v ∉ flipSet FX.graph X w b := by
      intro hv
      rw [h.Y_root] at hU2
      exact ((flipConfiguration_ne_iff (hpw.ne h.colours_ne) v).mpr hv) hU2
    have hB : ¬ MeetsRoot FX X v b (offRootComponent FX X v a b w) :=
      fun hB => hvX ((reach_X h hwv hpw).mpr hB)
    obtain ⟨-, hset⟩ := offroot_X h hwv hpw hB
    apply mem_image.mpr
    refine ⟨offRootComponent FX X v a b w, mem_filter.mpr
      ⟨mem_abBlocks.mpr ⟨w, hwv, Or.inl hXw, rfl⟩, hA, hB⟩, ?_⟩
    rw [h.Y_root, hset, hXw]
  · intro hU
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hU
    obtain ⟨hSb, hA, hB⟩ := mem_filter.mp hS
    obtain ⟨u, huv, hu, rfl⟩ := mem_abBlocks.mp hSb
    have hp : Partner a b (X u) (if X u = a then b else a) := by
      rcases hu with hu | hu
      · exact Or.inl ⟨hu, by simp [hu]⟩
      · exact Or.inr ⟨hu, by simp [hu, h.colours_ne.symm]⟩
    exact (row_Ba_only h huv hp hA hB).2.2.2.1

/-- The Lean `b`-family `Y`-off-root rows are exactly the `Y`-moves of the
blocks in `B_b \ B_a`. -/
theorem rootColourOffRows_symm_eq_Bb_only
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    rootColourOffRows FY FX Y X v =
      ((abBlocks FX X v a b).filter
        (fun S => MeetsRoot FX X v b S ∧ ¬ MeetsRoot FY Y v a S)).image
        (fun S => flipConfiguration Y S b a) := by
  rw [rootColourOffRows_eq_Ba_only h.symm]
  have hblocks : abBlocks FY Y v b a = abBlocks FX X v a b := by
    ext S
    simp only [mem_abBlocks]
    constructor
    · rintro ⟨u, huv, hu, rfl⟩
      refine ⟨u, huv, ?_, (block_common h u)⟩
      rw [h.agree_off_root u huv]
      exact hu.symm
    · rintro ⟨u, huv, hu, rfl⟩
      refine ⟨u, huv, ?_, (block_common h u).symm⟩
      rw [← h.agree_off_root u huv]
      exact hu.symm
  rw [hblocks]

/-! ## Uniqueness and exhaustion of the families -/

/-- `X`-side rows of the family labelled `c`. -/
def xFamilyRows (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) :
    Finset (V → C) :=
  if c = X v then rootColourOffRows FX FY X Y v
  else if c = Y v then {flipConfiguration X (flipSet FX.graph X v (Y v)) (X v) (Y v)}
  else regularMoveRows FX X v (Y v) c

lemma xFamilyRows_a {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    xFamilyRows FX FY X Y v a = rootColourOffRows FX FY X Y v := by
  simp [xFamilyRows, h.X_root]

lemma xFamilyRows_b {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    xFamilyRows FX FY X Y v b = {flipConfiguration X (flipSet FX.graph X v b) (X v) b} := by
  simp [xFamilyRows, h.X_root, h.Y_root, h.colours_ne.symm]

lemma xFamilyRows_regular {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) :
    xFamilyRows FX FY X Y v c = regularMoveRows FX X v b c := by
  simp [xFamilyRows, h.X_root, h.Y_root, hca, hcb]

lemma root_rows_subset_baseline {FX FY : HardListInstance V C} {X Y : V → C} {v : V}
    {a b : C} (h : RootLocalPair FX FY X Y v a b) {c : C} (hc : c = a ∨ c = b) :
    xFamilyRows FX FY X Y v c ⊆ baselineRootRows FX FY X Y v := by
  rcases hc with rfl | rfl
  · rw [xFamilyRows_a h]
    exact subset_insert _ _
  · rw [xFamilyRows_b h, ← h.Y_root]
    intro U hU
    rw [mem_singleton] at hU
    exact mem_insert.mpr (Or.inl hU)

/-- Distinct family labels have disjoint rows. -/
theorem xFamilyRows_disjoint {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) {c c' : C} (hne : c ≠ c') :
    Disjoint (xFamilyRows FX FY X Y v c) (xFamilyRows FX FY X Y v c') := by
  have hab := h.colours_ne
  by_cases hc : c = a ∨ c = b
  · by_cases hc' : c' = a ∨ c' = b
    · -- the two root-colour families
      rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl
      · exact (hne rfl).elim
      · rw [xFamilyRows_a h, xFamilyRows_b h, disjoint_singleton_right]
        simpa only [h.Y_root] using rootMove_not_rootColourOffRows h
      · rw [xFamilyRows_a h, xFamilyRows_b h, disjoint_singleton_left]
        simpa only [h.Y_root] using rootMove_not_rootColourOffRows h
      · exact (hne rfl).elim
    · push Not at hc'
      rw [xFamilyRows_regular h hc'.1 hc'.2]
      exact (baselineRootRows_disjoint_regular h hc'.1 hc'.2).mono_left
        (root_rows_subset_baseline h hc)
  · push Not at hc
    by_cases hc' : c' = a ∨ c' = b
    · rw [xFamilyRows_regular h hc.1 hc.2]
      exact ((baselineRootRows_disjoint_regular h hc.1 hc.2).mono_left
        (root_rows_subset_baseline h hc')).symm
    · push Not at hc'
      rw [xFamilyRows_regular h hc.1 hc.2, xFamilyRows_regular h hc'.1 hc'.2]
      exact regularMoveRows_disjoint h hc.1 hc.2 hc'.1 hc'.2 hne

/-- Every nonidentity `X`-row left with positive mass after the common
synchronous coupling lies in some family. -/
theorem xFamily_exists
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U : V → C) (hU : U ≠ X)
    (hp : 0 < (hardCommonOffRootPartial FX FY X Y v).leftResidual U) :
    ∃ c, U ∈ xFamilyRows FX FY X Y v c := by
  rcases hardCommon_residual_exhaustion h U hU hp with
    ⟨c, hca, hout⟩ | ⟨c, u, hcb, hu, hout, hv⟩
  · by_cases hcb : c = b
    · subst hcb
      refine ⟨c, ?_⟩
      rw [xFamilyRows_b h, mem_singleton, hout]
    · refine ⟨c, ?_⟩
      rw [xFamilyRows_regular h hca hcb]
      exact (mem_regularMoveRows FX X v b c U).mpr (Or.inl hout)
  · by_cases hca : c = a
    · subst hca
      refine ⟨c, ?_⟩
      rw [xFamilyRows_a h]
      apply mem_filter.mpr
      constructor
      · apply mem_image.mpr
        refine ⟨u, by simpa only [h.X_root] using hu, ?_⟩
        simpa only [h.Y_root] using hout.symm
      · rw [hout, flipConfiguration_of_not_mem hv]
    · refine ⟨c, ?_⟩
      rw [xFamilyRows_regular h hca hcb]
      have huX : u ∈ rootNeighbours FX X v c := (h.rootNeighbours_eq hca hcb).symm ▸ hu
      exact (mem_regularMoveRows FX X v b c U).mpr (Or.inr ⟨u, huX, hout⟩)

/-- `X`-side exhaustion and uniqueness. -/
theorem xFamily_exists_unique
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U : V → C) (hU : U ≠ X)
    (hp : 0 < (hardCommonOffRootPartial FX FY X Y v).leftResidual U) :
    ∃! c, U ∈ xFamilyRows FX FY X Y v c := by
  obtain ⟨c, hc⟩ := xFamily_exists h U hU hp
  refine ⟨c, hc, fun c' hc' => ?_⟩
  by_contra hne
  exact disjoint_left.mp (xFamilyRows_disjoint h hne) hc' hc

/-- `Y`-side exhaustion and uniqueness; the `Y` families are
`xFamilyRows FY FX Y X v`, i.e. the `a`-family is the `Y`-root move and the
`b`-family is `rootColourOffRows FY FX Y X v`. -/
theorem yFamily_exists_unique
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (Z : V → C) (hZ : Z ≠ Y)
    (hp : 0 < (hardCommonOffRootPartial FX FY X Y v).rightResidual Z) :
    ∃! c, Z ∈ xFamilyRows FY FX Y X v c := by
  rw [common_rightResidual_eq_swapped_left h] at hp
  exact xFamily_exists_unique h.symm Z hZ hp

/-- `lem:cv-move-partition`, packaged: family uniqueness/exhaustion on both
sides after the common synchronous coupling, the identification of the two
root-colour families with the block classes, and the four-row table. -/
theorem cv_move_partition
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) :
    -- every remaining nonidentity move lies in exactly one family
    (∀ U, U ≠ X → 0 < (hardCommonOffRootPartial FX FY X Y v).leftResidual U →
      ∃! c, U ∈ xFamilyRows FX FY X Y v c) ∧
    (∀ Z, Z ≠ Y → 0 < (hardCommonOffRootPartial FX FY X Y v).rightResidual Z →
      ∃! c, Z ∈ xFamilyRows FY FX Y X v c) ∧
    -- the families: regular colours, and the two root colours
    (∀ c, c ≠ a → c ≠ b → xFamilyRows FX FY X Y v c = regularMoveRows FX X v b c) ∧
    xFamilyRows FX FY X Y v a = rootColourOffRows FX FY X Y v ∧
    xFamilyRows FX FY X Y v b = {flipConfiguration X (flipSet FX.graph X v b) (X v) b} ∧
    xFamilyRows FY FX Y X v b = rootColourOffRows FY FX Y X v ∧
    xFamilyRows FY FX Y X v a = {flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a} ∧
    -- the root-colour off-root rows are the block classes `B_a \ B_b`, `B_b \ B_a`
    rootColourOffRows FX FY X Y v =
      ((abBlocks FX X v a b).filter
        (fun S => MeetsRoot FY Y v a S ∧ ¬ MeetsRoot FX X v b S)).image
        (fun S => flipConfiguration X S a b) ∧
    rootColourOffRows FY FX Y X v =
      ((abBlocks FX X v a b).filter
        (fun S => MeetsRoot FX X v b S ∧ ¬ MeetsRoot FY Y v a S)).image
        (fun S => flipConfiguration Y S b a) ∧
    -- the four-row table, for every block and proposal vertex in it
    (∀ u, u ≠ v → ∀ d, Partner a b (X u) d →
      let S := offRootComponent FX X v a b u
      (MeetsRoot FY Y v a S → ¬ MeetsRoot FX X v b S →
        flipSet FX.graph X u d = S ∧
        flipConfiguration X (flipSet FX.graph X u d) (X u) d ∈ rootColourOffRows FX FY X Y v ∧
        flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d =
          flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a) ∧
      (¬ MeetsRoot FY Y v a S → MeetsRoot FX X v b S →
        flipSet FY.graph Y u d = S ∧
        flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d ∈ rootColourOffRows FY FX Y X v ∧
        flipConfiguration X (flipSet FX.graph X u d) (X u) d =
          flipConfiguration X (flipSet FX.graph X v b) (X v) b) ∧
      (MeetsRoot FY Y v a S → MeetsRoot FX X v b S →
        S ⊆ flipSet FX.graph X v b ∧ S ⊆ flipSet FY.graph Y v a ∧
        flipConfiguration X (flipSet FX.graph X u d) (X u) d =
          flipConfiguration X (flipSet FX.graph X v b) (X v) b ∧
        flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d =
          flipConfiguration Y (flipSet FY.graph Y v a) (Y v) a ∧
        flipConfiguration X (flipSet FX.graph X u d) (X u) d ∉ rootColourOffRows FX FY X Y v ∧
        flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d ∉ rootColourOffRows FY FX Y X v) ∧
      (¬ MeetsRoot FY Y v a S → ¬ MeetsRoot FX X v b S →
        flipSet FX.graph X u d = S ∧ flipSet FY.graph Y u d = S ∧ v ∉ S ∧
        (flipAllowed FX (flipSet FX.graph X u d)
            (flipConfiguration X (flipSet FX.graph X u d) (X u) d) ↔
          flipAllowed FY (flipSet FY.graph Y u d)
            (flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d)) ∧
        (flipAllowed FX (flipSet FX.graph X u d)
            (flipConfiguration X (flipSet FX.graph X u d) (X u) d) →
          (hardCommonOffRootPartial FX FY X Y v).w
            (flipConfiguration X (flipSet FX.graph X u d) (X u) d)
            (flipConfiguration Y (flipSet FY.graph Y u d) (Y u) d) =
              mass (flipSet FX.graph X u d).card /
                ((Fintype.card V : ℝ) * Fintype.card C)))) := by
  refine ⟨xFamily_exists_unique h, yFamily_exists_unique h,
    fun c hca hcb => xFamilyRows_regular h hca hcb, xFamilyRows_a h, xFamilyRows_b h,
    xFamilyRows_a h.symm, xFamilyRows_b h.symm, rootColourOffRows_eq_Ba_only h,
    rootColourOffRows_symm_eq_Bb_only h, ?_⟩
  intro u huv d hp
  dsimp only
  refine ⟨fun hA hB => ?_, fun hA hB => ?_, fun hA hB => ?_, fun hA hB => ?_⟩
  · obtain ⟨-, hset, hmove, hrow, -, -, hY⟩ := row_Ba_only h huv hp hA hB
    exact ⟨hset, hmove ▸ hrow, hY⟩
  · obtain ⟨-, hset, hmove, hrow, -, -, hX⟩ := row_Bb_only h huv hp hA hB
    exact ⟨hset, hmove ▸ hrow, hX⟩
  · obtain ⟨h1, h2, -, -, h5, h6, h7, h8⟩ := row_both h huv hp hA hB
    exact ⟨h1, h2, h5, h6, h7, h8⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := row_neither h huv hp hA hB
    exact ⟨h2, h3, h1, h4, h5⟩

end

end ZeroFreeness.Appendix.CV
