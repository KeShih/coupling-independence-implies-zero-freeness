import ZeroFreeness.Coupling.Vigoda.HardRootAllocation

/-! Distinct colour groups occupy disjoint true non-holding move rows. -/
namespace ZeroFreeness
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

/-- The other colour in a nontrivial component move is recoverable from
its output when one of the two colours is fixed. -/
theorem component_move_colour_unique (G : SimpleGraph V) (X : V → C)
    (u w : V) (b c d : C) (huc : X u = c) (hwd : X w = d) (hcb : c ≠ b)
    (heq : flipConfiguration X (flipSet G X u b) (X u) b =
      flipConfiguration X (flipSet G X w b) (X w) b) : c = d := by
  have hchange : flipConfiguration X (flipSet G X w b) (X w) b u = b := by
    rw [← heq, flipConfiguration_at_start]
  have humem : u ∈ flipSet G X w b := by
    by_contra hu
    rw [flipConfiguration_of_not_mem hu, huc] at hchange
    exact hcb hchange
  rcases colour_eq_of_mem_flipSet humem with hc | hc
  · exact huc.symm.trans (hc.trans hwd)
  · exact (hcb (huc.symm.trans hc)).elim

/-- Actual rows belonging to one regular colour: its root move, or an
opposite-root-colour off-root move at one of its incidences. -/
def regularMoveRows (F : HardListInstance V C) (X : V → C) (v : V) (b c : C) :
    Finset (V → C) :=
  insert (flipConfiguration X (flipSet F.graph X v c) (X v) c)
    ((rootNeighbours F X v c).image
      (fun u => flipConfiguration X (flipSet F.graph X u b) (X u) b))

lemma mem_regularMoveRows (F : HardListInstance V C) (X : V → C) (v : V) (b c : C)
    (U : V → C) : U ∈ regularMoveRows F X v b c ↔
      U = flipConfiguration X (flipSet F.graph X v c) (X v) c ∨
      ∃ u ∈ rootNeighbours F X v c,
        U = flipConfiguration X (flipSet F.graph X u b) (X u) b := by
  simp only [regularMoveRows, Finset.mem_insert, Finset.mem_image]
  exact or_congr_right (by
    constructor
    · rintro ⟨u, hu, hU⟩
      exact ⟨u, hu, hU.symm⟩
    · rintro ⟨u, hu, hU⟩
      exact ⟨u, hu, hU.symm⟩)

/-- Regular colour groups have disjoint actual output rows; root colours
are read at the root, and off-root colours from their nontrivial move. -/
theorem regularMoveRows_disjoint
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c d : C}
    (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hda : d ≠ a) (hdb : d ≠ b) (hcd : c ≠ d) :
    Disjoint (regularMoveRows FX X v b c) (regularMoveRows FX X v b d) := by
  apply Finset.disjoint_left.mpr
  intro U hUc hUd
  rcases (mem_regularMoveRows FX X v b c U).mp hUc with rfl | ⟨u, hu, rfl⟩
  · rcases (mem_regularMoveRows FX X v b d _).mp hUd with heq | ⟨w, hw, heq⟩
    · have hc := congrFun heq v
      simp only [flipConfiguration_at_start] at hc
      exact hcd hc
    · have hwY : w ∈ rootNeighbours FY Y v d := (h.rootNeighbours_eq hda hdb) ▸ hw
      have hnot := regular_piece_no_root h.symm hda w hwY
      have hc := congrFun heq v
      rw [flipConfiguration_at_start, flipConfiguration_of_not_mem hnot, h.X_root] at hc
      exact hca hc
  · rcases (mem_regularMoveRows FX X v b d _).mp hUd with heq | ⟨w, hw, heq⟩
    · have huY : u ∈ rootNeighbours FY Y v c := (h.rootNeighbours_eq hca hcb) ▸ hu
      have hnot := regular_piece_no_root h.symm hca u huY
      have hc := congrFun heq v
      rw [flipConfiguration_of_not_mem hnot, flipConfiguration_at_start, h.X_root] at hc
      exact hda hc.symm
    · exact hcd (component_move_colour_unique FX.graph X u w b c d
        (mem_rootNeighbours.mp hu).2 (mem_rootNeighbours.mp hw).2 hcb heq)

end
end ZeroFreeness
