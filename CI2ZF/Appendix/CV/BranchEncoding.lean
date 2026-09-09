import CI2ZF.Appendix.CV.ComponentCharge
import CI2ZF.Appendix.CV.Record
import CI2ZF.Appendix.CV.Truncation

/-! The 21-state certificate alphabet encodes actual list-feasible graph
components. Availability and feasibility flags are obtained from the lists,
including the forced equality for singleton components. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

lemma offRoot_flip_at_incidence (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (hu : u ∈ rootNeighbours F X v c) :
    flipConfiguration X (offRootComponent F X v (X v) c u) (X v) c u = X v := by
  rw [flipConfiguration_of_mem (self_mem_offRootComponent F X v u (X v) c),
    (mem_rootNeighbours.mp hu).2, if_neg hc]

lemma component_encoding_exists (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (hu : u ∈ rootNeighbours F X v c) :
    ∃ b : Branch,
      branchSize b = min (offRootComponent F X v (X v) c u).card 7 ∧
      available b = decide (X v ∈ F.list u) ∧
      feasible b = decide (flipAllowed F (offRootComponent F X v (X v) c u)
        (flipConfiguration X (offRootComponent F X v (X v) c u) (X v) c)) := by
  let S := offRootComponent F X v (X v) c u
  have huS : u ∈ S := self_mem_offRootComponent F X v u (X v) c
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨u, huS⟩
  have hat : flipConfiguration X S (X v) c u = X v := offRoot_flip_at_incidence F X v c hc u hu
  apply branch_encoding_complete ⟨min S.card 7, by omega⟩
  · simp only [decide_eq_true_eq]
    intro hf
    have hf' := hf u huS
    change flipConfiguration X S (X v) c u ∈ F.list u at hf'
    rwa [hat] at hf'
  · intro hz
    dsimp only at hz
    omega
  · intro hone
    have hcard : S.card ≤ 1 := by dsimp only at hone; omega
    apply Bool.decide_congr
    constructor
    · intro hf
      have hf' := hf u huS
      change flipConfiguration X S (X v) c u ∈ F.list u at hf'
      rwa [hat] at hf'
    · intro ha w hw
      have hwu := Finset.card_le_one.mp hcard w hw u huS
      subst w
      change flipConfiguration X S (X v) c u ∈ F.list u
      rwa [hat]

/-- The branch record of an actual nonempty off-root component. -/
def componentBranch (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (hu : u ∈ rootNeighbours F X v c) : Branch :=
  Classical.choose (component_encoding_exists F X v c hc u hu)

lemma componentBranch_spec (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (hu : u ∈ rootNeighbours F X v c) :
    branchSize (componentBranch F X v c hc u hu) = min (offRootComponent F X v (X v) c u).card 7 ∧
      available (componentBranch F X v c hc u hu) = decide (X v ∈ F.list u) ∧
      feasible (componentBranch F X v c hc u hu) = decide
        (flipAllowed F (offRootComponent F X v (X v) c u)
          (flipConfiguration X (offRootComponent F X v (X v) c u) (X v) c)) :=
  Classical.choose_spec (component_encoding_exists F X v c hc u hu)

lemma componentBranch_pos (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (hu : u ∈ rootNeighbours F X v c) :
    0 < branchSize (componentBranch F X v c hc u hu) := by
  rw [(componentBranch_spec F X v c hc u hu).1]
  have hpos := Finset.card_pos.mpr ⟨u, self_mem_offRootComponent F X v u (X v) c⟩
  omega

lemma componentBranch_atom (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (hu : u ∈ rootNeighbours F X v c) :
    realAtom (componentBranch F X v c hc u hu) =
      pieceRate F X v c (offRootComponent F X v (X v) c u) := by
  obtain ⟨hs, _, hf⟩ := componentBranch_spec F X v c hc u hu
  simp only [realAtom, hs, hf, decide_eq_true_eq, mass_cap, pieceRate]

lemma componentBranch_atom_cost (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u : V) (hu : u ∈ rootNeighbours F X v c) :
    branchSize (componentBranch F X v c hc u hu) * realAtom (componentBranch F X v c hc u hu) =
      (offRootComponent F X v (X v) c u).card *
        pieceRate F X v c (offRootComponent F X v (X v) c u) := by
  obtain ⟨hs, _, hf⟩ := componentBranch_spec F X v c hc u hu
  simp only [realAtom, hs, hf, decide_eq_true_eq, pieceRate]
  split_ifs
  · exact size_mass_cap _
  · simp

lemma mass_one_add_cap (r : ℕ) : mass (1 + min r 7) = mass (1 + r) := by
  by_cases hr : r ≤ 7
  · rw [Nat.min_eq_left hr]
  · rw [Nat.min_eq_right (by omega), mass_zero_of_seven_le (1 + r) (by omega)]
    norm_num [mass]

lemma componentBranch_oneResidual (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (hav : c ∈ F.list v) (u : V) (hN : rootNeighbours F X v c = {u}) :
    oneResidual (componentBranch F X v c hc u (by simp [hN])) =
      componentResidual F X v c u (offRootComponent F X v (X v) c u) := by
  have hu : u ∈ rootNeighbours F X v c := by simp [hN]
  obtain ⟨hs, _, hf⟩ := componentBranch_spec F X v c hc u hu
  have hroot : flipAllowed F (flipSet F.graph X v c)
      (flipConfiguration X (flipSet F.graph X v c) (X v) c) ↔
      flipAllowed F (offRootComponent F X v (X v) c u)
        (flipConfiguration X (offRootComponent F X v (X v) c u) (X v) c) := by
    rw [root_flipAllowed_iff F X v c hc]
    simp [rootFamily, hN, hav]
  unfold oneResidual componentResidual
  rw [if_pos rfl, componentBranch_atom]
  simp only [hf, decide_eq_true_eq, hs, mass_one_add_cap, rootRate, hroot,
    root_flipSet_card_single_neighbour F X v u c hc hN]

lemma componentBranch_oneResidual_cost (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (hav : c ∈ F.list v) (u : V) (hN : rootNeighbours F X v c = {u}) :
    branchSize (componentBranch F X v c hc u (by simp [hN])) *
      oneResidual (componentBranch F X v c hc u (by simp [hN])) =
    (offRootComponent F X v (X v) c u).card *
      componentResidual F X v c u (offRootComponent F X v (X v) c u) := by
  rw [componentBranch_oneResidual F X v c hc hav u hN,
    (componentBranch_spec F X v c hc u (by simp [hN])).1]
  by_cases hr : (offRootComponent F X v (X v) c u).card ≤ 7
  · rw [Nat.min_eq_left hr]
  · have htail : 7 ≤ (offRootComponent F X v (X v) c u).card := by omega
    have hzero : componentResidual F X v c u (offRootComponent F X v (X v) c u) = 0 := by
      unfold componentResidual pieceRate rootRate
      rw [root_flipSet_card_single_neighbour F X v u c hc hN]
      simp [mass_zero_of_seven_le _ htail, mass_zero_of_seven_le (1 +
        (offRootComponent F X v (X v) c u).card) (by omega)]
    simp [hzero]

end
end CI2ZF.Appendix.CV
