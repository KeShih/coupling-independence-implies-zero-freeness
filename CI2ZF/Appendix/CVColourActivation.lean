import CI2ZF.Appendix.CVBinomial
import CI2ZF.Appendix.CVRootEvent
import CI2ZF.ActiveDegree
import CI2ZF.BoundaryActivation

/-! Physical root-edge and boundary-constraint labels for one colour,
with exact bridges to the actual activated graph and list. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def physicalColourIncidences (I : PinningData V C) (X : V → C) (v : V) (c : C) :
    Finset (I.graph.neighborSet v) := Finset.univ.filter fun u => X u.val = c

def rootColourEdges (I : PinningData V C) (X : V → C) (v : V) (c : C) : Finset I.Constraint :=
  (physicalColourIncidences I X v c).image (rootFreeConstraint I v)

def rootColourBoundarySet (I : PinningData V C) (v : V) (c : C) : Finset I.Constraint :=
  Finset.univ.image fun i : Fin (I.boundaryCount v c) => (Sum.inr ⟨v, c, i⟩ : I.Constraint)

lemma rootFreeConstraint_injective (I : PinningData V C) (v : V) :
    Function.Injective (rootFreeConstraint I v) := by
  intro u w he
  apply Subtype.ext
  have hh : s(v, u.val) = s(v, w.val) := congrArg Subtype.val (Sum.inl.inj he)
  rcases Sym2.eq_iff.mp hh with ⟨_, hh⟩ | ⟨hvw, huv⟩
  · exact hh
  · exact huv.trans hvw

lemma rootColourEdges_card (I : PinningData V C) (X : V → C) (v : V) (c : C) :
    (rootColourEdges I X v c).card = (physicalColourIncidences I X v c).card :=
  Finset.card_image_of_injective _ (rootFreeConstraint_injective I v)

lemma rootColourBoundarySet_card (I : PinningData V C) (v : V) (c : C) :
    (rootColourBoundarySet I v c).card = I.boundaryCount v c := by
  unfold rootColourBoundarySet
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j he
    simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using Sum.inr.inj he

lemma rootColourBoundarySet_false_iff (I : PinningData V C) (v : V) (c : C)
    (ω : I.Constraint → Bool) :
    (∀ k ∈ rootColourBoundarySet I v c, ω k = false) ↔
      ∀ i : Fin (I.boundaryCount v c), ω (Sum.inr ⟨v, c, i⟩) = false := by
  simp [rootColourBoundarySet]

theorem root_available_iff_boundary_false (I : PinningData V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (ω : I.Constraint → Bool) :
    c ∈ (activeHardListInstance I (activatedSet I X ω)).list v ↔
      ∀ k ∈ rootColourBoundarySet I v c, ω k = false := by
  rw [activeHardListInstance, Potts.mem_activeList_activated,
    rootColourBoundarySet_false_iff]
  constructor
  · intro hn i
    exact Bool.eq_false_iff.mpr (fun hi => hn ⟨⟨i, hi⟩, hc.symm⟩)
  · intro hi ⟨⟨i, hh⟩, _⟩
    rw [hi i] at hh
    contradiction

lemma rootColourEdges_boundary_disjoint (I : PinningData V C) (X : V → C)
    (v : V) (c d : C) : Disjoint (rootColourEdges I X v c) (rootColourBoundarySet I v d) := by
  apply Finset.disjoint_left.mpr
  intro k hk hd
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨i, _, he⟩ := Finset.mem_image.mp hd
  simp [rootFreeConstraint] at he

theorem activeRootIncidence_iff_coin (I : PinningData V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (ω : I.Constraint → Bool)
    (u : I.graph.neighborSet v) :
    u.val ∈ rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v c ↔
      X u.val = c ∧ ω (rootFreeConstraint I v u) = true := by
  rw [mem_rootNeighbours, activeHardListInstance, activeGraph_root_adj_iff, mem_activatedSet]
  change (ω (rootFreeConstraint I v u) = true ∧ X v ≠ X u.val) ∧ X u.val = c ↔ _
  constructor
  · intro hh
    exact ⟨hh.2, hh.1.1⟩
  · intro hh
    exact ⟨⟨hh.2, fun he => hc (hh.1.symm.trans he.symm)⟩, hh.1⟩

/-- The random active multiplicity is exactly the number of successful
coins on the physical root edges of that colour. -/
theorem activeRootNeighbours_card_eq_coinCount (I : PinningData V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (ω : I.Constraint → Bool) :
    (rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v c).card =
      coinCount (rootColourEdges I X v c) ω := by
  let F := activeHardListInstance I (activatedSet I X ω)
  let e : RootIncidence F X v c ≃
      {u : I.graph.neighborSet v // X u.val = c ∧ ω (rootFreeConstraint I v u) = true} :=
    { toFun := fun u => ⟨⟨u.val, activeGraph_le_original I _ (mem_rootNeighbours.mp u.property).1⟩,
        (activeRootIncidence_iff_coin I X v c hc ω _).mp u.property⟩
      invFun := fun u => ⟨u.val.val, (activeRootIncidence_iff_coin I X v c hc ω u.val).mpr u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have he := Fintype.card_congr e
  rw [Fintype.card_coe, Fintype.card_subtype] at he
  change (rootNeighbours _ X v c).card = _ at he
  rw [he]
  unfold coinCount coinSuccessSet rootColourEdges
  rw [Finset.filter_image, Finset.card_image_of_injective _ (rootFreeConstraint_injective I v)]
  congr 1
  ext u
  simp [physicalColourIncidences]

theorem activeRootNeighbours_card_le_physical (I : PinningData V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (ω : I.Constraint → Bool) :
    (rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v c).card ≤
      (physicalColourIncidences I X v c).card := by
  rw [activeRootNeighbours_card_eq_coinCount I X v c hc ω]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (rootColourEdges_card I X v c)

theorem expected_root_available (I : PinningData V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => if c ∈ (activeHardListInstance I (activatedSet I X ω)).list v then (1 : ℝ) else 0) =
      x ^ I.boundaryCount v c := by
  simp_rw [root_available_iff_boundary_false I X v c hc]
  have hp := coin_all_false_probability (1 - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ (rootColourBoundarySet I v c)
  simpa only [sub_sub_cancel, rootColourBoundarySet_card] using hp

/-- Availability and active multiplicity use disjoint actual labels. -/
theorem expected_available_rootMultiplicity (I : PinningData V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => if c ∈ (activeHardListInstance I (activatedSet I X ω)).list v then
        ((rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v c).card : ℝ) else 0) =
      (physicalColourIncidences I X v c).card * (1 - x) * x ^ I.boundaryCount v c := by
  simp_rw [root_available_iff_boundary_false I X v c hc,
    activeRootNeighbours_card_eq_coinCount I X v c hc]
  have hp := coinCount_joint_mean (1 - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
    (rootColourEdges I X v c) (rootColourBoundarySet I v c) (rootColourEdges_boundary_disjoint I X v c c)
  simpa only [sub_sub_cancel, rootColourEdges_card, rootColourBoundarySet_card] using hp

theorem expected_unavailable_rootMultiplicity (I : PinningData V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => if c ∉ (activeHardListInstance I (activatedSet I X ω)).list v then
        ((rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v c).card : ℝ) else 0) =
      (physicalColourIncidences I X v c).card * (1 - x) * (1 - x ^ I.boundaryCount v c) := by
  simp_rw [root_available_iff_boundary_false I X v c hc,
    activeRootNeighbours_card_eq_coinCount I X v c hc]
  have hp := coinCount_not_false_joint_mean (1 - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
    (rootColourEdges I X v c) (rootColourBoundarySet I v c) (rootColourEdges_boundary_disjoint I X v c c)
  simpa only [sub_sub_cancel, rootColourEdges_card, rootColourBoundarySet_card] using hp

theorem expected_rootMultiplicity (I : PinningData V C) (X : V → C)
    (v : V) (c : C) (hc : c ≠ X v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => ((rootNeighbours (activeHardListInstance I (activatedSet I X ω)) X v c).card : ℝ)) =
      (physicalColourIncidences I X v c).card * (1 - x) := by
  simp_rw [activeRootNeighbours_card_eq_coinCount I X v c hc]
  simpa only [rootColourEdges_card] using coinCount_mean (1 - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ (rootColourEdges I X v c)

/-- Averaging the actual root event gives exactly the physical low-colour
rebate used in the geometric coefficient. -/
theorem expected_active_rootEvent_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (choice : ∀ ω : I.Constraint → Bool,
      GlobalChoice (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree))
    (L : Finset C)
    (hL : ∀ c ∈ L, c ≠ X v ∧ c ≠ Y v ∧ (physicalColourIncidences I X v c).card ≤ 2)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
      expectReal (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
        (fun ω => rootEventMass
          (fullHardCoupling (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree)
            (choice ω)) X Y v) ≤
      Fintype.card C - (81 / 250) * (1 - x) *
        ∑ c ∈ L, (physicalColourIncidences I X v c).card * x ^ I.boundaryCount v c := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hp := expectReal_mono (commonCoinLaw (K := I.Constraint) (1 - x) ht)
    (fun ω => fullHardCoupling_rootEvent_le
      (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) (choice ω) L
      (fun c hc => ⟨(hL c hc).1, (hL c hc).2.1,
        (activeRootNeighbours_card_le_physical I X v c (hL c hc).1 ω).trans (hL c hc).2.2⟩))
  rw [expectReal_mul_const, expectReal_sub, expectReal_const,
    expectReal_mul_const, expectReal_finset_sum] at hp
  have he := Finset.sum_congr rfl (fun c hc =>
    expected_available_rootMultiplicity I X v c (hL c hc).1 x hx)
  rw [he] at hp
  convert hp using 1
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  ring

end
end CI2ZF.Appendix.CV
