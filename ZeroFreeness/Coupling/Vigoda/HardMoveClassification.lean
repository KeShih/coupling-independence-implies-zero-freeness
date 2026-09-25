import ZeroFreeness.Coupling.Vigoda.HardMoveSeparation

/-! Classification of actual positive-mass component moves. -/

namespace ZeroFreeness
open PottsCI PottsCI.Vigoda RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C]

/-- Every non-holding outcome with positive probability is a feasible
component move of the concrete hard kernel. -/
theorem hardStep_positive_move [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X U : V → C) (hU : U ≠ X)
    (hp : 0 < (hardStep F X).w U) :
    ∃ u c, c ≠ X u ∧
      flipAllowed F (flipSet F.graph X u c)
        (flipConfiguration X (flipSet F.graph X u c) (X u) c) ∧
      U = flipConfiguration X (flipSet F.graph X u c) (X u) c := by
  rw [hardStep_w] at hp
  have hex : ∃ p ∈ (Finset.univ : Finset (V × C)),
      0 < (Fintype.card (V × C) : ℝ)⁻¹ *
        (proposalDistribution F X p.1 p.2).w U := by
    by_contra hn
    push Not at hn
    have hle := Finset.sum_nonpos hn
    linarith
  obtain ⟨⟨u, c⟩, _, hterm⟩ := hex
  have hp' : 0 < (proposalDistribution F X u c).w U :=
    (mul_pos_iff_of_pos_left (by positivity)).mp hterm
  by_cases hc : c = X u
  · simp [proposalDistribution, hc, FinDist.pure, hU] at hp'
  · rw [proposalDistribution, if_neg hc, twoPoint_w] at hp'
    simp only [if_neg hU, add_zero] at hp'
    split_ifs at hp' with hout
    · refine ⟨u, c, hc, ?_, hout⟩
      by_contra ha
      simp [acceptanceProbability, ha] at hp'
    · exact (lt_irrefl _ hp').elim

/-- A component avoiding the root is precisely the component in the
root-deleted graph. This follows by checking every path prefix. -/
theorem flipSet_eq_offRootComponent_of_not_mem
    (F : HardListInstance V C) (X : V → C) (v u : V) (c : C)
    (hv : v ∉ flipSet F.graph X u c) :
    flipSet F.graph X u c = offRootComponent F X v (X u) c u := by
  have hu : u ≠ v := fun heq => hv (heq ▸ self_mem_flipSet)
  ext w
  simp only [mem_flipSet, mem_offRootComponent]
  constructor
  · intro hp
    induction hp with
    | refl => exact .refl
    | @tail y z hyz hstep ih =>
      have hy : y ≠ v := fun heq => hv (heq ▸ mem_flipSet.mpr hyz)
      have hz : z ≠ v := fun heq => hv (heq ▸ mem_flipSet.mpr (hyz.tail hstep))
      exact ih.tail ⟨hy, hz, hstep⟩
  · intro hp
    induction hp with
    | refl => exact .refl
    | tail _ hstep ih => exact ih.tail hstep.2.2

/-- A move off-root on both sides has identical component sets. -/
theorem common_component_sets
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (u : V) (c : C)
    (hvX : v ∉ flipSet FX.graph X u c) (hvY : v ∉ flipSet FY.graph Y u c) :
    flipSet FX.graph X u c = flipSet FY.graph Y u c := by
  have hu : u ≠ v := fun heq => hvX (heq ▸ self_mem_flipSet)
  rw [flipSet_eq_offRootComponent_of_not_mem FX X v u c hvX,
    flipSet_eq_offRootComponent_of_not_mem FY Y v u c hvY,
    h.offRootComponent_eq, h.agree_off_root u hu]

/-- Every positive-mass move either changes the root, is fully common,
or is an off-root move whose counterpart contains the root. -/
theorem hardStep_move_root_trichotomy [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U : V → C)
    (hU : U ≠ X) (hp : 0 < (hardStep FX X).w U) :
    (∃ c, c ≠ a ∧ U = flipConfiguration X (flipSet FX.graph X v c) (X v) c) ∨
    (∃ u c, c ≠ X u ∧
      flipAllowed FX (flipSet FX.graph X u c)
        (flipConfiguration X (flipSet FX.graph X u c) (X u) c) ∧
      U = flipConfiguration X (flipSet FX.graph X u c) (X u) c ∧
      v ∉ flipSet FX.graph X u c ∧
      (flipSet FX.graph X u c = flipSet FY.graph Y u c ∨
        v ∈ flipSet FY.graph Y u c)) := by
  obtain ⟨u, c, hc, ha, hout⟩ := hardStep_positive_move FX X U hU hp
  by_cases hvX : v ∈ flipSet FX.graph X u c
  · left
    obtain ⟨_, heq⟩ := component_move_from_member FX.graph X u c hc v hvX
    refine ⟨U v, ?_, ?_⟩
    · rw [hout, ← h.X_root]
      exact (flipConfiguration_ne_iff hc v).mpr hvX
    · rw [hout]
      exact heq.symm
  · right
    refine ⟨u, c, hc, ha, hout, hvX, ?_⟩
    by_cases hvY : v ∈ flipSet FY.graph Y u c
    · exact Or.inr hvY
    · exact Or.inl (common_component_sets h u c hvX hvY)

lemma offRootComponent_swap_colours (F : HardListInstance V C) (X : V → C)
    (v u : V) (a b : C) :
    offRootComponent F X v a b u = offRootComponent F X v b a u := by
  have hr : offRootAlternatingAdj F X v a b = offRootAlternatingAdj F X v b a := by
    funext w z
    apply propext
    simp only [offRootAlternatingAdj, alternatingAdj_comm_colours (c₁ := a) (c₂ := b)]
  simp only [offRootComponent, hr]

/-- An off-root component affected by the other root can be represented
by an actual neighbour of that root, proposing the other root colour.
The statement includes the two root-colour groups. -/
theorem affected_component_from_neighbour
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (u : V) (c : C) (hc : c ≠ X u)
    (hvX : v ∉ flipSet FX.graph X u c) (hvY : v ∈ flipSet FY.graph Y u c) :
    ∃ d w, d ≠ b ∧ w ∈ rootNeighbours FY Y v d ∧
      flipConfiguration X (flipSet FX.graph X u c) (X u) c =
        flipConfiguration X (flipSet FX.graph X w b) (X w) b ∧
      v ∉ flipSet FX.graph X w b := by
  have huv : u ≠ v := fun heq => hvX (heq ▸ self_mem_flipSet)
  have hxy := h.agree_off_root u huv
  have hcY : c ≠ Y u := by simpa only [← hxy] using hc
  let Z := flipConfiguration Y (flipSet FY.graph Y u c) (Y u) c
  let d := Z v
  have hdb : d ≠ b := by
    rw [← h.Y_root]
    exact (flipConfiguration_ne_iff hcY v).mpr hvY
  have hneY : Y v ≠ d := by rw [h.Y_root]; exact hdb.symm
  have hpair := proposal_pair_of_changes_root (G := FY.graph) hneY
    (show Z v = d from rfl)
  obtain ⟨hsetY, _⟩ := component_move_from_member FY.graph Y u c hcY v hvY
  have huRoot : u ∈ flipSet FY.graph Y v d := by
    rw [hsetY]
    exact self_mem_flipSet
  obtain ⟨w, hw, huw⟩ :=
    ((mem_root_flipSet_iff (by simpa only [h.Y_root] using hdb)).mp huRoot).resolve_left huv
  have hoff : offRootComponent FX X v (X u) c u =
      offRootComponent FY Y v (Y v) d u := by
    rw [h.offRootComponent_eq, hxy]
    rcases hpair with ⟨hu, hc'⟩ | ⟨hu, hc'⟩
    · rw [hu, hc', h.Y_root]
    · rw [hu, hc', h.Y_root]
      exact offRootComponent_swap_colours FY Y v u d b
  have hpiece : flipSet FX.graph X u c =
      offRootComponent FY Y v (Y v) d w := by
    rw [flipSet_eq_offRootComponent_of_not_mem FX X v u c hvX, hoff]
    exact offRootComponent_eq_of_mem huw
  have hwS : w ∈ flipSet FX.graph X u c := by
    rw [hpiece]
    exact self_mem_offRootComponent FY Y v w (Y v) d
  have hXw : X w = d := (h.agree_off_root w (rootNeighbour_ne_root hw)).trans
    (mem_rootNeighbours.mp hw).2
  have hmoveAtW : flipConfiguration X (flipSet FX.graph X u c) (X u) c w = b := by
    rw [flipConfiguration_of_mem hwS, hxy, hXw]
    rcases hpair with ⟨hu, hc'⟩ | ⟨hu, hc'⟩
    · rw [hu, hc']
      simp [hdb, h.Y_root]
    · rw [hu, hc']
      simp [h.Y_root]
  obtain ⟨hsetX, hmoveX⟩ := component_move_from_member FX.graph X u c hc w hwS
  rw [hmoveAtW] at hsetX hmoveX
  exact ⟨d, w, hdb, hw, hmoveX.symm, hsetX.symm ▸ hvX⟩

/-- After the common allocation, every positive residual non-holding
row belongs to a root move or to an actual affected-neighbour group.
There is no support-exhaustion assumption in this result. -/
theorem hardCommon_residual_exhaustion [Nonempty V] [Nonempty C]
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) (U : V → C) (hU : U ≠ X)
    (hp : 0 < (hardCommonOffRootPartial FX FY X Y v).leftResidual U) :
    (∃ c, c ≠ a ∧ U = flipConfiguration X (flipSet FX.graph X v c) (X v) c) ∨
    (∃ c u, c ≠ b ∧ u ∈ rootNeighbours FY Y v c ∧
      U = flipConfiguration X (flipSet FX.graph X u b) (X u) b ∧
      v ∉ flipSet FX.graph X u b) := by
  let k := hardCommonOffRootPartial FX FY X Y v
  have hpU : 0 < (hardStep FX X).w U := by
    have hn : 0 ≤ ∑ Z, k.w U Z := Finset.sum_nonneg (fun Z _ => k.nonneg U Z)
    change 0 < (hardStep FX X).w U - ∑ Z, k.w U Z at hp
    linarith
  rcases hardStep_move_root_trichotomy h U hU hpU with hroot | ⟨u, c, hc, ha, hout, hv, hm⟩
  · exact Or.inl hroot
  · rcases hm with hcommon | haffected
    · exfalso
      have hfull := hardCommonOffRoot_component_match h u c hc hcommon hv ha
      have hmass := hardStep_component_mass FX X u c hc ha
      rw [← hmass, ← hout] at hfull
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun Z => k.w U Z) (fun Z _ => k.nonneg U Z)
        (Finset.mem_univ (flipConfiguration Y (flipSet FY.graph Y u c) (Y u) c))
      change k.w U _ = (hardStep FX X).w U at hfull
      rw [hfull] at hle
      change 0 < (hardStep FX X).w U - ∑ Z, k.w U Z at hp
      linarith
    · obtain ⟨d, w, hdb, hw, heq, hvw⟩ :=
        affected_component_from_neighbour h u c hc hv haffected
      exact Or.inr ⟨d, w, hdb, hw, hout.trans heq, hvw⟩

end
end ZeroFreeness
