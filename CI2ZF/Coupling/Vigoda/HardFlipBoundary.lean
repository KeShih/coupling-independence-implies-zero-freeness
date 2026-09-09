import CI2ZF.Coupling.Vigoda.ComponentCoupling

/-!
# One-colour list deletion for the concrete hard Vigoda kernel

All kernels in this module are the actual component-flip kernels.  A list
colour deletion can reject only the two-colour component containing its
vertex.  The proof below uses this geometry, rather than assuming a row
transport estimate.
-/

namespace PottsCI.Vigoda
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

/-- Delete one colour from one list, preserving the graph. -/
noncomputable def deleteListColour (F : HardListInstance V C) (r : V) (a : C) :
    HardListInstance V C where
  graph := F.graph
  list u := if u = r then (F.list u).erase a else F.list u

@[simp] lemma deleteListColour_graph (F : HardListInstance V C) (r : V) (a : C) :
    (deleteListColour F r a).graph = F.graph := rfl

lemma deleteListColour_proper_iff (F : HardListInstance V C) (r : V) (a : C)
    (X : V → C) :
    (deleteListColour F r a).IsProper X ↔ F.IsProper X ∧ X r ≠ a := by
  constructor
  · rintro ⟨hp, hl⟩
    refine ⟨⟨hp, ?_⟩, ?_⟩
    · intro u
      have h := hl u
      by_cases hu : u = r
      · simpa [deleteListColour, hu] using (Finset.mem_erase.mp (by simpa [deleteListColour, hu] using h)).2
      · simpa [deleteListColour, hu] using h
    · have h := hl r
      exact (Finset.mem_erase.mp (by simpa [deleteListColour] using h)).1
  · rintro ⟨⟨hp, hl⟩, ha⟩
    refine ⟨hp, fun u => ?_⟩
    by_cases hu : u = r
    · subst u
      simpa [deleteListColour] using Finset.mem_erase.mpr ⟨ha, hl r⟩
    · simpa [deleteListColour, hu] using hl u

lemma flipAllowed_deleteListColour_iff (F : HardListInstance V C) (r : V) (a : C)
    (S : Finset V) (Y : V → C) :
    flipAllowed (deleteListColour F r a) S Y ↔
      flipAllowed F S Y ∧ (r ∈ S → Y r ≠ a) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u hu
      have hl := h u hu
      by_cases hur : u = r
      · subst u
        exact (Finset.mem_erase.mp (by simpa [deleteListColour] using hl)).2
      · simpa [deleteListColour, hur] using hl
    · intro hr
      have hl := h r hr
      exact (Finset.mem_erase.mp (by simpa [deleteListColour] using hl)).1
  · rintro ⟨h, ha⟩ u hu
    by_cases hur : u = r
    · subst u
      simpa [deleteListColour] using Finset.mem_erase.mpr ⟨ha hu, h r hu⟩
    · simpa [deleteListColour, hur] using h u hu

lemma alternating_reachable_reverse {G : SimpleGraph V} {X : V → C} {a b : C}
    {u v : V} (h : Relation.ReflTransGen (alternatingAdj G X a b) u v) :
    Relation.ReflTransGen (alternatingAdj G X a b) v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact (Relation.ReflTransGen.single (alternatingAdj_symm hstep)).trans ih

lemma proposal_pair_of_changes_root {G : SimpleGraph V} {X : V → C}
    {u r : V} {c a : C} (hra : X r ≠ a)
    (hchange : flipConfiguration X (flipSet G X u c) (X u) c r = a) :
    (X u = X r ∧ c = a) ∨ (X u = a ∧ c = X r) := by
  have hr : r ∈ flipSet G X u c := by
    by_contra hn
    rw [flipConfiguration_of_not_mem hn] at hchange
    exact hra hchange
  rw [flipConfiguration_of_mem hr] at hchange
  by_cases h : X r = X u
  · rw [if_pos h] at hchange
    exact Or.inl ⟨h.symm, hchange⟩
  · rw [if_neg h] at hchange
    rcases colour_eq_of_mem_flipSet hr with h' | h'
    · exact (h h').elim
    · exact Or.inr ⟨hchange, h'.symm⟩

lemma flipSet_eq_of_changes_root {G : SimpleGraph V} {X : V → C}
    {u r : V} {c a : C} (hra : X r ≠ a)
    (hchange : flipConfiguration X (flipSet G X u c) (X u) c r = a) :
    flipSet G X u c = flipSet G X r a := by
  have hr : r ∈ flipSet G X u c := by
    by_contra hn
    rw [flipConfiguration_of_not_mem hn] at hchange
    exact hra hchange
  have hp := proposal_pair_of_changes_root hra hchange
  have hrel : alternatingAdj G X (X u) c = alternatingAdj G X (X r) a := by
    funext w z
    apply propext
    rcases hp with ⟨hu, hc⟩ | ⟨hu, hc⟩
    · rw [hu, hc]
    · rw [hu, hc]
      exact alternatingAdj_comm_colours
  have hur := mem_flipSet.mp hr
  rw [hrel] at hur
  ext w
  rw [mem_flipSet, mem_flipSet, hrel]
  exact ⟨fun h => (alternating_reachable_reverse hur).trans h, fun h => hur.trans h⟩

lemma affected_proposal_location {G : SimpleGraph V} {X : V → C}
    {u r : V} {c a : C} (hra : X r ≠ a)
    (hchange : flipConfiguration X (flipSet G X u c) (X u) c r = a) :
    u ∈ flipSet G X r a ∧ c = if X u = X r then a else X r := by
  refine ⟨?_, ?_⟩
  · rw [← flipSet_eq_of_changes_root hra hchange]
    exact self_mem_flipSet
  · rcases proposal_pair_of_changes_root hra hchange with ⟨hu, hc⟩ | ⟨hu, hc⟩
    · simp [hu, hc]
    · have hne : X u ≠ X r := by simpa [hu] using Ne.symm hra
      simp [hne, hc]

lemma proposalDistribution_delete_eq_of_root_ne (F : HardListInstance V C)
    (X : V → C) (r : V) (a : C) (u : V) (c : C)
    (hroot : flipConfiguration X (flipSet F.graph X u c) (X u) c r ≠ a) :
    proposalDistribution (deleteListColour F r a) X u c = proposalDistribution F X u c := by
  unfold proposalDistribution
  split
  · rfl
  · congr 1
    unfold acceptanceProbability
    simp only [deleteListColour_graph, flipAllowed_deleteListColour_iff]
    have hi : (r ∈ flipSet F.graph X u c →
        flipConfiguration X (flipSet F.graph X u c) (X u) c r ≠ a) := fun _ => hroot
    exact if_congr ⟨And.left, fun h => ⟨h, hi⟩⟩ rfl rfl

lemma proposalDistribution_delete_eq_pure_of_root_eq (F : HardListInstance V C)
    (X : V → C) (r : V) (a : C) (u : V) (c : C) (hra : X r ≠ a)
    (hroot : flipConfiguration X (flipSet F.graph X u c) (X u) c r = a) :
    proposalDistribution (deleteListColour F r a) X u c = FinDist.pure X := by
  unfold proposalDistribution
  split
  · rfl
  · have hr : r ∈ flipSet F.graph X u c := by
      by_contra hn
      rw [flipConfiguration_of_not_mem hn] at hroot
      exact hra hroot
    have hbad : ¬ flipAllowed (deleteListColour F r a) (flipSet F.graph X u c)
        (flipConfiguration X (flipSet F.graph X u c) (X u) c) := by
      intro h
      exact ((flipAllowed_deleteListColour_iff F r a _ _).mp h).2 hr hroot
    have hp : acceptanceProbability (deleteListColour F r a) X u c = 0 := by
      unfold acceptanceProbability
      exact if_neg hbad
    apply FinDist.ext
    funext Y
    rw [twoPoint_w, hp]
    simp [FinDist.pure]
    exact ite_self 0

lemma ham_flip_eq_card {G : SimpleGraph V} {X : V → C} {u : V} {c : C}
    (hc : c ≠ X u) :
    ham (flipConfiguration X (flipSet G X u c) (X u) c) X =
      ((flipSet G X u c).card : ℝ) := by
  unfold ham hamCard
  congr 1
  congr 1
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, flipConfiguration_ne_iff hc]

lemma product_pure_cost (mu : FinDist (V → C)) (X : V → C) :
    (FinDist.Coupling.prod mu (FinDist.pure X)).cost ham = ∑ Y, mu.w Y * ham Y X := by
  unfold FinDist.Coupling.cost FinDist.Coupling.prod
  simp only [FinDist.pure, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma twoPoint_pure_cost (Y X : V → C) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.Coupling.prod (twoPoint Y X p hp0 hp1) (FinDist.pure X)).cost ham =
      p * ham Y X := by
  rw [product_pure_cost]
  simp only [twoPoint_w, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, ham_self, mul_zero, add_zero]

lemma proposal_W_pure_le (F : HardListInstance V C) (X : V → C) (u : V) (c : C) :
    FinDist.W ham (proposalDistribution F X u c) (FinDist.pure X) ≤
      vigodaMass (flipSet F.graph X u c).card := by
  unfold proposalDistribution
  split
  · rw [FinDist.W_self ham_nonneg ham_self]
    exact vigodaMass_nonneg _
  · rename_i hc
    apply (FinDist.W_le_cost ham_nonneg
      (FinDist.Coupling.prod _ (FinDist.pure X))).trans
    rw [twoPoint_pure_cost, ham_flip_eq_card hc]
    unfold acceptanceProbability
    split
    · have hs : ((flipSet F.graph X u c).card : ℝ) ≠ 0 := by
        exact_mod_cast (flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c)).ne'
      rw [div_mul_cancel₀ _ hs]
    · simpa using vigodaMass_nonneg (flipSet F.graph X u c).card

/-- A concrete proposal can differ after deleting one list colour only at
one colour label for a vertex in the affected component. -/
lemma proposal_delete_W_bound (F : HardListInstance V C) (X : V → C)
    (r : V) (a : C) (hra : X r ≠ a) (u : V) (c : C) :
    FinDist.W ham (proposalDistribution F X u c)
        (proposalDistribution (deleteListColour F r a) X u c) ≤
      if u ∈ flipSet F.graph X r a ∧ c = (if X u = X r then a else X r)
      then vigodaMass (flipSet F.graph X r a).card else 0 := by
  by_cases hchange : flipConfiguration X (flipSet F.graph X u c) (X u) c r = a
  · rw [proposalDistribution_delete_eq_pure_of_root_eq F X r a u c hra hchange]
    rw [if_pos (affected_proposal_location hra hchange)]
    have hbound := proposal_W_pure_le F X u c
    rw [flipSet_eq_of_changes_root hra hchange] at hbound
    exact hbound
  · rw [proposalDistribution_delete_eq_of_root_ne F X r a u c hchange]
    rw [FinDist.W_self ham_nonneg ham_self]
    by_cases hloc : u ∈ flipSet F.graph X r a ∧ c = (if X u = X r then a else X r)
    · rw [if_pos hloc]
      exact vigodaMass_nonneg _
    · rw [if_neg hloc]

/-- The affected component supplies exactly one colour label per vertex. -/
lemma sum_affected_proposals (S : Finset V) (f : V → C) (b : ℝ) :
    (∑ p : V × C, if p.1 ∈ S ∧ p.2 = f p.1 then b else 0) = (S.card : ℝ) * b := by
  rw [Fintype.sum_prod_type]
  have hinner : ∀ u : V,
      (∑ c : C, if u ∈ S ∧ c = f u then b else 0) = if u ∈ S then b else 0 := by
    intro u
    by_cases hu : u ∈ S
    · simp [hu]
    · simp [hu]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  simp

/-- The actual hard component-flip kernel has one-list-colour sensitivity
at most `1 / (|V| |C|)`.  The input need only avoid the deleted colour. -/
theorem hardStep_deleteListColour_W_le [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) (r : V) (a : C) (hra : X r ≠ a) :
    FinDist.W ham (hardStep F X) (hardStep (deleteListColour F r a) X) ≤
      1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  unfold hardStep
  apply (FinDist.W_bind_diag ham_nonneg (FinDist.uniform (V × C)) _ _).trans
  let S := flipSet F.graph X r a
  let k : ℝ := (Fintype.card (V × C) : ℝ)⁻¹
  have hk : 0 ≤ k := by dsimp [k]; positivity
  calc
    _ ≤ ∑ p : V × C, k * (if p.1 ∈ S ∧ p.2 = (if X p.1 = X r then a else X r)
        then vigodaMass S.card else 0) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (proposal_delete_W_bound F X r a hra p.1 p.2) hk
    _ = (S.card : ℝ) * (k * vigodaMass S.card) := by
      simp_rw [mul_ite, mul_zero]
      exact sum_affected_proposals S (fun u => if X u = X r then a else X r) _
    _ = k * ((S.card : ℝ) * vigodaMass S.card) := by ring
    _ ≤ k * 1 := mul_le_mul_of_nonneg_left (vigoda_branch_bound S.card) hk
    _ = 1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
      simp [k, Fintype.card_prod, Nat.cast_mul]

end PottsCI.Vigoda
