import CI2ZF.Coupling.CV.Kernel
import CI2ZF.Coupling.Vigoda.HardFlipBoundary
import CI2ZF.Coupling.Vigoda.SoftFlipBoundary
import CI2ZF.Potts.Model.RootChildren

/-! Boundary sensitivity of the actual CV kernels, using the labelled constraint
embedding and concrete component geometry. No row-discrepancy bound is assumed. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist CI2ZF.Potts
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

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

lemma proposal_W_pure_le (F : HardListInstance V C) (X : V → C) (u : V) (c : C) :
    FinDist.W ham (proposalDistribution F X u c) (FinDist.pure X) ≤
      mass (flipSet F.graph X u c).card := by
  unfold proposalDistribution
  split
  · rw [FinDist.W_self ham_nonneg ham_self]
    exact mass_nonneg _
  · rename_i hc
    apply (FinDist.W_le_cost ham_nonneg
      (FinDist.Coupling.prod _ (FinDist.pure X))).trans
    rw [twoPoint_pure_cost, ham_flip_eq_card hc]
    unfold acceptanceProbability
    split
    · have hs : ((flipSet F.graph X u c).card : ℝ) ≠ 0 := by
        exact_mod_cast (flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c)).ne'
      rw [div_mul_cancel₀ _ hs]
    · simpa using mass_nonneg (flipSet F.graph X u c).card

/-- A concrete proposal can differ after deleting one list colour only at
one colour label for a vertex in the affected component. -/
lemma proposal_delete_W_bound (F : HardListInstance V C) (X : V → C)
    (r : V) (a : C) (hra : X r ≠ a) (u : V) (c : C) :
    FinDist.W ham (proposalDistribution F X u c)
        (proposalDistribution (deleteListColour F r a) X u c) ≤
      if u ∈ flipSet F.graph X r a ∧ c = (if X u = X r then a else X r)
      then mass (flipSet F.graph X r a).card else 0 := by
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
      exact mass_nonneg _
    · rw [if_neg hloc]

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
        then mass S.card else 0) := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_left (proposal_delete_W_bound F X r a hra p.1 p.2) hk
    _ = (S.card : ℝ) * (k * mass S.card) := by
      simp_rw [mul_ite, mul_zero]
      exact sum_affected_proposals S (fun u => if X u = X r then a else X r) _
    _ = k * ((S.card : ℝ) * mass S.card) := by ring
    _ ≤ k * 1 := mul_le_mul_of_nonneg_left (size_mass_le_one S.card) hk
    _ = 1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
      simp [k, Fintype.card_prod, Nat.cast_mul]

lemma softCVKernel_eq_coin_mixture [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X : V → C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softCVKernel I x hx0 hx1 X =
      (commonCoinLaw (K := I.Constraint) (1 - x) ⟨by linarith, by linarith⟩).bind
        (fun ω => hardStep (activeHardListInstance I (activatedSet I X ω)) X) := by
  change (I.activeLawGivenSpin x hx0 hx1 X).bind
    (fun A => hardStep (activeHardListInstance I A) X) = _
  rw [← activatedSet_law I X x hx0 hx1]
  exact mapLaw_bind _ _ _

lemma activated_hardStep_addBoundary_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (ω : (addBoundary I r a).Constraint → Bool) :
    W ham
      (hardStep (activeHardListInstance I (activatedSet I X
        (fun k => ω (boundaryConstraintEmbedding I r a k)))) X)
      (hardStep (activeHardListInstance (addBoundary I r a)
        (activatedSet (addBoundary I r a) X ω)) X) ≤
      if ω (freshBoundaryConstraint I r a) = true then
        1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0 := by
  rw [activeHardListInstance_addBoundary]
  by_cases h : ω (freshBoundaryConstraint I r a) = true ∧ X r ≠ a
  · rw [if_pos h, if_pos h.1]
    exact hardStep_deleteListColour_W_le _ X r a h.2
  · rw [if_neg h, W_self ham_nonneg ham_self]
    by_cases hf : ω (freshBoundaryConstraint I r a) = true
    · rw [if_pos hf]
      positivity
    · rw [if_neg hf]

/-- Adding one actual boundary-count occurrence changes each soft row by
at most `(1-x)/(|V||C|)` in Hamming Wasserstein distance. -/
theorem softCVKernel_addBoundary_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softCVKernel I x hx0 hx1 X)
      (softCVKernel (addBoundary I r a) x hx0 hx1 X) ≤
        (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  let p := commonCoinLaw (K := (addBoundary I r a).Constraint) (1 - x) ht
  let restrict := fun (ω : (addBoundary I r a).Constraint → Bool) (k : I.Constraint) =>
    ω (boundaryConstraintEmbedding I r a k)
  have hold : (commonCoinLaw (K := I.Constraint) (1 - x) ht).bind
      (fun ω => hardStep (activeHardListInstance I (activatedSet I X ω)) X) =
      p.bind (fun ω => hardStep (activeHardListInstance I (activatedSet I X (restrict ω))) X) := by
    rw [← map_commonCoinLaw_embedding (boundaryConstraintEmbedding I r a) (1 - x) ht]
    exact mapLaw_bind _ _ _
  rw [softCVKernel_eq_coin_mixture, softCVKernel_eq_coin_mixture]
  rw [hold]
  apply (W_bind_diag ham_nonneg p _ _).trans
  calc
    _ ≤ ∑ ω, p.w ω * (if ω (freshBoundaryConstraint I r a) = true then
          1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (activated_hardStep_addBoundary_W_le I r a X ω) (p.nonneg ω)
    _ = (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
      have h := expectReal_product_coordinate
        (fun _ : (addBoundary I r a).Constraint => bernoulliLaw (1 - x) ht)
        (freshBoundaryConstraint I r a)
        (fun b : Bool => if b = true then
          1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0)
      simpa [p, commonCoinLaw, expectReal, bernoulliLaw, div_eq_mul_inv] using h

/-- The same concrete boundary sensitivity in the child-to-middle direction. -/
theorem softCVKernel_addBoundary_W_le_reverse [Nonempty V] [Nonempty C]
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softCVKernel (addBoundary I r a) x hx0 hx1 X)
      (softCVKernel I x hx0 hx1 X) ≤
        (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  rw [W_ham_comm]
  exact softCVKernel_addBoundary_W_le I r a X x hx0 hx1

local instance (priority := 2000) cVBoundaryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- Adding the same pinned colour at every vertex of a finite set changes
each actual soft row by at most one single-occurrence budget per vertex. -/
theorem softCVKernel_addBoundarySet_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (S : Finset V) (a : C) (X : V → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softCVKernel (addBoundarySet I S a) x hx0 hx1 X)
      (softCVKernel I x hx0 hx1 X) ≤
        (1 - x) * S.card / ((Fintype.card V : ℝ) * Fintype.card C) := by
  induction S using Finset.induction_on with
  | empty => simp [W_self ham_nonneg ham_self]
  | @insert u S hu ih =>
    rw [addBoundarySet_insert I S u a hu]
    calc
      _ ≤ W ham
          (softCVKernel (addBoundary (addBoundarySet I S a) u a) x hx0 hx1 X)
          (softCVKernel (addBoundarySet I S a) x hx0 hx1 X) +
          W ham (softCVKernel (addBoundarySet I S a) x hx0 hx1 X)
            (softCVKernel I x hx0 hx1 X) :=
        W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle _ _ _
      _ ≤ (1 - x) / ((Fintype.card V : ℝ) * Fintype.card C) +
          (1 - x) * S.card / ((Fintype.card V : ℝ) * Fintype.card C) :=
        add_le_add (softCVKernel_addBoundary_W_le_reverse
          (addBoundarySet I S a) u a X x hx0 hx1) ih
      _ = _ := by rw [Finset.card_insert_of_notMem hu, Nat.cast_add, Nat.cast_one]; ring

/-- The concrete child-to-middle perturbation bound required in root CI. -/
theorem rootChild_soft_boundary_W_le [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (a : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (X : RootRemaining tau r → C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softCVKernel (rootChildData tau G r a) x hx0 hx1 X)
      (softCVKernel (rootMiddleData tau G r) x hx0 hx1 X) ≤
        (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  rw [rootChildData_eq_addBoundarySet]
  apply (softCVKernel_addBoundarySet_W_le _ _ _ _ x hx0 hx1).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact_mod_cast rootBoundaryVertices_card_le tau G r hdegree

end
end CI2ZF.Appendix.CV
