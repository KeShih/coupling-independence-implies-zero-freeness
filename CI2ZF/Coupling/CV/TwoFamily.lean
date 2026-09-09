import CI2ZF.Coupling.CV.BranchEncoding

/-! Exact two-incidence family records from actual graph components. The
second occurrence of a repeated component is a zero marker. Truncation
preserves the root cost, both residuals, and both size-weighted costs. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def fullFamily (a₀ a₁ : Branch) (i : Bool) : UnboundedFamily :=
  { rootCost := (realFamily a₀ a₁ i).rootCost
    residual₀ := (realFamily a₀ a₁ i).residual₀
    residual₁ := (realFamily a₀ a₁ i).residual₁
    cost₀ := branchSize a₀ * (realFamily a₀ a₁ i).residual₀
    cost₁ := branchSize a₁ * (realFamily a₀ a₁ i).residual₁ }

lemma fullFamily_eq_unboundedFamily (a₀ a₁ : Branch) (i : Bool) :
    fullFamily a₀ a₁ i = unboundedFamily (branchSize a₀) (branchSize a₁)
      (feasible a₀) (feasible a₁) i := by
  rfl

def secondComponentBranch (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u w : V) (hw : w ∈ rootNeighbours F X v c) : Branch :=
  if offRootComponent F X v (X v) c u = offRootComponent F X v (X v) c w
  then 0 else componentBranch F X v c hc w hw

def componentFamily (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (u w : V) (i : Bool) : UnboundedFamily :=
  let S := offRootComponent F X v (X v) c u
  let T := offRootComponent F X v (X v) c w
  unboundedFamily S.card (if S = T then 0 else T.card)
    (decide (flipAllowed F S (flipConfiguration X S (X v) c)))
    (if S = T then false else decide (flipAllowed F T (flipConfiguration X T (X v) c))) i

/-- The finite family retains all actual costs, even when a component is
larger than seven or meets both root neighbours. -/
theorem fullFamily_eq_componentFamily (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (u w : V) (hu : u ∈ rootNeighbours F X v c)
    (hw : w ∈ rootNeighbours F X v c) (i : Bool) :
    fullFamily (componentBranch F X v c hc u hu) (secondComponentBranch F X v c hc u w hw) i =
      componentFamily F X v c u w i := by
  obtain ⟨hs, _, hf⟩ := componentBranch_spec F X v c hc u hu
  obtain ⟨ht, _, hg⟩ := componentBranch_spec F X v c hc w hw
  rw [fullFamily_eq_unboundedFamily]
  unfold secondComponentBranch componentFamily
  split_ifs with heq
  · simp only [hs, hf, heq, if_true, show branchSize (0 : Branch) = 0 from rfl,
      show feasible (0 : Branch) = false from rfl]
    simpa [heq] using unboundedFamily_cap
      (offRootComponent F X v (X v) c u).card 0
      (decide (flipAllowed F (offRootComponent F X v (X v) c u)
        (flipConfiguration X (offRootComponent F X v (X v) c u) (X v) c))) false i
  · simp only [hs, ht, hf, hg, heq, if_false]
    exact unboundedFamily_cap _ _ _ _ _

/-- Root matching at the Boolean index has exactly this family record. The
only excluded choice is the second copy of one repeated component. -/
theorem componentFamily_eq_actual (F : HardListInstance V C) (X : V → C) (v : V) (c : C)
    (hc : c ≠ X v) (hav : c ∈ F.list v) (u w : V)
    (hN : rootNeighbours F X v c = {u, w}) (i : Bool)
    (hi : i = true → offRootComponent F X v (X v) c u ≠ offRootComponent F X v (X v) c w) :
    componentFamily F X v c u w i =
      { rootCost := rootCharge F X v c (if i then w else u)
        residual₀ := componentResidual F X v c (if i then w else u)
          (offRootComponent F X v (X v) c u)
        residual₁ := if offRootComponent F X v (X v) c u = offRootComponent F X v (X v) c w
          then 0 else componentResidual F X v c (if i then w else u)
            (offRootComponent F X v (X v) c w)
        cost₀ := (offRootComponent F X v (X v) c u).card *
          componentResidual F X v c (if i then w else u) (offRootComponent F X v (X v) c u)
        cost₁ := if offRootComponent F X v (X v) c u = offRootComponent F X v (X v) c w
          then 0 else (offRootComponent F X v (X v) c w).card *
            componentResidual F X v c (if i then w else u) (offRootComponent F X v (X v) c w) } := by
  let S := offRootComponent F X v (X v) c u
  let T := offRootComponent F X v (X v) c w
  have hSne : offRootComponent F X v (X v) c u ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨u, self_mem_offRootComponent F X v u (X v) c⟩
  have hTne : offRootComponent F X v (X v) c w ≠ ∅ :=
    Finset.nonempty_iff_ne_empty.mp ⟨w, self_mem_offRootComponent F X v w (X v) c⟩
  have hroot : flipAllowed F (flipSet F.graph X v c)
      (flipConfiguration X (flipSet F.graph X v c) (X v) c) ↔
      flipAllowed F S (flipConfiguration X S (X v) c) ∧
        flipAllowed F T (flipConfiguration X T (X v) c) := by
    rw [root_flipAllowed_iff F X v c hc]
    simp [rootFamily, hN, hav, S, T]
  have hS : (rootFamily F X v c) = {S, T} := by simp [rootFamily, hN, S, T]
  by_cases hST : S = T
  · have hi0 : i = false := by
      cases i
      · rfl
      · exact (hi rfl hST).elim
    subst i
    have hsize : (flipSet F.graph X v c).card = 1 + S.card := by
      rw [root_flipSet_card F X v c hc, hS]
      simp only [hST, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.sum_singleton]
    simp [componentFamily, unboundedFamily, rootCharge, componentResidual, pieceRate, rootRate, hroot,
      hsize, ← hST, S, T, hSne]
  · have hsize : (flipSet F.graph X v c).card = 1 + S.card + T.card :=
      root_flipSet_card_two_neighbours F X v u w c hc hN hST
    have hne : offRootComponent F X v (X v) c u ≠ offRootComponent F X v (X v) c w := hST
    cases i <;> simp [componentFamily, unboundedFamily, rootCharge, componentResidual,
      pieceRate, rootRate, hroot, hsize, hne, Ne.symm hne, S, T, hSne, hTne]
    ring

end
end CI2ZF.Appendix.CV
