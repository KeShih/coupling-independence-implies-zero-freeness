import CI2ZF.Appendix.CV.DiscountSupport
import CI2ZF.Appendix.CV.Geometry
import CI2ZF.ActiveDegree
import CI2ZF.HardSingletonRegular

/-! Fresh colours in the full pinned graph produce feasible synchronous
singleton moves for every actual active-constraint outcome. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

def freshColours (I : PinningData V C) (X : V → C) (s : V) (a b : C) : Finset C :=
  Finset.univ \ (({a, b} ∪ (I.graph.neighborFinset s).image X) ∪
    (Finset.univ.filter fun c => 0 < I.boundaryCount s c))

lemma mem_freshColours (I : PinningData V C) (X : V → C) (s : V) (a b c : C) :
    c ∈ freshColours I X s a b ↔ c ≠ a ∧ c ≠ b ∧
      (∀ t, I.graph.Adj s t → X t ≠ c) ∧ I.boundaryCount s c = 0 := by
  simp only [freshColours, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · intro hn
    refine ⟨fun hh => hn (Or.inl (Or.inl (Or.inl hh))),
      fun hh => hn (Or.inl (Or.inl (Or.inr hh))), ?_, ?_⟩
    · intro t ht heq; exact hn (Or.inl (Or.inr ⟨t, ht, heq⟩))
    · exact Nat.eq_zero_of_not_pos (fun hh => hn (Or.inr hh))
  · rintro ⟨ha, hb, hn, hz⟩ hh
    rcases hh with (hh | ⟨t, ht, heq⟩) | hp
    · exact hh.elim ha hb
    · exact hn t ht heq
    · omega

/-- At least `q-Δ-2` colours remain, with repeated pinned colours counted
by their original boundary multiplicities. -/
theorem freshColours_card (I : PinningData V C) (X : V → C) (s : V) (a b : C)
    {Δ : ℕ} (hdegree : I.graph.degree s + ∑ c, I.boundaryCount s c ≤ Δ) :
    Fintype.card C ≤ (freshColours I X s a b).card + Δ + 2 := by
  classical
  let B := Finset.univ.filter fun c => 0 < I.boundaryCount s c
  have hB : B.card ≤ ∑ c, I.boundaryCount s c := by
    calc
      B.card = ∑ _c ∈ B, 1 := by simp
      _ ≤ ∑ c ∈ B, I.boundaryCount s c := Finset.sum_le_sum fun c hc => by
        exact (Finset.mem_filter.mp hc).2
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by simp)
  let D := ({a, b} ∪ (I.graph.neighborFinset s).image X) ∪ B
  have hD : D.card ≤ Δ + 2 := by
    have h1 := Finset.card_union_le ({a, b} : Finset C) ((I.graph.neighborFinset s).image X)
    have h2 := Finset.card_union_le ({a, b} ∪ (I.graph.neighborFinset s).image X) B
    have hi := Finset.card_image_le (s := I.graph.neighborFinset s) (f := X)
    have hp : ({a, b} : Finset C).card ≤ 2 := by by_cases hh : a = b <;> simp [hh]
    have hg : (I.graph.neighborFinset s).card = I.graph.degree s := by simp
    change ((_ ∪ _) ∪ B).card ≤ _
    omega
  have hid := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
  change (Finset.univ \ D).card + D.card = Finset.univ.card at hid
  change Fintype.card C ≤ (Finset.univ \ D).card + Δ + 2
  simpa only [Finset.card_univ] using hid.symm.trans_le (by omega)

lemma active_fresh_singleton (I : PinningData V C) (X : V → C)
    (ω : I.Constraint → Bool) (s : V) (a b c : C)
    (hs : X s = a ∨ X s = b) (hc : c ∈ freshColours I X s a b) :
    flipSet (activeHardListInstance I (activatedSet I X ω)).graph X s c = {s} ∧
      flipAllowed (activeHardListInstance I (activatedSet I X ω)) {s}
        (Function.update X s c) := by
  obtain ⟨hca, hcb, hn, hz⟩ := (mem_freshColours I X s a b c).mp hc
  have hcs : c ≠ X s := by
    rcases hs with hs | hs
    · simpa only [hs] using hca
    · simpa only [hs] using hcb
  constructor
  · apply root_flipSet_singleton_of_no_neighbours _ X s c hcs
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht, htc⟩ := mem_rootNeighbours.mp ht
    exact hn t (activeGraph_le_original I _ ht) htc
  · intro t ht
    have heq : t = s := Finset.mem_singleton.mp ht
    subst t
    simp only [Function.update_self, activeHardListInstance, activeList,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨i, _⟩
    have hi := i.isLt
    omega

lemma flipConfiguration_singleton (X : V → C) (s : V) (c : C) :
    flipConfiguration X {s} (X s) c = Function.update X s c := by
  classical
  funext t
  by_cases ht : t = s
  · subst t; simp [flipConfiguration]
  · simp [flipConfiguration, ht]

/-- A fresh blocker recolouring appears in the actual completed coupling
with the full singleton probability in every active outcome. -/
theorem fullHardCoupling_fresh_entry [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (ω : I.Constraint → Bool)
    (v : V) (a b : C) (hXa : X v = a) (hYb : Y v = b) (hab : a ≠ b)
    (hagree : ∀ t, t ≠ v → X t = Y t)
    (choice : GlobalChoice (activatedSet_rootLocal I X Y ω v a b hXa hYb hab hagree))
    (s : V) (hsv : s ≠ v) (hs : X s = a ∨ X s = b) (c : C)
    (hc : c ∈ freshColours I X s a b) :
    (fullHardCoupling (activatedSet_rootLocal I X Y ω v a b hXa hYb hab hagree) choice).w
      (Function.update X s c) (Function.update Y s c) =
        1 / ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hcdata := (mem_freshColours I X s a b c).mp hc
  have hcY : c ∈ freshColours I Y s a b := by
    apply (mem_freshColours I Y s a b c).mpr
    refine ⟨hcdata.1, hcdata.2.1, ?_, hcdata.2.2.2⟩
    intro t ht
    by_cases htv : t = v
    · subst t; rw [hYb]; exact hcdata.2.1.symm
    · rw [← hagree t htv]; exact hcdata.2.2.1 t ht
  have hx := active_fresh_singleton I X ω s a b c hs hc
  have hy := active_fresh_singleton I Y ω s a b c (by rwa [← hagree s hsv]) hcY
  let h := activatedSet_rootLocal I X Y ω v a b hXa hYb hab hagree
  have hcs : c ≠ X s := by rcases hs with hs | hs <;> simp_all
  have ha : flipAllowed (activeHardListInstance I (activatedSet I X ω))
      (flipSet (activeHardListInstance I (activatedSet I X ω)).graph X s c)
      (flipConfiguration X (flipSet (activeHardListInstance I (activatedSet I X ω)).graph X s c)
        (X s) c) := by rw [hx.1, flipConfiguration_singleton]; exact hx.2
  have hm := hardCommonOffRoot_component_match h s c hcs (hx.1.trans hy.1.symm)
    (by rw [hx.1]; simpa only [Finset.mem_singleton] using hsv.symm) ha
  rw [hx.1, hy.1, flipConfiguration_singleton, flipConfiguration_singleton] at hm
  have hmass := hardStep_component_mass (activeHardListInstance I (activatedSet I X ω)) X s c hcs ha
  rw [hx.1, flipConfiguration_singleton] at hmass
  simp only [Finset.card_singleton, mass] at hm hmass
  apply le_antisymm
  · exact (coupling_entry_le_left _ _ _).trans_eq hmass
  · rw [← hm]
    exact fullHardCoupling_dominate_common h choice _ _

end
end CI2ZF.Appendix.CV
