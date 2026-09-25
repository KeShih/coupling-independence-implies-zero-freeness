import ZeroFreeness.Potts.Geometry.ComponentFactorization
import ZeroFreeness.Potts.Model.RootChildren
import ZeroFreeness.Potts.Model.PinningRestrictionComposition

/-! An actual bounded-degree ambient graph realizes a pinning datum.
Unpinned ambient vertices outside the free image are deleted, rather
than replaced by new pinned leaves. This retains general graph classes
closed only under induced subgraphs. -/
namespace ZeroFreeness.Potts
open PottsCI Separator Component
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) ambientRealizationDecEq (T : Type*) : DecidableEq T :=
  Classical.decEq T
set_option linter.unusedSectionVars false
universe u v w
variable {V : Type u} {A : Type v} {C : Type w}
  [Fintype V] [Fintype A] [Fintype C]

structure AmbientRealization (I : PinningData V C) (G : SimpleGraph A) where
  free : V ↪ A
  pin : A → Option C
  free_unpinned : ∀ v, pin (free v) = none
  graph_eq : I.graph = G.comap free
  count_eq : ∀ v c, I.boundaryCount v c =
    ∑ a : A, if G.Adj (free v) a ∧ pin a = some c then 1 else 0

theorem boundaryCount_eq_sum_all_colour? (tau : PartialColouring A C)
    (G : SimpleGraph A) (v : tau.FreeVertex) (c : C) :
    tau.boundaryCount G v c =
      ∑ a : A, if G.Adj v.val a ∧ tau.colour? a = some c then 1 else 0 := by
  rw [boundaryCount_eq_sum_colour?]
  let f : A → ℕ := fun a => if G.Adj v.val a ∧ tau.colour? a = some c then 1 else 0
  have hf : ∀ a ∈ (Finset.univ : Finset A), a ∉ tau.domain → f a = 0 := by
    intro a _ ha
    simp [f, tau.colour?_of_not_mem ha]
  have hs := Finset.sum_subset (f := f) (Finset.subset_univ tau.domain) hf
  convert hs using 1
  apply Finset.sum_congr rfl
  intro a _
  dsimp [f]
  split_ifs <;> rfl

def AmbientRealization.ofPartialColouring (tau : PartialColouring A C)
    (G : SimpleGraph A) : AmbientRealization (tau.toPinningData G) G where
  free := Function.Embedding.subtype _
  pin := tau.colour?
  free_unpinned v := tau.colour?_of_not_mem v.property
  graph_eq := rfl
  count_eq := boundaryCount_eq_sum_all_colour? tau G

def AmbientRealization.restrict {I : PinningData V C} {G : SimpleGraph A}
    (h : AmbientRealization I G) (p : V → Prop) :
    AmbientRealization (restrictData I p) G where
  free := (Function.Embedding.subtype p).trans h.free
  pin := h.pin
  free_unpinned v := h.free_unpinned v.val
  graph_eq := by
    change I.graph.comap Subtype.val = _
    rw [h.graph_eq]
    rfl
  count_eq v c := h.count_eq v.val c

def AmbientRealization.relabel {W : Type*} [Fintype W]
    {I : PinningData V C} {G : SimpleGraph A} (h : AmbientRealization I G) (e : V ≃ W) :
    AmbientRealization (relabelData I e) G where
  free := e.symm.toEmbedding.trans h.free
  pin := h.pin
  free_unpinned w := h.free_unpinned (e.symm w)
  graph_eq := by
    change I.graph.comap e.symm = _
    rw [h.graph_eq]
    rfl
  count_eq w c := h.count_eq (e.symm w) c

namespace AmbientRealization
variable {I : PinningData V C} {G : SimpleGraph A} (h : AmbientRealization I G)

def active : Set A := Set.range h.free ∪ {a | h.pin a ≠ none}

def activeGraph : SimpleGraph h.active := G.induce h.active

def activePinning : PartialColouring h.active C where
  domain := Finset.univ.filter (fun a => h.pin a.val ≠ none)
  colour a := (h.pin a.val.val).get
    (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp a.property).2)

@[simp] theorem activePinning_mem_domain (a : h.active) :
    a ∈ h.activePinning.domain ↔ h.pin a.val ≠ none := by
  simp [activePinning]

theorem activePinning_colour? (a : h.active) : h.activePinning.colour? a = h.pin a.val := by
  by_cases hn : h.pin a.val = none
  · rw [PartialColouring.colour?_of_not_mem _ (by simpa using hn)]
    exact hn.symm
  · rw [PartialColouring.colour?_of_mem _ ((h.activePinning_mem_domain a).mpr hn)]
    exact Option.coe_get _

def activeFree (v : V) : h.activePinning.FreeVertex :=
  ⟨⟨h.free v, Or.inl ⟨v, rfl⟩⟩, by
    simp [PartialColouring.freeSet, activePinning, h.free_unpinned]⟩

@[simp] theorem activeFree_val (v : V) : (h.activeFree v).val.val = h.free v := rfl

def activeFreeEquiv : V ≃ h.activePinning.FreeVertex :=
  Equiv.ofBijective h.activeFree ⟨by
    intro v w he
    apply h.free.injective
    exact congrArg (fun a : h.activePinning.FreeVertex => a.val.val) he,
  by
    intro a
    have hpin : h.pin a.val.val = none := by
      have hn : a.val ∉ h.activePinning.domain := a.property
      rw [h.activePinning_mem_domain] at hn
      exact not_not.mp hn
    have hrange : a.val.val ∈ Set.range h.free :=
      a.val.property.resolve_right (fun hn => hn hpin)
    obtain ⟨v, hv⟩ := hrange
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hv⟩

@[simp] theorem activeFreeEquiv_apply (v : V) : h.activeFreeEquiv v = h.activeFree v := rfl

theorem sum_active_eq_sum (f : A → ℕ) (hf : ∀ a, a ∉ h.active → f a = 0) :
    (∑ a : h.active, f a.val) = ∑ a : A, f a := by
  have hc : (∑ a : {a : A // a ∉ h.active}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hf a.val a.property
  have hs := Fintype.sum_subtype_add_sum_subtype (fun a => a ∈ h.active) f
  rw [hc, add_zero] at hs
  exact hs

/-- After deleting the unused ambient vertices, the actual partial
coloring on the induced graph realizes precisely the given datum. -/
theorem activePinning_data :
    relabelData (h.activePinning.toPinningData h.activeGraph) h.activeFreeEquiv.symm = I := by
  change PinningData.mk _ _ = PinningData.mk I.graph I.boundaryCount
  apply congrArg₂ PinningData.mk
  · ext v w
    change G.Adj (h.free v) (h.free w) ↔ I.graph.Adj v w
    rw [h.graph_eq]
    rfl
  · funext v c
    change h.activePinning.boundaryCount h.activeGraph (h.activeFree v) c = _
    trans ∑ a : h.active, if h.activeGraph.Adj (h.activeFree v).val a ∧
      h.activePinning.colour? a = some c then 1 else 0
    · exact boundaryCount_eq_sum_all_colour? h.activePinning h.activeGraph (h.activeFree v) c
    simp_rw [h.activePinning_colour?]
    change (∑ a : h.active,
      if G.Adj (h.free v) a.val ∧ h.pin a.val = some c then 1 else 0) = _
    rw [h.count_eq]
    have hs := h.sum_active_eq_sum
      (fun a => if G.Adj (h.free v) a ∧ h.pin a = some c then 1 else 0) (by
        intro a ha
        have hn : h.pin a = none := by
          by_contra hn
          exact ha (Or.inr hn)
        simp [hn])
    exact hs

end AmbientRealization

def AmbientRealization.restrictPinning {A V W : Type u} [Fintype A] [Fintype V]
    [Fintype W] {I : PinningData V C} {G : SimpleGraph A}
    (h : AmbientRealization I G) (e : W ↪ V) (p : V → Option C)
    (hp : ∀ w, p (e w) = none) : AmbientRealization (restrictPinningData I e p) G where
  free := e.trans h.free
  pin := composePinning h.free h.pin p
  free_unpinned := composePinning_free h.free e h.pin p hp
  graph_eq := by
    change I.graph.comap e = _
    rw [h.graph_eq]
    rfl
  count_eq w c := by
    rw [restrictPinningData_count, h.count_eq]
    have hs := sum_composePinning h.free h.pin p h.free_unpinned
      (fun a q => if G.Adj (h.free (e w)) a ∧ q = some c then 1 else 0)
      (by intro a; simp)
    change _ = ∑ a : A,
      if G.Adj (h.free (e w)) a ∧ composePinning h.free h.pin p a = some c then 1 else 0
    rw [hs]
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    rw [h.graph_eq]
    split_ifs <;> simp_all [SimpleGraph.comap]

end
end ZeroFreeness.Potts
