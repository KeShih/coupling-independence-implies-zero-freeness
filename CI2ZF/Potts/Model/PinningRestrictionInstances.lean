import CI2ZF.Potts.Model.PinningFamily
import CI2ZF.Potts.Geometry.OptionComponentFactorization
import CI2ZF.Potts.Transfer.ExteriorRepinning

/-! Existing actual Potts children, induced pieces, and separator exterior
operations are instances of the single restriction-and-pinning operation. -/
namespace CI2ZF.Potts
open PottsCI Separator Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
variable {V W U S O : Type u} {C : Type v}

theorem restrictPinningData_none [Fintype V] (I : PinningData V C) (e : W ↪ V) :
    restrictPinningData I e (fun _ => none) =
      ⟨I.graph.comap e, fun w c => I.boundaryCount (e w) c⟩ := by
  unfold restrictPinningData
  congr 1
  funext w c
  simp

theorem restrictPinningData_id [Fintype V] (I : PinningData V C) :
    restrictPinningData I (Function.Embedding.refl V) (fun _ => none) = I := by
  rw [restrictPinningData_none]
  cases I
  rfl

theorem relabelData_eq_restrictPinningData [Fintype V]
    (I : PinningData V C) (e : V ≃ W) :
    relabelData I e = restrictPinningData I e.symm.toEmbedding (fun _ => none) := by
  rw [restrictPinningData_none]
  rfl

theorem cutData_eq_restrictPinningData [Fintype V]
    (I : PinningData V C) (p : V → Prop) :
    Component.restrictData I p =
      restrictPinningData I (Function.Embedding.subtype p) (fun _ => none) := by
  rw [restrictPinningData_none]
  rfl

def someEmbedding : O ↪ Option O := ⟨Option.some, Option.some_injective _⟩

def rootOnlyPinning (a : C) : Option O → Option C := Option.elim' (some a) (fun _ => none)

theorem optionMiddleData_eq_restrictPinningData [Fintype O]
    (I : PinningData (Option O) C) :
    optionMiddleData I = restrictPinningData I someEmbedding (fun _ => none) := by
  rw [restrictPinningData_none]
  rfl

theorem optionChildData_eq_restrictPinningData [Fintype O] [Fintype C]
    (I : PinningData (Option O) C) (a : C) :
    optionChildData I a = restrictPinningData I someEmbedding (rootOnlyPinning a) := by
  have hg : (optionChildData I a).graph =
      (restrictPinningData I someEmbedding (rootOnlyPinning a)).graph := rfl
  have hb : (optionChildData I a).boundaryCount =
      (restrictPinningData I someEmbedding (rootOnlyPinning a)).boundaryCount := by
    funext o c
    rw [optionChildData_count, restrictPinningData_count, Fintype.sum_option]
    simp [someEmbedding, rootOnlyPinning, I.graph.adj_comm, eq_comm]
  exact congrArg₂ PinningData.mk hg hb

def shellOnlyPinning (ξ : S → C) : Separator.Vertex U S O → Option C :=
  Sum.elim (fun _ => none) (Sum.elim (fun s => some (ξ s)) (fun _ => none))

theorem exteriorData_eq_restrictPinningData [Fintype U] [Fintype S] [Fintype O]
    (I : PinningData (Separator.Vertex U S O) C) (ξ : S → C) :
    exteriorData I ξ = restrictPinningData I outsideEmbedding (shellOnlyPinning ξ) := by
  have hg : (exteriorData I ξ).graph =
      (restrictPinningData I outsideEmbedding (shellOnlyPinning ξ)).graph := rfl
  have hb : (exteriorData I ξ).boundaryCount =
      (restrictPinningData I outsideEmbedding (shellOnlyPinning ξ)).boundaryCount := by
    funext o c
    simp only [exteriorData, restrictPinningData, Fintype.sum_sum_type,
      shellOnlyPinning, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, and_false,
      if_false, Finset.sum_const_zero, zero_add, add_zero, Option.some.injEq]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    simp only [I.graph.adj_comm]
  exact congrArg₂ PinningData.mk hg hb

def exceptShellPinning (ξ : S → C) (s : S) : Separator.Vertex U S O → Option C :=
  Sum.elim (fun _ => none)
    (Sum.elim (fun t => if t = s then none else some (ξ t)) (fun _ => none))

theorem unpinnedExteriorData_eq_restrictPinningData [Fintype U] [Fintype S] [Fintype O]
    (I : PinningData (Separator.Vertex U S O) C) (ξ : S → C) (s : S) :
    unpinnedExteriorData I ξ s = restrictPinningData I (unpinShellEmbedding s) (exceptShellPinning ξ s) := by
  have hg : (unpinnedExteriorData I ξ s).graph =
      (restrictPinningData I (unpinShellEmbedding s) (exceptShellPinning ξ s)).graph := rfl
  have hb : (unpinnedExteriorData I ξ s).boundaryCount =
      (restrictPinningData I (unpinShellEmbedding s) (exceptShellPinning ξ s)).boundaryCount := by
    funext w c
    simp only [unpinnedExteriorData, restrictPinningData, Fintype.sum_sum_type,
      exceptShellPinning, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, and_false,
      if_false, Finset.sum_const_zero, zero_add, add_zero]
    congr 1
    symm
    calc
      _ = ∑ t ∈ Finset.univ.erase s,
          if I.graph.Adj (unpinShellEmbedding s w) (Sum.inr (Sum.inl t)) ∧
            (if t = s then none else some (ξ t)) = some c then 1 else 0 := by
        symm
        apply Finset.sum_subset (Finset.erase_subset _ _)
        intro t ht hn
        have he : t = s := by simpa only [Finset.mem_erase, ht, and_true, not_not] using hn
        subst t
        simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [if_neg (Finset.mem_erase.mp ht).1, Option.some.injEq, I.graph.adj_comm]
  exact congrArg₂ PinningData.mk hg hb

namespace PinningFamily
variable [Fintype C] (F : PinningFamily.{u, v} C)

theorem relabel_mem [Fintype V] [Fintype W] {I : PinningData V C}
    (hI : F.contains I) (e : V ≃ W) : F.contains (relabelData I e) := by
  rw [relabelData_eq_restrictPinningData]
  exact F.restrict_mem I _ _ (fun _ => rfl) hI

theorem cut_mem [Fintype V] {I : PinningData V C}
    (hI : F.contains I) (p : V → Prop) : F.contains (Component.restrictData I p) := by
  rw [cutData_eq_restrictPinningData]
  exact F.restrict_mem I _ _ (fun _ => rfl) hI

theorem optionMiddle_mem [Fintype O] {I : PinningData (Option O) C}
    (hI : F.contains I) : F.contains (optionMiddleData I) := by
  rw [optionMiddleData_eq_restrictPinningData]
  exact F.restrict_mem I _ _ (fun _ => rfl) hI

theorem optionChild_mem [Fintype O] {I : PinningData (Option O) C}
    (hI : F.contains I) (a : C) : F.contains (optionChildData I a) := by
  rw [optionChildData_eq_restrictPinningData]
  exact F.restrict_mem I _ _ (fun _ => rfl) hI

theorem exterior_mem [Fintype U] [Fintype S] [Fintype O]
    {I : PinningData (Separator.Vertex U S O) C} (hI : F.contains I) (ξ : S → C) :
    F.contains (exteriorData I ξ) := by
  rw [exteriorData_eq_restrictPinningData]
  exact F.restrict_mem I _ _ (fun _ => rfl) hI

theorem unpinnedExterior_mem [Fintype U] [Fintype S] [Fintype O]
    {I : PinningData (Separator.Vertex U S O) C} (hI : F.contains I) (ξ : S → C) (s : S) :
    F.contains (unpinnedExteriorData I ξ s) := by
  rw [unpinnedExteriorData_eq_restrictPinningData]
  apply F.restrict_mem I _ _ _ hI
  intro w
  cases w with
  | none => simp only [unpinShellEmbedding_none, exceptShellPinning,
      Sum.elim_inr, Sum.elim_inl, if_true]
  | some o => rfl

end PinningFamily
end
end CI2ZF.Potts
