import CI2ZF.Potts.Geometry.AmbientRealization
import CI2ZF.Potts.Model.PinningFamily
import CI2ZF.Potts.Transfer.FamilyCouplingInputs

/-! The original graph-class coupling hypothesis and its ambient
realization family. Membership is closed under induced pullbacks,
including isomorphic relabeling; adding new leaves is not assumed. -/
namespace CI2ZF.Potts
open PottsCI PottsCI.FinDist
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 3000) graphClassInputsDecEq (T : Type*) : DecidableEq T :=
  Classical.decEq T
universe u v

structure GraphClass where
  contains : {A : Type u} → [Fintype A] → SimpleGraph A → Prop
  comap_mem : ∀ {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (e : B ↪ A), contains G → contains (G.comap e)

def GraphClassRootCouplingBound (F : GraphClass.{u}) (C : Type v) [Fintype C]
    (x : PinningData.NonnegativeParameter) (cost : ℝ) : Prop :=
  ∀ {A : Type u} [Fintype A] (G : SimpleGraph A), F.contains G →
    ∀ (tau : PartialColouring A C) (r : tau.FreeVertex) (a b : C)
      (ha : 0 < (rootChildData tau G r a).partition x)
      (hb : 0 < (rootChildData tau G r b).partition x),
      W ham ((rootChildData tau G r a).gibbs x x.property ha)
        ((rootChildData tau G r b).gibbs x x.property hb) ≤ cost

structure GraphClassTransferInputs (F : GraphClass.{u}) (C : Type v) [Fintype C] : Prop where
  hard : ∃ cost : ℝ, GraphClassRootCouplingBound F C PinningData.hardParameter cost
  positive : ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∃ cost : ℝ,
    ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ∈ Set.Icc delta 1 →
      GraphClassRootCouplingBound F C x cost

namespace GraphClass

def pinningFamily (F : GraphClass.{u}) (C : Type v) [Fintype C] : PinningFamily.{u, v} C where
  contains {V} _ I := ∃ (A : Type u) (hA : Fintype A),
    let : Fintype A := hA
    ∃ G : SimpleGraph A, F.contains G ∧ Nonempty (AmbientRealization I G)
  restrict_mem := by
    intro V W _ _ I e p hp hI
    obtain ⟨A, hA, G, hG, ⟨R⟩⟩ := hI
    let : Fintype A := hA
    exact ⟨A, hA, G, hG, ⟨R.restrictPinning e p hp⟩⟩

theorem original_pinning_mem (F : GraphClass.{u}) (C : Type v) [Fintype C]
    {A : Type u} [Fintype A] (G : SimpleGraph A) (hG : F.contains G)
    (tau : PartialColouring A C) : (F.pinningFamily C).contains (tau.toPinningData G) :=
  ⟨A, inferInstance, G, hG, ⟨AmbientRealization.ofPartialColouring tau G⟩⟩

theorem activeGraph_mem (F : GraphClass.{u}) {C : Type v} [Fintype C]
    {V A : Type u} [Fintype V] [Fintype A] {I : PinningData V C}
    {G : SimpleGraph A} (hG : F.contains G) (R : AmbientRealization I G) :
    F.contains R.activeGraph := F.comap_mem G (Function.Embedding.subtype _) hG

end GraphClass
end
end CI2ZF.Potts
