import CI2ZF.Potts.Model.Real.Model
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-! Restrict the free vertices and add new pinned neighbours while retaining
all old boundary counts. Uncoloured omitted vertices are simply deleted. -/
namespace CI2ZF.Potts
open PottsCI
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
variable {V W T : Type u} {C : Type v}

def restrictPinningData [Fintype V] (I : PinningData V C)
    (e : W ↪ V) (p : V → Option C) : PinningData W C where
  graph := I.graph.comap e
  boundaryCount w c := I.boundaryCount (e w) c +
    ∑ v : V, if I.graph.Adj (e w) v ∧ p v = some c then 1 else 0

@[simp] theorem restrictPinningData_graph [Fintype V]
    (I : PinningData V C) (e : W ↪ V) (p : V → Option C) :
    (restrictPinningData I e p).graph = I.graph.comap e := rfl

@[simp] theorem restrictPinningData_count [Fintype V]
    (I : PinningData V C) (e : W ↪ V) (p : V → Option C) (w : W) (c : C) :
    (restrictPinningData I e p).boundaryCount w c = I.boundaryCount (e w) c +
      ∑ v : V, if I.graph.Adj (e w) v ∧ p v = some c then 1 else 0 := rfl

/-- Preserve the earlier pinning outside the former free set, and add the
new pinning on that set. -/
def composePinning (e : W ↪ V) (p : V → Option C) (q : W → Option C) : V → Option C :=
  Function.extend e q p

@[simp] theorem composePinning_apply (e : W ↪ V) (p : V → Option C)
    (q : W → Option C) (w : W) : composePinning e p q (e w) = q w :=
  e.injective.extend_apply q p w

theorem composePinning_of_not_mem_range (e : W ↪ V) (p : V → Option C)
    (q : W → Option C) (v : V) (hv : v ∉ Set.range e) : composePinning e p q v = p v :=
  Function.extend_apply' q p v hv

theorem composePinning_free (e : W ↪ V) (f : T ↪ W) (p : V → Option C)
    (q : W → Option C) (hq : ∀ t, q (f t) = none) :
    ∀ t, composePinning e p q ((f.trans e) t) = none := by
  intro t
  exact (composePinning_apply e p q (f t)).trans (hq t)

end
end CI2ZF.Potts
