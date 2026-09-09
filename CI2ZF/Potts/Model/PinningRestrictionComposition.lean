import CI2ZF.Potts.Model.PinningRestriction

/-! Two genuine restrictions compose. Old pinned occurrences and newly
pinned free vertices have disjoint support, so no constraint is duplicated. -/
namespace CI2ZF.Potts
open PottsCI Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
variable {V W T : Type u} {C : Type v} [Fintype V] [Fintype W]

theorem sum_composePinning_none (e : W ↪ V) (q : W → Option C)
    (g : V → Option C → ℕ) (hg : ∀ v, g v none = 0) :
    (∑ v : V, g v (composePinning e (fun _ => none) q v)) = ∑ w : W, g (e w) (q w) := by
  symm
  apply Finset.sum_of_injOn e e.injective.injOn (by intro w _; exact mem_univ _)
  · intro v _ hv
    have hn : v ∉ Set.range e := by
      rintro ⟨w, rfl⟩
      exact hv ⟨w, mem_univ _, rfl⟩
    rw [composePinning_of_not_mem_range e _ q v hn]
    exact hg v
  · intro w _
    rw [composePinning_apply]

/-- Additive decomposition of the actual old and new pinned contributions. -/
theorem sum_composePinning (e : W ↪ V) (p : V → Option C) (q : W → Option C)
    (hp : ∀ w, p (e w) = none) (g : V → Option C → ℕ) (hg : ∀ v, g v none = 0) :
    (∑ v : V, g v (composePinning e p q v)) =
      (∑ v : V, g v (p v)) + ∑ w : W, g (e w) (q w) := by
  have he (v : V) : g v (composePinning e p q v) =
      g v (p v) + g v (composePinning e (fun _ => none) q v) := by
    by_cases hv : v ∈ Set.range e
    · obtain ⟨w, rfl⟩ := hv
      rw [composePinning_apply, composePinning_apply, hp, hg, zero_add]
    · rw [composePinning_of_not_mem_range e p q v hv,
        composePinning_of_not_mem_range e _ q v hv, hg, add_zero]
  simp_rw [he]
  rw [Finset.sum_add_distrib, sum_composePinning_none e q g hg]

/-- Restriction composition as equality of the actual graph and every
boundary count. Only the earlier pinning must vanish on the former free
vertices; no proper-colouring premise is required. -/
theorem restrictPinningData_restrict (I : PinningData V C)
    (e : W ↪ V) (p : V → Option C) (f : T ↪ W) (q : W → Option C)
    (hp : ∀ w, p (e w) = none) :
    restrictPinningData (restrictPinningData I e p) f q =
      restrictPinningData I (f.trans e) (composePinning e p q) := by
  have hg : (restrictPinningData (restrictPinningData I e p) f q).graph =
      (restrictPinningData I (f.trans e) (composePinning e p q)).graph := rfl
  have hb : (restrictPinningData (restrictPinningData I e p) f q).boundaryCount =
      (restrictPinningData I (f.trans e) (composePinning e p q)).boundaryCount := by
    funext t c
    simp only [restrictPinningData_count]
    have hs := sum_composePinning e p q hp
      (fun v a => if I.graph.Adj (e (f t)) v ∧ a = some c then 1 else 0)
      (by intro v; simp)
    change (I.boundaryCount (e (f t)) c +
      (∑ v : V, if I.graph.Adj (e (f t)) v ∧ p v = some c then 1 else 0)) +
      (∑ w : W, if I.graph.Adj (e (f t)) (e w) ∧ q w = some c then 1 else 0) =
      I.boundaryCount (e (f t)) c +
      ∑ v : V, if I.graph.Adj (e (f t)) v ∧ composePinning e p q v = some c then 1 else 0
    rw [hs, Nat.add_assoc]
  exact congrArg₂ PinningData.mk hg hb

end
end CI2ZF.Potts
