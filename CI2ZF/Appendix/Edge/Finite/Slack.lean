import CI2ZF.Appendix.Edge.Finite.Pinning

/-! The activity-minus-neighbour slack is inherited by every deletion and
compatible pinning, with the endpoint fibre loss charged exactly once. -/
namespace CI2ZF.Appendix.Edge.FiniteSystem
open PottsCI Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L]

lemma adjacent_comm (I : FiniteSystem V E A L) (e f : E) :
    I.Adjacent e f ↔ I.Adjacent f e := by
  constructor <;> rintro ⟨v, hve, hvf⟩ <;> exact ⟨v, hvf, hve⟩

lemma compatible_pin_shared (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a : A) (f : {f : E // f ≠ e}) (v : V)
    (hve : v ∈ I.endpoints e) (hvf : v ∈ I.endpoints f.val) (b : A) :
    (I.remove e).Compatible (I.pinBoundary B e a) f b ↔
      I.Compatible B f.val b ∧ I.label f.val v b ≠ I.label e v a := by
  rw [I.compatible_pin_iff]
  constructor
  · exact fun h => ⟨h.1, h.2 v hve hvf⟩
  · rintro ⟨hc, hb⟩
    refine ⟨hc, fun w hwe hwf => ?_⟩
    have hw : w = v := by
      by_contra hne
      exact f.property (I.linear e f.val w v hwe hwf hve hvf hne).symm
    simpa only [hw] using hb

/-- Pinning one edge removes at most one fibre of activity at every adjacent
edge, and removes no activity at a nonadjacent edge. -/
theorem compatibleMass_pin_lower (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a : A) (f : {f : E // f ≠ e}) (hfibre : I.FibreBound) :
    I.compatibleMass B f.val - (if I.Adjacent f.val e then 1 else 0) ≤
      (I.remove e).compatibleMass (I.pinBoundary B e a) f := by
  by_cases hadj : I.Adjacent f.val e
  · obtain ⟨v, hvf, hve⟩ := hadj
    have hpoint (b : A) : (if I.Compatible B f.val b then I.activity f.val b else 0) ≤
        (if (I.remove e).Compatible (I.pinBoundary B e a) f b then I.activity f.val b else 0) +
          (if I.label f.val v b = I.label e v a then I.activity f.val b else 0) := by
      rw [I.compatible_pin_shared B e a f v hve hvf b]
      by_cases hc : I.Compatible B f.val b <;>
        by_cases heq : I.label f.val v b = I.label e v a <;> simp [hc, heq, I.activity_nonneg]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hpoint b)
    rw [Finset.sum_add_distrib] at hs
    have hb := hfibre f.val v hvf (I.label e v a)
    change I.compatibleMass B f.val ≤
      (I.remove e).compatibleMass (I.pinBoundary B e a) f + _ at hs
    have ha : I.Adjacent f.val e := ⟨v, hvf, hve⟩
    rw [if_pos ha]
    linarith
  · have heq (b : A) : (I.remove e).Compatible (I.pinBoundary B e a) f b ↔
        I.Compatible B f.val b := by
      rw [I.compatible_pin_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, fun v hve hvf => (hadj ⟨v, hvf, hve⟩).elim⟩⟩
    rw [if_neg hadj, sub_zero]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro b _
    change (if I.Compatible B f.val b then I.activity f.val b else 0) =
      (if (I.remove e).Compatible (I.pinBoundary B e a) f b then I.activity f.val b else 0)
    rw [heq]

/-- The weighted slack used by the recursive coupling is preserved under
an arbitrary pinned edge state. -/
theorem pin_slack (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a : A) (f : {f : E // f ≠ e}) (hfibre : I.FibreBound) :
    I.compatibleMass B f.val - I.edgeDegree f.val ≤
      (I.remove e).compatibleMass (I.pinBoundary B e a) f - (I.remove e).edgeDegree f := by
  have hm := I.compatibleMass_pin_lower B e a f hfibre
  have hd := I.remove_degree e f
  have hd' := congrArg (fun n : ℕ => (n : ℝ)) hd
  push_cast at hd'
  by_cases ha : I.Adjacent f.val e
  · simp only [ha, if_true] at hm hd'
    linarith
  · simp only [ha, if_false] at hm hd'
    linarith

lemma Bounds.pin (I : FiniteSystem V E A L) (B : Boundary V L) {Δ : ℕ}
    (h : I.Bounds B Δ) (e : E) (a : A) :
    (I.remove e).Bounds (I.pinBoundary B e a) Δ := by
  refine ⟨I.pin_load_le B e a h.1, I.remove_fibreBound e h.2.1, fun f => ?_⟩
  exact (h.2.2 f.val).trans (I.pin_slack B e a f h.2.1)

end
end CI2ZF.Appendix.Edge.FiniteSystem
