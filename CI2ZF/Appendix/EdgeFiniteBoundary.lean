import CI2ZF.Appendix.EdgeFiniteGibbs

/-! Single occupied-label additions, avoidance events, and the mixed
endpoint boundaries used by the unmatched exposure coupling. -/
namespace CI2ZF.Appendix.Edge.FiniteSystem
open PottsCI PottsCI.FinDist Finset FiniteLaw
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq A := Classical.decEq A
local instance (priority := 2000) : DecidableEq L := Classical.decEq L

def addBoundary (B : Boundary V L) (v : V) (l : L) : Boundary V L :=
  Function.update B v (insert l (B v))

@[simp] lemma addBoundary_self (B : Boundary V L) (v : V) (l : L) :
    addBoundary B v l v = insert l (B v) := Function.update_self _ _ _

lemma addBoundary_other (B : Boundary V L) (v w : V) (l : L) (h : w ≠ v) :
    addBoundary B v l w = B w := Function.update_of_ne h _ _

lemma addBoundary_comm (B : Boundary V L) (v : V) (l r : L) :
    addBoundary (addBoundary B v l) v r = addBoundary (addBoundary B v r) v l := by
  ext w
  by_cases hw : w = v
  · subst w; simp [Finset.insert_comm]
  · simp only [addBoundary_other B v w l hw, addBoundary_other B v w r hw,
      addBoundary_other _ v w r hw, addBoundary_other _ v w l hw]

lemma compatible_add_iff (I : FiniteSystem V E A L) (B : Boundary V L)
    (v : V) (l : L) (e : E) (a : A) :
    I.Compatible (addBoundary B v l) e a ↔ I.Compatible B e a ∧
      (v ∈ I.endpoints e → I.label e v a ≠ l) := by
  constructor
  · intro h
    constructor
    · intro w hw
      by_cases hwv : w = v
      · subst w
        have hh := h v hw
        rw [addBoundary_self] at hh
        exact fun hm => hh (Finset.mem_insert_of_mem hm)
      · simpa only [addBoundary_other B v w l hwv] using h w hw
    · intro hv heq
      have hh := h v hv
      rw [addBoundary_self] at hh
      exact hh (Finset.mem_insert.mpr (Or.inl heq))
  · rintro ⟨hc, hl⟩ w hw
    by_cases hwv : w = v
    · subst w
      rw [addBoundary_self]
      intro hh
      exact (Finset.mem_insert.mp hh).elim (hl hw) (hc v hw)
    · simpa only [addBoundary_other B v w l hwv] using hc w hw

def Avoids (I : FiniteSystem V E A L) (v : V) (l : L) (σ : E → A) : Prop :=
  ∀ e, v ∈ I.endpoints e → I.label e v (σ e) ≠ l

lemma admissible_add_iff (I : FiniteSystem V E A L) (B : Boundary V L)
    (v : V) (l : L) (σ : E → A) :
    I.Admissible (addBoundary B v l) σ ↔ I.Admissible B σ ∧ I.Avoids v l σ := by
  simp only [Admissible, I.compatible_add_iff, Avoids, forall_and]
  tauto

lemma configurationWeight_add (I : FiniteSystem V E A L) (B : Boundary V L)
    (v : V) (l : L) (σ : E → A) :
    I.configurationWeight (addBoundary B v l) σ =
      if I.Avoids v l σ then I.configurationWeight B σ else 0 := by
  simp only [configurationWeight, I.admissible_add_iff]
  by_cases ha : I.Admissible B σ <;> by_cases hv : I.Avoids v l σ <;> simp [ha, hv]

lemma compatibleMass_add_lower (I : FiniteSystem V E A L) (B : Boundary V L)
    (v : V) (l : L) (e : E) (hf : I.FibreBound) :
    I.compatibleMass B e - 1 ≤ I.compatibleMass (addBoundary B v l) e := by
  by_cases hv : v ∈ I.endpoints e
  · have hpoint (a : A) : (if I.Compatible B e a then I.activity e a else 0) ≤
        (if I.Compatible (addBoundary B v l) e a then I.activity e a else 0) +
          (if I.label e v a = l then I.activity e a else 0) := by
      rw [I.compatible_add_iff]
      by_cases hc : I.Compatible B e a <;> by_cases hl : I.label e v a = l <;>
        simp [hc, hl, hv, I.activity_nonneg]
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
    rw [Finset.sum_add_distrib] at hs
    have hh := hf e v hv l
    change I.compatibleMass B e ≤ I.compatibleMass (addBoundary B v l) e + _ at hs
    linarith
  · have heq : I.compatibleMass (addBoundary B v l) e = I.compatibleMass B e := by
      apply Finset.sum_congr rfl
      intro a _
      rw [I.compatible_add_iff]
      simp only [hv, false_implies, and_true]
    rw [heq]
    linarith

lemma Bounds.add_partition_pos (I : FiniteSystem V E A L) (B : Boundary V L) {Δ : ℕ}
    (h : I.Bounds B Δ) (v : V) (l : L) : 0 < I.partition (addBoundary B v l) := by
  apply I.partition_pos _ h.2.1
  intro e
  have hm := I.compatibleMass_add_lower B v l e h.2.1
  have hs := h.2.2 e
  have hd := Nat.cast_nonneg (α := ℝ) Δ
  linarith

lemma gibbs_avoidance_mass (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) (v : V) (l : L) :
    eventMass (I.gibbs B hZ) (I.Avoids v l) = I.partition (addBoundary B v l) / I.partition B := by
  unfold partition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  rw [I.configurationWeight_add]
  by_cases hs : I.Avoids v l σ <;> simp [gibbs, hs, partition]

/-- The common avoidance law in the exposure table is the Gibbs law with
both occupied endpoint labels inserted. -/
theorem conditional_gibbs_avoidance (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) (v : V) (l : L)
    (hZa : 0 < I.partition (addBoundary B v l)) :
    conditional (I.gibbs B hZ) (I.Avoids v l) = I.gibbs (addBoundary B v l) hZa := by
  have hm := I.gibbs_avoidance_mass B hZ v l
  have hp : 0 < eventMass (I.gibbs B hZ) (I.Avoids v l) := by rw [hm]; exact div_pos hZa hZ
  ext σ
  rw [conditional_w _ _ hp, hm]
  change (if I.Avoids v l σ then I.configurationWeight B σ / I.partition B else 0) /
    (I.partition (addBoundary B v l) / I.partition B) =
      I.configurationWeight (addBoundary B v l) σ / I.partition (addBoundary B v l)
  rw [I.configurationWeight_add]
  by_cases hs : I.Avoids v l σ
  · simp only [if_pos hs]
    exact div_div_div_cancel_right₀ hZ.ne' _ _
  · simp only [if_neg hs, zero_div]

lemma compatible_congr (I : FiniteSystem V E A L) {B D : Boundary V L} (e : E)
    (h : ∀ v ∈ I.endpoints e, B v = D v) (a : A) :
    I.Compatible B e a ↔ I.Compatible D e a := by
  constructor <;> intro ha v hv
  · rw [← h v hv]; exact ha v hv
  · rw [h v hv]; exact ha v hv

/-- After deleting an edge, no remaining edge sees both of its endpoints.
Hence a boundary assembled from two valid conditioned systems retains
all three load/fibre/activity bounds. -/
theorem Bounds.mixed_endpoints (I : FiniteSystem V E A L) (e : E)
    {v w : V} (hv : v ∈ I.endpoints e) (hw : w ∈ I.endpoints e) (hvw : v ≠ w)
    (B D : Boundary V L) (hagree : ∀ z, z ≠ v → z ≠ w → B z = D z) {Δ : ℕ}
    (hB : (I.remove e).Bounds B Δ) (hD : (I.remove e).Bounds D Δ) :
    (I.remove e).Bounds (Function.update D v (B v)) Δ := by
  refine ⟨?_, hB.2.1, ?_⟩
  · intro z
    by_cases hz : z = v
    · subst z; simpa only [Function.update_self] using hB.1 v
    · simpa only [Function.update_of_ne hz] using hD.1 z
  · intro f
    by_cases hvf : v ∈ I.endpoints f.val
    · have hnotw : w ∉ I.endpoints f.val := by
        intro hwf
        exact f.property (I.linear e f.val v w hv hvf hw hwf hvw).symm
      have hm : (I.remove e).compatibleMass (Function.update D v (B v)) f =
          (I.remove e).compatibleMass B f := by
        apply Finset.sum_congr rfl
        intro a _
        have hh : (I.remove e).Compatible (Function.update D v (B v)) f a ↔
            (I.remove e).Compatible B f a := by
          apply (I.remove e).compatible_congr f
          intro z hz
          by_cases hzv : z = v
          · subst z; exact Function.update_self _ _ _
          · rw [Function.update_of_ne hzv]
            have hzw : z ≠ w := by intro heq; exact hnotw (heq ▸ hz)
            exact (hagree z hzv hzw).symm
        rw [hh]
      rw [hm]
      exact hB.2.2 f
    · have hm : (I.remove e).compatibleMass (Function.update D v (B v)) f =
          (I.remove e).compatibleMass D f := by
        apply Finset.sum_congr rfl
        intro a _
        have hh : (I.remove e).Compatible (Function.update D v (B v)) f a ↔
            (I.remove e).Compatible D f a := by
          apply (I.remove e).compatible_congr f
          intro z hz
          have hzv : z ≠ v := by intro heq; exact hvf (heq ▸ hz)
          exact Function.update_of_ne hzv _ _
        rw [hh]
      rw [hm]
      exact hD.2.2 f

end
end CI2ZF.Appendix.Edge.FiniteSystem
