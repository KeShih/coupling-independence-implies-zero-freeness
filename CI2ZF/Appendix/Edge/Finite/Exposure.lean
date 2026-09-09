import CI2ZF.Appendix.Edge.Finite.Boundary

/-! The exposure events form a genuine disjoint partition of the supported
hard-label configurations. -/
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

def Occurs (I : FiniteSystem V E A L) (v : V) (l : L) (j : ↑(I.incident v)) (σ : E → A) : Prop :=
  I.label j.val v (σ j.val) = l

lemma incident_mem (I : FiniteSystem V E A L) (v : V) (j : ↑(I.incident v)) :
    v ∈ I.endpoints j.val := (Finset.mem_filter.mp j.property).2

lemma occurrence_unique (I : FiniteSystem V E A L) (v : V) (l : L) {σ : E → A}
    (hs : I.PairwiseLabels σ) {j k : ↑(I.incident v)}
    (hj : I.Occurs v l j σ) (hk : I.Occurs v l k σ) : j = k := by
  apply Subtype.ext
  by_contra hne
  exact hs j.val k.val hne v (I.incident_mem v j) (I.incident_mem v k) (hj.trans hk.symm)

lemma avoids_iff_no_occurrence (I : FiniteSystem V E A L) (v : V) (l : L) (σ : E → A) :
    I.Avoids v l σ ↔ ∀ j : ↑(I.incident v), ¬I.Occurs v l j σ := by
  constructor
  · intro h j; exact h j.val (I.incident_mem v j)
  · intro h e he
    exact h ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩

lemma gibbs_pos_admissible (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) {σ : E → A} (hs : 0 < (I.gibbs B hZ).w σ) :
    I.Admissible B σ := by
  have hw : 0 < I.configurationWeight B σ := (div_pos_iff_of_pos_right hZ).mp hs
  exact (I.configurationWeight_pos_iff B σ).mp hw |>.1

/-- At most one free edge incident to a vertex uses any given label, so
avoidance and the indexed occurrence events partition the Gibbs law. -/
theorem gibbs_exposure_partition (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) (v : V) (l : L) (σ : E → A) :
    (if I.Avoids v l σ then (I.gibbs B hZ).w σ else 0) +
      (∑ j : ↑(I.incident v), if I.Occurs v l j σ then (I.gibbs B hZ).w σ else 0) =
        (I.gibbs B hZ).w σ := by
  rcases eq_or_lt_of_le ((I.gibbs B hZ).nonneg σ) with hz | hp
  · simp only [← hz, ite_self, Finset.sum_const_zero, add_zero]
  · have hs := I.gibbs_pos_admissible B hZ hp
    by_cases ha : I.Avoids v l σ
    · have hn := (I.avoids_iff_no_occurrence v l σ).mp ha
      simp only [if_pos ha, hn, if_false, Finset.sum_const_zero, add_zero]
    · have hex : ∃ j : ↑(I.incident v), I.Occurs v l j σ := by
        by_contra hh
        apply ha
        rw [I.avoids_iff_no_occurrence]
        exact fun j hj => hh ⟨j, hj⟩
      obtain ⟨j, hj⟩ := hex
      rw [if_neg ha, zero_add]
      have hh : (∑ k : ↑(I.incident v), if I.Occurs v l k σ then (I.gibbs B hZ).w σ else 0) =
          (if I.Occurs v l j σ then (I.gibbs B hZ).w σ else 0) := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          have hk : ¬I.Occurs v l k σ := fun hk => hkj (I.occurrence_unique v l hs.2 hk hj)
          exact if_neg hk
        · simp
      rw [hh, if_pos hj]

lemma occurrence_index_card (I : FiniteSystem V E A L) (B : Boundary V L)
    (v : V) (l : L) {Δ : ℕ} (h : I.Bounds (addBoundary B v l) Δ) :
    (Fintype.card ↑(I.incident v) : ℝ) ≤ (Δ : ℝ) - 1 := by
  have hs := h.1 v
  rw [addBoundary_self] at hs
  have hc : 1 ≤ (insert l (B v)).card := Finset.one_le_card.mpr ⟨l, Finset.mem_insert_self _ _⟩
  have hh : (I.incident v).card + 1 ≤ Δ :=
    (Nat.add_le_add_left hc _).trans hs
  have hr : ((I.incident v).card : ℝ) + 1 ≤ (Δ : ℝ) := by exact_mod_cast hh
  simpa only [Fintype.card_coe] using (le_sub_iff_add_le.mpr hr)

lemma admissible_join_unpinned_iff (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a b : A) (τ : {f : E // f ≠ e} → A) :
    I.Admissible B (joinConfig e a τ) ↔
      (I.remove e).Admissible B τ ∧ I.GoodAt B e (joinConfig e b τ) a := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro f
      change I.Compatible B f.val (τ f)
      simpa only [joinConfig_other] using hc f.val
    · intro f g hfg z hzf hzg
      have hne : f.val ≠ g.val := fun hh => hfg (Subtype.ext hh)
      simpa [remove] using hp f.val g.val hne z hzf hzg
    · simpa using hc e
    · intro f
      let ff : {f : E // f ≠ e} := ⟨f.val, I.neighbour_ne e f⟩
      have hf := hp e f.val (Ne.symm ff.property) (I.sharedVertex e f)
        (I.sharedVertex_left e f) (I.sharedVertex_right e f)
      rw [joinConfig_self] at hf
      change I.label e (I.sharedVertex e f) a ≠
        I.label ff.val (I.sharedVertex e f) (joinConfig e b τ ff.val)
      rw [joinConfig_other]
      change I.label e (I.sharedVertex e f) a ≠
        I.label ff.val (I.sharedVertex e f) (joinConfig e a τ ff.val) at hf
      rw [joinConfig_other] at hf
      exact hf
  · rintro ⟨hr, hg⟩
    rw [I.admissible_join_iff]
    refine ⟨hg.1, ?_, hr.2⟩
    intro f
    rw [I.compatible_pin_iff]
    refine ⟨hr.1 f, fun z hze hzf => ?_⟩
    have hh := I.goodAt_pair hg f.val (Ne.symm f.property) z hze hzf
    rw [joinConfig_other] at hh
    exact Ne.symm hh

/-- A second exact split exposes the local greedy-availability factor. -/
lemma configurationWeight_join_available (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a b : A) (τ : {f : E // f ≠ e} → A) :
    I.configurationWeight B (joinConfig e a τ) =
      (if I.GoodAt B e (joinConfig e b τ) a then I.activity e a else 0) *
        (I.remove e).configurationWeight B τ := by
  simp only [configurationWeight, I.admissible_join_unpinned_iff B e a b τ]
  by_cases hr : (I.remove e).Admissible B τ <;>
    by_cases hg : I.GoodAt B e (joinConfig e b τ) a <;> simp only [hr, hg, and_true, and_false,
      if_true, if_false, mul_zero, zero_mul]
  rw [product_split e]
  simp [remove]

end
end CI2ZF.Appendix.Edge.FiniteSystem
