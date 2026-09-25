import ZeroFreeness.Coupling.Edge.Finite.Model
import Mathlib.Logic.Equiv.Prod

/-! Exact deletion and pinning for the finite weighted slot system. -/
namespace ZeroFreeness.Appendix.Edge.FiniteSystem
open PottsCI Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L]

def remove (I : FiniteSystem V E A L) (e : E) : FiniteSystem V {f : E // f ≠ e} A L where
  endpoints f := I.endpoints f.val
  endpoints_card f := I.endpoints_card f.val
  linear f g v w hvf hvg hwf hwg hvw :=
    Subtype.ext (I.linear f.val g.val v w hvf hvg hwf hwg hvw)
  label f := I.label f.val
  activity f := I.activity f.val
  activity_nonneg f := I.activity_nonneg f.val

def pinBoundary (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (a : A) : Boundary V L :=
  fun v => if v ∈ I.endpoints e then insert (I.label e v a) (B v) else B v

def joinConfig (e : E) (a : A) (τ : {f : E // f ≠ e} → A) : E → A :=
  (Equiv.funSplitAt e A).symm (a, τ)

@[simp] lemma joinConfig_self (e : E) (a : A) (τ : {f : E // f ≠ e} → A) :
    joinConfig e a τ e = a := by simp [joinConfig, Equiv.funSplitAt, Equiv.piSplitAt]

@[simp] lemma joinConfig_other (e : E) (a : A) (τ : {f : E // f ≠ e} → A)
    (f : {f : E // f ≠ e}) : joinConfig e a τ f.val = τ f := by
  simp [joinConfig, Equiv.funSplitAt, Equiv.piSplitAt, f.property]

lemma compatible_pin_iff (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (a : A)
    (f : {f : E // f ≠ e}) (b : A) :
    (I.remove e).Compatible (I.pinBoundary B e a) f b ↔
      I.Compatible B f.val b ∧ ∀ v, v ∈ I.endpoints e → v ∈ I.endpoints f.val →
        I.label f.val v b ≠ I.label e v a := by
  simp only [Compatible, remove, pinBoundary]
  constructor
  · intro h
    constructor
    · intro v hv
      by_cases he : v ∈ I.endpoints e
      · exact (show I.label f.val v b ≠ I.label e v a ∧ I.label f.val v b ∉ B v from by simpa [he] using h v hv).2
      · simpa [he] using h v hv
    · intro v he hf
      exact (show I.label f.val v b ≠ I.label e v a ∧ I.label f.val v b ∉ B v from by simpa [he] using h v hf).1
  · rintro ⟨hc, hx⟩ v hv
    by_cases he : v ∈ I.endpoints e
    · simpa [he] using And.intro (hx v he hv) (hc v hv)
    · simpa [he] using hc v hv

/-- A full configuration is admissible exactly when its exposed edge is
boundary-compatible and its restriction obeys the resulting pinned boundary. -/
theorem admissible_join_iff (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a : A) (τ : {f : E // f ≠ e} → A) :
    I.Admissible B (joinConfig e a τ) ↔ I.Compatible B e a ∧
      (I.remove e).Admissible (I.pinBoundary B e a) τ := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨by simpa using hc e, ?_, ?_⟩
    · intro f
      rw [I.compatible_pin_iff]
      refine ⟨by simpa using hc f.val, ?_⟩
      intro v he hf
      simpa using hp f.val e f.property v hf he
    · intro f g hfg v hvf hvg
      have hne : f.val ≠ g.val := fun h => hfg (Subtype.ext h)
      simpa [remove] using hp f.val g.val hne v hvf hvg
  · rintro ⟨hc, hr, hp⟩
    constructor
    · intro f
      by_cases hfe : f = e
      · subst f; simpa using hc
      · let ff : {f : E // f ≠ e} := ⟨f, hfe⟩
        have h := ((I.compatible_pin_iff B e a ff (τ ff)).mp (hr ff)).1
        simpa [joinConfig, Equiv.funSplitAt, Equiv.piSplitAt, hfe, ff] using h
    · intro f g hfg v hvf hvg
      by_cases hfe : f = e
      · subst f
        let gg : {f : E // f ≠ e} := ⟨g, hfg.symm⟩
        have h := ((I.compatible_pin_iff B e a gg (τ gg)).mp (hr gg)).2 v hvf hvg
        simpa [joinConfig, Equiv.funSplitAt, Equiv.piSplitAt, hfg.symm, gg] using Ne.symm h
      · by_cases hge : g = e
        · subst g
          let ff : {f : E // f ≠ e} := ⟨f, hfe⟩
          have h := ((I.compatible_pin_iff B e a ff (τ ff)).mp (hr ff)).2 v hvg hvf
          simpa [joinConfig, Equiv.funSplitAt, Equiv.piSplitAt, hfe, ff] using h
        · let ff : {f : E // f ≠ e} := ⟨f, hfe⟩
          let gg : {f : E // f ≠ e} := ⟨g, hge⟩
          have hne : ff ≠ gg := fun h => hfg (congrArg Subtype.val h)
          simpa [joinConfig, Equiv.funSplitAt, Equiv.piSplitAt, hfe, hge, ff, gg, remove] using hp ff gg hne v hvf hvg

lemma product_split (e : E) (f : E → ℝ) :
    (∏ j, f j) = f e * ∏ j : {j : E // j ≠ e}, f j.val := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ e)]
  congr 1
  exact Finset.prod_subtype (Finset.univ.erase e) (by simp) f

/-- Exact factorization of the unnormalized Gibbs weight under pinning. -/
theorem configurationWeight_join (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a : A) (τ : {f : E // f ≠ e} → A) :
    I.configurationWeight B (joinConfig e a τ) =
      (if I.Compatible B e a then I.activity e a else 0) *
        (I.remove e).configurationWeight (I.pinBoundary B e a) τ := by
  simp only [configurationWeight, I.admissible_join_iff]
  by_cases hc : I.Compatible B e a <;>
    by_cases hr : (I.remove e).Admissible (I.pinBoundary B e a) τ <;>
    simp only [hc, hr, and_self, and_false, and_true, if_true, if_false,
      mul_zero, zero_mul]
  rw [product_split e]
  simp [remove]

/-- Summing the exact split over the remaining edges gives the exposed-edge
partition function, including states with zero activity. -/
theorem partition_split (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) :
    I.partition B = ∑ a, (if I.Compatible B e a then I.activity e a else 0) *
      (I.remove e).partition (I.pinBoundary B e a) := by
  unfold partition
  rw [← Fintype.sum_equiv (Equiv.funSplitAt e A).symm
    (fun p => I.configurationWeight B (joinConfig e p.1 p.2))
    (I.configurationWeight B) (fun p => rfl)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [I.configurationWeight_join]
  exact (Finset.mul_sum _ _ _).symm

lemma remove_fibreBound (I : FiniteSystem V E A L) (e : E) (h : I.FibreBound) :
    (I.remove e).FibreBound := fun f v hv l => h f.val v hv l

private lemma card_subtype_remove (s : Finset E) (e : E) :
    (s.subtype (fun f => f ≠ e)).card + (if e ∈ s then 1 else 0) = s.card := by
  rw [Finset.card_subtype]
  have hf : s.filter (fun f => f ≠ e) = s.erase e := by ext f; simp [and_comm]
  rw [hf]
  by_cases he : e ∈ s
  · simpa only [if_pos he] using Finset.card_erase_add_one he
  · simp [he]

lemma remove_incident_card (I : FiniteSystem V E A L) (e : E) (v : V) :
    ((I.remove e).incident v).card + (if v ∈ I.endpoints e then 1 else 0) =
      (I.incident v).card := by
  have hs : (I.remove e).incident v = (I.incident v).subtype (fun f => f ≠ e) := by
    ext f
    constructor
    · intro hf
      apply Finset.mem_subtype.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hf).2⟩
    · intro hf
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp (Finset.mem_subtype.mp hf)).2⟩
  rw [hs]
  have hh := card_subtype_remove (I.incident v) e
  have hi : e ∈ I.incident v ↔ v ∈ I.endpoints e := Finset.mem_filter_univ _
  simpa only [hi] using hh

lemma remove_degree (I : FiniteSystem V E A L) (e : E) (f : {f : E // f ≠ e}) :
    (I.remove e).edgeDegree f + (if I.Adjacent f.val e then 1 else 0) = I.edgeDegree f.val := by
  have hs : (I.remove e).neighbours f = (I.neighbours f.val).subtype (fun g => g ≠ e) := by
    ext g
    constructor
    · intro hg
      have h := (Finset.mem_filter.mp hg).2
      apply Finset.mem_subtype.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => h.1 (Subtype.ext heq), h.2⟩
    · intro hg
      have h := (Finset.mem_filter.mp (Finset.mem_subtype.mp hg)).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun heq => h.1 (congrArg Subtype.val heq), h.2⟩
  unfold edgeDegree
  rw [hs]
  have hh := card_subtype_remove (I.neighbours f.val) e
  have hi : e ∈ I.neighbours f.val ↔ I.Adjacent f.val e := by
    exact ⟨fun h => (Finset.mem_filter.mp h).2.2,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Ne.symm f.property, h⟩⟩
  simpa only [hi] using hh

lemma pin_load_le (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (a : A)
    {Δ : ℕ} (hload : ∀ v, (I.incident v).card + (B v).card ≤ Δ) :
    ∀ v, ((I.remove e).incident v).card + (I.pinBoundary B e a v).card ≤ Δ := by
  intro v
  have hc := I.remove_incident_card e v
  by_cases hv : v ∈ I.endpoints e
  · simp only [hv, if_true] at hc
    have hb := Finset.card_insert_le (I.label e v a) (B v)
    simp only [pinBoundary, hv, if_true]
    calc
      _ ≤ ((I.remove e).incident v).card + ((B v).card + 1) := Nat.add_le_add_left hb _
      _ = (I.incident v).card + (B v).card := by rw [← Nat.add_assoc, Nat.add_right_comm, hc]
      _ ≤ Δ := hload v
  · simp only [hv, if_false, Nat.add_zero] at hc
    simpa only [pinBoundary, hv, if_false, hc] using hload v

end
end ZeroFreeness.Appendix.Edge.FiniteSystem
