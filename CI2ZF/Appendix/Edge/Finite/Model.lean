import CI2ZF.FiniteCoupling
import Mathlib.Data.Finset.Card

/-! Finite weighted endpoint-label systems underlying the slot lift.
Edges have two distinct endpoints, and two distinct edges share at most
one endpoint. All Gibbs weights below use the actual distinct-label constraint.
-/
namespace CI2ZF.Appendix.Edge
open PottsCI Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option linter.unusedSectionVars false

structure FiniteSystem (V E A L : Type*) where
  endpoints : E → Finset V
  endpoints_card : ∀ e, (endpoints e).card = 2
  linear : ∀ e f v w, v ∈ endpoints e → v ∈ endpoints f →
    w ∈ endpoints e → w ∈ endpoints f → v ≠ w → e = f
  label : E → V → A → L
  activity : E → A → ℝ
  activity_nonneg : ∀ e a, 0 ≤ activity e a

namespace FiniteSystem
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L]

abbrev Boundary (V L : Type*) := V → Finset L

def Adjacent (I : FiniteSystem V E A L) (e f : E) : Prop :=
  ∃ v, v ∈ I.endpoints e ∧ v ∈ I.endpoints f

def neighbours (I : FiniteSystem V E A L) (e : E) : Finset E :=
  univ.filter fun f => f ≠ e ∧ I.Adjacent e f

def edgeDegree (I : FiniteSystem V E A L) (e : E) : ℕ := (I.neighbours e).card

def incident (I : FiniteSystem V E A L) (v : V) : Finset E :=
  univ.filter fun e => v ∈ I.endpoints e

def Compatible (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (a : A) : Prop :=
  ∀ v ∈ I.endpoints e, I.label e v a ∉ B v

def PairwiseLabels (I : FiniteSystem V E A L) (σ : E → A) : Prop :=
  ∀ e f, e ≠ f → ∀ v, v ∈ I.endpoints e → v ∈ I.endpoints f →
    I.label e v (σ e) ≠ I.label f v (σ f)

def Admissible (I : FiniteSystem V E A L) (B : Boundary V L) (σ : E → A) : Prop :=
  (∀ e, I.Compatible B e (σ e)) ∧ I.PairwiseLabels σ

def configurationWeight (I : FiniteSystem V E A L) (B : Boundary V L) (σ : E → A) : ℝ :=
  if I.Admissible B σ then ∏ e, I.activity e (σ e) else 0

def partition (I : FiniteSystem V E A L) (B : Boundary V L) : ℝ :=
  ∑ σ : E → A, I.configurationWeight B σ

lemma configurationWeight_nonneg (I : FiniteSystem V E A L) (B : Boundary V L) (σ : E → A) :
    0 ≤ I.configurationWeight B σ := by
  unfold configurationWeight
  split_ifs
  · exact Finset.prod_nonneg fun e _ => I.activity_nonneg e (σ e)
  · rfl

lemma partition_nonneg (I : FiniteSystem V E A L) (B : Boundary V L) : 0 ≤ I.partition B :=
  Finset.sum_nonneg fun σ _ => I.configurationWeight_nonneg B σ

def gibbs (I : FiniteSystem V E A L) (B : Boundary V L) (hZ : 0 < I.partition B) :
    FinDist (E → A) where
  w σ := I.configurationWeight B σ / I.partition B
  nonneg σ := div_nonneg (I.configurationWeight_nonneg B σ) hZ.le
  sum_one := by rw [← Finset.sum_div]; exact div_self hZ.ne'

lemma configurationWeight_pos_iff (I : FiniteSystem V E A L) (B : Boundary V L) (σ : E → A) :
    0 < I.configurationWeight B σ ↔ I.Admissible B σ ∧ ∀ e, 0 < I.activity e (σ e) := by
  by_cases h : I.Admissible B σ
  · simp only [configurationWeight, h, if_true, true_and]
    constructor
    · intro hp e
      have hn : I.activity e (σ e) ≠ 0 := (Finset.prod_ne_zero_iff.mp hp.ne') e (Finset.mem_univ e)
      exact lt_of_le_of_ne (I.activity_nonneg e (σ e)) hn.symm
    · intro hp
      exact Finset.prod_pos fun e _ => hp e
  · simp [configurationWeight, h]

def compatibleMass (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) : ℝ :=
  ∑ a, if I.Compatible B e a then I.activity e a else 0

def FibreBound (I : FiniteSystem V E A L) : Prop :=
  ∀ e v, v ∈ I.endpoints e → ∀ l : L,
    (∑ a, if I.label e v a = l then I.activity e a else 0) ≤ 1

def Bounds (I : FiniteSystem V E A L) (B : Boundary V L) (Δ : ℕ) : Prop :=
  (∀ v, (I.incident v).card + (B v).card ≤ Δ) ∧ I.FibreBound ∧
    ∀ e, (Δ : ℝ) + 2 ≤ I.compatibleMass B e - I.edgeDegree e

lemma neighbour_ne (I : FiniteSystem V E A L) (e : E) (f : ↑(I.neighbours e)) : f.val ≠ e :=
  (Finset.mem_filter.mp f.property).2.1

lemma neighbour_adjacent (I : FiniteSystem V E A L) (e : E) (f : ↑(I.neighbours e)) : I.Adjacent e f.val :=
  (Finset.mem_filter.mp f.property).2.2

def sharedVertex (I : FiniteSystem V E A L) (e : E) (f : ↑(I.neighbours e)) : V :=
  (I.neighbour_adjacent e f).choose

lemma sharedVertex_left (I : FiniteSystem V E A L) (e : E) (f : ↑(I.neighbours e)) :
    I.sharedVertex e f ∈ I.endpoints e := (I.neighbour_adjacent e f).choose_spec.1

lemma sharedVertex_right (I : FiniteSystem V E A L) (e : E) (f : ↑(I.neighbours e)) :
    I.sharedVertex e f ∈ I.endpoints f.val := (I.neighbour_adjacent e f).choose_spec.2

lemma sharedVertex_unique (I : FiniteSystem V E A L) (e : E) (f : ↑(I.neighbours e))
    (v : V) (hve : v ∈ I.endpoints e) (hvf : v ∈ I.endpoints f.val) : v = I.sharedVertex e f := by
  by_contra hne
  exact I.neighbour_ne e f (I.linear e f.val v (I.sharedVertex e f) hve hvf
    (I.sharedVertex_left e f) (I.sharedVertex_right e f) hne).symm

def GoodAt (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (σ : E → A) (a : A) : Prop :=
  I.Compatible B e a ∧ ∀ f : ↑(I.neighbours e),
    I.label e (I.sharedVertex e f) a ≠ I.label f.val (I.sharedVertex e f) (σ f.val)

def availableMass (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (σ : E → A) : ℝ :=
  ∑ a, if I.GoodAt B e σ a then I.activity e a else 0

lemma goodAt_pair (I : FiniteSystem V E A L) {B : Boundary V L} {e : E} {σ : E → A} {a : A}
    (ha : I.GoodAt B e σ a) (f : E) (hef : e ≠ f) (v : V)
    (hve : v ∈ I.endpoints e) (hvf : v ∈ I.endpoints f) :
    I.label e v a ≠ I.label f v (σ f) := by
  let ff : ↑(I.neighbours e) := ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hef.symm, v, hve, hvf⟩⟩
  have heq := I.sharedVertex_unique e ff v hve hvf
  simpa only [← heq] using ha.2 ff

/-- Each adjacent free edge excludes one endpoint fibre, because the base
edge system is simple. This is the actual greedy-availability inequality. -/
theorem availableMass_lower (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (σ : E → A)
    (hfibre : I.FibreBound) : I.compatibleMass B e - I.edgeDegree e ≤ I.availableMass B e σ := by
  let bad (f : ↑(I.neighbours e)) (a : A) : ℝ :=
    if I.label e (I.sharedVertex e f) a = I.label f.val (I.sharedVertex e f) (σ f.val)
      then I.activity e a else 0
  have hbad (f : ↑(I.neighbours e)) (a : A) : 0 ≤ bad f a := by
    dsimp [bad]
    split_ifs <;> first | exact I.activity_nonneg e a | rfl
  have hpoint (a : A) : (if I.Compatible B e a then I.activity e a else 0) ≤
      (if I.GoodAt B e σ a then I.activity e a else 0) + ∑ f, bad f a := by
    by_cases hg : I.GoodAt B e σ a
    · simp only [hg.1, hg, if_true]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun f _ => hbad f a)
    · by_cases hc : I.Compatible B e a
      · have hh : ∃ f : ↑(I.neighbours e),
            I.label e (I.sharedVertex e f) a = I.label f.val (I.sharedVertex e f) (σ f.val) := by
          by_contra hn
          push Not at hn
          exact hg ⟨hc, hn⟩
        obtain ⟨f, hf⟩ := hh
        simp only [hc, hg, if_true, if_false, zero_add]
        have hs := Finset.single_le_sum (s := Finset.univ) (f := fun f => bad f a)
          (fun f _ => hbad f a) (Finset.mem_univ f)
        simpa only [bad, if_pos hf] using hs
      · simp only [hc, hg, if_false, zero_add]
        exact Finset.sum_nonneg fun f _ => hbad f a
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpoint a)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  have hf (f : ↑(I.neighbours e)) : (∑ a, bad f a) ≤ 1 :=
    hfibre e (I.sharedVertex e f) (I.sharedVertex_left e f) _
  have hb : (∑ f : ↑(I.neighbours e), ∑ a, bad f a) ≤ I.edgeDegree e := by
    apply (Finset.sum_le_sum (s := Finset.univ) (fun f _ => hf f)).trans_eq
    simp [edgeDegree]
  change I.compatibleMass B e ≤ I.availableMass B e σ + _ at hsum
  linarith

lemma exists_positive_goodAt (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (σ : E → A)
    (hfibre : I.FibreBound) (hslack : I.edgeDegree e < I.compatibleMass B e) :
    ∃ a, I.GoodAt B e σ a ∧ 0 < I.activity e a := by
  have hl := I.availableMass_lower B e σ hfibre
  have hp : 0 < I.availableMass B e σ := by linarith
  obtain ⟨a, _, ha⟩ := Finset.sum_pos_iff_of_nonneg
    (fun a _ => show 0 ≤ if I.GoodAt B e σ a then I.activity e a else 0 by
      split_ifs <;> first | exact I.activity_nonneg e a | rfl) |>.mp hp
  by_cases hg : I.GoodAt B e σ a
  · exact ⟨a, hg, by simpa [hg] using ha⟩
  · simp [hg] at ha

/-- Greedy extension on an arbitrary set of free edges. -/
private lemma exists_partial_admissible [Nonempty A] (I : FiniteSystem V E A L)
    (B : Boundary V L) (hfibre : I.FibreBound)
    (hslack : ∀ e, (I.edgeDegree e : ℝ) < I.compatibleMass B e) (s : Finset E) :
    ∃ σ : E → A, (∀ e ∈ s, I.Compatible B e (σ e) ∧ 0 < I.activity e (σ e)) ∧
      ∀ e ∈ s, ∀ f ∈ s, e ≠ f → ∀ v, v ∈ I.endpoints e → v ∈ I.endpoints f →
        I.label e v (σ e) ≠ I.label f v (σ f) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance, by simp⟩
  | @insert e s hes ih =>
    obtain ⟨σ, hσ, hp⟩ := ih
    obtain ⟨a, ha, hap⟩ := I.exists_positive_goodAt B e σ hfibre (hslack e)
    refine ⟨Function.update σ e a, ?_, ?_⟩
    · intro f hf
      rcases Finset.mem_insert.mp hf with rfl | hfs
      · simpa only [Function.update_self] using And.intro ha.1 hap
      · have hfe : f ≠ e := by intro h; exact hes (h ▸ hfs)
        simpa only [Function.update_of_ne hfe] using hσ f hfs
    · intro f hf g hg hfg v hvf hvg
      by_cases hfe : f = e
      · subst f
        have hge : g ≠ e := hfg.symm
        simpa only [Function.update_self, Function.update_of_ne hge] using
          I.goodAt_pair ha g hfg v hvf hvg
      · by_cases hge : g = e
        · subst g
          simpa only [Function.update_self, Function.update_of_ne hfe] using
            (I.goodAt_pair ha f (Ne.symm hfe) v hvg hvf).symm
        · simpa only [Function.update_of_ne hfe, Function.update_of_ne hge] using
            hp f (Finset.mem_of_mem_insert_of_ne hf hfe) g
              (Finset.mem_of_mem_insert_of_ne hg hge) hfg v hvf hvg

/-- The true hard-label Gibbs partition is positive under strict greedy slack. -/
theorem partition_pos (I : FiniteSystem V E A L) (B : Boundary V L)
    (hfibre : I.FibreBound) (hslack : ∀ e, (I.edgeDegree e : ℝ) < I.compatibleMass B e) :
    0 < I.partition B := by
  cases isEmpty_or_nonempty E with
  | inl he =>
    let _ := he
    let σ : E → A := isEmptyElim
    have hs : 0 < I.configurationWeight B σ := by
      rw [I.configurationWeight_pos_iff]
      exact ⟨⟨fun e => isEmptyElim e, fun e => isEmptyElim e⟩, fun e => isEmptyElim e⟩
    exact hs.trans_le (Finset.single_le_sum (fun τ _ => I.configurationWeight_nonneg B τ)
      (Finset.mem_univ σ))
  | inr he =>
    let _ := he
    let e : E := Classical.choice he
    have hp : 0 < I.compatibleMass B e := (Nat.cast_nonneg _).trans_lt (hslack e)
    obtain ⟨a, _, ha⟩ := (Finset.sum_pos_iff_of_nonneg (fun a _ => show
        0 ≤ if I.Compatible B e a then I.activity e a else 0 by
      split_ifs <;> first | exact I.activity_nonneg e a | rfl)).mp hp
    let _ : Nonempty A := ⟨a⟩
    obtain ⟨σ, hσ, hs⟩ := I.exists_partial_admissible B hfibre hslack univ
    have hadm : I.Admissible B σ := ⟨fun e => (hσ e (mem_univ e)).1,
      fun e f hef v hve hvf => hs e (mem_univ e) f (mem_univ f) hef v hve hvf⟩
    have hw := I.configurationWeight_pos_iff B σ |>.mpr
      ⟨hadm, fun e => (hσ e (mem_univ e)).2⟩
    exact hw.trans_le (Finset.single_le_sum (fun τ _ => I.configurationWeight_nonneg B τ)
      (Finset.mem_univ σ))

lemma Bounds.partition_pos (I : FiniteSystem V E A L) (B : Boundary V L) {Δ : ℕ}
    (h : I.Bounds B Δ) : 0 < I.partition B := by
  apply I.partition_pos B h.2.1
  intro e
  have hs := h.2.2 e
  have hd := Nat.cast_nonneg (α := ℝ) Δ
  linarith

end FiniteSystem
end
end CI2ZF.Appendix.Edge
