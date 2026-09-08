import CI2ZF.Appendix.CVArithmetic
import PottsCI.PathCoupling

/-! The weighted configuration-space path metric used in the CV appendix.
This module proves the shortest-path construction and the adjacent geodesic
claim from edge bounds. It also proves path coupling for this metric. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.FinDist
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- A route changes exactly one coordinate at each step. -/
inductive Route : (V → C) → (V → C) → Type _
  | nil (X : V → C) : Route X X
  | cons {X Y Z : V → C} (adjacent : hamCard X Y = 1) (tail : Route Y Z) : Route X Z

namespace Route

def length {X Y : V → C} : Route X Y → ℕ
  | .nil _ => 0
  | .cons _ p => 1 + length p

def cost (ell : (V → C) → (V → C) → ℝ) {X Y : V → C} : Route X Y → ℝ
  | .nil _ => 0
  | .cons (Y := Z) _ p => ell X Z + cost ell p

def append {X Y Z : V → C} (p : Route X Y) (q : Route Y Z) : Route X Z :=
  match p with
  | .nil _ => q
  | .cons h p => .cons h (append p q)

lemma cost_append (ell : (V → C) → (V → C) → ℝ) {X Y Z : V → C}
    (p : Route X Y) (q : Route Y Z) : cost ell (append p q) = cost ell p + cost ell q := by
  induction p with
  | nil => simp [append, cost]
  | cons h p ih => simp [append, cost, ih, add_assoc]

def reverse {X Y : V → C} (p : Route X Y) : Route Y X :=
  match p with
  | .nil _ => .nil _
  | .cons h p => append (reverse p) (.cons (by rw [hamCard_comm]; exact h) (.nil _))

lemma cost_reverse (ell : (V → C) → (V → C) → ℝ)
    (hsym : ∀ X Y, ell X Y = ell Y X) {X Y : V → C} (p : Route X Y) :
    cost ell (reverse p) = cost ell p := by
  induction p with
  | nil => rfl
  | @cons X Z Y h p ih => simp [reverse, cost_append, cost, ih, hsym X Z, add_comm]

lemma ham_le_length {X Y : V → C} (p : Route X Y) : hamCard X Y ≤ length p := by
  induction p with
  | nil => simp [length, hamCard_self]
  | @cons X Z Y h p ih =>
    have ht := hamCard_triangle X Z Y
    simp only [length]
    omega

lemma lower_length (ell : (V → C) → (V → C) → ℝ) {m : ℝ}
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y)
    {X Y : V → C} (p : Route X Y) : m * length p ≤ cost ell p := by
  induction p with
  | nil => simp [length, cost]
  | @cons X Z Y h p ih =>
    have he := hlow X Z h
    simp only [length, cost, Nat.cast_add, Nat.cast_one]
    linarith

lemma lower_hamming (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y)
    {X Y : V → C} (p : Route X Y) : m * ham X Y ≤ cost ell p := by
  have hcast : ham X Y ≤ (length p : ℝ) := by unfold ham; exact_mod_cast ham_le_length p
  exact (mul_le_mul_of_nonneg_left hcast hm).trans (lower_length ell hlow p)

lemma exists_cost_le_hamming (ell : (V → C) → (V → C) → ℝ)
    (hupper : ∀ X Y, hamCard X Y = 1 → ell X Y ≤ 1) (X Y : V → C) :
    ∃ p : Route X Y, cost ell p ≤ ham X Y := by
  suffices ∀ k : ℕ, ∀ X Y : V → C, hamCard X Y = k →
      ∃ p : Route X Y, cost ell p ≤ (k : ℝ) by exact this _ X Y rfl
  intro k
  induction k with
  | zero =>
    intro X Y h
    have := hamCard_eq_zero h
    subst Y
    exact ⟨.nil X, by simp [cost]⟩
  | succ k ih =>
    intro X Y h
    obtain ⟨Z, hxz, hzy⟩ := exists_intermediate h
    obtain ⟨p, hp⟩ := ih Z Y hzy
    refine ⟨.cons hxz p, ?_⟩
    have he := hupper X Z hxz
    simp only [cost, Nat.cast_add, Nat.cast_one]
    linarith

lemma nonempty (X Y : V → C) : Nonempty (Route X Y) := by
  obtain ⟨p, _⟩ := exists_cost_le_hamming (fun _ _ => 1) (by intros; rfl) X Y
  exact ⟨p⟩

end Route

/-- The infimum is over actual one-coordinate routes, including the empty route. -/
def pathMetric (ell : (V → C) → (V → C) → ℝ) (X Y : V → C) : ℝ :=
  sInf (Set.range (Route.cost ell : Route X Y → ℝ))

lemma routeCost_nonempty (ell : (V → C) → (V → C) → ℝ) (X Y : V → C) :
    (Set.range (Route.cost ell : Route X Y → ℝ)).Nonempty := by
  obtain ⟨p⟩ := Route.nonempty X Y
  exact ⟨_, ⟨p, rfl⟩⟩

lemma routeCost_bddBelow (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y) (X Y : V → C) :
    BddBelow (Set.range (Route.cost ell : Route X Y → ℝ)) := by
  refine ⟨m * ham X Y, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact p.lower_hamming ell hm hlow

lemma pathMetric_le_cost (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y) {X Y : V → C} (p : Route X Y) :
    pathMetric ell X Y ≤ p.cost ell :=
  csInf_le (routeCost_bddBelow ell hm hlow X Y) ⟨p, rfl⟩

lemma pathMetric_comparison (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y)
    (hupper : ∀ X Y, hamCard X Y = 1 → ell X Y ≤ 1) (X Y : V → C) :
    m * ham X Y ≤ pathMetric ell X Y ∧ pathMetric ell X Y ≤ ham X Y := by
  constructor
  · apply le_csInf (routeCost_nonempty ell X Y)
    rintro _ ⟨p, rfl⟩
    exact p.lower_hamming ell hm hlow
  · obtain ⟨p, hp⟩ := Route.exists_cost_le_hamming ell hupper X Y
    exact (pathMetric_le_cost ell hm hlow p).trans hp

lemma pathMetric_nonneg (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y) (X Y : V → C) :
    0 ≤ pathMetric ell X Y := by
  apply le_csInf (routeCost_nonempty ell X Y)
  rintro _ ⟨p, rfl⟩
  exact (mul_nonneg hm (ham_nonneg X Y)).trans (p.lower_hamming ell hm hlow)

lemma pathMetric_self (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y) (X : V → C) :
    pathMetric ell X X = 0 :=
  le_antisymm (pathMetric_le_cost ell hm hlow (.nil X)) (pathMetric_nonneg ell hm hlow X X)

lemma pathMetric_triangle (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y) (X Y Z : V → C) :
    pathMetric ell X Z ≤ pathMetric ell X Y + pathMetric ell Y Z := by
  suffices pathMetric ell X Z - pathMetric ell Y Z ≤ pathMetric ell X Y by linarith
  apply le_csInf (routeCost_nonempty ell X Y)
  rintro _ ⟨p, rfl⟩
  suffices pathMetric ell X Z - p.cost ell ≤ pathMetric ell Y Z by linarith
  apply le_csInf (routeCost_nonempty ell Y Z)
  rintro _ ⟨q, rfl⟩
  have h := pathMetric_le_cost ell hm hlow (p.append q)
  rw [Route.cost_append] at h
  linarith

lemma pathMetric_comm (ell : (V → C) → (V → C) → ℝ) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y)
    (hsym : ∀ X Y, ell X Y = ell Y X) (X Y : V → C) :
    pathMetric ell X Y = pathMetric ell Y X := by
  have h (X Y : V → C) : pathMetric ell X Y ≤ pathMetric ell Y X := by
    apply le_csInf (routeCost_nonempty ell Y X)
    rintro _ ⟨p, rfl⟩
    have h := pathMetric_le_cost ell hm hlow p.reverse
    rwa [Route.cost_reverse ell hsym] at h
  exact le_antisymm (h X Y) (h Y X)

/-- If twice the edge lower bound exceeds one, every adjacent edge is a geodesic. -/
lemma pathMetric_adjacent (ell : (V → C) → (V → C) → ℝ) {m : ℝ}
    (hm : 0 ≤ m) (hm2 : 1 < 2 * m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y)
    (hupper : ∀ X Y, hamCard X Y = 1 → ell X Y ≤ 1)
    {X Y : V → C} (hxy : hamCard X Y = 1) : pathMetric ell X Y = ell X Y := by
  apply le_antisymm
  · simpa [Route.cost] using pathMetric_le_cost ell hm hlow (.cons hxy (.nil Y))
  · apply le_csInf (routeCost_nonempty ell X Y)
    rintro _ ⟨p, rfl⟩
    cases p with
    | nil => simp [hamCard_self] at hxy
    | cons h p =>
      cases p with
      | nil => simp [Route.cost]
      | cons h' p =>
        have hc := (Route.cons h (Route.cons h' p)).lower_length ell hlow
        have hn : 0 ≤ (p.length : ℝ) := Nat.cast_nonneg _
        have he := hupper X Y hxy
        simp only [Route.length, Nat.cast_add, Nat.cast_one] at hc
        nlinarith

/-- Weighted path coupling: contraction on adjacent pairs propagates through
all actual routes and therefore through their infimum. -/
theorem pathMetric_W_contract [Fintype C]
    (ell : (V → C) → (V → C) → ℝ) {m c : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ X Y, hamCard X Y = 1 → m ≤ ell X Y) (hc : 0 ≤ c)
    (K : (V → C) → FinDist (V → C))
    (hadj : ∀ X Y, hamCard X Y = 1 →
      W (pathMetric ell) (K X) (K Y) ≤ c * ell X Y) (X Y : V → C) :
    W (pathMetric ell) (K X) (K Y) ≤ c * pathMetric ell X Y := by
  have hnonneg := pathMetric_nonneg ell hm hlow
  have hzero := pathMetric_self ell hm hlow
  have htriangle := pathMetric_triangle ell hm hlow
  have hp {X Y : V → C} (p : Route X Y) :
      W (pathMetric ell) (K X) (K Y) ≤ c * p.cost ell := by
    induction p with
    | nil => simpa [Route.cost] using (W_self hnonneg hzero (K _)).le
    | @cons X Z Y h p ih =>
      have ht := W_triangle hnonneg hnonneg hnonneg htriangle (K X) (K Z) (K Y)
      have he := hadj X Z h
      simp only [Route.cost]
      nlinarith
  rcases eq_or_lt_of_le hc with hc | hc
  · subst c
    obtain ⟨p⟩ := Route.nonempty X Y
    simpa using hp p
  · rw [mul_comm c]
    apply (div_le_iff₀ hc).mp
    apply le_csInf (routeCost_nonempty ell X Y)
    rintro _ ⟨p, rfl⟩
    exact (div_le_iff₀ hc).mpr (by nlinarith [hp p])

end
end CI2ZF.Appendix.CV
