import CI2ZF.Potts.Model.Real.SoftKernel
import CI2ZF.Coupling.Foundations.PathCoupling
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Components and hard flip kernels for the near-Vigoda argument

This file formalizes the graph-theoretic layer below the one-step
near-Vigoda coupling.  In particular it supplies:

* two-colour components and component swaps;
* preservation of proper list-colourings and the double-flip identity;
* the Vigoda proposal kernel, reversibility, and stationarity on a hard fibre;
* the Hamming bounds used to complete a partial coupling;
* an exact structural interface for two active instances which agree away
  from their unique disagreement vertex.

The global, cross-proposal allocation of root-containing and off-root flip
masses is not asserted here; it is proved later, as
`conditionalHardCouplingEstimate` in `PottsCITheorem`.
-/

namespace PottsCI
namespace Vigoda

open Finset

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V C : Type*}
variable [Fintype V] [Fintype C]

/-! ## Hard list instances and two-colour components -/

/-- A finite graph together with the allowed colour list at every vertex. -/
structure HardListInstance (V C : Type*) where
  graph : SimpleGraph V
  list : V → Finset C

/-- Proper list-colourings of a hard instance. -/
def HardListInstance.IsProper (F : HardListInstance V C) (X : V → C) : Prop :=
  (∀ u v, F.graph.Adj u v → X u ≠ X v) ∧ ∀ u, X u ∈ F.list u

/-- Alternating adjacency for the colour pair `c₁,c₂`. -/
def alternatingAdj (G : SimpleGraph V) (X : V → C) (c₁ c₂ : C) (u v : V) : Prop :=
  G.Adj u v ∧ ((X u = c₁ ∧ X v = c₂) ∨ (X u = c₂ ∧ X v = c₁))

lemma alternatingAdj_comm_colours {G : SimpleGraph V} {X : V → C} {c₁ c₂ : C} {u v : V} :
    alternatingAdj G X c₁ c₂ u v ↔ alternatingAdj G X c₂ c₁ u v := by
  unfold alternatingAdj
  tauto

lemma alternatingAdj_symm {G : SimpleGraph V} {X : V → C} {c₁ c₂ : C} {u v : V}
    (h : alternatingAdj G X c₁ c₂ u v) : alternatingAdj G X c₁ c₂ v u := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with h | h
  · exact Or.inr ⟨h.2, h.1⟩
  · exact Or.inl ⟨h.2, h.1⟩

/-- The two-colour component containing `u`, represented as a finite set. -/
noncomputable def flipSet (G : SimpleGraph V) (X : V → C) (u : V) (c : C) : Finset V :=
  Finset.univ.filter fun w =>
    Relation.ReflTransGen (alternatingAdj G X (X u) c) u w

@[simp]
lemma mem_flipSet {G : SimpleGraph V} {X : V → C} {u : V} {c : C} {w : V} :
    w ∈ flipSet G X u c ↔
      Relation.ReflTransGen (alternatingAdj G X (X u) c) u w := by
  simp [flipSet]

@[simp]
lemma self_mem_flipSet {G : SimpleGraph V} {X : V → C} {u : V} {c : C} :
    u ∈ flipSet G X u c :=
  mem_flipSet.mpr Relation.ReflTransGen.refl

lemma flipSet_nonempty {G : SimpleGraph V} {X : V → C} {u : V} {c : C} :
    (flipSet G X u c).Nonempty := ⟨u, self_mem_flipSet⟩

lemma flipSet_card_pos {G : SimpleGraph V} {X : V → C} {u : V} {c : C} :
    0 < (flipSet G X u c).card :=
  Finset.card_pos.mpr flipSet_nonempty

/-- Every vertex of a two-colour component has one of its two colours. -/
lemma colour_eq_of_mem_flipSet {G : SimpleGraph V} {X : V → C} {u : V} {c : C} {w : V}
    (hw : w ∈ flipSet G X u c) : X w = X u ∨ X w = c := by
  rw [mem_flipSet] at hw
  induction hw with
  | refl => exact Or.inl rfl
  | tail _ hstep _ =>
      rcases hstep.2 with h | h
      · exact Or.inr h.2
      · exact Or.inl h.2

/-- Swap `c₁` and `c₂` on `S`, leaving all other vertices unchanged. -/
noncomputable def flipConfiguration (X : V → C) (S : Finset V) (c₁ c₂ : C) : V → C :=
  fun w => if w ∈ S then if X w = c₁ then c₂ else c₁ else X w

@[simp]
lemma flipConfiguration_of_mem {X : V → C} {S : Finset V} {c₁ c₂ : C} {w : V}
    (hw : w ∈ S) :
    flipConfiguration X S c₁ c₂ w = if X w = c₁ then c₂ else c₁ := by
  simp [flipConfiguration, hw]

@[simp]
lemma flipConfiguration_of_not_mem {X : V → C} {S : Finset V} {c₁ c₂ : C} {w : V}
    (hw : w ∉ S) : flipConfiguration X S c₁ c₂ w = X w := by
  simp [flipConfiguration, hw]

lemma flipConfiguration_ne_iff {G : SimpleGraph V} {X : V → C} {u : V} {c : C}
    (hc : c ≠ X u) (w : V) :
    flipConfiguration X (flipSet G X u c) (X u) c w ≠ X w ↔
      w ∈ flipSet G X u c := by
  constructor
  · intro hne
    by_contra hw
    exact hne (flipConfiguration_of_not_mem hw)
  · intro hw
    rw [flipConfiguration_of_mem hw]
    by_cases h : X w = X u
    · simp [h, hc]
    · rcases colour_eq_of_mem_flipSet hw with h' | h'
      · exact absurd h' h
      · rw [if_neg h, h']
        exact Ne.symm hc

/-- Every graph neighbour just outside a two-colour component avoids both
component colours. -/
lemma proper_boundary_colour {F : HardListInstance V C} {X : V → C}
    (hX : F.IsProper X) {u : V} {c : C} {w z : V}
    (hw : w ∈ flipSet F.graph X u c) (hz : z ∉ flipSet F.graph X u c)
    (hadj : F.graph.Adj w z) : X z ≠ X u ∧ X z ≠ c := by
  constructor
  · intro hzu
    apply hz
    rw [mem_flipSet]
    refine (mem_flipSet.mp hw).tail ⟨hadj, ?_⟩
    rcases colour_eq_of_mem_flipSet hw with h | h
    · exact absurd (h.trans hzu.symm) (hX.1 w z hadj)
    · exact Or.inr ⟨h, hzu⟩
  · intro hzc
    apply hz
    rw [mem_flipSet]
    refine (mem_flipSet.mp hw).tail ⟨hadj, ?_⟩
    rcases colour_eq_of_mem_flipSet hw with h | h
    · exact Or.inl ⟨h, hzc⟩
    · exact absurd (h.trans hzc.symm) (hX.1 w z hadj)

/-- Whether the proposed component swap respects all lists. -/
def flipAllowed (F : HardListInstance V C) (S : Finset V) (Y : V → C) : Prop :=
  ∀ w ∈ S, Y w ∈ F.list w

/-- An allowed component swap preserves proper list-colourings. -/
lemma flip_preserves_proper {F : HardListInstance V C} {X : V → C}
    (hX : F.IsProper X) {u : V} {c : C} (hc : c ≠ X u)
    (hAllowed : flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c)) :
    F.IsProper (flipConfiguration X (flipSet F.graph X u c) (X u) c) := by
  constructor
  · intro w z hadj
    by_cases hw : w ∈ flipSet F.graph X u c <;>
      by_cases hz : z ∈ flipSet F.graph X u c
    · rw [flipConfiguration_of_mem hw, flipConfiguration_of_mem hz]
      have hne := hX.1 w z hadj
      rcases colour_eq_of_mem_flipSet hw with h1 | h1 <;>
        rcases colour_eq_of_mem_flipSet hz with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [if_pos h1, if_neg (fun hh => hc (h2.symm.trans hh))]
        exact hc
      · rw [if_neg (fun hh => hc (h1.symm.trans hh)), if_pos h2]
        exact fun hh => hc hh.symm
      · exact absurd (h1.trans h2.symm) hne
    · rw [flipConfiguration_of_mem hw, flipConfiguration_of_not_mem hz]
      obtain ⟨hz1, hz2⟩ := proper_boundary_colour hX hw hz hadj
      split
      · exact fun hh => hz2 hh.symm
      · exact fun hh => hz1 hh.symm
    · rw [flipConfiguration_of_not_mem hw, flipConfiguration_of_mem hz]
      obtain ⟨hz1, hz2⟩ := proper_boundary_colour hX hz hw hadj.symm
      split
      · exact hz2
      · exact hz1
    · rw [flipConfiguration_of_not_mem hw, flipConfiguration_of_not_mem hz]
      exact hX.1 w z hadj
  · intro w
    by_cases hw : w ∈ flipSet F.graph X u c
    · exact hAllowed w hw
    · rw [flipConfiguration_of_not_mem hw]
      exact hX.2 w

@[simp]
lemma flipConfiguration_at_start {G : SimpleGraph V} {X : V → C} {u : V} {c : C} :
    flipConfiguration X (flipSet G X u c) (X u) c u = c := by
  rw [flipConfiguration_of_mem self_mem_flipSet, if_pos rfl]

/-- Double-flip identity: the reverse proposal has the same component and
returns to the original colouring. -/
lemma flip_involutive {F : HardListInstance V C} {X : V → C}
    (hX : F.IsProper X) {u : V} {c : C} (hc : c ≠ X u) :
    let X' := flipConfiguration X (flipSet F.graph X u c) (X u) c
    flipSet F.graph X' u (X u) = flipSet F.graph X u c ∧
      flipConfiguration X' (flipSet F.graph X u c) c (X u) = X := by
  dsimp only
  have hX'u : flipConfiguration X (flipSet F.graph X u c) (X u) c u = c :=
    flipConfiguration_at_start
  have hswap : ∀ w ∈ flipSet F.graph X u c,
      (flipConfiguration X (flipSet F.graph X u c) (X u) c w = c ↔ X w = X u) ∧
      (flipConfiguration X (flipSet F.graph X u c) (X u) c w = X u ↔ X w = c) := by
    intro w hw
    rw [flipConfiguration_of_mem hw]
    rcases colour_eq_of_mem_flipSet hw with h | h
    · rw [if_pos h]
      constructor
      · exact ⟨fun _ => h, fun _ => rfl⟩
      · exact ⟨fun hcu => absurd hcu hc,
          fun hwc => absurd (h.symm.trans hwc) (fun hh => hc hh.symm)⟩
    · have hne : X w ≠ X u := by simpa [h] using hc
      rw [if_neg hne]
      constructor
      · exact ⟨fun hh => absurd hh.symm hc,
          fun hwu => absurd (h.symm.trans hwu) hc⟩
      · exact ⟨fun _ => h, fun _ => rfl⟩
  have hstepIff : ∀ w z, w ∈ flipSet F.graph X u c → z ∈ flipSet F.graph X u c →
      (alternatingAdj F.graph
          (flipConfiguration X (flipSet F.graph X u c) (X u) c) c (X u) w z ↔
        alternatingAdj F.graph X (X u) c w z) := by
    intro w z hw hz
    unfold alternatingAdj
    constructor
    · rintro ⟨hadj, h | h⟩
      · exact ⟨hadj, Or.inl ⟨((hswap w hw).1).mp h.1, ((hswap z hz).2).mp h.2⟩⟩
      · exact ⟨hadj, Or.inr ⟨((hswap w hw).2).mp h.1, ((hswap z hz).1).mp h.2⟩⟩
    · rintro ⟨hadj, h | h⟩
      · exact ⟨hadj, Or.inl ⟨((hswap w hw).1).mpr h.1, ((hswap z hz).2).mpr h.2⟩⟩
      · exact ⟨hadj, Or.inr ⟨((hswap w hw).2).mpr h.1, ((hswap z hz).1).mpr h.2⟩⟩
  have hforward : ∀ w,
      Relation.ReflTransGen (alternatingAdj F.graph X (X u) c) u w →
      Relation.ReflTransGen
        (alternatingAdj F.graph
          (flipConfiguration X (flipSet F.graph X u c) (X u) c) c (X u)) u w := by
    intro w hw
    induction hw with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b z hab hstep ih =>
        have hbS : b ∈ flipSet F.graph X u c := mem_flipSet.mpr hab
        have hzS : z ∈ flipSet F.graph X u c := mem_flipSet.mpr (hab.tail hstep)
        exact ih.tail ((hstepIff b z hbS hzS).mpr hstep)
  have hbackward : ∀ w,
      Relation.ReflTransGen
        (alternatingAdj F.graph
          (flipConfiguration X (flipSet F.graph X u c) (X u) c) c (X u)) u w →
      w ∈ flipSet F.graph X u c := by
    intro w hw
    induction hw with
    | refl => exact self_mem_flipSet
    | @tail b z hab hstep ih =>
        by_contra hz
        obtain ⟨h1, h2⟩ := proper_boundary_colour hX ih hz hstep.1
        have hz' : flipConfiguration X (flipSet F.graph X u c) (X u) c z = X z :=
          flipConfiguration_of_not_mem hz
        rcases hstep.2 with h | h
        · exact h1 (hz' ▸ h.2)
        · exact h2 (hz' ▸ h.2)
  constructor
  · ext w
    rw [mem_flipSet, hX'u, mem_flipSet]
    constructor
    · intro hw
      exact mem_flipSet.mp (hbackward w hw)
    · exact hforward w
  · funext w
    by_cases hw : w ∈ flipSet F.graph X u c
    · rw [flipConfiguration_of_mem hw]
      rcases colour_eq_of_mem_flipSet hw with h | h
      · have hX'w : flipConfiguration X (flipSet F.graph X u c) (X u) c w = c :=
          ((hswap w hw).1).mpr h
        rw [hX'w, if_pos rfl, h]
      · have hX'w : flipConfiguration X (flipSet F.graph X u c) (X u) c w = X u :=
          ((hswap w hw).2).mpr h
        rw [hX'w, if_neg (fun hh => hc hh.symm), h]
    · rw [flipConfiguration_of_not_mem hw, flipConfiguration_of_not_mem hw]

/-! ## The Vigoda profile and hard transition -/

/-- Aggregated accepted-flip masses in the classical Vigoda profile. -/
noncomputable def vigodaMass : ℕ → ℝ
  | 1 => 1
  | 2 => 13 / 42
  | 3 => 1 / 6
  | 4 => 2 / 21
  | 5 => 1 / 21
  | 6 => 1 / 84
  | _ => 0

lemma vigodaMass_nonneg (r : ℕ) : 0 ≤ vigodaMass r := by
  match r with
  | 0 => norm_num [vigodaMass]
  | 1 => norm_num [vigodaMass]
  | 2 => norm_num [vigodaMass]
  | 3 => norm_num [vigodaMass]
  | 4 => norm_num [vigodaMass]
  | 5 => norm_num [vigodaMass]
  | 6 => norm_num [vigodaMass]
  | _ + 7 => simp [vigodaMass]

lemma vigodaMass_le_one (r : ℕ) : vigodaMass r ≤ 1 := by
  match r with
  | 0 => norm_num [vigodaMass]
  | 1 => norm_num [vigodaMass]
  | 2 => norm_num [vigodaMass]
  | 3 => norm_num [vigodaMass]
  | 4 => norm_num [vigodaMass]
  | 5 => norm_num [vigodaMass]
  | 6 => norm_num [vigodaMass]
  | _ + 7 => simp [vigodaMass]

/-- The root-changing size charge used in the reserved-holding coupling. -/
lemma vigoda_central_bound (r : ℕ) :
    ((r : ℝ) - 2) * vigodaMass r ≤ 4 / 21 := by
  match r with
  | 0 => norm_num [vigodaMass]
  | 1 => norm_num [vigodaMass]
  | 2 => norm_num [vigodaMass]
  | 3 => norm_num [vigodaMass]
  | 4 => norm_num [vigodaMass]
  | 5 => norm_num [vigodaMass]
  | 6 => norm_num [vigodaMass]
  | _ + 7 => simp [vigodaMass]; norm_num

/-- Every one-sided component move has size-times-mass at most one. -/
lemma vigoda_branch_bound (r : ℕ) : (r : ℝ) * vigodaMass r ≤ 1 := by
  match r with
  | 0 => norm_num [vigodaMass]
  | 1 => norm_num [vigodaMass]
  | 2 => norm_num [vigodaMass]
  | 3 => norm_num [vigodaMass]
  | 4 => norm_num [vigodaMass]
  | 5 => norm_num [vigodaMass]
  | 6 => norm_num [vigodaMass]
  | _ + 7 => simp [vigodaMass]

lemma vigoda_size_minus_one_bound (r : ℕ) :
    ((r : ℝ) - 1) * vigodaMass r ≤ 1 / 3 := by
  match r with
  | 0 => norm_num [vigodaMass]
  | 1 => norm_num [vigodaMass]
  | 2 => norm_num [vigodaMass]
  | 3 => norm_num [vigodaMass]
  | 4 => norm_num [vigodaMass]
  | 5 => norm_num [vigodaMass]
  | 6 => norm_num [vigodaMass]
  | _ + 7 => simp [vigodaMass]

/-- The port-pair box inequality from the paper, proved for all admissible
real residual masses rather than only for the finite corners. -/
lemma vigoda_port_box_bound (j r k s : ℕ)
    (hj : 1 ≤ j) (hjr : j ≤ r) (hk : 1 ≤ k) (hks : k ≤ s)
    (alpha beta : ℝ)
    (ha0 : 0 ≤ alpha) (har : alpha ≤ vigodaMass r)
    (hb0 : 0 ≤ beta) (hbs : beta ≤ vigodaMass s) :
    ((r : ℝ) / j) * alpha + ((s : ℝ) / k) * beta -
        min (alpha / j) (beta / k) ≤ 4 / 3 := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hj.trans hjr
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hk.trans hks
  have hrm1 : 0 ≤ (r : ℝ) - 1 := by linarith
  have hsm1 : 0 ≤ (s : ℝ) - 1 := by linarith
  have hcentralR := vigoda_size_minus_one_bound r
  have hcentralS := vigoda_size_minus_one_bound s
  have hbranchR := vigoda_branch_bound r
  have hbranchS := vigoda_branch_bound s
  rcases le_total (alpha / j) (beta / k) with hmin | hmin
  · rw [min_eq_left hmin]
    have heq :
        (r : ℝ) / j * alpha + (s : ℝ) / k * beta - alpha / j =
          ((r : ℝ) - 1) / j * alpha + (s : ℝ) / k * beta := by ring
    rw [heq]
    have hleft : ((r : ℝ) - 1) / j * alpha ≤
        ((r : ℝ) - 1) * vigodaMass r :=
      calc
        ((r : ℝ) - 1) / j * alpha ≤ ((r : ℝ) - 1) * alpha :=
          mul_le_mul_of_nonneg_right (div_le_self hrm1 hj1) ha0
        _ ≤ ((r : ℝ) - 1) * vigodaMass r :=
          mul_le_mul_of_nonneg_left har hrm1
    have hright : (s : ℝ) / k * beta ≤ (s : ℝ) * vigodaMass s :=
      calc
        (s : ℝ) / k * beta ≤ (s : ℝ) * beta :=
          mul_le_mul_of_nonneg_right (div_le_self (by positivity) hk1) hb0
        _ ≤ (s : ℝ) * vigodaMass s :=
          mul_le_mul_of_nonneg_left hbs (by positivity)
    linarith
  · rw [min_eq_right hmin]
    have heq :
        (r : ℝ) / j * alpha + (s : ℝ) / k * beta - beta / k =
          (r : ℝ) / j * alpha + ((s : ℝ) - 1) / k * beta := by ring
    rw [heq]
    have hleft : (r : ℝ) / j * alpha ≤ (r : ℝ) * vigodaMass r :=
      calc
        (r : ℝ) / j * alpha ≤ (r : ℝ) * alpha :=
          mul_le_mul_of_nonneg_right (div_le_self (by positivity) hj1) ha0
        _ ≤ (r : ℝ) * vigodaMass r :=
          mul_le_mul_of_nonneg_left har (by positivity)
    have hright : ((s : ℝ) - 1) / k * beta ≤
        ((s : ℝ) - 1) * vigodaMass s :=
      calc
        ((s : ℝ) - 1) / k * beta ≤ ((s : ℝ) - 1) * beta :=
          mul_le_mul_of_nonneg_right (div_le_self hsm1 hk1) hb0
        _ ≤ ((s : ℝ) - 1) * vigodaMass s :=
          mul_le_mul_of_nonneg_left hbs hsm1
    linarith

/-- A two-point distribution, used for accept/reject proposals. -/
def twoPoint {S : Type*} [Fintype S] [DecidableEq S]
    (accepted rejected : S) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinDist S where
  w := fun s => (if s = accepted then p else 0) +
    (if s = rejected then 1 - p else 0)
  nonneg := fun s => add_nonneg (by split <;> linarith) (by split <;> linarith)
  sum_one := by
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

@[simp]
lemma twoPoint_w {S : Type*} [Fintype S] [DecidableEq S]
    (accepted rejected : S) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : S) :
    (twoPoint accepted rejected p hp0 hp1).w s =
      (if s = accepted then p else 0) + (if s = rejected then 1 - p else 0) := rfl

/-- Acceptance probability for a nontrivial proposal. -/
noncomputable def acceptanceProbability (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : ℝ :=
  if flipAllowed F (flipSet F.graph X u c)
      (flipConfiguration X (flipSet F.graph X u c) (X u) c) then
    vigodaMass (flipSet F.graph X u c).card / (flipSet F.graph X u c).card
  else 0

lemma acceptanceProbability_nonneg (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : 0 ≤ acceptanceProbability F X u c := by
  unfold acceptanceProbability
  split
  · exact div_nonneg (vigodaMass_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

lemma acceptanceProbability_le_one (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : acceptanceProbability F X u c ≤ 1 := by
  unfold acceptanceProbability
  split
  · have hcard : (1 : ℝ) ≤ (flipSet F.graph X u c).card := by
      exact_mod_cast flipSet_card_pos (G := F.graph) (X := X) (u := u) (c := c)
    rw [div_le_one (by positivity)]
    exact (vigodaMass_le_one _).trans hcard
  · exact zero_le_one

/-- Outcome law for one proposal `(u,c)`. -/
noncomputable def proposalDistribution (F : HardListInstance V C)
    (X : V → C) (u : V) (c : C) : FinDist (V → C) :=
  if c = X u then FinDist.pure X
  else twoPoint (flipConfiguration X (flipSet F.graph X u c) (X u) c) X
    (acceptanceProbability F X u c)
    (acceptanceProbability_nonneg F X u c)
    (acceptanceProbability_le_one F X u c)

/-- One hard Vigoda step. -/
noncomputable def hardStep [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) : FinDist (V → C) :=
  (FinDist.uniform (V × C)).bind fun p => proposalDistribution F X p.1 p.2

/-! ## Reversibility and stationarity of the hard transition -/

/-- A proposal with the wrong target colour at the proposal vertex cannot
move `X` to a distinct colouring `Y`. -/
lemma proposalDistribution_eq_zero {F : HardListInstance V C} {X Y : V → C}
    (hXY : X ≠ Y) (u : V) (c : C) (hc : c ≠ Y u) :
    (proposalDistribution F X u c).w Y = 0 := by
  unfold proposalDistribution
  split
  · simp [FinDist.pure, Ne.symm hXY]
  · rw [twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm), add_zero]
    rw [if_neg]
    intro hYflip
    apply hc
    have hroot := flipConfiguration_at_start
      (G := F.graph) (X := X) (u := u) (c := c)
    rw [← hYflip] at hroot
    exact hroot.symm

/-- The matched proposal from a proper colouring has the same transition
mass as its reverse proposal. -/
lemma proposalDistribution_reversible {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : F.IsProper Y) (hXY : X ≠ Y) (u : V) :
    (proposalDistribution F X u (Y u)).w Y =
      (proposalDistribution F Y u (X u)).w X := by
  by_cases hu : X u = Y u
  · unfold proposalDistribution
    rw [if_pos hu.symm, if_pos hu]
    simp [FinDist.pure, hXY, Ne.symm hXY]
  · have huY : Y u ≠ X u := fun h => hu h.symm
    unfold proposalDistribution
    rw [if_neg huY, if_neg hu, twoPoint_w, twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm),
      if_neg (show X ≠ Y from hXY), add_zero]
    by_cases hflip :
        Y = flipConfiguration X (flipSet F.graph X u (Y u)) (X u) (Y u)
    · obtain ⟨hset, hconf⟩ := flip_involutive hX (u := u) (c := Y u) huY
      rw [← hflip] at hset hconf
      unfold acceptanceProbability
      rw [hset, hconf, ← hflip]
      have hAllowedY : flipAllowed F (flipSet F.graph X u (Y u)) Y :=
        fun w _ => hY.2 w
      have hAllowedX : flipAllowed F (flipSet F.graph X u (Y u)) X :=
        fun w _ => hX.2 w
      simp [hAllowedY, hAllowedX]
    · have hflip' :
          X ≠ flipConfiguration Y (flipSet F.graph Y u (X u)) (Y u) (X u) := by
        intro hflip'
        apply hflip
        obtain ⟨hset, hconf⟩ := flip_involutive hY (u := u) (c := X u) hu
        rw [← hflip'] at hset hconf
        rw [hset]
        exact hconf.symm
      simp [hflip, hflip']

lemma hardStep_w [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X Y : V → C) :
    (hardStep F X).w Y = ∑ p : V × C,
      ((Fintype.card (V × C) : ℝ))⁻¹ *
        (proposalDistribution F X p.1 p.2).w Y := rfl

/-- Starting from a proper colouring, the hard transition stays in the
proper fibre. -/
lemma hardStep_support [Nonempty V] [Nonempty C]
    {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : ¬F.IsProper Y) : (hardStep F X).w Y = 0 := by
  rw [hardStep_w]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [mul_eq_zero]
  right
  obtain ⟨u, c⟩ := p
  have hXY : X ≠ Y := fun h => hY (h ▸ hX)
  unfold proposalDistribution
  split
  · simp [FinDist.pure, Ne.symm hXY]
  · rename_i hcx
    rw [twoPoint_w]
    simp only [if_neg (show Y ≠ X from fun h => hXY h.symm), add_zero]
    by_cases hYflip :
        Y = flipConfiguration X (flipSet F.graph X u c) (X u) c
    · rw [if_pos hYflip]
      unfold acceptanceProbability
      rw [if_neg]
      intro hAllowed
      exact hY (hYflip ▸ flip_preserves_proper hX hcx hAllowed)
    · rw [if_neg hYflip]

/-- Detailed balance of the hard Vigoda transition on proper list-colourings.
-/
theorem hardStep_reversible [Nonempty V] [Nonempty C]
    {F : HardListInstance V C} {X Y : V → C}
    (hX : F.IsProper X) (hY : F.IsProper Y) :
    (hardStep F X).w Y = (hardStep F Y).w X := by
  rcases eq_or_ne X Y with rfl | hXY
  · rfl
  · rw [hardStep_w, hardStep_w, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hleft :
        ∑ c : C, ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F X u c).w Y =
          ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F X u (Y u)).w Y := by
      refine Finset.sum_eq_single (Y u) (fun c _ hc => ?_)
        (fun h => absurd (Finset.mem_univ _) h)
      rw [proposalDistribution_eq_zero hXY u c hc, mul_zero]
    have hright :
        ∑ c : C, ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F Y u c).w X =
          ((Fintype.card (V × C) : ℝ))⁻¹ *
            (proposalDistribution F Y u (X u)).w X := by
      refine Finset.sum_eq_single (X u) (fun c _ hc => ?_)
        (fun h => absurd (Finset.mem_univ _) h)
      rw [proposalDistribution_eq_zero hXY.symm u c hc, mul_zero]
    rw [hleft, hright, proposalDistribution_reversible hX hY hXY u]

/-- Uniform probability law on the nonempty proper-colouring fibre. -/
noncomputable def uniformProperFibre (F : HardListInstance V C)
    (hne : ∃ X : V → C, F.IsProper X) : FinDist (V → C) where
  w := fun X => if F.IsProper X then
    (((Finset.univ.filter fun Y : V → C => F.IsProper Y).card : ℝ))⁻¹ else 0
  nonneg := fun X => by split <;> positivity
  sum_one := by
    obtain ⟨X, hX⟩ := hne
    have hpos : 0 < (Finset.univ.filter fun Y : V → C => F.IsProper Y).card := by
      exact Finset.card_pos.mpr ⟨X, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hX⟩⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
      mul_inv_cancel₀ (by exact_mod_cast hpos.ne')]

@[simp]
lemma uniformProperFibre_w (F : HardListInstance V C)
    (hne : ∃ X : V → C, F.IsProper X) (X : V → C) :
    (uniformProperFibre F hne).w X = if F.IsProper X then
      (((Finset.univ.filter fun Y : V → C => F.IsProper Y).card : ℝ))⁻¹ else 0 := rfl

/-- The hard Vigoda transition preserves the uniform hard-fibre law. -/
theorem hardStep_stationary [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (hne : ∃ X : V → C, F.IsProper X) :
    FinDist.IsStationary (hardStep F) (uniformProperFibre F hne) := by
  apply FinDist.ext
  funext Y
  simp only [FinDist.bind_w]
  by_cases hY : F.IsProper Y
  · have hterm : ∀ X : V → C,
        (uniformProperFibre F hne).w X * (hardStep F X).w Y =
          (uniformProperFibre F hne).w X * (hardStep F Y).w X := by
      intro X
      by_cases hX : F.IsProper X
      · rw [hardStep_reversible hX hY]
      · rw [uniformProperFibre_w, if_neg hX, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun X _ => hterm X]
    have hsum :
        ∑ X : V → C, (uniformProperFibre F hne).w X * (hardStep F Y).w X =
          (((Finset.univ.filter fun Z : V → C => F.IsProper Z).card : ℝ))⁻¹ := by
      simp only [uniformProperFibre_w, ite_mul, zero_mul]
      rw [← Finset.sum_filter]
      rw [← Finset.mul_sum]
      have hfull :
          ∑ X ∈ Finset.univ.filter (fun Z : V → C => F.IsProper Z),
              (hardStep F Y).w X = ∑ X : V → C, (hardStep F Y).w X := by
        refine Finset.sum_subset (Finset.filter_subset _ _) ?_
        intro X _ hX
        apply hardStep_support hY
        intro hp
        exact hX (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
      rw [hfull, FinDist.sum_one, mul_one]
    rw [hsum, uniformProperFibre_w, if_pos hY]
  · have hterm : ∀ X : V → C,
        (uniformProperFibre F hne).w X * (hardStep F X).w Y = 0 := by
      intro X
      by_cases hX : F.IsProper X
      · rw [hardStep_support hX hY, mul_zero]
      · rw [uniformProperFibre_w, if_neg hX, zero_mul]
    rw [Finset.sum_eq_zero fun X _ => hterm X,
      uniformProperFibre_w, if_neg hY]

/-- Package the concrete hard Vigoda transition as the abstract hard-fibre
kernel consumed by `PinningData.softKernel`.  The sole bridge assumption says
that the supplied list instance represents exactly the inequalities selected
by the active set; there is no dynamical hypothesis left to prove. -/
noncomputable def hardFibreKernelOfListInstance [Nonempty V] [Nonempty C]
    (I : PinningData V C) (A : Finset (PinningData.Constraint I))
    (F : HardListInstance V C)
    (hrep : ∀ X : V → C, F.IsProper X ↔ I.ActiveCompatible X A) :
    PinningData.HardFibreKernel I A where
  kernel := hardStep F
  supported := by
    intro X Y hX hY
    apply hardStep_support ((hrep X).mpr hX)
    exact fun h => hY ((hrep Y).mp h)
  stationary := by
    intro hne
    have hproper : ∃ X : V → C, F.IsProper X := by
      obtain ⟨X, hX⟩ := hne
      exact ⟨X, (hrep X).mpr (Finset.mem_filter.mp hX).2⟩
    have hstat := hardStep_stationary F hproper
    have hfibres :
        I.uniformHardFibre A hne = uniformProperFibre F hproper := by
      apply FinDist.ext
      funext X
      rw [I.uniformHardFibre_w, uniformProperFibre_w]
      have hcard : (I.compatibleColorings A).card =
          (Finset.univ.filter fun Y : V → C => F.IsProper Y).card := by
        congr 1
        ext Y
        simp [PinningData.compatibleColorings, hrep Y]
      rw [hcard]
      exact if_congr (hrep X).symm rfl rfl
    rw [hfibres]
    exact hstat

/-! ## The concrete list instance selected by an active set -/

/-- Graph formed by the active free-edge occurrences. -/
noncomputable def activeGraph (I : PinningData V C)
    (A : Finset (PinningData.Constraint I)) : SimpleGraph V where
  Adj u v := ∃ e : PinningData.FreeEdge I,
    (Sum.inl e : PinningData.Constraint I) ∈ A ∧ e.1 = s(u, v)
  symm := ⟨by
    rintro u v ⟨e, he, hvalue⟩
    exact ⟨e, he, hvalue.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by
    intro u
    rintro ⟨e, _, hvalue⟩
    have he := e.2
    rw [hvalue] at he
    simp at he⟩

/-- Colours not deleted by any active labelled boundary occurrence. -/
noncomputable def activeList (I : PinningData V C)
    (A : Finset (PinningData.Constraint I)) (u : V) : Finset C :=
  Finset.univ.filter fun c =>
    ¬ ∃ i : Fin (I.boundaryCount u c),
      (Sum.inr ⟨u, c, i⟩ : PinningData.Constraint I) ∈ A

/-- The hard list instance represented by an active set. -/
noncomputable def activeHardListInstance (I : PinningData V C)
    (A : Finset (PinningData.Constraint I)) : HardListInstance V C where
  graph := activeGraph I A
  list := activeList I A

/-- Exact bridge between the constraint-occurrence definition of an active
fibre and ordinary proper list-colourings. -/
theorem activeHardListInstance_isProper_iff
    (I : PinningData V C) (A : Finset (PinningData.Constraint I)) (X : V → C) :
    (activeHardListInstance I A).IsProper X ↔ I.ActiveCompatible X A := by
  constructor
  · rintro ⟨hedge, hlist⟩ k hk
    rcases k with e | b
    · rcases e with ⟨e, heI⟩
      induction e using Sym2.ind with
      | _ u v =>
          have hadj : (activeGraph I A).Adj u v :=
            ⟨⟨s(u, v), heI⟩, hk, rfl⟩
          exact hedge u v hadj
    · rcases b with ⟨u, c, i⟩
      have hallowed := hlist u
      simp only [activeHardListInstance, activeList, Finset.mem_filter,
        Finset.mem_univ, true_and] at hallowed
      intro huc
      apply hallowed
      subst huc
      exact ⟨i, hk⟩
  · intro hactive
    constructor
    · intro u v hadj
      rcases hadj with ⟨e, heA, hvalue⟩
      have hsatisfied := hactive (Sum.inl e) heA
      dsimp only [PinningData.constraintSatisfied] at hsatisfied
      rw [hvalue] at hsatisfied
      exact hsatisfied
    · intro u
      simp only [activeHardListInstance, activeList, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rintro ⟨i, hi⟩
      have hsatisfied := hactive
        (Sum.inr ⟨u, X u, i⟩ : PinningData.Constraint I) hi
      exact hsatisfied rfl

/-- The actual active-set Vigoda kernel, with all hard-fibre obligations
discharged by the concrete list representation above. -/
noncomputable def activeVigodaHardFibreKernel [Nonempty V] [Nonempty C]
    (I : PinningData V C) (A : Finset (PinningData.Constraint I)) :
    PinningData.HardFibreKernel I A :=
  hardFibreKernelOfListInstance I A (activeHardListInstance I A)
    (activeHardListInstance_isProper_iff I A)

/-- The concrete soft Vigoda kernel obtained by sampling active constraints
and then applying `hardStep` to their induced list instance. -/
noncomputable def softVigodaKernel [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (V → C) → FinDist (V → C) :=
  I.softKernel x hx0 hx1 fun A => activeVigodaHardFibreKernel I A

/-- The concrete soft Vigoda kernel has the Potts Gibbs law as stationary
law; no fibre-stationarity hypothesis remains. -/
theorem softVigodaKernel_stationary [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    FinDist.IsStationary (softVigodaKernel I x hx0 hx1)
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) :=
  I.softKernel_stationary x hx0 hx1 fun A => activeVigodaHardFibreKernel I A

/-! ## The exact root-local interface consumed by the allocation proof -/

/-- Two active hard instances generated from adjacent configurations agree
away from their unique disagreement vertex.  The extra two fields record the
regular-colour incident-edge agreement and the fact that one-sided root list
deletions can involve only the two root colours. -/
structure RootLocalPair (FX FY : HardListInstance V C)
    (X Y : V → C) (v : V) (a b : C) : Prop where
  X_root : X v = a
  Y_root : Y v = b
  colours_ne : a ≠ b
  agree_off_root : ∀ u, u ≠ v → X u = Y u
  properX : FX.IsProper X
  properY : FY.IsProper Y
  offRoot_edge_iff : ∀ u w, u ≠ v → w ≠ v →
    (FX.graph.Adj u w ↔ FY.graph.Adj u w)
  offRoot_list_eq : ∀ u, u ≠ v → FX.list u = FY.list u
  regular_root_edge_iff : ∀ u c, u ≠ v → X u = c → c ≠ a → c ≠ b →
    (FX.graph.Adj v u ↔ FY.graph.Adj v u)
  root_list_regular_iff : ∀ c, c ≠ a → c ≠ b →
    (c ∈ FX.list v ↔ c ∈ FY.list v)

/-- For a regular colour, alternating adjacency agrees away from the root. -/
lemma RootLocalPair.alternatingAdj_iff_off_root
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c₁ c₂ : C}
    (h : RootLocalPair FX FY X Y v a b)
    {u w : V} (hu : u ≠ v) (hw : w ≠ v) :
    alternatingAdj FX.graph X c₁ c₂ u w ↔ alternatingAdj FY.graph Y c₁ c₂ u w := by
  unfold alternatingAdj
  rw [h.offRoot_edge_iff u w hu hw, h.agree_off_root u hu, h.agree_off_root w hw]

/-- Alternating adjacency in the graph with the root removed. -/
def offRootAlternatingAdj (F : HardListInstance V C) (X : V → C)
    (v : V) (c₁ c₂ : C) (u w : V) : Prop :=
  u ≠ v ∧ w ≠ v ∧ alternatingAdj F.graph X c₁ c₂ u w

/-- A two-colour component computed after deleting the root. -/
noncomputable def offRootComponent (F : HardListInstance V C) (X : V → C)
    (v : V) (c₁ c₂ : C) (u : V) : Finset V :=
  Finset.univ.filter fun w =>
    Relation.ReflTransGen (offRootAlternatingAdj F X v c₁ c₂) u w

/-- The two active instances have exactly the same two-colour components after
the root is deleted. -/
lemma RootLocalPair.offRootComponent_eq
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c₁ c₂ : C}
    (h : RootLocalPair FX FY X Y v a b) (u : V) :
    offRootComponent FX X v c₁ c₂ u = offRootComponent FY Y v c₁ c₂ u := by
  have hrel : offRootAlternatingAdj FX X v c₁ c₂ =
      offRootAlternatingAdj FY Y v c₁ c₂ := by
    funext w z
    apply propext
    unfold offRootAlternatingAdj
    constructor
    · rintro ⟨hw, hz, hstep⟩
      exact ⟨hw, hz, (h.alternatingAdj_iff_off_root hw hz).mp hstep⟩
    · rintro ⟨hw, hz, hstep⟩
      exact ⟨hw, hz, (h.alternatingAdj_iff_off_root hw hz).mpr hstep⟩
  unfold offRootComponent
  rw [hrel]

/-- For a regular colour, the `{a,c}` component relation in the two active
instances is identical along every path avoiding the root. -/
lemma RootLocalPair.path_iff_off_root
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b)
    (_hcA : c ≠ a) (hcB : c ≠ b) {u w : V}
    (hu : u ≠ v)
    (hpathAvoids : ∀ z,
      Relation.ReflTransGen (alternatingAdj FX.graph X a c) u z → z ≠ v) :
    Relation.ReflTransGen (alternatingAdj FX.graph X a c) u w ↔
      Relation.ReflTransGen (alternatingAdj FY.graph Y a c) u w := by
  constructor
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail y z hyz hstep ih =>
        have hy : y ≠ v := hpathAvoids y hyz
        have hz : z ≠ v := hpathAvoids z (hyz.tail hstep)
        exact ih.tail ((h.alternatingAdj_iff_off_root hy hz).mp hstep)
  · intro hp
    -- The reverse path stays off-root because its edges are converted one by
    -- one; `hpathAvoids` is applied to the converted prefix.
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail y z hyz hstep ih =>
        have hy : y ≠ v := hpathAvoids y ih
        by_cases hz : z = v
        · subst hz
          exfalso
          rcases hstep.2 with hstep | hstep
          · exact hcB (hstep.2.symm.trans h.Y_root)
          · exact h.colours_ne (hstep.2.symm.trans h.Y_root)
        · exact ih.tail ((h.alternatingAdj_iff_off_root hy hz).mpr hstep)


/-! ## Coupled activations from common Bernoulli bits -/

/-- If `B` records the common successful Bernoulli bits, the active set at a
colouring is obtained by retaining exactly the constraints eligible there. -/
noncomputable def activeSetFromBits (I : PinningData V C)
    (B : Finset (PinningData.Constraint I)) (X : V → C) :
    Finset (PinningData.Constraint I) := B ∩ I.eligibleSet X

@[simp]
lemma mem_activeSetFromBits (I : PinningData V C)
    (B : Finset (PinningData.Constraint I)) (X : V → C)
    (k : PinningData.Constraint I) :
    k ∈ activeSetFromBits I B X ↔ k ∈ B ∧ I.constraintSatisfied X k := by
  simp [activeSetFromBits]

lemma activeSetFromBits_compatible (I : PinningData V C)
    (B : Finset (PinningData.Constraint I)) (X : V → C) :
    I.ActiveCompatible X (activeSetFromBits I B X) := by
  intro k hk
  exact (mem_activeSetFromBits I B X k).mp hk |>.2

private lemma active_free_edge_satisfaction_iff
    (I : PinningData V C) (B : Finset (PinningData.Constraint I))
    (X Y : V → C) (u w : V) (hu : X u = Y u) (hw : X w = Y w)
    (e : PinningData.FreeEdge I) (hvalue : e.1 = s(u, w)) :
    (Sum.inl e : PinningData.Constraint I) ∈ activeSetFromBits I B X ↔
      (Sum.inl e : PinningData.Constraint I) ∈ activeSetFromBits I B Y := by
  simp only [mem_activeSetFromBits, and_congr_right_iff]
  intro _
  change Sym2.lift _ e.1 ↔ Sym2.lift _ e.1
  rw [hvalue]
  simp only [Sym2.lift_mk]
  rw [hu, hw]

private lemma active_boundary_satisfaction_iff
    (I : PinningData V C) (B : Finset (PinningData.Constraint I))
    (X Y : V → C) (u : V) (c : C) (hu : X u = Y u)
    (i : Fin (I.boundaryCount u c)) :
    (Sum.inr ⟨u, c, i⟩ : PinningData.Constraint I) ∈ activeSetFromBits I B X ↔
      (Sum.inr ⟨u, c, i⟩ : PinningData.Constraint I) ∈ activeSetFromBits I B Y := by
  simp only [mem_activeSetFromBits, PinningData.constraintSatisfied,
    and_congr_right_iff]
  intro _
  rw [hu]

/-- The common-bit construction produces exactly the root-local pair used by
the component proof.  This is the formal version of the paper's coupled-
activation root-locality lemma. -/
theorem rootLocalPair_activeSetFromBits
    (I : PinningData V C) (B : Finset (PinningData.Constraint I))
    (X Y : V → C) (v : V) (a b : C)
    (hXa : X v = a) (hYb : Y v = b) (hab : a ≠ b)
    (hagree : ∀ u, u ≠ v → X u = Y u) :
    RootLocalPair
      (activeHardListInstance I (activeSetFromBits I B X))
      (activeHardListInstance I (activeSetFromBits I B Y))
      X Y v a b := by
  refine
    { X_root := hXa
      Y_root := hYb
      colours_ne := hab
      agree_off_root := hagree
      properX := (activeHardListInstance_isProper_iff I _ X).mpr
        (activeSetFromBits_compatible I B X)
      properY := (activeHardListInstance_isProper_iff I _ Y).mpr
        (activeSetFromBits_compatible I B Y)
      offRoot_edge_iff := ?_
      offRoot_list_eq := ?_
      regular_root_edge_iff := ?_
      root_list_regular_iff := ?_ }
  · intro u w hu hw
    constructor
    · rintro ⟨e, he, hvalue⟩
      exact ⟨e,
        (active_free_edge_satisfaction_iff I B X Y u w
          (hagree u hu) (hagree w hw) e hvalue).mp he,
        hvalue⟩
    · rintro ⟨e, he, hvalue⟩
      exact ⟨e,
        (active_free_edge_satisfaction_iff I B X Y u w
          (hagree u hu) (hagree w hw) e hvalue).mpr he,
        hvalue⟩
  · intro u hu
    ext c
    simp only [activeHardListInstance, activeList, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro hX hcontra
      obtain ⟨i, hi⟩ := hcontra
      apply hX
      exact ⟨i, (active_boundary_satisfaction_iff I B X Y u c
        (hagree u hu) i).mpr hi⟩
    · intro hY hcontra
      obtain ⟨i, hi⟩ := hcontra
      apply hY
      exact ⟨i, (active_boundary_satisfaction_iff I B X Y u c
        (hagree u hu) i).mp hi⟩
  · intro u c hu huc hca hcb
    constructor
    · rintro ⟨e, he, hvalue⟩
      refine ⟨e, ?_, hvalue⟩
      rw [mem_activeSetFromBits] at he ⊢
      refine ⟨he.1, ?_⟩
      change Sym2.lift _ e.1
      rw [hvalue]
      simp only [Sym2.lift_mk]
      rw [hYb, ← hagree u hu, huc]
      exact hcb.symm
    · rintro ⟨e, he, hvalue⟩
      refine ⟨e, ?_, hvalue⟩
      rw [mem_activeSetFromBits] at he ⊢
      refine ⟨he.1, ?_⟩
      change Sym2.lift _ e.1
      rw [hvalue]
      simp only [Sym2.lift_mk]
      rw [hXa, huc]
      exact hca.symm
  · intro c hca hcb
    simp only [activeHardListInstance, activeList, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hXc : X v ≠ c := by simpa [hXa] using hca.symm
    have hYc : Y v ≠ c := by simpa [hYb] using hcb.symm
    simp only [mem_activeSetFromBits, PinningData.constraintSatisfied]
    constructor
    · rintro hnot ⟨i, hi, _⟩
      exact hnot ⟨i, hi, hXc⟩
    · rintro hnot ⟨i, hi, _⟩
      exact hnot ⟨i, hi, hYc⟩

/-! ## Hamming estimates for partial-coupling completion -/

/-- If the starting pair differs only at `v`, and each output changes only on
the indicated set, then every output disagreement lies in their union and
`v`. -/
lemma hamCard_flip_bound {X Y X' Y' : V → C} {v : V} {SX SY : Finset V}
    (hXY : ∀ w, w ≠ v → X w = Y w)
    (hX' : ∀ w, w ∉ SX → X' w = X w)
    (hY' : ∀ w, w ∉ SY → Y' w = Y w) :
    hamCard X' Y' ≤ 1 + SX.card + SY.card := by
  have hsub : (Finset.univ.filter fun w => X' w ≠ Y' w) ⊆ insert v (SX ∪ SY) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_insert, Finset.mem_union]
    by_contra hcon
    push Not at hcon
    obtain ⟨hwv, hwX, hwY⟩ := hcon
    rw [hX' w hwX, hY' w hwY, hXY w hwv] at hw
    exact hw rfl
  calc
    hamCard X' Y' = (Finset.univ.filter fun w => X' w ≠ Y' w).card := rfl
    _ ≤ (insert v (SX ∪ SY)).card := Finset.card_le_card hsub
    _ ≤ 1 + SX.card + SY.card := by
      have hi := Finset.card_insert_le v (SX ∪ SY)
      have hu := Finset.card_union_le SX SY
      omega

lemma hamCard_flip_stay_le {F : HardListInstance V C} {X Y : V → C} {v : V}
    (hXY : ∀ w, w ≠ v → X w = Y w) (u : V) (c : C) :
    hamCard (flipConfiguration X (flipSet F.graph X u c) (X u) c) Y
      ≤ 1 + (flipSet F.graph X u c).card := by
  have h := hamCard_flip_bound (X := X) (Y := Y)
    (X' := flipConfiguration X (flipSet F.graph X u c) (X u) c) (Y' := Y)
    (v := v) (SX := flipSet F.graph X u c) (SY := ∅)
    hXY (fun w hw => flipConfiguration_of_not_mem hw) (fun _ _ => rfl)
  simpa using h

end Vigoda
end PottsCI
