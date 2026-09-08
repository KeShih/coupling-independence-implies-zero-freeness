import PottsCI.FinDist
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Tactic.Push

/-!
# Hamming distance, path coupling, and the total-variation bound

The Hamming metric on configuration spaces `V → C`, the path-coupling
argument (one-step contraction for adjacent configurations extends to
arbitrary pairs, and then to arbitrary starting distributions), and the
maximal-coupling bound `W ≤ B·‖μ − ν‖₁/2` used for the `x → 0` limit in
Proposition 5.2 of the paper.
-/

namespace PottsCI

open Finset

variable {V : Type*} {C : Type*} [Fintype V] [DecidableEq C]

/-- Hamming distance between two configurations, as a natural number. -/
def hamCard (x y : V → C) : ℕ := (Finset.univ.filter fun u => x u ≠ y u).card

/-- Hamming distance as a real-valued cost function; this is the `Ham` of the
paper, and `FinDist.W ham` is the paper's `W_Ham`. -/
def ham (x y : V → C) : ℝ := hamCard x y

lemma ham_nonneg : ∀ x y : V → C, 0 ≤ ham x y := fun _ _ => Nat.cast_nonneg _

lemma hamCard_self (x : V → C) : hamCard x x = 0 := by simp [hamCard]

lemma ham_self (x : V → C) : ham x x = 0 := by simp [ham, hamCard_self]

lemma hamCard_comm (x y : V → C) : hamCard x y = hamCard y x := by
  unfold hamCard
  congr 1
  ext u
  simp [ne_comm]

lemma ham_comm (x y : V → C) : ham x y = ham y x := by
  unfold ham; rw [hamCard_comm]

lemma hamCard_eq_zero {x y : V → C} (h : hamCard x y = 0) : x = y := by
  funext u
  by_contra hne
  have hu : u ∈ Finset.univ.filter fun v => x v ≠ y v := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hne
  rw [hamCard, Finset.card_eq_zero] at h
  rw [h] at hu
  exact absurd hu (Finset.notMem_empty u)

lemma hamCard_triangle [DecidableEq V] (x y z : V → C) :
    hamCard x z ≤ hamCard x y + hamCard y z := by
  unfold hamCard
  have hsub : (Finset.univ.filter fun u => x u ≠ z u)
      ⊆ (Finset.univ.filter fun u => x u ≠ y u) ∪ (Finset.univ.filter fun u => y u ≠ z u) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hcon
    push Not at hcon
    exact hu (hcon.1.trans hcon.2)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

lemma ham_triangle [DecidableEq V] (x y z : V → C) : ham x z ≤ ham x y + ham y z := by
  unfold ham
  exact_mod_cast hamCard_triangle x y z

lemma hamCard_le_card (x y : V → C) : hamCard x y ≤ Fintype.card V := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ]

lemma ham_le_card (x y : V → C) : ham x y ≤ Fintype.card V := by
  unfold ham
  exact_mod_cast hamCard_le_card x y

/-- Going one step along a Hamming geodesic: if `x` and `y` are at Hamming
distance `k+1`, there is `z` adjacent to `x` with `hamCard z y = k`. -/
lemma exists_intermediate [DecidableEq V] {x y : V → C} {k : ℕ} (h : hamCard x y = k + 1) :
    ∃ z : V → C, hamCard x z = 1 ∧ hamCard z y = k := by
  have hne : (Finset.univ.filter fun u => x u ≠ y u).Nonempty := by
    rw [← Finset.card_pos, ← hamCard, h]
    exact Nat.succ_pos k
  obtain ⟨u, hu⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  refine ⟨Function.update x u (y u), ?_, ?_⟩
  · have hset : (Finset.univ.filter fun v => x v ≠ Function.update x u (y u) v) = {u} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Function.update_apply]
      rcases eq_or_ne v u with rfl | hv
      · simpa using hu
      · simp [hv]
    rw [hamCard, hset, Finset.card_singleton]
  · have hset : (Finset.univ.filter fun v => Function.update x u (y u) v ≠ y v)
        = (Finset.univ.filter fun v => x v ≠ y v).erase u := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        Function.update_apply]
      rcases eq_or_ne v u with rfl | hv
      · simp
      · simp [hv]
    rw [hamCard, hset, Finset.card_erase_of_mem (by simpa using hu), ← hamCard, h]
    omega

/-- **Path coupling, pointwise form.**  A one-step transport bound `c` for
adjacent configurations extends to `c · Ham(x,y)` for arbitrary pairs, by
composing couplings along a Hamming geodesic. -/
lemma W_ham_le_of_adjacent [DecidableEq V] [Fintype C]
    (K : (V → C) → FinDist (V → C)) {c : ℝ}
    (h1 : ∀ x y : V → C, hamCard x y = 1 → FinDist.W ham (K x) (K y) ≤ c) :
    ∀ x y : V → C, FinDist.W ham (K x) (K y) ≤ c * hamCard x y := by
  have main : ∀ k : ℕ, ∀ x y : V → C, hamCard x y = k →
      FinDist.W ham (K x) (K y) ≤ c * k := by
    intro k
    induction k with
    | zero =>
      intro x y hxy
      have hxy' : x = y := hamCard_eq_zero hxy
      subst hxy'
      rw [FinDist.W_self ham_nonneg ham_self]
      simp
    | succ k ih =>
      intro x y hxy
      obtain ⟨z, hz1, hzk⟩ := exists_intermediate hxy
      have htri := FinDist.W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle
        (K x) (K z) (K y)
      have h2 := h1 x z hz1
      have h3 := ih z y hzk
      have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      calc FinDist.W ham (K x) (K y)
          ≤ FinDist.W ham (K x) (K z) + FinDist.W ham (K z) (K y) := htri
        _ ≤ c + c * k := add_le_add h2 h3
        _ = c * ((k : ℝ) + 1) := by ring
        _ = c * ((k + 1 : ℕ) : ℝ) := by rw [hcast]
  intro x y
  exact main (hamCard x y) x y rfl

/-- **Path coupling for measures**: adjacent one-step contraction lifts to
arbitrary starting distributions. -/
lemma W_ham_bind_contract [DecidableEq V] [Fintype C]
    (K : (V → C) → FinDist (V → C)) {c : ℝ} (hc : 0 ≤ c)
    (h1 : ∀ x y : V → C, hamCard x y = 1 → FinDist.W ham (K x) (K y) ≤ c)
    (α β : FinDist (V → C)) :
    FinDist.W ham (α.bind K) (β.bind K) ≤ c * FinDist.W ham α β := by
  refine FinDist.W_bind_contract ham_nonneg ham_nonneg hc K ?_ α β
  intro x y
  exact W_ham_le_of_adjacent K h1 x y

/-! ## The maximal-coupling (total variation) bound -/

/-- Transport cost is at most `B/2` times the `ℓ¹`-distance of the weight
functions, for any cost bounded by `B` and vanishing on the diagonal.  Proof by
the maximal coupling: couple the common mass `min μ ν` diagonally and the
residual masses independently. -/
lemma W_le_half_l1 {S : Type*} [Fintype S] [DecidableEq S] {d : S → S → ℝ} {B : ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0) (hB : ∀ x y, d x y ≤ B)
    (μ ν : FinDist S) :
    FinDist.W d μ ν ≤ B * (∑ x, |μ.w x - ν.w x|) / 2 := by
  classical
  set m : S → ℝ := fun x => min (μ.w x) (ν.w x) with hm
  set t : ℝ := ∑ x, (μ.w x - m x) with htdef
  have hm0 : ∀ x, 0 ≤ m x := fun x => le_min (μ.nonneg x) (ν.nonneg x)
  have hmμ : ∀ x, m x ≤ μ.w x := fun x => min_le_left _ _
  have hmν : ∀ x, m x ≤ ν.w x := fun x => min_le_right _ _
  have hμm0 : ∀ x, 0 ≤ μ.w x - m x := fun x => sub_nonneg.mpr (hmμ x)
  have hνm0 : ∀ x, 0 ≤ ν.w x - m x := fun x => sub_nonneg.mpr (hmν x)
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun x _ => hμm0 x
  -- `t` is also the total residual mass on the `ν` side
  have htν : t = ∑ x, (ν.w x - m x) := by
    rw [htdef, Finset.sum_sub_distrib, Finset.sum_sub_distrib, μ.sum_one, ν.sum_one]
  -- `∑ |μ - ν| = 2 t`
  have habs : ∀ x, |μ.w x - ν.w x| = (μ.w x - m x) + (ν.w x - m x) := by
    intro x
    rcases le_total (μ.w x) (ν.w x) with h | h
    · rw [abs_of_nonpos (by linarith)]
      simp only [hm]
      rw [min_eq_left h]
      ring
    · rw [abs_of_nonneg (by linarith)]
      simp only [hm]
      rw [min_eq_right h]
      ring
  have hl1 : ∑ x, |μ.w x - ν.w x| = 2 * t := by
    calc ∑ x, |μ.w x - ν.w x| = ∑ x, ((μ.w x - m x) + (ν.w x - m x)) :=
          Finset.sum_congr rfl fun x _ => habs x
      _ = t + t := by rw [Finset.sum_add_distrib, ← htdef, ← htν]
      _ = 2 * t := by ring
  rcases eq_or_lt_of_le ht0 with ht | ht
  · -- no residual mass: `μ = ν`
    have hμν : μ = ν := by
      have hzero : ∀ x ∈ Finset.univ, μ.w x - m x = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hμm0 x).mp (htdef.symm.trans ht.symm)
      have hzero' : ∀ x ∈ Finset.univ, ν.w x - m x = 0 := by
        have hn : (0:ℝ) = ∑ x, (ν.w x - m x) := ht.trans htν
        exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hνm0 x).mp hn.symm
      ext x
      have h1 := hzero x (Finset.mem_univ x)
      have h2 := hzero' x (Finset.mem_univ x)
      linarith
    subst hμν
    rw [FinDist.W_self hd hd0]
    have hz : ∑ x, |μ.w x - μ.w x| = 0 := by simp
    rw [hz]
    simp
  · -- positive residual mass: exhibit the maximal coupling
    have htne : t ≠ 0 := ne_of_gt ht
    have hγ0 : ∀ x y : S, 0 ≤ (if y = x then m x else 0) + (μ.w x - m x) * (ν.w y - m y) / t := by
      intro x y
      refine add_nonneg ?_ (div_nonneg (mul_nonneg (hμm0 x) (hνm0 y)) ht0)
      split
      · exact hm0 x
      · exact le_rfl
    have hrow : ∀ x : S,
        ∑ y, ((if y = x then m x else 0) + (μ.w x - m x) * (ν.w y - m y) / t) = μ.w x := by
      intro x
      rw [Finset.sum_add_distrib]
      have h1 : ∑ y : S, (if y = x then m x else 0) = m x := by simp
      have h2 : ∑ y : S, (μ.w x - m x) * (ν.w y - m y) / t = μ.w x - m x := by
        rw [← Finset.sum_div, ← Finset.mul_sum, ← htν, mul_div_assoc, div_self htne, mul_one]
      rw [h1, h2]
      ring
    have hcol : ∀ y : S,
        ∑ x, ((if y = x then m x else 0) + (μ.w x - m x) * (ν.w y - m y) / t) = ν.w y := by
      intro y
      rw [Finset.sum_add_distrib]
      have h1 : ∑ x : S, (if y = x then m x else 0) = m y := by simp
      have h2 : ∑ x : S, (μ.w x - m x) * (ν.w y - m y) / t = ν.w y - m y := by
        rw [← Finset.sum_div, ← Finset.sum_mul, ← htdef, mul_comm, mul_div_assoc,
          div_self htne, mul_one]
      rw [h1, h2]
      ring
    set γ : FinDist.Coupling μ ν :=
      ⟨fun x y => (if y = x then m x else 0) + (μ.w x - m x) * (ν.w y - m y) / t,
        hγ0, hrow, hcol⟩ with hγdef
    have hcost : γ.cost d ≤ B * t := by
      have hterm : ∀ x y : S, γ.w x y * d x y
          = (if y = x then m x else 0) * d x y
            + (μ.w x - m x) * (ν.w y - m y) / t * d x y := by
        intro x y
        show ((if y = x then m x else 0) + (μ.w x - m x) * (ν.w y - m y) / t) * d x y = _
        ring
      have hpart1 : ∑ x, ∑ y, (if y = x then m x else 0) * d x y = 0 := by
        refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
        rcases eq_or_ne y x with rfl | h
        · rw [if_pos rfl, hd0, mul_zero]
        · rw [if_neg h, zero_mul]
      have hpart2 : ∑ x, ∑ y, (μ.w x - m x) * (ν.w y - m y) / t * d x y ≤ B * t := by
        have hb : ∀ x y : S, (μ.w x - m x) * (ν.w y - m y) / t * d x y
            ≤ (μ.w x - m x) * (ν.w y - m y) / t * B := fun x y =>
          mul_le_mul_of_nonneg_left (hB x y)
            (div_nonneg (mul_nonneg (hμm0 x) (hνm0 y)) ht0)
        calc ∑ x, ∑ y, (μ.w x - m x) * (ν.w y - m y) / t * d x y
            ≤ ∑ x, ∑ y, (μ.w x - m x) * (ν.w y - m y) / t * B :=
              Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hb x y
          _ = (∑ x, (μ.w x - m x)) * (∑ y, (ν.w y - m y)) * t⁻¹ * B := by
              simp_rw [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]
              conv_rhs => rw [Finset.sum_mul]
          _ = t * t * t⁻¹ * B := by rw [← htdef, ← htν]
          _ = B * t := by field_simp
      calc γ.cost d = ∑ x, ∑ y, γ.w x y * d x y := rfl
        _ = ∑ x, ∑ y, ((if y = x then m x else 0) * d x y
              + (μ.w x - m x) * (ν.w y - m y) / t * d x y) :=
            Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y
        _ = (∑ x, ∑ y, (if y = x then m x else 0) * d x y)
              + ∑ x, ∑ y, (μ.w x - m x) * (ν.w y - m y) / t * d x y := by
            simp_rw [Finset.sum_add_distrib]
        _ ≤ 0 + B * t := add_le_add hpart1.le hpart2
        _ = B * t := by ring
    calc FinDist.W d μ ν ≤ γ.cost d := FinDist.W_le_cost hd γ
      _ ≤ B * t := hcost
      _ = B * (∑ x, |μ.w x - ν.w x|) / 2 := by rw [hl1]; ring

end PottsCI
