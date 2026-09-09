import CI2ZF.Coupling.Foundations.FiniteCoupling
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Countable endpoint-slot activities

The following summation and fibre-removal results apply to any countable
probability weights. They justify the activity, fibre, and slack calculations
in the Edge-Potts appendix. Existence of weights whose distinct-slot moments
are `x ^ (k.choose 2)` is not asserted here: it requires the deformed
exponential zero and factorization theorems used in the paper.
-/

namespace CI2ZF.Appendix.Edge

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

/-- Nonnegative probability weights on the countable slot labels. -/
structure SlotWeights where
  weight : ℕ → ℝ
  nonneg : ∀ r, 0 ≤ weight r
  hasSum_one : HasSum weight 1

namespace SlotWeights

lemma summable (κ : SlotWeights) : Summable κ.weight := κ.hasSum_one.summable

@[simp] lemma tsum_eq_one (κ : SlotWeights) : ∑' r, κ.weight r = 1 :=
  κ.hasSum_one.tsum_eq

lemma le_one (κ : SlotWeights) (r : ℕ) : κ.weight r ≤ 1 := by
  simpa using κ.summable.le_tsum r (fun s _ => κ.nonneg s)

lemma pair_hasSum (κ : SlotWeights) :
    HasSum (fun p : ℕ × ℕ => κ.weight p.1 * κ.weight p.2) 1 := by
  simpa using κ.hasSum_one.mul κ.hasSum_one
    (κ.summable.mul_of_nonneg κ.summable κ.nonneg κ.nonneg)

end SlotWeights

variable {C : Type*} [Fintype C]

/-- The two endpoint slots use a fixed original colour-pinning exponent. -/
def slotActivity (κ : SlotWeights) (x : ℝ) (b : C → ℕ)
    (ξ : C × (ℕ × ℕ)) : ℝ := x ^ b ξ.1 * κ.weight ξ.2.1 * κ.weight ξ.2.2

lemma slotActivity_nonneg (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x)
    (b : C → ℕ) (ξ : C × (ℕ × ℕ)) : 0 ≤ slotActivity κ x b ξ :=
  mul_nonneg (mul_nonneg (pow_nonneg hx _) (κ.nonneg _)) (κ.nonneg _)

lemma slotActivity_hasSum (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x) (b : C → ℕ) :
    HasSum (slotActivity κ x b) (∑ c, x ^ b c) := by
  have hc : HasSum (fun c => x ^ b c) (∑ c, x ^ b c) := hasSum_fintype _
  have hp := κ.pair_hasSum
  have hs := hc.mul hp (hc.summable.mul_of_nonneg hp.summable
    (fun c => pow_nonneg hx _) (fun p => mul_nonneg (κ.nonneg _) (κ.nonneg _)))
  change HasSum (fun ξ : C × (ℕ × ℕ) => x ^ b ξ.1 * κ.weight ξ.2.1 * κ.weight ξ.2.2) _
  simpa only [mul_assoc, mul_one] using hs

lemma slotActivity_total (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x) (b : C → ℕ) :
    ∑' ξ, slotActivity κ x b ξ = ∑ c, x ^ b c :=
  (slotActivity_hasSum κ hx b).tsum_eq

lemma slotActivity_total_le (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (b : C → ℕ) : ∑' ξ, slotActivity κ x b ξ ≤ Fintype.card C := by
  rw [slotActivity_total κ hx]
  calc
    (∑ c, x ^ b c) ≤ ∑ _ : C, (1 : ℝ) :=
      Finset.sum_le_sum fun _ _ => pow_le_one₀ hx hx1
    _ = Fintype.card C := by simp

lemma slotActivity_left_fibre (κ : SlotWeights) (x : ℝ) (b : C → ℕ) (c : C) (r : ℕ) :
    (∑' s, slotActivity κ x b (c, r, s)) = x ^ b c * κ.weight r := by
  simp [slotActivity, tsum_mul_left]

lemma slotActivity_right_fibre (κ : SlotWeights) (x : ℝ) (b : C → ℕ) (c : C) (s : ℕ) :
    (∑' r, slotActivity κ x b (c, r, s)) = x ^ b c * κ.weight s := by
  simp only [slotActivity, tsum_mul_right, tsum_mul_left, κ.tsum_eq_one, mul_one]

lemma slotActivity_left_fibre_le_one (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (b : C → ℕ) (c : C) (r : ℕ) :
    (∑' s, slotActivity κ x b (c, r, s)) ≤ 1 := by
  rw [slotActivity_left_fibre]
  exact mul_le_one₀ (pow_le_one₀ hx hx1) (κ.nonneg r) (κ.le_one r)

lemma slotActivity_right_fibre_le_one (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x)
    (hx1 : x ≤ 1) (b : C → ℕ) (c : C) (s : ℕ) :
    (∑' r, slotActivity κ x b (c, r, s)) ≤ 1 := by
  rw [slotActivity_right_fibre]
  exact mul_le_one₀ (pow_le_one₀ hx hx1) (κ.nonneg s) (κ.le_one s)

lemma one_sub_nat_le_pow {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 1 - n ≤ x ^ n := by
  cases n with
  | zero => simp
  | succ n =>
    have := pow_nonneg hx (n + 1)
    have : (1 : ℝ) - (n + 1 : ℕ) ≤ 0 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
    exact this.trans (pow_nonneg hx _)

/-- The initial total activity loses at most one per pinned incidence. -/
lemma slotActivity_total_lower (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x)
    (b : C → ℕ) :
    (Fintype.card C : ℝ) - (∑ c, b c : ℕ) ≤ ∑' ξ, slotActivity κ x b ξ := by
  rw [slotActivity_total κ hx]
  calc
    (Fintype.card C : ℝ) - (∑ c, b c : ℕ) = ∑ c, (1 - (b c : ℝ)) := by simp
    _ ≤ ∑ c, x ^ b c := Finset.sum_le_sum fun c _ => one_sub_nat_le_pow hx _

/-- The numerical initial slack, once the graph incidence count is known. -/
lemma slotActivity_initial_slack (κ : SlotWeights) {x : ℝ} (hx : 0 ≤ x)
    (b : C → ℕ) {Δ d : ℕ} (hq : 3 * Δ ≤ Fintype.card C)
    (hincidence : d + (∑ c, b c) + 2 ≤ 2 * Δ) :
    Δ + 2 ≤ (∑' ξ, slotActivity κ x b ξ) - d := by
  have htotal := slotActivity_total_lower κ hx b
  have hq' : (3 : ℝ) * Δ ≤ Fintype.card C := by exact_mod_cast hq
  have hi' : (d : ℝ) + (∑ c, b c : ℕ) + 2 ≤ 2 * Δ := by exact_mod_cast hincidence
  linarith

section Removal

variable {S L : Type*}

/-- Total activity after restricting to a set of compatible states. -/
def compatibleWeight (w : S → ℝ) (P : S → Prop) (s : S) : ℝ := if P s then w s else 0

def compatibleMass (w : S → ℝ) (P : S → Prop) : ℝ := ∑' s, compatibleWeight w P s

lemma compatible_summable (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hs : Summable w)
    (P : S → Prop) : Summable (compatibleWeight w P) := by
  classical
  unfold compatibleWeight
  exact Summable.of_nonneg_of_le (fun s => by split_ifs <;> simp only [hw s, le_refl])
    (fun s => by split_ifs <;> simp only [hw s, le_refl]) hs

lemma compatibleMass_nonneg (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (P : S → Prop) :
    0 ≤ compatibleMass w P := by
  classical
  apply tsum_nonneg
  intro s
  unfold compatibleWeight
  split_ifs <;> simp only [hw s, le_refl]

set_option backward.isDefEq.respectTransparency false in
/-- Adding one forbidden endpoint label removes no more than that fibre's
total activity, even on the infinite state space. -/
lemma compatibleMass_forbid_lower (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hs : Summable w) (P : S → Prop) (label : S → L) (ζ : L) :
    compatibleMass w P - compatibleMass w (fun s => label s = ζ) ≤
      compatibleMass w (fun s => P s ∧ label s ≠ ζ) := by
  classical
  have hps := compatible_summable w hw hs P
  have hfs := compatible_summable w hw hs (fun s => label s = ζ)
  have hns := compatible_summable w hw hs (fun s => P s ∧ label s ≠ ζ)
  have hpoint (s : S) : compatibleWeight w P s ≤
      compatibleWeight w (fun z => P z ∧ label z ≠ ζ) s +
      compatibleWeight w (fun z => label z = ζ) s := by
    by_cases hp : P s <;> by_cases hz : label s = ζ <;> simp [compatibleWeight, hp, hz, hw s]
  have hbound := Summable.tsum_le_tsum hpoint hps (hns.add hfs)
  rw [hns.tsum_add hfs] at hbound
  unfold compatibleMass
  linarith

/-- The unit fibre bound and the removal of exactly one adjacent free edge
preserve `M - d`. This is the countable pinning-step slack calculation. -/
lemma compatibleMass_slack_inherited (w : S → ℝ) (hw : ∀ s, 0 ≤ w s)
    (hs : Summable w) (P : S → Prop) (label : S → L) (ζ : L)
    {d slack : ℝ} (hfibre : compatibleMass w (fun s => label s = ζ) ≤ 1)
    (hold : slack ≤ compatibleMass w P - d) :
    slack ≤ compatibleMass w (fun s => P s ∧ label s ≠ ζ) - (d - 1) := by
  have h := compatibleMass_forbid_lower w hw hs P label ζ
  linarith

lemma exists_positive_compatible (w : S → ℝ) (P : S → Prop)
    (hpos : 0 < compatibleMass w P) : ∃ s, P s ∧ 0 < w s := by
  classical
  by_contra hn
  push Not at hn
  have hle : compatibleMass w P ≤ 0 := by
    apply tsum_nonpos
    intro s
    unfold compatibleWeight
    split_ifs with h
    · exact hn s h
    · rfl
  linarith

end Removal

end
end CI2ZF.Appendix.Edge
