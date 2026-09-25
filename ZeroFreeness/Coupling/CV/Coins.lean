import ZeroFreeness.Coupling.Vigoda.ActivationAverage
import ZeroFreeness.Coupling.Foundations.CoinRestriction

/-! Exact probabilities and independence of finite labelled common-coin
patterns, including the endpoint activation parameters. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K]

def coinPattern (A B : Finset K) (ω : K → Bool) : Prop :=
  (∀ k ∈ A, ω k = true) ∧ ∀ k ∈ B, ω k = false

def coinPatternProbability (t : ℝ) (ht : t ∈ Set.Icc 0 1) (A B : Finset K) : ℝ :=
  expectReal (commonCoinLaw t ht) (fun ω => if coinPattern A B ω then 1 else 0)

lemma prod_membership_const (S : Finset K) (z : ℝ) :
    (∏ k : K, if k ∈ S then z else 1) = z ^ S.card := by
  rw [Finset.prod_ite]
  simp

theorem coinPatternProbability_eq (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (A B : Finset K) (hAB : Disjoint A B) :
    coinPatternProbability t ht A B = t ^ A.card * (1 - t) ^ B.card := by
  let f (k : K) (b : Bool) : ℝ :=
    if (k ∈ A → b = true) ∧ (k ∈ B → b = false) then 1 else 0
  have he (ω : K → Bool) : (∏ k, f k (ω k)) =
      if coinPattern A B ω then 1 else 0 := by
    simp [f, Fintype.prod_boole, coinPattern, forall_and]
    split_ifs with hh
    · exact (if_pos hh).symm
    · exact (if_neg hh).symm
  have hc (k : K) : expectReal (bernoulliLaw t ht) (f k) =
      (if k ∈ A then t else 1) * (if k ∈ B then 1 - t else 1) := by
    by_cases ha : k ∈ A
    · have hb : k ∉ B := Finset.disjoint_left.mp hAB ha
      simp [f, ha, hb, expectReal, bernoulliLaw]
    · by_cases hb : k ∈ B <;> simp [f, ha, hb, expectReal, bernoulliLaw]
  have hp := expectReal_productLaw (fun _ : K => bernoulliLaw t ht) f
  simp_rw [he, hc] at hp
  rw [Finset.prod_mul_distrib, prod_membership_const, prod_membership_const] at hp
  exact hp

theorem coinPatternProbability_eq_inactive (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (A B : Finset K) (hAB : Disjoint A B) :
    coinPatternProbability (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩ A B =
      (1 - x) ^ A.card * x ^ B.card := by
  simpa only [sub_sub_cancel] using coinPatternProbability_eq (1 - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ A B hAB

lemma coinPattern_and_false (A B D : Finset K) (ω : K → Bool) :
    coinPattern A B ω ∧ (∀ k ∈ D, ω k = false) ↔ coinPattern A (B ∪ D) ω := by
  simp only [coinPattern, Finset.mem_union, or_imp, forall_and]
  tauto

/-- A finite true/false pattern is independent of all-false constraints on
a disjoint set. -/
theorem coinPattern_and_false_expect (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (A B D : Finset K) (hAB : Disjoint A B) (hD : Disjoint (A ∪ B) D) :
    expectReal (commonCoinLaw t ht)
      (fun ω => if coinPattern A B ω ∧ (∀ k ∈ D, ω k = false) then 1 else 0) =
      coinPatternProbability t ht A B * (1 - t) ^ D.card := by
  have hAD : Disjoint A D := (Finset.disjoint_union_left.mp hD).1
  have hBD : Disjoint B D := (Finset.disjoint_union_left.mp hD).2
  simp only [coinPattern_and_false]
  change coinPatternProbability t ht A (B ∪ D) = _
  rw [coinPatternProbability_eq t ht A (B ∪ D) (Finset.disjoint_union_right.mpr ⟨hAB, hAD⟩),
    coinPatternProbability_eq t ht A B hAB, Finset.card_union_of_disjoint hBD, pow_add]
  ring

theorem coinPattern_and_false_expect_inactive (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (A B D : Finset K) (hAB : Disjoint A B) (hD : Disjoint (A ∪ B) D) :
    expectReal (commonCoinLaw (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => if coinPattern A B ω ∧ (∀ k ∈ D, ω k = false) then 1 else 0) =
      ((1 - x) ^ A.card * x ^ B.card) * x ^ D.card := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hp := coinPattern_and_false_expect (1 - x) ht A B D hAB hD
  rw [coinPatternProbability_eq (1 - x) ht A B hAB] at hp
  simpa only [sub_sub_cancel] using hp

/-- The complementary availability case uses the same independent pattern. -/
theorem coinPattern_and_not_false_expect (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (A B D : Finset K) (hAB : Disjoint A B) (hD : Disjoint (A ∪ B) D) :
    expectReal (commonCoinLaw t ht)
      (fun ω => if coinPattern A B ω ∧ ¬(∀ k ∈ D, ω k = false) then 1 else 0) =
      coinPatternProbability t ht A B * (1 - (1 - t) ^ D.card) := by
  have hi (P Q : Prop) [Decidable P] [Decidable Q] :
      (if P ∧ ¬Q then (1 : ℝ) else 0) =
        (if P then 1 else 0) - (if P ∧ Q then 1 else 0) := by
    by_cases hp : P <;> by_cases hq : Q <;> simp [hp, hq]
  have hpoint (ω : K → Bool) :
      (if coinPattern A B ω ∧ ¬(∀ k ∈ D, ω k = false) then (1 : ℝ) else 0) =
        (if coinPattern A B ω then 1 else 0) -
          (if coinPattern A B ω ∧ (∀ k ∈ D, ω k = false) then 1 else 0) := by
    exact hi (coinPattern A B ω) (∀ k ∈ D, ω k = false)
  simp_rw [hpoint]
  rw [expectReal_sub, coinPattern_and_false_expect t ht A B D hAB hD]
  change coinPatternProbability t ht A B - _ = _
  ring

theorem coinPattern_and_not_false_expect_inactive (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (A B D : Finset K) (hAB : Disjoint A B) (hD : Disjoint (A ∪ B) D) :
    expectReal (commonCoinLaw (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => if coinPattern A B ω ∧ ¬(∀ k ∈ D, ω k = false) then 1 else 0) =
      ((1 - x) ^ A.card * x ^ B.card) * (1 - x ^ D.card) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hp := coinPattern_and_not_false_expect (1 - x) ht A B D hAB hD
  rw [coinPatternProbability_eq (1 - x) ht A B hAB] at hp
  simpa only [sub_sub_cancel] using hp

end
end ZeroFreeness.Appendix.CV
