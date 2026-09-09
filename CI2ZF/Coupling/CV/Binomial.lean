import CI2ZF.Coupling.CV.Coins
import CI2ZF.Coupling.CV.Averaging

/-! Exact active-multiplicity probabilities for arbitrary finite sets of
physical root-edge labels, independent of root-list boundary labels. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] [DecidableEq K]

def coinSuccessSet (A : Finset K) (ω : K → Bool) : Finset K := A.filter fun k => ω k = true

def coinCount (A : Finset K) (ω : K → Bool) : ℕ := (coinSuccessSet A ω).card

lemma coinPattern_iff_successSet (A S : Finset K) (hS : S ⊆ A) (ω : K → Bool) :
    coinPattern S (A \ S) ω ↔ coinSuccessSet A ω = S := by
  constructor
  · intro hp
    ext k
    constructor
    · intro hk
      obtain ⟨hka, hkt⟩ := Finset.mem_filter.mp hk
      by_contra hks
      have hkf := hp.2 k (Finset.mem_sdiff.mpr ⟨hka, hks⟩)
      rw [hkt] at hkf
      contradiction
    · intro hk
      exact Finset.mem_filter.mpr ⟨hS hk, hp.1 k hk⟩
  · intro he
    constructor
    · intro k hk
      have hf : k ∈ coinSuccessSet A ω := he.symm ▸ hk
      exact (Finset.mem_filter.mp hf).2
    · intro k hk
      obtain ⟨hka, hks⟩ := Finset.mem_sdiff.mp hk
      have hn : ω k ≠ true := by
        intro ht
        have hf : k ∈ coinSuccessSet A ω := Finset.mem_filter.mpr ⟨hka, ht⟩
        exact hks (he ▸ hf)
      exact Bool.eq_false_iff.mpr hn

lemma coinCount_event_partition (A D : Finset K) (j : ℕ) (ω : K → Bool) :
    (if coinCount A ω = j ∧ (∀ k ∈ D, ω k = false) then (1 : ℝ) else 0) =
      ∑ S ∈ A.powersetCard j,
        if coinPattern S (A \ S) ω ∧ (∀ k ∈ D, ω k = false) then 1 else 0 := by
  classical
  by_cases hj : coinCount A ω = j
  · have hmem : coinSuccessSet A ω ∈ A.powersetCard j :=
      Finset.mem_powersetCard.mpr ⟨Finset.filter_subset _ _, hj⟩
    rw [Finset.sum_eq_single_of_mem (coinSuccessSet A ω) hmem]
    · have hs : coinSuccessSet A ω ⊆ A := Finset.filter_subset _ _
      rw [coinPattern_iff_successSet A (coinSuccessSet A ω) hs ω]
      simp only [hj, true_and]
    · intro S hS hne
      have hs := Finset.mem_powersetCard.mp hS
      rw [coinPattern_iff_successSet A S hs.1 ω]
      exact if_neg (fun hh => hne hh.1.symm)
  · rw [if_neg (fun hh => hj hh.1)]
    symm
    apply Finset.sum_eq_zero
    intro S hS
    obtain ⟨hs, hcard⟩ := Finset.mem_powersetCard.mp hS
    rw [coinPattern_iff_successSet A S hs ω]
    apply if_neg
    intro hh
    apply hj
    unfold coinCount
    rw [hh.1, hcard]

lemma expectReal_finset_sum {S J : Type*} [Fintype S] (p : FinDist S)
    (A : Finset J) (f : J → S → ℝ) :
    expectReal p (fun s => ∑ j ∈ A, f j s) = ∑ j ∈ A, expectReal p (f j) := by
  simp only [expectReal, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The joint binomial law and disjoint list-survival event, derived from
the actual finite product coins rather than assumed as a distribution. -/
theorem coinCount_joint_probability (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (A D : Finset K) (hAD : Disjoint A D) (j : ℕ) :
    expectReal (commonCoinLaw t ht)
      (fun ω => if coinCount A ω = j ∧ (∀ k ∈ D, ω k = false) then 1 else 0) =
      (A.card.choose j : ℝ) * t ^ j * (1 - t) ^ (A.card - j) * (1 - t) ^ D.card := by
  simp_rw [coinCount_event_partition]
  rw [expectReal_finset_sum]
  have he (S : Finset K) (hS : S ∈ A.powersetCard j) :
      expectReal (commonCoinLaw t ht)
        (fun ω => if coinPattern S (A \ S) ω ∧ (∀ k ∈ D, ω k = false) then 1 else 0) =
        t ^ j * (1 - t) ^ (A.card - j) * (1 - t) ^ D.card := by
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hS
    have hdis : Disjoint S (A \ S) := Finset.disjoint_left.mpr
      (fun k hk hks => (Finset.mem_sdiff.mp hks).2 hk)
    have hUD : Disjoint (S ∪ (A \ S)) D := by
      rw [Finset.union_sdiff_of_subset hsub]
      exact hAD
    rw [coinPattern_and_false_expect t ht S (A \ S) D hdis hUD,
      coinPatternProbability_eq t ht S (A \ S) hdis,
      Finset.card_sdiff_of_subset hsub, hcard]
  rw [Finset.sum_congr rfl (fun S hS => he S hS)]
  simp only [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  ring

lemma coinCount_as_sum (A : Finset K) (ω : K → Bool) :
    (coinCount A ω : ℝ) = ∑ k ∈ A, if ω k = true then 1 else 0 := by
  exact Finset.natCast_card_filter _ _

theorem coinCount_joint_mean (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (A D : Finset K) (hAD : Disjoint A D) :
    expectReal (commonCoinLaw t ht)
      (fun ω => if (∀ k ∈ D, ω k = false) then (coinCount A ω : ℝ) else 0) =
      (A.card : ℝ) * t * (1 - t) ^ D.card := by
  have he (ω : K → Bool) :
      (if (∀ k ∈ D, ω k = false) then (coinCount A ω : ℝ) else 0) =
        ∑ k ∈ A, if ω k = true ∧ (∀ j ∈ D, ω j = false) then 1 else 0 := by
    have hi (P : Prop) [Decidable P] :
        (if P then (coinCount A ω : ℝ) else 0) =
          ∑ k ∈ A, if ω k = true ∧ P then 1 else 0 := by
      by_cases hp : P
      · simp only [hp, if_true, and_true, coinCount_as_sum]
      · simp only [hp, if_false, and_false, Finset.sum_const_zero]
    exact hi (∀ k ∈ D, ω k = false)
  simp_rw [he]
  rw [expectReal_finset_sum]
  have heach (k : K) (hk : k ∈ A) :
      expectReal (commonCoinLaw t ht)
        (fun ω => if ω k = true ∧ (∀ j ∈ D, ω j = false) then 1 else 0) =
        t * (1 - t) ^ D.card := by
    have hd : Disjoint ({k} : Finset K) D := by
      simpa using (Finset.disjoint_left.mp hAD hk : k ∉ D)
    have hp := coinPatternProbability_eq t ht {k} D hd
    simpa only [coinPatternProbability, coinPattern, Finset.mem_singleton,
      forall_eq, Finset.card_singleton, pow_one] using hp
  rw [Finset.sum_congr rfl (fun k hk => heach k hk)]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

theorem coinCount_mean (t : ℝ) (ht : t ∈ Set.Icc 0 1) (A : Finset K) :
    expectReal (commonCoinLaw t ht) (fun ω => (coinCount A ω : ℝ)) = (A.card : ℝ) * t := by
  simpa using coinCount_joint_mean t ht A ∅ (Finset.disjoint_empty_right _)

theorem coin_all_false_probability (t : ℝ) (ht : t ∈ Set.Icc 0 1) (D : Finset K) :
    expectReal (commonCoinLaw t ht)
      (fun ω => if ∀ k ∈ D, ω k = false then (1 : ℝ) else 0) = (1 - t) ^ D.card := by
  have hp := coinPatternProbability_eq t ht ∅ D (by simp)
  simpa only [coinPatternProbability, coinPattern, Finset.notMem_empty, IsEmpty.forall_iff,
    implies_true, true_and, Finset.card_empty, pow_zero, one_mul] using hp

theorem coinCount_not_false_joint_mean (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (A D : Finset K) (hAD : Disjoint A D) :
    expectReal (commonCoinLaw t ht)
      (fun ω => if ¬(∀ k ∈ D, ω k = false) then (coinCount A ω : ℝ) else 0) =
      (A.card : ℝ) * t * (1 - (1 - t) ^ D.card) := by
  have hi (P : Prop) [Decidable P] (r : ℝ) :
      (if ¬P then r else 0) = r - (if P then r else 0) := by
    by_cases hp : P <;> simp [hp]
  simp_rw [hi]
  rw [expectReal_sub, coinCount_mean, coinCount_joint_mean t ht A D hAD]
  ring

theorem coinCount_low_joint_mean (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (A D : Finset K) (hAD : Disjoint A D) (hA : 2 ≤ A.card) :
    expectReal (commonCoinLaw t ht)
      (fun ω => if coinCount A ω ≤ 2 ∧ (∀ k ∈ D, ω k = false)
        then (coinCount A ω : ℝ) else 0) =
      (A.card : ℝ) * t * (1 - t) ^ (A.card - 2) *
        (1 + ((A.card - 2 : ℕ) : ℝ) * t) * (1 - t) ^ D.card := by
  have he (ω : K → Bool) :
      (if coinCount A ω ≤ 2 ∧ (∀ k ∈ D, ω k = false) then (coinCount A ω : ℝ) else 0) =
        (if coinCount A ω = 1 ∧ (∀ k ∈ D, ω k = false) then 1 else 0) +
          2 * (if coinCount A ω = 2 ∧ (∀ k ∈ D, ω k = false) then 1 else 0) := by
    have hi (n : ℕ) (P : Prop) [Decidable P] :
        (if n ≤ 2 ∧ P then (n : ℝ) else 0) =
          (if n = 1 ∧ P then 1 else 0) + 2 * (if n = 2 ∧ P then 1 else 0) := by
      by_cases hp : P
      · simp only [hp, and_true]
        by_cases hn : n ≤ 2
        · interval_cases n <;> norm_num
        · have h1 : n ≠ 1 := by omega
          have h2 : n ≠ 2 := by omega
          simp only [if_neg hn, if_neg h1, if_neg h2, mul_zero, add_zero]
      · simp only [hp, and_false, if_false, mul_zero, add_zero]
    exact hi (coinCount A ω) (∀ k ∈ D, ω k = false)
  simp_rw [he]
  rw [expectReal_add, expectReal_mul_const, coinCount_joint_probability t ht A D hAD 1,
    coinCount_joint_probability t ht A D hAD 2]
  simp only [Nat.choose_one_right, pow_one]
  rw [Nat.cast_choose_two]
  have hm1 : A.card - 1 = A.card - 2 + 1 := by omega
  have hm2 : ((A.card - 2 : ℕ) : ℝ) = (A.card : ℝ) - 2 := by
    exact Nat.cast_sub hA
  rw [hm1, pow_succ, hm2]
  ring

theorem coinCount_low_mean_inactive (x : ℝ) (hx : x ∈ Set.Icc 0 1)
    (A : Finset K) (hA : 2 ≤ A.card) :
    expectReal (commonCoinLaw (1 - x) ⟨by linarith [hx.2], by linarith [hx.1]⟩)
      (fun ω => if coinCount A ω ≤ 2 then (coinCount A ω : ℝ) else 0) =
      (A.card : ℝ) * (1 - x) * x ^ (A.card - 2) *
        (1 + ((A.card - 2 : ℕ) : ℝ) * (1 - x)) := by
  have hp := coinCount_low_joint_mean (1 - x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ A ∅ (Finset.disjoint_empty_right _) hA
  simpa only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true,
    Finset.card_empty, pow_zero, mul_one, sub_sub_cancel] using hp

end
end CI2ZF.Appendix.CV
