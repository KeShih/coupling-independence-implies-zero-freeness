import CI2ZF.Coupling.Edge.Approximation
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.Order.IntermediateValue

/-!
# Real-root calculations for the finite slot approximations

The elementary dilation-interlacing argument uses signs of products between
successive positive roots. This module develops that argument for the
reflected deformed binomial polynomials.
-/

namespace CI2ZF.Appendix.Edge

open Polynomial
open scoped BigOperators

noncomputable section

lemma card_fin_lt {n k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun i : Fin n => i.val < k)).card = k := by
  by_cases hkn : k < n
  · have hset : Finset.univ.filter (fun i : Fin n => i.val < k) =
        Finset.Iio (⟨k, hkn⟩ : Fin n) := by
      ext i
      simp [Fin.lt_def]
    rw [hset, Fin.card_Iio]
  · have heq : k = n := by omega
    subst k
    simp

lemma sign_product {n k : ℕ} (hk : k ≤ n) :
    (∏ i : Fin n, if i.val < k then (-1 : ℝ) else 1) = (-1 : ℝ) ^ k := by
  rw [Finset.prod_ite]
  simp [card_fin_lt hk]

def normalizedRootProduct {n : ℕ} (r : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∏ i, (1 - t / r i)

/-- Between roots, the sign is determined by the number already crossed. -/
lemma normalizedRootProduct_sign {n k : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (hk : k ≤ n) (t : ℝ)
    (hbelow : ∀ i, i.val < k → r i < t)
    (habove : ∀ i, k ≤ i.val → t < r i) :
    0 < (-1 : ℝ) ^ k * normalizedRootProduct r t := by
  rw [← sign_product hk, normalizedRootProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro i _
  by_cases hi : i.val < k
  · rw [if_pos hi]
    have h := (one_lt_div (hr i)).mpr (hbelow i hi)
    linarith
  · rw [if_neg hi, one_mul]
    have h := (div_lt_one (hr i)).mpr (habove i (by omega))
    linarith

lemma normalizedRootProduct_at_root {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, r i ≠ 0) (i : Fin n) : normalizedRootProduct r (r i) = 0 := by
  unfold normalizedRootProduct
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [div_self (hr i), sub_self]

lemma normalizedRootProduct_zero {n : ℕ} (r : Fin n → ℝ) :
    normalizedRootProduct r 0 = 1 := by simp [normalizedRootProduct]

def normalizedFactorPolynomial {n : ℕ} (r : Fin n → ℝ) : Polynomial ℝ :=
  ∏ i, (1 - C (r i)⁻¹ * X)

lemma normalizedFactorPolynomial_eval {n : ℕ} (r : Fin n → ℝ) (t : ℝ) :
    (normalizedFactorPolynomial r).eval t = normalizedRootProduct r t := by
  simp only [normalizedFactorPolynomial, eval_prod, eval_sub, eval_one, eval_mul, eval_C,
    eval_X, normalizedRootProduct]
  apply Finset.prod_congr rfl
  intro i _
  rw [div_eq_mul_inv, mul_comm]

lemma normalizedFactorPolynomial_degree_le {n : ℕ} (r : Fin n → ℝ) :
    (normalizedFactorPolynomial r).natDegree ≤ n := by
  calc
    _ ≤ ∑ i : Fin n, (1 - C (r i)⁻¹ * X : Polynomial ℝ).natDegree := natDegree_prod_le _ _
    _ ≤ ∑ _ : Fin n, 1 := by
      apply Finset.sum_le_sum
      intro i _
      have hmul : (C (r i)⁻¹ * X : Polynomial ℝ).natDegree ≤ 1 := by
        calc
          _ ≤ (C (r i)⁻¹ : Polynomial ℝ).natDegree + (X : Polynomial ℝ).natDegree :=
            natDegree_mul_le
          _ = 1 := by simp
      exact (natDegree_sub_le _ _).trans (by simpa using hmul)
    _ = n := by simp

/-- Degree, constant term, and the distinct nonzero roots determine the
normalized factorization; no root-factorization theorem is assumed. -/
lemma eq_normalizedFactorPolynomial {n : ℕ} (p : Polynomial ℝ) (r : Fin n → ℝ)
    (hr0 : ∀ i, r i ≠ 0) (hr : Function.Injective r)
    (hdeg : p.natDegree ≤ n) (hzero : p.eval 0 = 1)
    (hroots : ∀ i, p.eval (r i) = 0) : p = normalizedFactorPolynomial r := by
  let f : Option (Fin n) → ℝ := fun i => match i with | none => 0 | some j => r j
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some j => exact False.elim (hr0 j h.symm)
    | some i =>
      cases b with
      | none => exact False.elim (hr0 i h)
      | some j => exact congrArg some (hr h)
  apply eq_of_natDegree_lt_card_of_eval_eq p (normalizedFactorPolynomial r) hf
  · intro i
    cases i with
    | none => simpa [f, normalizedFactorPolynomial_eval, normalizedRootProduct_zero] using hzero
    | some i =>
      change p.eval (r i) = (normalizedFactorPolynomial r).eval (r i)
      rw [hroots i, normalizedFactorPolynomial_eval, normalizedRootProduct_at_root r hr0 i]
  · have hq := normalizedFactorPolynomial_degree_le r
    simp only [Fintype.card_option, Fintype.card_fin]
    omega

lemma normalizedRootProduct_neg_sign {n : ℕ} (r : Fin n → ℝ) (t : ℝ) :
    (-1 : ℝ) ^ n * normalizedRootProduct r t = ∏ i, (t / r i - 1) := by
  have hconst : (∏ _ : Fin n, (-1 : ℝ)) = (-1 : ℝ) ^ n := by simp
  rw [← hconst, normalizedRootProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

/-- Explicit tail sign for the dilation recurrence. The finite proof uses
only products and inequalities, without asymptotic results on polynomials. -/
lemma dilation_tail_sign {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    {x t : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (ht : (2 / x) ^ n < t) (hlarge : ∀ i, 2 * r i / x < t) :
    0 < (-1 : ℝ) ^ (n + 1) *
      (normalizedRootProduct r t - t * normalizedRootProduct r (x * t)) := by
  have ht0 : 0 < t := lt_trans (pow_pos (div_pos (by norm_num) hx) _) ht
  have hi (i : Fin n) : 2 < x * (t / r i) := by
    have h := (div_lt_iff₀ hx).mp (hlarge i)
    rw [← mul_div_assoc]
    apply (lt_div_iff₀ (hr i)).mpr
    simpa [mul_comm] using h
  have hA (i : Fin n) : 0 < t / r i - 1 := by
    have hdiv : 0 < t / r i := div_pos ht0 (hr i)
    have h := hi i
    nlinarith
  have hfactor (i : Fin n) : x / 2 * (t / r i - 1) ≤ x * t / r i - 1 := by
    have h := hi i
    rw [mul_div_assoc]
    nlinarith
  have hprod : (x / 2) ^ n * (∏ i, (t / r i - 1)) ≤ ∏ i, (x * t / r i - 1) := by
    calc
      _ = ∏ i : Fin n, (x / 2 * (t / r i - 1)) := by
        simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ _ := Finset.prod_le_prod (fun i _ => mul_nonneg (by positivity) (hA i).le)
        (fun i _ => hfactor i)
  have hpow : (2 / x) ^ n * (x / 2) ^ n = 1 := by
    rw [← mul_pow]
    have h : 2 / x * (x / 2) = (1 : ℝ) := by field_simp
    rw [h, one_pow]
  have htpow : 1 < t * (x / 2) ^ n := by
    calc
      1 = (2 / x) ^ n * (x / 2) ^ n := hpow.symm
      _ < _ := mul_lt_mul_of_pos_right ht (pow_pos (by positivity) _)
  have hprodpos : 0 < ∏ i, (t / r i - 1) := Finset.prod_pos fun i _ => hA i
  have hstrict := mul_lt_mul_of_pos_right htpow hprodpos
  have hweak := mul_le_mul_of_nonneg_left hprod ht0.le
  rw [pow_succ]
  calc
    0 < t * (∏ i, (x * t / r i - 1)) - (∏ i, (t / r i - 1)) := by nlinarith
    _ = (-1 : ℝ) ^ n * -1 *
        (normalizedRootProduct r t - t * normalizedRootProduct r (x * t)) := by
      rw [← normalizedRootProduct_neg_sign r t, ← normalizedRootProduct_neg_sign r (x * t)]
      ring

lemma exists_dilation_tail {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ∃ t, 0 < t ∧ (∀ i, r i / x < t) ∧
      0 < (-1 : ℝ) ^ (n + 1) *
        (normalizedRootProduct r t - t * normalizedRootProduct r (x * t)) := by
  let t := (2 / x) ^ n + 1 + ∑ i, 2 * r i / x
  have hsum : 0 ≤ ∑ i, 2 * r i / x := Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (by norm_num) (hr i).le) hx.le
  have ht : (2 / x) ^ n < t := by dsimp [t]; linarith
  have hlarge (i : Fin n) : 2 * r i / x < t := by
    have hi : 2 * r i / x ≤ ∑ j, 2 * r j / x :=
      Finset.single_le_sum (f := fun j : Fin n => 2 * r j / x)
        (fun j _ => div_nonneg (mul_nonneg (by norm_num) (hr j).le) hx.le) (Finset.mem_univ i)
    have hp := pow_pos (div_pos (by norm_num : (0 : ℝ) < 2) hx) n
    dsimp [t]
    linarith
  refine ⟨t, lt_trans (pow_pos (div_pos (by norm_num) hx) _) ht,
    fun i => ?_, dilation_tail_sign r hr hx hx1 ht hlarge⟩
  have h := hlarge i
  have hdiv := div_pos (hr i) hx
  rw [mul_div_assoc] at h
  linarith

/-- A continuous function with strictly opposite endpoint signs has an
interior zero. Multiplying by a nonzero common sign is allowed. -/
lemma exists_zero_between_signed {f : ℝ → ℝ} (hf : Continuous f)
    {a b ε : ℝ} (hab : a < b) (hε : ε ≠ 0)
    (ha : 0 < ε * f a) (hb : ε * f b < 0) :
    ∃ t, a < t ∧ t < b ∧ f t = 0 := by
  have hcont : Continuous (fun t => ε * f t) := continuous_const.mul hf
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc' hab.le hcont.continuousOn
    (show 0 ∈ Set.Icc (ε * f b) (ε * f a) from ⟨hb.le, ha.le⟩)
  have htne_a : t ≠ a := by intro h; subst t; linarith
  have htne_b : t ≠ b := by intro h; subst t; linarith
  refine ⟨t, lt_of_le_of_ne ht.1 (Ne.symm htne_a), lt_of_le_of_ne ht.2 htne_b, ?_⟩
  exact (mul_eq_zero.mp hzero).resolve_left hε

/-- Positive roots with the strict separation needed by a dilation by `x`. -/
def RootsSeparated {n : ℕ} (x : ℝ) (r : Fin n → ℝ) : Prop :=
  ∀ i j, i < j → r i < x * r j

lemma RootsSeparated.strictMono {n : ℕ} {x : ℝ} {r : Fin n → ℝ}
    (hsep : RootsSeparated x r) (hx1 : x < 1) (hr : ∀ i, 0 < r i) : StrictMono r := by
  intro i j hij
  have h := hsep i j hij
  have hmul : x * r j < r j := by nlinarith [hr j]
  exact h.trans hmul

def dilationFunction {n : ℕ} (r : Fin n → ℝ) (x t : ℝ) : ℝ :=
  normalizedRootProduct r t - t * normalizedRootProduct r (x * t)

lemma dilationFunction_continuous {n : ℕ} (r : Fin n → ℝ) (x : ℝ) :
    Continuous (dilationFunction r x) := by
  unfold dilationFunction normalizedRootProduct
  fun_prop

@[simp] lemma dilationFunction_zero {n : ℕ} (r : Fin n → ℝ) (x : ℝ) :
    dilationFunction r x 0 = 1 := by simp [dilationFunction, normalizedRootProduct_zero]

lemma dilationFunction_at_root_sign {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : ℝ} (hx1 : x < 1) (hsep : RootsSeparated x r) (i : Fin n) :
    0 < (-1 : ℝ) ^ (i.val + 1) * dilationFunction r x (r i) := by
  have hmono := hsep.strictMono hx1 hr
  have hsign : 0 < (-1 : ℝ) ^ i.val * normalizedRootProduct r (x * r i) := by
    apply normalizedRootProduct_sign r hr (Nat.le_of_lt i.isLt)
    · intro j hji
      exact hsep j i hji
    · intro j hij
      have hle := hmono.monotone (show i ≤ j from hij)
      have hlt : x * r i < r i := by nlinarith [hr i]
      exact hlt.trans_le hle
  unfold dilationFunction
  rw [normalizedRootProduct_at_root r (fun j => (hr j).ne') i, zero_sub, pow_succ]
  nlinarith [mul_pos (hr i) hsign]

lemma dilationFunction_at_dilated_root_sign {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hsep : RootsSeparated x r) (i : Fin n) :
    0 < (-1 : ℝ) ^ (i.val + 1) * dilationFunction r x (r i / x) := by
  have hmono := hsep.strictMono hx1 hr
  have hsign : 0 < (-1 : ℝ) ^ (i.val + 1) * normalizedRootProduct r (r i / x) := by
    apply normalizedRootProduct_sign r hr i.isLt
    · intro j hji
      have hle := hmono.monotone (show j ≤ i from by omega)
      apply (lt_div_iff₀ hx).mpr
      have hmul : r j * x < r j := by nlinarith [hr j]
      exact hmul.trans_le hle
    · intro j hij
      apply (div_lt_iff₀ hx).mpr
      simpa [mul_comm] using hsep i j (by change i.val < j.val; omega)
  have hcancel : x * (r i / x) = r i := by field_simp
  simpa only [dilationFunction, hcancel, normalizedRootProduct_at_root r (fun j => (hr j).ne') i,
    mul_zero, sub_zero] using hsign

def rootIntervalLower {n : ℕ} (r : Fin n → ℝ) (x : ℝ) (k : Fin (n + 1)) : ℝ :=
  if h : k.val = 0 then 0 else r ⟨k.val - 1, by have := k.isLt; omega⟩ / x

def rootIntervalUpper {n : ℕ} (r : Fin n → ℝ) (T : ℝ) (k : Fin (n + 1)) : ℝ :=
  if h : k.val < n then r ⟨k.val, h⟩ else T

lemma rootIntervalLower_nonneg {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    {x : ℝ} (hx : 0 < x) (k : Fin (n + 1)) : 0 ≤ rootIntervalLower r x k := by
  unfold rootIntervalLower
  split_ifs with hk
  · exact le_rfl
  · exact (div_pos (hr _) hx).le

lemma rootInterval_nonempty {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    {x T : ℝ} (hx : 0 < x) (hsep : RootsSeparated x r)
    (hT : 0 < T) (hTr : ∀ i, r i / x < T) (k : Fin (n + 1)) :
    rootIntervalLower r x k < rootIntervalUpper r T k := by
  by_cases hk0 : k.val = 0
  · simp only [rootIntervalLower, dif_pos hk0]
    unfold rootIntervalUpper
    split_ifs
    · exact hr _
    · exact hT
  · simp only [rootIntervalLower, dif_neg hk0]
    unfold rootIntervalUpper
    split_ifs with hkn
    · apply (div_lt_iff₀ hx).mpr
      have hindices : (⟨k.val - 1, by have := k.isLt; omega⟩ : Fin n) < ⟨k.val, hkn⟩ := by
        change k.val - 1 < k.val
        omega
      simpa [mul_comm] using hsep _ _ hindices
    · exact hTr _

lemma rootInterval_lower_sign {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hsep : RootsSeparated x r)
    (k : Fin (n + 1)) :
    0 < (-1 : ℝ) ^ k.val * dilationFunction r x (rootIntervalLower r x k) := by
  by_cases hk0 : k.val = 0
  · simp [rootIntervalLower, hk0]
  · let i : Fin n := ⟨k.val - 1, by have := k.isLt; omega⟩
    have hs := dilationFunction_at_dilated_root_sign r hr hx hx1 hsep i
    have hi : i.val + 1 = k.val := by dsimp [i]; omega
    simpa only [rootIntervalLower, dif_neg hk0, hi] using hs

lemma rootInterval_upper_sign {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    {x T : ℝ} (hx1 : x < 1) (hsep : RootsSeparated x r)
    (hTsign : 0 < (-1 : ℝ) ^ (n + 1) * dilationFunction r x T)
    (k : Fin (n + 1)) :
    0 < (-1 : ℝ) ^ (k.val + 1) * dilationFunction r x (rootIntervalUpper r T k) := by
  by_cases hkn : k.val < n
  · simpa only [rootIntervalUpper, dif_pos hkn] using
      dilationFunction_at_root_sign r hr hx1 hsep ⟨k.val, hkn⟩
  · have hk : k.val = n := by have := k.isLt; omega
    simpa [rootIntervalUpper, hk] using hTsign

/-- Dilation interlacing produces one new positive root in every gap and
preserves strict `x`-separation. -/
lemma exists_separated_dilation_roots {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hsep : RootsSeparated x r) :
    ∃ s : Fin (n + 1) → ℝ, (∀ i, 0 < s i) ∧ RootsSeparated x s ∧
      ∀ i, dilationFunction r x (s i) = 0 := by
  obtain ⟨T, hT, hTr, hTsign⟩ := exists_dilation_tail r hr hx hx1
  have hex (k : Fin (n + 1)) : ∃ t, rootIntervalLower r x k < t ∧
      t < rootIntervalUpper r T k ∧ dilationFunction r x t = 0 := by
    have hlo := rootInterval_lower_sign r hr hx hx1 hsep k
    have hhi := rootInterval_upper_sign r hr hx1 hsep hTsign k
    rw [pow_succ] at hhi
    apply exists_zero_between_signed (dilationFunction_continuous r x)
      (rootInterval_nonempty r hr hx hsep hT hTr k) (pow_ne_zero _ (by norm_num)) hlo
    nlinarith
  choose s hs using hex
  have hspos (i : Fin (n + 1)) : 0 < s i :=
    lt_of_le_of_lt (rootIntervalLower_nonneg r hr hx i) (hs i).1
  refine ⟨s, hspos, ?_, fun i => (hs i).2.2⟩
  intro i j hij
  have hi : i.val < n := by have := j.isLt; change i.val < j.val at hij; omega
  have hj : j.val ≠ 0 := by change i.val < j.val at hij; omega
  let a : Fin n := ⟨i.val, hi⟩
  let b : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have ha : s i < r a := by simpa only [rootIntervalUpper, dif_pos hi] using (hs i).2.1
  have hb : r b / x < s j := by simpa only [rootIntervalLower, dif_neg hj] using (hs j).1
  have hab : a ≤ b := by change i.val ≤ j.val - 1; change i.val < j.val at hij; omega
  have hrab := (hsep.strictMono hx1 hr).monotone hab
  have hb' := (div_lt_iff₀ hx).mp hb
  calc
    s i < r a := ha
    _ ≤ r b := hrab
    _ < x * s j := by simpa [mul_comm] using hb'

def reflectedSlotApproxPolynomial (x : ℝ) (n : ℕ) : Polynomial ℝ :=
  (slotApproxPolynomial x n).comp (C (-1) * X)

lemma reflectedSlotApproxPolynomial_eval (x t : ℝ) (n : ℕ) :
    (reflectedSlotApproxPolynomial x n).eval t = (slotApproxPolynomial x n).eval (-t) := by
  simp [reflectedSlotApproxPolynomial]

lemma reflectedSlotApproxPolynomial_degree_le (x : ℝ) (n : ℕ) :
    (reflectedSlotApproxPolynomial x n).natDegree ≤ n := by
  calc
    _ ≤ (slotApproxPolynomial x n).natDegree * (C (-1) * X : Polynomial ℝ).natDegree :=
      natDegree_comp_le
    _ = (slotApproxPolynomial x n).natDegree := by simp
    _ ≤ n := slotApproxPolynomial_natDegree_le x n

@[simp] lemma reflectedSlotApproxPolynomial_eval_zero (x : ℝ) (n : ℕ) :
    (reflectedSlotApproxPolynomial x n).eval 0 = 1 := by
  rw [reflectedSlotApproxPolynomial_eval, neg_zero, ← coeff_zero_eq_eval_zero]
  exact slotApproxPolynomial_constant x n

lemma reflectedSlotApproxPolynomial_eval_succ (x t : ℝ) (n : ℕ) :
    (reflectedSlotApproxPolynomial x (n + 1)).eval t =
      (reflectedSlotApproxPolynomial x n).eval t -
        t * (reflectedSlotApproxPolynomial x n).eval (x * t) := by
  simp only [reflectedSlotApproxPolynomial_eval, slotApproxPolynomial_eval_succ,
    mul_neg, neg_mul, sub_eq_add_neg]

/-- Every deformed binomial polynomial has a complete strictly separated
negative-root factorization. The proof is finite and elementary. -/
lemma slotApproxPolynomial_separated_factorization {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (n : ℕ) : ∃ r : Fin n → ℝ, (∀ i, 0 < r i) ∧ RootsSeparated x r ∧
      reflectedSlotApproxPolynomial x n = normalizedFactorPolynomial r := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · simp [reflectedSlotApproxPolynomial, normalizedFactorPolynomial]
  | succ n ih =>
    obtain ⟨r, hr, hsep, hfactor⟩ := ih
    obtain ⟨s, hs, hssep, hsroots⟩ := exists_separated_dilation_roots r hr hx hx1 hsep
    refine ⟨s, hs, hssep, eq_normalizedFactorPolynomial _ s (fun i => (hs i).ne')
      (hssep.strictMono hx1 hs).injective (reflectedSlotApproxPolynomial_degree_le x _)
      (reflectedSlotApproxPolynomial_eval_zero x _) ?_⟩
    intro i
    rw [reflectedSlotApproxPolynomial_eval_succ, hfactor,
      normalizedFactorPolynomial_eval, normalizedFactorPolynomial_eval]
    exact hsroots i

end
end CI2ZF.Appendix.Edge
