import CI2ZF.Coupling.Foundations.FiniteCoupling
import CI2ZF.Coupling.Foundations.EndpointContinuity
import CI2ZF.Holant.Signatures

/-!
# Finite comparison lemmas for the Holant recursive coupling

These are the finite probabilistic ingredients of the recursive endpoint
comparison.  In particular, the anti-monotone change of density is proved
by symmetrizing a finite double sum; it is not an assumed marginal-order
property.  The Boolean coupling and its transport estimate include the
zero-mass branches.
-/

namespace CI2ZF.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist

noncomputable section

variable {S : Type*} [Fintype S]

/-- Symmetrization of the difference between two weighted first moments. -/
theorem moment_cross_identity (a b h : S → ℝ) :
    2 * ((∑ x, a x * h x) * (∑ y, b y) -
      (∑ x, a x) * (∑ y, b y * h y)) =
      ∑ x, ∑ y, (h x - h y) * (a x * b y - b x * a y) := by
  have hswap : (∑ x, ∑ y, (h y - h x) * a x * b y) =
      ∑ x, ∑ y, (h x - h y) * a y * b x := by
    rw [Finset.sum_comm]
  have hexpand : (∑ x, ∑ y,
      (h x - h y) * (a x * b y - b x * a y)) =
      (∑ x, ∑ y, (h x - h y) * a x * b y) -
      (∑ x, ∑ y, (h x - h y) * a y * b x) := by
    simp only [← Finset.sum_sub_distrib]
    congr 1
    ext x
    congr 1
    ext y
    ring
  rw [hexpand, ← hswap]
  have hneg : (∑ x, ∑ y, (h y - h x) * a x * b y) =
      -(∑ x, ∑ y, (h x - h y) * a x * b y) := by
    simp only [← Finset.sum_neg_distrib]
    congr 1
    ext x
    congr 1
    ext y
    ring
  rw [hneg]
  have hfactor : (∑ x, ∑ y, (h x - h y) * a x * b y) =
      (∑ x, a x * h x) * (∑ y, b y) -
        (∑ x, a x) * (∑ y, b y * h y) := by
    have hp₁ : (∑ x, a x * h x) * (∑ y, b y) =
        ∑ x, ∑ y, a x * h x * b y := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    have hp₂ : (∑ x, a x) * (∑ y, b y * h y) =
        ∑ x, ∑ y, a x * (b y * h y) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    rw [hp₁, hp₂]
    simp only [← Finset.sum_sub_distrib]
    congr 1
    ext x
    congr 1
    ext y
    ring
  rw [hfactor]
  ring

/-- An ordered likelihood ratio orders the normalized expectation.  The
cross-product formulation remains meaningful when some weights vanish. -/
theorem normalized_moment_le (a b h : S → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x)
    (hZa : 0 < ∑ x, a x) (hZb : 0 < ∑ x, b x)
    (hcross : ∀ x y, 0 ≤ (h x - h y) * (a x * b y - b x * a y)) :
    expectReal (normalizeWeights b hb hZb) h ≤
      expectReal (normalizeWeights a ha hZa) h := by
  have hsum : 0 ≤ ∑ x, ∑ y,
      (h x - h y) * (a x * b y - b x * a y) :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => hcross x y
  rw [← moment_cross_identity] at hsum
  have hcross' : (∑ x, b x * h x) * (∑ x, a x) ≤
      (∑ x, a x * h x) * (∑ x, b x) := by nlinarith
  unfold expectReal
  simp only [normalizeWeights_apply, div_mul_eq_mul_div, ← Finset.sum_div]
  exact (div_le_div_iff₀ hZb hZa).2 hcross'

/-- Chen--Gu's expected-degree comparison follows directly from adjacent
log-concavity, for every nonnegative exterior weight.  Thus global
correlations in the rest of the graph require no independence assumption. -/
theorem shifted_degree_expectation_le (f : Holant.Signature)
    (base : S → ℝ) (degree : S → ℕ) (hbase : ∀ x, 0 ≤ base x)
    (hZ : 0 < ∑ x, base x * f.value (degree x))
    (hZ' : 0 < ∑ x, base x * f.value (degree x + 1)) :
    expectReal
      (normalizeWeights (fun x => base x * f.value (degree x + 1))
        (fun x => mul_nonneg (hbase x) (f.nonneg _)) hZ')
      (fun x => (degree x : ℝ)) ≤
    expectReal
      (normalizeWeights (fun x => base x * f.value (degree x))
        (fun x => mul_nonneg (hbase x) (f.nonneg _)) hZ)
      (fun x => (degree x : ℝ)) := by
  apply normalized_moment_le
  intro x y
  have hcore : 0 ≤ ((degree x : ℝ) - degree y) *
      (f.value (degree x) * f.value (degree y + 1) -
        f.value (degree x + 1) * f.value (degree y)) := by
    rcases le_total (degree y) (degree x) with h | h
    · apply mul_nonneg
      · exact sub_nonneg.mpr (by exact_mod_cast h)
      · have hcross := f.ratio_cross_le h
        nlinarith
    · apply mul_nonneg_of_nonpos_of_nonpos
      · exact sub_nonpos.mpr (by exact_mod_cast h)
      · exact sub_nonpos.mpr (f.ratio_cross_le h)
  calc
    0 ≤ (base x * base y) * (((degree x : ℝ) - degree y) *
        (f.value (degree x) * f.value (degree y + 1) -
          f.value (degree x + 1) * f.value (degree y))) :=
      mul_nonneg (mul_nonneg (hbase x) (hbase y)) hcore
    _ = _ := by ring

/-- The marginal of the value `true` at one Boolean coordinate. -/
def oneMarginal {E : Type*} [Fintype E] [DecidableEq E]
    (μ : FinDist (E → Bool)) (e : E) : ℝ :=
  ∑ σ, μ.w σ * if σ e then 1 else 0

/-- Expected selected degree is the sum of incident one-edge marginals. -/
theorem expected_degree_eq_sum_marginal {E : Type*} [Fintype E] [DecidableEq E]
    (μ : FinDist (E → Bool)) (I : Finset E) :
    expectReal μ (fun σ => ∑ e ∈ I, if σ e then 1 else 0) =
      ∑ e ∈ I, oneMarginal μ e := by
  unfold expectReal oneMarginal
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- Comparing expected incident degrees provides an edge at which the
unshifted marginal dominates.  This is the edge-selection step in the
recursive coupling, without requiring all incident marginals to be ordered. -/
theorem exists_ordered_edge {E : Type*} [Fintype E] [DecidableEq E]
    (μ ν : FinDist (E → Bool)) (I : Finset E) (hI : I.Nonempty)
    (hdeg : expectReal ν (fun σ => ∑ e ∈ I, if σ e then 1 else 0) ≤
      expectReal μ (fun σ => ∑ e ∈ I, if σ e then 1 else 0)) :
    ∃ e ∈ I, oneMarginal ν e ≤ oneMarginal μ e := by
  simp only [expected_degree_eq_sum_marginal] at hdeg
  exact Finset.exists_le_of_sum_le hI hdeg

/-- A Bernoulli law, including both degenerate endpoints. -/
def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinDist Bool where
  w b := if b then p else 1 - p
  nonneg b := by cases b <;> simp <;> linarith
  sum_one := by simp

/-- The monotone optimal coupling of Bernoulli laws with `q ≤ p`.
Only `00`, `11`, and `10` can have positive mass. -/
def bernoulliCoupling {p q : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1) :
    Coupling (bernoulli p (hq0.trans hqp) hp1)
      (bernoulli q hq0 (hqp.trans hp1)) where
  w a b := if a then (if b then q else p - q) else (if b then 0 else 1 - p)
  nonneg a b := by cases a <;> cases b <;> simp <;> linarith
  sum_row a := by cases a <;> simp [bernoulli]
  sum_col b := by cases b <;> simp [bernoulli]

/-- The recursive coupling's exact three-branch transport bound. -/
theorem three_branch_W_le {p q : ℝ} (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1)
    {d : S → S → ℝ} (hd : ∀ x y, 0 ≤ d x y)
    (K L : Bool → FinDist S) :
    W d ((bernoulli p (hq0.trans hqp) hp1).bind K)
        ((bernoulli q hq0 (hqp.trans hp1)).bind L) ≤
      (1 - p) * W d (K false) (L false) + q * W d (K true) (L true) +
        (p - q) * W d (K true) (L false) := by
  have h := W_bind_le hd (bernoulliCoupling hq0 hqp hp1) K L
  simpa [Fintype.sum_bool, bernoulliCoupling, add_comm, add_left_comm,
    add_assoc] using h

/-- The strengthened one-step induction used to avoid stopping-time
formalization.  `z = (1-p)z₀` is the probability of the all-zero incident
configuration; the `00` branch retains that probability. -/
theorem recursive_cost_step {p q P z z₀ c₀ c₁ c₁₀ : ℝ}
    (hq0 : 0 ≤ q) (hqp : q ≤ p) (hp1 : p ≤ 1)
    (hz : z = (1 - p) * z₀)
    (hc₀ : c₀ ≤ P * (1 - z₀)) (hc₁ : c₁ ≤ P - 1)
    (hc₁₀ : c₁₀ ≤ 1 + (P - 1)) :
    (1 - p) * c₀ + q * c₁ + (p - q) * c₁₀ ≤ P * (1 - z) := by
  have h₀ := mul_le_mul_of_nonneg_left hc₀ (sub_nonneg.mpr hp1)
  have h₁ := mul_le_mul_of_nonneg_left hc₁ hq0
  have h₁₀ := mul_le_mul_of_nonneg_left hc₁₀ (sub_nonneg.mpr hqp)
  calc
    (1 - p) * c₀ + q * c₁ + (p - q) * c₁₀ ≤
        (1 - p) * (P * (1 - z₀)) + q * (P - 1) + (p - q) * (1 + (P - 1)) :=
      add_le_add (add_le_add h₀ h₁) h₁₀
    _ = P * (1 - z) - q := by rw [hz]; ring
    _ ≤ P * (1 - z) := sub_le_self _ hq0

/-- A uniform lower bound on the all-zero incident probability closes
the strengthened recurrence. -/
theorem root_zero_closes_bound {P z c : ℝ} (hP : 0 < P)
    (hz : 1 / P ≤ z) (hc : c ≤ P * (1 - z)) : c ≤ P - 1 := by
  have hmul := (div_le_iff₀ hP).1 hz
  nlinarith

end

end CI2ZF.HolantCoupling
