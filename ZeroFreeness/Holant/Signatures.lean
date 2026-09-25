import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic

/-!
# Finite log-concave Holant signatures

Signatures are extended by zero beyond their finite arity.  The hypotheses
are precisely nonnegativity, interval positive support, adjacent
log-concavity, and a positive zeroth entry.  Initial support, all shift
comparisons, residual closure, and finiteness are conclusions.
-/

namespace ZeroFreeness.Holant

/-- A finite symmetric Boolean signature, with a positive empty input. -/
structure Signature where
  arity : ℕ
  value : ℕ → ℝ
  nonneg : ∀ k, 0 ≤ value k
  outside : ∀ k, arity < k → value k = 0
  zero_pos : 0 < value 0
  support_interval : ∀ {i j k}, i ≤ j → j ≤ k →
    0 < value i → 0 < value k → 0 < value j
  log_concave : ∀ k, k + 2 ≤ arity →
    value k * value (k + 2) ≤ value (k + 1) ^ 2

namespace Signature

@[ext] theorem ext {f g : Signature} (ha : f.arity = g.arity)
    (hv : f.value = g.value) : f = g := by
  cases f
  cases g
  cases ha
  cases hv
  rfl

/-- Positive support is an initial interval; this follows from interval
support and positivity at zero. -/
theorem initial_support (f : Signature) {i k : ℕ} (hik : i ≤ k)
    (hk : 0 < f.value k) : 0 < f.value i :=
  f.support_interval (Nat.zero_le i) hik f.zero_pos hk

theorem positive_le_arity (f : Signature) {k : ℕ} (hk : 0 < f.value k) :
    k ≤ f.arity := by
  by_contra h
  rw [f.outside k (by omega)] at hk
  exact (lt_irrefl 0) hk

theorem zero_of_zero_le (f : Signature) {i k : ℕ} (hi : f.value i = 0)
    (hik : i ≤ k) : f.value k = 0 := by
  by_contra hk
  have hkpos := lt_of_le_of_ne (f.nonneg k) (Ne.symm hk)
  have hipos := f.initial_support hik hkpos
  simp [hi] at hipos

/-- Successive ratios decrease throughout the positive support. -/
theorem ratio_antitone (f : Signature) {a b : ℕ} (hab : a ≤ b)
    (hb : 0 < f.value (b + 1)) :
    f.value (b + 1) / f.value b ≤ f.value (a + 1) / f.value a := by
  induction b generalizing a with
  | zero =>
      have : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      rcases eq_or_lt_of_le hab with hab | hab
      · subst a
        exact le_rfl
      have ha : a ≤ b := by omega
      have hb1 : 0 < f.value (b + 1) :=
        f.initial_support (by omega) hb
      have hb0 : 0 < f.value b := f.initial_support (by omega) hb
      have harity : b + 2 ≤ f.arity := by
        simpa [Nat.succ_eq_add_one, Nat.add_assoc] using f.positive_le_arity hb
      have hlc := f.log_concave b harity
      have hstep : f.value (b + 1 + 1) / f.value (b + 1) ≤
          f.value (b + 1) / f.value b := by
        apply (div_le_div_iff₀ hb1 hb0).2
        nlinarith [hlc]
      exact hstep.trans (ih ha hb1)

/-- The division-free ratio comparison, including all zero tails. -/
theorem ratio_cross_le (f : Signature) {k l : ℕ} (hkl : k ≤ l) :
    f.value k * f.value (l + 1) ≤ f.value (k + 1) * f.value l := by
  by_cases hz : f.value (l + 1) = 0
  · simp only [hz, mul_zero]
    exact mul_nonneg (f.nonneg _) (f.nonneg _)
  have hp : 0 < f.value (l + 1) :=
    lt_of_le_of_ne (f.nonneg _) (Ne.symm hz)
  have hk : 0 < f.value k := f.initial_support (by omega) hp
  have hl : 0 < f.value l := f.initial_support (by omega) hp
  have h := (div_le_div_iff₀ hl hk).1 (f.ratio_antitone hkl hp)
  simpa [mul_comm] using h

/-- The multiplicative form of shift monotonicity, before normalization. -/
theorem shift_product_le (f : Signature) (t k : ℕ) :
    f.value (t + k) * f.value 0 ≤ f.value t * f.value k := by
  induction k with
  | zero => simp
  | succ k ih =>
      by_cases hzero : f.value (t + (k + 1)) = 0
      · simp only [hzero, zero_mul]
        exact mul_nonneg (f.nonneg t) (f.nonneg (k + 1))
      have hpos : 0 < f.value (t + (k + 1)) :=
        lt_of_le_of_ne (f.nonneg _) (Ne.symm hzero)
      have hk : 0 < f.value k := f.initial_support (by omega) hpos
      have htk : 0 < f.value (t + k) := f.initial_support (by omega) hpos
      have hratio := f.ratio_antitone (a := k) (b := t + k) (by omega)
        (show 0 < f.value (t + k + 1) by simpa [Nat.add_assoc] using hpos)
      have hcross : f.value (t + (k + 1)) * f.value k ≤
          f.value (k + 1) * f.value (t + k) := by
        simpa [Nat.add_assoc] using (div_le_div_iff₀ htk hk).1 hratio
      have hscale₁ := mul_le_mul_of_nonneg_right hcross (le_of_lt f.zero_pos)
      have hscale₂ := mul_le_mul_of_nonneg_left ih (f.nonneg (k + 1))
      apply (mul_le_mul_iff_left₀ hk).1
      calc
        (f.value (t + Nat.succ k) * f.value 0) * f.value k =
            (f.value (t + (k + 1)) * f.value k) * f.value 0 := by
              simp only [Nat.succ_eq_add_one]
              ring
        _ ≤ (f.value (k + 1) * f.value (t + k)) * f.value 0 := hscale₁
        _ = f.value (k + 1) * (f.value (t + k) * f.value 0) := by ring
        _ ≤ f.value (k + 1) * (f.value t * f.value k) := hscale₂
        _ = (f.value t * f.value (Nat.succ k)) * f.value k := by
          simp only [Nat.succ_eq_add_one]
          ring

/-- Equation (holant-shift-monotonicity), including the zero-support cases. -/
theorem shift_monotonicity (f : Signature) (hnorm : f.value 0 = 1)
    {t k : ℕ} (ht : 0 < f.value t) :
    f.value (t + k) / f.value t ≤ f.value k := by
  apply (div_le_iff₀ ht).2
  have h := f.shift_product_le t k
  rw [hnorm, mul_one] at h
  simpa [mul_comm] using h

theorem first_shift_le (f : Signature) (hnorm : f.value 0 = 1)
    (hfirst : 0 < f.value 1) (k : ℕ) :
    f.value (k + 1) / f.value 1 ≤ f.value k := by
  simpa [Nat.add_comm] using f.shift_monotonicity hnorm (k := k) hfirst

/-- Every normalized signature has at most geometric growth, uniformly
including entries outside its positive support. -/
theorem value_growth_bound (f : Signature) (hnorm : f.value 0 = 1) (k : ℕ) :
    f.value k ≤ (max 1 (f.value 1)) ^ k := by
  induction k with
  | zero => simp [hnorm]
  | succ k ih =>
    have hs := f.shift_product_le 1 k
    rw [hnorm, mul_one] at hs
    calc
      f.value (k + 1) ≤ f.value 1 * f.value k := by simpa [Nat.add_comm] using hs
      _ ≤ max 1 (f.value 1) * (max 1 (f.value 1)) ^ k :=
        mul_le_mul (le_max_right _ _) ih (f.nonneg k)
          ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))
      _ = (max 1 (f.value 1)) ^ (k + 1) := by rw [pow_succ']

/-- The normalized residual after fixing `j` selected inputs and leaving
`r` free inputs. The entries beyond `r` are extended by zero. -/
noncomputable def normalizedResidual (f : Signature) (j r : ℕ)
    (hjr : j + r ≤ f.arity) (hj : 0 < f.value j) : Signature where
  arity := r
  value k := if k ≤ r then f.value (j + k) / f.value j else 0
  nonneg k := by
    split
    · exact div_nonneg (f.nonneg _) (le_of_lt hj)
    · exact le_rfl
  outside k hk := by simp [show ¬ k ≤ r by omega]
  zero_pos := by simp [ne_of_gt hj]
  support_interval := by
    intro a b c hab hbc ha hc
    have hcr : c ≤ r := by
      by_contra h
      simp [h] at hc
    have hbr : b ≤ r := by omega
    have har : a ≤ r := by omega
    simp only [if_pos har] at ha
    simp only [if_pos hcr] at hc
    simp only [if_pos hbr]
    apply div_pos
    · apply f.support_interval (i := j + a) (k := j + c) (by omega) (by omega)
      · exact (div_pos_iff_of_pos_right hj).1 ha
      · exact (div_pos_iff_of_pos_right hj).1 hc
    · exact hj
  log_concave k hk := by
    have hk0 : k ≤ r := by omega
    have hk1 : k + 1 ≤ r := by omega
    simp only [if_pos hk0, if_pos hk1, if_pos hk]
    have hlc := f.log_concave (j + k) (by omega)
    have hscale := div_le_div_of_nonneg_right hlc (sq_nonneg (f.value j))
    simpa [div_pow, div_mul_div_comm, Nat.add_assoc, pow_two] using hscale

@[simp] theorem normalizedResidual_arity (f : Signature) (j r : ℕ)
    (hjr : j + r ≤ f.arity) (hj : 0 < f.value j) :
    (f.normalizedResidual j r hjr hj).arity = r := rfl

@[simp] theorem normalizedResidual_value (f : Signature) (j r : ℕ)
    (hjr : j + r ≤ f.arity) (hj : 0 < f.value j) (k : ℕ) :
    (f.normalizedResidual j r hjr hj).value k =
      if k ≤ r then f.value (j + k) / f.value j else 0 := rfl

@[simp] theorem normalizedResidual_zero (f : Signature) (j r : ℕ)
    (hjr : j + r ≤ f.arity) (hj : 0 < f.value j) :
    (f.normalizedResidual j r hjr hj).value 0 = 1 := by
  simp [ne_of_gt hj]

/-- A positive residual entry is exactly a positive entry of its source. -/
theorem normalizedResidual_pos_iff (f : Signature) (j r : ℕ)
    (hjr : j + r ≤ f.arity) (hj : 0 < f.value j) {k : ℕ} (hk : k ≤ r) :
    0 < (f.normalizedResidual j r hjr hj).value k ↔ 0 < f.value (j + k) := by
  simp only [normalizedResidual_value, if_pos hk]
  exact div_pos_iff_of_pos_right hj

/-- Residuals of residuals are residuals of the original signature.  This
is an exact equality of signatures, including the normalization factors. -/
theorem normalizedResidual_comp (f : Signature) (j r : ℕ)
    (hjr : j + r ≤ f.arity) (hj : 0 < f.value j) (t s : ℕ)
    (hts : t + s ≤ r) (ht : 0 < (f.normalizedResidual j r hjr hj).value t) :
    (f.normalizedResidual j r hjr hj).normalizedResidual t s hts ht =
      f.normalizedResidual (j + t) s (by omega)
        ((f.normalizedResidual_pos_iff j r hjr hj (by omega)).1 ht) := by
  apply Signature.ext
  · rfl
  funext k
  change (if k ≤ s then
      (if t + k ≤ r then f.value (j + (t + k)) / f.value j else 0) /
        (if t ≤ r then f.value (j + t) / f.value j else 0) else 0) =
    (if k ≤ s then f.value ((j + t) + k) / f.value (j + t) else 0)
  by_cases hk : k ≤ s
  · have htkr : t + k ≤ r := by omega
    have htr : t ≤ r := by omega
    simp only [if_pos hk, if_pos htkr, if_pos htr]
    rw [div_div_div_cancel_right₀ (ne_of_gt hj)]
    rw [Nat.add_assoc]
  · simp only [if_neg hk]

/-- Bounded indices describing all admissible residuals of one signature. -/
structure ResidualData (f : Signature) where
  shift : Fin (f.arity + 1)
  remaining : Fin (f.arity + 1)
  bound : shift.val + remaining.val ≤ f.arity
  positive : 0 < f.value shift.val

@[ext] theorem ResidualData.ext {f : Signature} {d e : ResidualData f}
    (hs : d.shift = e.shift) (hr : d.remaining = e.remaining) : d = e := by
  cases d
  cases e
  cases hs
  cases hr
  rfl

instance (f : Signature) : Finite (ResidualData f) :=
  Finite.of_injective (fun d : ResidualData f => (d.shift, d.remaining))
    (fun _ _ h => ResidualData.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

noncomputable instance (f : Signature) : Fintype (ResidualData f) := Fintype.ofFinite _

noncomputable def ResidualData.signature {f : Signature} (d : ResidualData f) :
    Signature := f.normalizedResidual d.shift d.remaining d.bound d.positive

/-- Being one of the normalized residuals used in the paper. -/
def IsResidual (f g : Signature) : Prop :=
  ∃ j r, ∃ (hjr : j + r ≤ f.arity) (hj : 0 < f.value j),
    g = f.normalizedResidual j r hjr hj

/-- The actual finite list of residual signatures, with duplicate values removed. -/
noncomputable def allResiduals (f : Signature) : Finset Signature := by
  classical
  exact Finset.univ.image (fun d : ResidualData f => d.signature)

@[simp] theorem mem_allResiduals (f g : Signature) :
    g ∈ f.allResiduals ↔ f.IsResidual g := by
  classical
  simp only [allResiduals, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d.shift, d.remaining, d.bound, d.positive, rfl⟩
  · rintro ⟨j, r, hjr, hj, rfl⟩
    refine ⟨⟨⟨j, by omega⟩, ⟨r, by omega⟩, hjr, hj⟩, rfl⟩

/-- Closure is transitive, including arbitrary mixtures of zero and one
pinnings at the incident edges. -/
theorem IsResidual.trans {f g h : Signature} (hfg : f.IsResidual g)
    (hgh : g.IsResidual h) : f.IsResidual h := by
  rcases hfg with ⟨j, r, hjr, hj, rfl⟩
  rcases hgh with ⟨t, s, hts, ht, rfl⟩
  refine ⟨j + t, s, by simpa only [normalizedResidual_arity] using
    (show j + t + s ≤ f.arity by
      simp only [normalizedResidual_arity] at hts
      omega),
    (f.normalizedResidual_pos_iff j r hjr hj (by
      simp only [normalizedResidual_arity] at hts
      omega)).1 ht, ?_⟩
  exact f.normalizedResidual_comp j r hjr hj t s hts ht

theorem IsResidual.zero {f g : Signature} (hfg : f.IsResidual g) : g.value 0 = 1 := by
  rcases hfg with ⟨j, r, hjr, hj, rfl⟩
  exact f.normalizedResidual_zero j r hjr hj

/-- A zero-child restriction is a residual, with no positivity test beyond
its unchanged zeroth entry. -/
theorem zero_child_isResidual (g : Signature) (r : ℕ) (hr : r ≤ g.arity) :
    g.IsResidual (g.normalizedResidual 0 r (by omega) g.zero_pos) :=
  ⟨0, r, by omega, g.zero_pos, rfl⟩

/-- A normalized one-child shift is a residual whenever its first entry
is positive. Its definition does not use any edge activity. -/
theorem one_child_isResidual (g : Signature) (r : ℕ) (hr : r + 1 ≤ g.arity)
    (hfirst : 0 < g.value 1) :
    g.IsResidual (g.normalizedResidual 1 r (by omega) hfirst) :=
  ⟨1, r, by omega, hfirst, rfl⟩

end Signature
/-- The finite residual family generated by the input family. -/
noncomputable def residualFamily (F : Finset Signature) : Finset Signature := by
  classical
  exact F.biUnion Signature.allResiduals

@[simp] theorem mem_residualFamily (F : Finset Signature) (g : Signature) :
    g ∈ residualFamily F ↔ ∃ f ∈ F, f.IsResidual g := by
  classical
  simp [residualFamily]

/-- In particular, the residual family is finite as a set of signatures. -/
theorem residualFamily_finite (F : Finset Signature) :
    {g | ∃ f ∈ F, f.IsResidual g}.Finite := by
  convert (residualFamily F).finite_toSet using 1
  ext g
  simp

theorem residualFamily_zero (F : Finset Signature) {g : Signature}
    (hg : g ∈ residualFamily F) : g.value 0 = 1 := by
  obtain ⟨f, _, hfg⟩ := (mem_residualFamily F g).1 hg
  exact hfg.zero

/-- Every further admissible child stays in the same finite family. -/
theorem residualFamily_closed (F : Finset Signature) {g h : Signature}
    (hg : g ∈ residualFamily F) (hgh : g.IsResidual h) : h ∈ residualFamily F := by
  obtain ⟨f, hf, hfg⟩ := (mem_residualFamily F g).1 hg
  exact (mem_residualFamily F h).2 ⟨f, hf, hfg.trans hgh⟩

/-- One finite constant controls the growth of every residual signature.
The inserted value one also covers the empty input family. -/
noncomputable def residualGrowthBound (F : Finset Signature) : ℝ := by
  classical
  exact (insert 1 ((residualFamily F).image fun g => g.value 1)).max'
    (Finset.insert_nonempty _ _)

theorem residualGrowthBound_one_le (F : Finset Signature) :
    1 ≤ residualGrowthBound F := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem residualGrowthBound_nonneg (F : Finset Signature) :
    0 ≤ residualGrowthBound F := (by norm_num : (0 : ℝ) ≤ 1).trans
      (residualGrowthBound_one_le F)

theorem residual_first_le_growthBound (F : Finset Signature) {g : Signature}
    (hg : g ∈ residualFamily F) : g.value 1 ≤ residualGrowthBound F := by
  classical
  exact Finset.le_max' (insert 1 ((residualFamily F).image fun h => h.value 1))
    (g.value 1) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, hg, rfl⟩))

/-- A uniform coefficient-growth estimate for the whole residual family. -/
theorem residual_value_le_pow_growthBound (F : Finset Signature) {g : Signature}
    (hg : g ∈ residualFamily F) (k : ℕ) :
    g.value k ≤ (residualGrowthBound F) ^ k := by
  have h := g.value_growth_bound (residualFamily_zero F hg) k
  exact h.trans (pow_le_pow_left₀
    ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _))
    (max_le (residualGrowthBound_one_le F) (residual_first_le_growthBound F hg)) k)

end ZeroFreeness.Holant
