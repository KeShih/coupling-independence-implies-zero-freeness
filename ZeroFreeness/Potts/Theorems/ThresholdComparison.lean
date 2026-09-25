import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Comparison of integer colour thresholds (main.tex, lines 236-241)

`main.tex` compares the new condition `q ≥ 11Δ/6` (for `Δ ≥ 2`) with the
three earlier rows of `tab:intro-thresholds`:

* Bencs, Davies, Patel, Regts: `q ≥ eΔ + 1`;
* Liu, Sinclair, Srivastava: `Δ ≥ 3`, `q ≥ 2Δ`;
* Bencs, Berrekkal, Regts (2026): `q, Δ ≥ 3`, `q ≥ 1.998Δ`.

It claims that for integer `q` the new condition is strictly weaker than
the previous ones for `Δ = 2` and every `Δ ≥ 6`, and coincides with
`q ≥ 2Δ` for `3 ≤ Δ ≤ 5`.  Both claims are proved below, with `q : ℕ`.
-/

namespace ZeroFreeness.Potts

/-- The new condition of `thm:intro-main`: `Δ ≥ 2` and `q ≥ 11Δ/6`. -/
def NewCond (q Δ : ℕ) : Prop := 2 ≤ Δ ∧ (11 : ℝ) / 6 * Δ ≤ q

/-- Bencs, Davies, Patel, and Regts: `q ≥ eΔ + 1`. -/
def BDPRCond (q Δ : ℕ) : Prop := Real.exp 1 * Δ + 1 ≤ q

/-- Liu, Sinclair, and Srivastava: `Δ ≥ 3` and `q ≥ 2Δ`. -/
def LSSCond (q Δ : ℕ) : Prop := 3 ≤ Δ ∧ (2 : ℝ) * Δ ≤ q

/-- Bencs, Berrekkal, and Regts (2026): `q, Δ ≥ 3` and `q ≥ 1.998Δ`. -/
def BBRCond (q Δ : ℕ) : Prop := 3 ≤ q ∧ 3 ≤ Δ ∧ (1.998 : ℝ) * Δ ≤ q

/-- Some earlier row of the table applies. -/
def PreviousCond (q Δ : ℕ) : Prop := BDPRCond q Δ ∨ LSSCond q Δ ∨ BBRCond q Δ

theorem newCond_iff (q Δ : ℕ) : NewCond q Δ ↔ 2 ≤ Δ ∧ 11 * Δ ≤ 6 * q := by
  unfold NewCond
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, ?_⟩
    have : (11 : ℝ) * Δ ≤ 6 * q := by linarith
    exact_mod_cast this
  · rintro ⟨h2, h⟩
    refine ⟨h2, ?_⟩
    have : (11 : ℝ) * Δ ≤ 6 * q := by exact_mod_cast h
    linarith

theorem lssCond_iff (q Δ : ℕ) : LSSCond q Δ ↔ 3 ≤ Δ ∧ 2 * Δ ≤ q := by
  unfold LSSCond
  constructor
  · rintro ⟨h3, h⟩
    exact ⟨h3, by exact_mod_cast h⟩
  · rintro ⟨h3, h⟩
    exact ⟨h3, by exact_mod_cast h⟩

theorem bbrCond_iff (q Δ : ℕ) : BBRCond q Δ ↔ 3 ≤ q ∧ 3 ≤ Δ ∧ 1998 * Δ ≤ 1000 * q := by
  unfold BBRCond
  constructor
  · rintro ⟨h3, h3', h⟩
    refine ⟨h3, h3', ?_⟩
    have : (1998 : ℝ) * Δ ≤ 1000 * q := by norm_num at h; linarith
    exact_mod_cast this
  · rintro ⟨h3, h3', h⟩
    refine ⟨h3, h3', ?_⟩
    have : (1998 : ℝ) * Δ ≤ 1000 * q := by exact_mod_cast h
    norm_num
    linarith

theorem bdprCond_imp {q Δ : ℕ} (h : BDPRCond q Δ) : 2 * Δ + 1 ≤ q := by
  unfold BDPRCond at h
  have he : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero
    linarith
  have hΔ : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  have : (2 : ℝ) * Δ + 1 ≤ q := by nlinarith
  exact_mod_cast this

theorem not_bdprCond_of_lt {q Δ : ℕ} (h : q ≤ 2 * Δ) : ¬ BDPRCond q Δ := by
  intro hb
  have := bdprCond_imp hb
  omega

/-- Every earlier row implies the new condition as soon as `Δ ≥ 2`. -/
theorem previousCond_imp_newCond {q Δ : ℕ} (hΔ : 2 ≤ Δ) (h : PreviousCond q Δ) :
    NewCond q Δ := by
  rw [newCond_iff]
  refine ⟨hΔ, ?_⟩
  rcases h with h | h | h
  · have := bdprCond_imp h
    omega
  · have := (lssCond_iff q Δ).mp h
    omega
  · have := (bbrCond_iff q Δ).mp h
    omega

/-- **Strictly weaker for `Δ = 2` and every `Δ ≥ 6`.**  Every earlier row
implies the new condition, and some integer `q` satisfies the new condition
but none of the earlier rows. -/
theorem newCond_strictly_weaker {Δ : ℕ} (hΔ : Δ = 2 ∨ 6 ≤ Δ) :
    (∀ q : ℕ, PreviousCond q Δ → NewCond q Δ) ∧
      ∃ q : ℕ, NewCond q Δ ∧ ¬ PreviousCond q Δ := by
  have hΔ2 : 2 ≤ Δ := by omega
  refine ⟨fun q h => previousCond_imp_newCond hΔ2 h, ?_⟩
  rcases hΔ with rfl | hΔ6
  · refine ⟨4, (newCond_iff 4 2).mpr ⟨le_rfl, by norm_num⟩, ?_⟩
    rintro (h | h | h)
    · exact not_bdprCond_of_lt (by norm_num) h
    · exact absurd h.1 (by norm_num)
    · exact absurd h.2.1 (by norm_num)
  · refine ⟨(11 * Δ + 5) / 6, (newCond_iff _ _).mpr ⟨hΔ2, by omega⟩, ?_⟩
    rintro (h | h | h)
    · exact not_bdprCond_of_lt (by omega) h
    · have := (lssCond_iff _ _).mp h
      omega
    · have := (bbrCond_iff _ _).mp h
      omega

/-- For `Δ ≥ 6`, the smallest integer `q = ⌈11Δ/6⌉` allowed by the new
condition satisfies no earlier row.  (For `Δ = 2` the witness is `q = 4`,
see `newCond_strictly_weaker`.) -/
theorem least_new_colour_not_previous {Δ : ℕ} (hΔ : 6 ≤ Δ) :
    NewCond ((11 * Δ + 5) / 6) Δ ∧ ¬ PreviousCond ((11 * Δ + 5) / 6) Δ ∧
      ∀ q : ℕ, NewCond q Δ → (11 * Δ + 5) / 6 ≤ q := by
  refine ⟨(newCond_iff _ _).mpr ⟨by omega, by omega⟩, ?_, ?_⟩
  · rintro (h | h | h)
    · exact not_bdprCond_of_lt (by omega) h
    · have := (lssCond_iff _ _).mp h
      omega
    · have := (bbrCond_iff _ _).mp h
      omega
  · intro q hq
    have := (newCond_iff q Δ).mp hq
    omega

/-- **Coincidence for `3 ≤ Δ ≤ 5`.**  For integer `q`, the new condition is
equivalent to `q ≥ 2Δ` (the LSS row), and it is also equivalent to the BBR
row; every earlier row still implies it. -/
theorem newCond_iff_lss_of_small {Δ : ℕ} (h3 : 3 ≤ Δ) (h5 : Δ ≤ 5) (q : ℕ) :
    (NewCond q Δ ↔ LSSCond q Δ) ∧ (NewCond q Δ ↔ BBRCond q Δ) ∧
      (PreviousCond q Δ → NewCond q Δ) := by
  refine ⟨?_, ?_, previousCond_imp_newCond (by omega)⟩
  · rw [newCond_iff, lssCond_iff]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨h3, by omega⟩
    · rintro ⟨_, h⟩
      exact ⟨by omega, by omega⟩
  · rw [newCond_iff, bbrCond_iff]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨by omega, h3, by interval_cases Δ <;> omega⟩
    · rintro ⟨_, _, h⟩
      exact ⟨by omega, by omega⟩

end ZeroFreeness.Potts
