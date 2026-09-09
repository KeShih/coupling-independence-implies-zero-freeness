import CI2ZF.Appendix.Girth.Tree.Relative
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Spatial decay and root relative mixing for finite trees

Potential-coordinate decay is converted to ordinary message distance with
the exact inverse derivative bound `3/8`, then to the root logarithmic
estimate with the constant stated in the appendix.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset Set PottsCI

set_option linter.unusedSectionVars false

noncomputable section

theorem inversePotential_quarter {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (Real.log 3)) :
    inversePotential u ≤ 1 / 4 := by
  have hlo : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu.1
  have hhi : Real.exp u ≤ 3 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3)] using Real.exp_le_exp.mpr hu.2
  have hd : 0 < Real.exp u + 1 := by positivity
  have hr0 : 0 ≤ (Real.exp u - 1) / (Real.exp u + 1) := div_nonneg (by linarith) hd.le
  have hr1 : (Real.exp u - 1) / (Real.exp u + 1) ≤ 1 / 2 :=
    (div_le_iff₀ hd).mpr (by linarith)
  unfold inversePotential
  nlinarith

theorem inversePotentialDeriv_bounds {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (Real.log 3)) :
    0 ≤ inversePotentialDeriv u ∧ inversePotentialDeriv u ≤ 3 / 8 := by
  have hm0 := inversePotential_nonneg u
  have hm1 := inversePotential_quarter hu
  have hs0 := Real.sqrt_nonneg (inversePotential u)
  have hs1 : Real.sqrt (inversePotential u) ≤ 1 / 2 := by
    nlinarith [Real.sq_sqrt hm0]
  rw [inversePotential_deriv_formula hu.1]
  refine ⟨mul_nonneg (by linarith) hs0, ?_⟩
  have haux : 0 ≤ 3 / 4 - (1 / 2 : ℝ) * Real.sqrt (inversePotential u) - inversePotential u := by
    linarith
  have hp := mul_nonneg (sub_nonneg.mpr hs1) haux
  nlinarith [Real.sq_sqrt hm0]

theorem raw_distance_from_potential {m n : ℝ}
    (hm : m ∈ Icc (0 : ℝ) (1 / 4)) (hn : n ∈ Icc (0 : ℝ) (1 / 4)) :
    |n - m| ≤ (3 / 8 : ℝ) * |messagePotential n - messagePotential m| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Icc (0 : ℝ) (Real.log 3)) => (hasDerivAt_inversePotential u).hasDerivWithinAt)
    (fun u hu => by
      rw [Real.norm_eq_abs, abs_of_nonneg (inversePotentialDeriv_bounds hu).1]
      exact (inversePotentialDeriv_bounds hu).2)
    (convex_Icc (0 : ℝ) (Real.log 3)) (messagePotential_mem hm) (messagePotential_mem hn)
  simpa only [Real.norm_eq_abs,
    inversePotential_messagePotential hm.1 (by linarith [hm.2]),
    inversePotential_messagePotential hn.1 (by linarith [hn.2])] using h

variable {C : Type*} [Fintype C] [DecidableEq C]

theorem raw_l1_from_potential (m n : C → ℝ)
    (hm : ∀ c, m c ∈ Icc (0 : ℝ) (1 / 4))
    (hn : ∀ c, n c ∈ Icc (0 : ℝ) (1 / 4)) :
    (∑ c, |n c - m c|) ≤ (3 / 8 : ℝ) * Real.sqrt (Fintype.card C : ℝ) *
      Real.sqrt (∑ c, (messagePotential (n c) - messagePotential (m c)) ^ 2) := by
  let f : C → ℝ := fun c => messagePotential (n c) - messagePotential (m c)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C) (fun _ => (1 : ℝ)) (fun c => |f c|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hE : 0 ≤ ∑ c, f c ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hsum0 : 0 ≤ ∑ c, |f c| := Finset.sum_nonneg fun c _ => abs_nonneg _
  have hroot : (∑ c, |f c|) ≤ Real.sqrt (Fintype.card C : ℝ) * Real.sqrt (∑ c, f c ^ 2) := by
    have hq := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card C) : (0 : ℝ) ≤ Fintype.card C)
    have he := Real.sq_sqrt hE
    have hh : (Real.sqrt (Fintype.card C : ℝ) * Real.sqrt (∑ c, f c ^ 2)) ^ 2 =
        (Fintype.card C : ℝ) * ∑ c, f c ^ 2 := by rw [mul_pow, hq, he]
    have hp : 0 ≤ Real.sqrt (Fintype.card C : ℝ) * Real.sqrt (∑ c, f c ^ 2) := by positivity
    nlinarith
  calc
    _ ≤ ∑ c, (3 / 8 : ℝ) * |f c| := Finset.sum_le_sum fun c _ => raw_distance_from_potential (hm c) (hn c)
    _ = (3 / 8 : ℝ) * ∑ c, |f c| := (Finset.mul_sum ..).symm
    _ ≤ (3 / 8 : ℝ) * (Real.sqrt (Fintype.card C : ℝ) * Real.sqrt (∑ c, f c ^ 2)) :=
      mul_le_mul_of_nonneg_left hroot (by norm_num)
    _ = _ := by ring

def decayRate (q : ℝ) : ℝ := Real.exp (-4 / (81 * q))

theorem decayRate_pos (q : ℝ) : 0 < decayRate q := Real.exp_pos _

theorem decayRate_lt_one {q : ℝ} (hq : 0 < q) : decayRate q < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem decayRate_sq (q : ℝ) : decayRate q ^ 2 = Real.exp (-8 / (81 * q)) := by
  rw [decayRate, ← Real.exp_nat_mul]
  congr 1
  ring

namespace CavityTree

theorem weightSquare_lower {t : CavityTree C} {Δ : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hq : Δ + 3 ≤ Fintype.card C) (hbudget : t.DegreeBudget Δ) :
    1 ≤ t.weightSquare x := by
  have he : 0 < 1 - t.entropy x := sub_pos.mpr (entropy_lt_one hx hq hbudget)
  apply (le_div_iff₀ he).mpr
  have hz : 0 ≤ t.entropy x := entropyCorrection_nonneg
    (messageOddsBound_pos (t.palette_slack hx hq hbudget))
  linarith

/-- Ordinary message decay with the appendix's exact `3q/8` prefactor. -/
theorem message_l1_decay {k : ℕ} {t u : CavityTree C} (hag : Agreement k t u)
    {Δ : ℕ} {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hq : Δ + 3 ≤ Fintype.card C)
    (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ) :
    (∑ c, |(1 - x) * u.probability x c - (1 - x) * t.probability x c|) ≤
      (3 / 8 : ℝ) * (Fintype.card C : ℝ) * Real.exp (1 / 12) * Real.log 3 *
        decayRate (Fintype.card C) ^ k := by
  let E : ℝ := ∑ c, (messagePotential ((1 - x) * u.probability x c) -
    messagePotential ((1 - x) * t.probability x c)) ^ 2
  let B : ℝ := Real.exp (1 / 12) * Real.sqrt (Fintype.card C : ℝ) * Real.log 3 *
    decayRate (Fintype.card C) ^ k
  have hE : 0 ≤ E := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hB : 0 ≤ B := by
    unfold B
    exact mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
      (Real.log_nonneg (by norm_num))) (pow_nonneg (decayRate_pos _).le _)
  have hBsq : B ^ 2 = Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k *
      cutEnergy (Fintype.card C) := by
    have he : Real.exp (1 / 12 : ℝ) ^ 2 = Real.exp (1 / 6) := by
      rw [← Real.exp_nat_mul]
      norm_num
    have hp : (decayRate (Fintype.card C) ^ k) ^ 2 =
        (decayRate (Fintype.card C) ^ 2) ^ k := by simp only [← pow_mul, Nat.mul_comm]
    unfold B cutEnergy
    rw [mul_pow, mul_pow, mul_pow, he, Real.sq_sqrt (Nat.cast_nonneg _), hp, decayRate_sq]
    ring
  have hdecay := potential_decay hag hx hx1 hq ht hu
  have hEmul : E ≤ t.weightSquare x * E := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (weightSquare_lower hx.le hq ht) hE
  have hEb : E ≤ B ^ 2 := by rw [hBsq]; exact hEmul.trans hdecay
  have hroot : Real.sqrt E ≤ B := by nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg E]
  have hraw := raw_l1_from_potential
    (fun c => (1 - x) * t.probability x c) (fun c => (1 - x) * u.probability x c)
    (t.scaled_probability_domain hx hx1.le hq ht).1 (u.scaled_probability_domain hx hx1.le hq hu).1
  calc
    _ ≤ (3 / 8 : ℝ) * Real.sqrt (Fintype.card C : ℝ) * Real.sqrt E := hraw
    _ ≤ (3 / 8 : ℝ) * Real.sqrt (Fintype.card C : ℝ) * B := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by
      unfold B
      have hs := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card C) : (0 : ℝ) ≤ Fintype.card C)
      calc
        _ = (3 / 8 : ℝ) * Real.sqrt (Fintype.card C : ℝ) ^ 2 * Real.exp (1 / 12) *
            Real.log 3 * decayRate (Fintype.card C) ^ k := by ring
        _ = _ := by rw [hs]

/-- The full root has only three slack units. All child messages are actual
cavity probabilities, so their established bounds apply. -/
theorem root_partition_three (d : ℕ) (b : C → ℕ) (t : Fin d → CavityTree C)
    {Δ : ℕ} {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hq : Δ + 3 ≤ Fintype.card C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (t i).DegreeBudget Δ) :
    3 ≤ messagePartition (paletteWeight x b) (fun i c => (1 - x) * (t i).probability x c) := by
  have hdom := fun i => (t i).scaled_probability_domain hx hx1 hq (ht i)
  have hpart := messagePartition_lower
    (fun c => ⟨paletteWeight_nonneg hx.le b c, paletteWeight_le_one hx.le hx1 b c⟩)
    (fun i c => ⟨((hdom i).1 c).1, by linarith [((hdom i).1 c).2]⟩)
    (fun i => (hdom i).2.trans (by linarith : 1 - x ≤ 1))
  have hpal := palette_mass_lower hx.le b
  have hslack := root_three_slack (s := 1 - x) hq hroot (by linarith)
  simp only [Fintype.card_fin, mul_one, Nat.cast_sum] at *
  linarith

/-- Uniform logarithmic relative SSM on the actual finite-tree Gibbs laws.
The depth is `k+2`: the shell-adjacent update is bounded by the potential
diameter and the next `k` updates contract. -/
theorem relative_spatial_decay (k d : ℕ) (b : C → ℕ) (t u : Fin d → CavityTree C)
    (hag : ∀ i, Agreement k (t i) (u i))
    {Δ : ℕ} {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hq : Δ + 3 ≤ Fintype.card C)
    (hroot : d + (∑ c, b c) ≤ Δ)
    (ht : ∀ i, (t i).DegreeBudget Δ) (hu : ∀ i, (u i).DegreeBudget Δ) (c : C) :
    |Real.log ((CavityTree.node d b t).probability x c /
      (CavityTree.node d b u).probability x c)| ≤
      (5 / 8 : ℝ) * (Δ : ℝ) * (Fintype.card C : ℝ) * Real.exp (1 / 12) * Real.log 3 *
        decayRate (Fintype.card C) ^ k := by
  have h := relative_root_bound (paletteWeight x b)
    (fun i c => (1 - x) * (t i).probability x c)
    (fun i c => (1 - x) * (u i).probability x c)
    (fun c => ⟨pow_pos hx _, paletteWeight_le_one hx.le hx1.le b c⟩)
    (fun i => ((t i).scaled_probability_domain hx hx1.le hq (ht i)).1)
    (fun i => ((u i).scaled_probability_domain hx hx1.le hq (hu i)).1)
    (root_partition_three d b t hx hx1.le hq hroot ht)
    (root_partition_three d b u hx hx1.le hq hroot hu) c
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) fun i _ =>
    message_l1_decay (hag i) hx hx1 hq (ht i) (hu i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hd : (d : ℝ) ≤ Δ := by exact_mod_cast (show d ≤ Δ by omega)
  have hp : 0 ≤ (3 / 8 : ℝ) * (Fintype.card C : ℝ) * Real.exp (1 / 12) * Real.log 3 *
      decayRate (Fintype.card C) ^ k := by
    exact mul_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num)))
      (pow_nonneg (decayRate_pos _).le _)
  have hd' := mul_le_mul_of_nonneg_right hd hp
  have hs' : (∑ i, ∑ c, |(1 - x) * (t i).probability x c - (1 - x) * (u i).probability x c|) ≤
      (Δ : ℝ) * ((3 / 8 : ℝ) * (Fintype.card C : ℝ) * Real.exp (1 / 12) * Real.log 3 *
        decayRate (Fintype.card C) ^ k) := by
    simpa only [abs_sub_comm] using hs.trans hd'
  exact h.trans (by nlinarith)

end CavityTree

end

end CI2ZF.Appendix.Girth
