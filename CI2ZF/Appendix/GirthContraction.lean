import CI2ZF.Appendix.GirthMarginal
import CI2ZF.Appendix.GirthJacobian

/-!
# Uniform contraction of the explicit weighted tree matrix

The parent probability law in this file is computed from the actual weighted
recursion. Its marginal and occupancy bounds are proved in the imported
files. This establishes the quantitative matrix estimate underlying
`hg-strong-jacobian`; identification with the differential and integration
along potential-coordinate segments remain separate analytic steps.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C D : Type*} [Fintype C] [Fintype D] [DecidableEq C]

/-- A soft local tree recursion, including the structural parameters of its
children. The fields are local weight, degree, and mass conditions. -/
structure LocalRecursion (C D : Type*) [Fintype C] [Fintype D] where
  unary : C → ℝ
  unary_pos : ∀ c, 0 < unary c
  unary_le_one : ∀ c, unary c ≤ 1
  input : D → C → ℝ
  childDegree : D → ℕ
  childPalette : D → ℝ
  child_slack : ∀ i, (childDegree i : ℝ) + 4 ≤ childPalette i
  input_nonneg : ∀ i c, 0 ≤ input i c
  input_cap : ∀ i c, input i c ≤ messageCap (childDegree i) (childPalette i)
  input_mass : ∀ i, ∑ c, input i c ≤ 1
  palette : ℝ
  palette_lower : palette ≤ ∑ c, unary c
  parent_slack : (Fintype.card D : ℝ) + 4 ≤ palette

namespace LocalRecursion

variable (I : LocalRecursion C D)

theorem palette_pos : 0 < I.palette := by
  have hd : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
  linarith [I.parent_slack]

theorem input_quarter (i : D) (c : C) : I.input i c ≤ 1 / 4 :=
  (I.input_cap i c).trans (messageCap_bounds (I.child_slack i)).2

theorem partition_pos : 0 < messagePartition I.unary I.input := by
  have hfour := messagePartition_ge_four
    (fun c => ⟨(I.unary_pos c).le, I.unary_le_one c⟩) I.palette_lower
    (show (1 : ℝ) ≤ 1 from le_rfl)
    (fun i => show MessageDomain 1 (I.input i) from
      ⟨fun c => ⟨I.input_nonneg i c, I.input_quarter i c⟩, I.input_mass i⟩)
    (show 4 ≤ I.palette - (Fintype.card D : ℝ) by linarith [I.parent_slack])
  linarith

def law : FinDist C := messageLaw I.unary I.input
  (fun c => messageWeight_nonneg (fun b => (I.unary_pos b).le)
    (fun i b => by linarith [I.input_quarter i b]) c) I.partition_pos

theorem law_pos (c : C) : 0 < I.law.w c := messageMarginal_pos I.unary_pos
  (fun i b => by linarith [I.input_quarter i b]) I.partition_pos c

def parentOdds : ℝ := messageOddsBound (Fintype.card D) I.palette

def parentEntropy : ℝ := entropyCorrection I.parentOdds

def childEntropy (i : D) : ℝ := entropyCorrection (messageOddsBound (I.childDegree i) (I.childPalette i))

theorem law_lt_one (c : C) : I.law.w c < 1 :=
  (sharp_message_marginal I.unary I.input
    (fun b => ⟨(I.unary_pos b).le, I.unary_le_one b⟩) I.palette_lower I.parent_slack
    (fun i b => ⟨I.input_nonneg i b, I.input_quarter i b⟩) I.input_mass c).2.1

theorem law_odds_le (c : C) : I.law.w c / (1 - I.law.w c) ≤ I.parentOdds :=
  (sharp_message_marginal I.unary I.input
    (fun b => ⟨(I.unary_pos b).le, I.unary_le_one b⟩) I.palette_lower I.parent_slack
    (fun i b => ⟨I.input_nonneg i b, I.input_quarter i b⟩) I.input_mass c).2.2.1

theorem law_occupancy_le (c : C) :
    I.law.w c * (∑ i, I.input i c) ≤
      Real.exp (-1 + ((∑ i, I.childEntropy i) + (Fintype.card D : ℝ)) / I.palette) / I.palette := by
  have h := message_occupancy_bound I.unary I.input
    (fun i => messageCap (I.childDegree i) (I.childPalette i))
    (fun b => ⟨(I.unary_pos b).le, I.unary_le_one b⟩) I.palette_pos I.palette_lower
    (fun i => ⟨(messageCap_bounds (I.child_slack i)).1,
      lt_of_le_of_lt (messageCap_bounds (I.child_slack i)).2 (by norm_num)⟩)
    (fun i b => ⟨I.input_nonneg i b, I.input_cap i b⟩) I.input_mass c
  simp_rw [cap_log_eq_entropy (I.child_slack _)] at h
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, childEntropy, law, messageLaw] using h

theorem inverse_square_bound (c : C) :
    1 / (1 - I.law.w c) ^ 2 ≤ Real.exp (2 * I.parentOdds) := by
  have hp : 0 < 1 - I.law.w c := sub_pos.mpr (I.law_lt_one c)
  have hi : 1 / (1 - I.law.w c) = 1 + I.law.w c / (1 - I.law.w c) := by field_simp; ring
  have hb : 1 / (1 - I.law.w c) ≤ Real.exp I.parentOdds := by
    rw [hi]
    linarith [I.law_odds_le c, Real.add_one_le_exp I.parentOdds]
  have hs := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / (1 - I.law.w c)) hb 2
  have he : Real.exp I.parentOdds ^ 2 = Real.exp (2 * I.parentOdds) := by
    simpa using (Real.exp_nat_mul I.parentOdds 2).symm
  simpa only [div_pow, one_pow, he] using hs

theorem parent_weight_bound : 1 / (1 - I.parentEntropy) ≤ Real.exp (I.parentOdds / 2) :=
  entropy_weight_inverse_bound (messageOddsBound_pos I.parent_slack)
    (messageOddsBound_le_third I.parent_slack)

theorem parent_weight_nonneg : 0 ≤ 1 / (1 - I.parentEntropy) := by
  apply div_nonneg zero_le_one
  exact sub_nonneg.mpr (entropyCorrection_lt_one (messageOddsBound_pos I.parent_slack)
    (messageOddsBound_le_third I.parent_slack)).le

/-- A complete uniform matrix contraction for the actual local recursion.
The child hypothesis is precisely the squared weighted block norm budget. -/
theorem weighted_matrix_contraction (h : D → C → ℝ) {q T : ℝ}
    (hq : I.palette ≤ q) (hT : 0 ≤ T)
    (hh : ∀ i, (∑ c, h i c ^ 2) ≤ T * (1 - I.childEntropy i)) :
    (1 / (1 - I.parentEntropy)) * (∑ c, blockAction I.law I.input h c ^ 2) ≤
      Real.exp (-8 / (81 * q)) * T := by
  let S : ℝ := ∑ i, I.childEntropy i
  let d : ℝ := Fintype.card D
  let E : ℝ := ∑ c, blockAction I.law I.input h c ^ 2
  let F₁ : ℝ := Real.exp (2 * I.parentOdds)
  let F₂ : ℝ := Real.exp (-1 + (S + d) / I.palette) / I.palette
  have hF₁ : 0 ≤ F₁ := (Real.exp_pos _).le
  have hF₂ : 0 ≤ F₂ := div_nonneg (Real.exp_pos _).le I.palette_pos.le
  have hin : (∑ i, ∑ c, h i c ^ 2) ≤ T * (d - S) := by
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun i _ => hh i)
    simpa only [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, d, S] using hs
  have hb := blockAction_energy_le I.law I.law_pos I.input h I.input_nonneg hF₁ hF₂
    I.inverse_square_bound I.law_occupancy_le
  have hE : E ≤ F₁ * F₂ * (T * (d - S)) := hb.trans
    (mul_le_mul_of_nonneg_left hin (mul_nonneg hF₁ hF₂))
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun c _ => sq_nonneg _
  calc
    _ ≤ Real.exp (I.parentOdds / 2) * E :=
      mul_le_mul_of_nonneg_right I.parent_weight_bound hE0
    _ ≤ Real.exp (I.parentOdds / 2) * (F₁ * F₂ * (T * (d - S))) :=
      mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
    _ = Real.exp (I.parentOdds / 2) * F₁ * F₂ * (T * (d - S)) := by ring
    _ ≤ Real.exp ((5 / 2 : ℝ) * I.parentOdds - 8 / I.palette) * T :=
      weighted_amortization I.palette_pos I.parent_slack hT
    _ ≤ Real.exp (-8 / (81 * q)) * T := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (contraction_exponent_margin I.parent_slack hq)) hT

end LocalRecursion

end

end CI2ZF.Appendix.Girth
