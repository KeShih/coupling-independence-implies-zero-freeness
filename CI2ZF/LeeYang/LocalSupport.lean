import CI2ZF.Potts.Transfer.LocalResponseLog
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Local field polynomials have a fixed hard support. Their normalized
perturbation is bounded by averaging monomials, so neither the number of
admissible states nor the names of the local vertices enter the radius. -/
namespace CI2ZF.LeeYang
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {A W C : Type*} [Fintype W]

/-- A local field polynomial with its actual finite set of surviving states. -/
def supportedFieldPartition (T : Finset A) (σ : A → W → C) (ℓ : W → C → ℂ) : ℂ :=
  ∑ a ∈ T, ∏ w, ℓ w (σ a w)

@[simp] theorem supportedFieldPartition_one (T : Finset A) (σ : A → W → C) :
    supportedFieldPartition T σ (fun _ _ => 1) = (T.card : ℂ) := by
  simp [supportedFieldPartition]

theorem supportedFieldPartition_zero_at_one_iff (T : Finset A) (σ : A → W → C) :
    supportedFieldPartition T σ (fun _ _ => 1) = 0 ↔ T = ∅ := by
  simp

/-- Perturbing fields never creates a hard-admissible local state. -/
theorem supportedFieldPartition_zero_of_zero_at_one (T : Finset A) (σ : A → W → C)
    (hz : supportedFieldPartition T σ (fun _ _ => 1) = 0) (ℓ : W → C → ℂ) :
    supportedFieldPartition T σ ℓ = 0 := by
  rw [(supportedFieldPartition_zero_at_one_iff T σ).mp hz]
  simp [supportedFieldPartition]

theorem supportedFieldPartition_one_ne_zero (T : Finset A) (σ : A → W → C)
    (hT : T.Nonempty) : supportedFieldPartition T σ (fun _ _ => 1) ≠ 0 := by
  simpa using hT.ne_empty

/-- An explicit product perturbation bound, including the empty product. -/
theorem norm_prod_sub_one_le (s : Finset W) (f : W → ℂ) {θ : ℝ}
    (_hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hf : ∀ w ∈ s, ‖f w - 1‖ ≤ θ) :
    ‖(∏ w ∈ s, f w) - 1‖ ≤ ((2 : ℝ) ^ s.card - 1) * θ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert w s hw ih =>
    have hwθ := hf w (Finset.mem_insert_self _ _)
    have hw2 : ‖f w‖ ≤ 2 := by
      have ht := norm_add_le (f w - 1) (1 : ℂ)
      simp only [sub_add_cancel, norm_one] at ht
      linarith
    have ih' := ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))
    rw [Finset.prod_insert hw, Finset.card_insert_of_notMem hw]
    have he : f w * (∏ v ∈ s, f v) - 1 =
        f w * ((∏ v ∈ s, f v) - 1) + (f w - 1) := by ring
    rw [he]
    calc
      _ ≤ ‖f w * ((∏ v ∈ s, f v) - 1)‖ + ‖f w - 1‖ := norm_add_le _ _
      _ = ‖f w‖ * ‖(∏ v ∈ s, f v) - 1‖ + ‖f w - 1‖ := by rw [norm_mul]
      _ ≤ 2 * (((2 : ℝ) ^ s.card - 1) * θ) + θ :=
        add_le_add (mul_le_mul hw2 ih' (norm_nonneg _) (by norm_num)) hwθ
      _ = _ := by rw [pow_succ]; ring

theorem norm_local_monomial_sub_one_le (σ : W → C) (ℓ : W → C → ℂ)
    {B : ℕ} (hB : Fintype.card W ≤ B) {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hℓ : ∀ w c, ‖ℓ w c - 1‖ ≤ θ) :
    ‖(∏ w, ℓ w (σ w)) - 1‖ ≤ (2 : ℝ)^B * θ := by
  have h := norm_prod_sub_one_le Finset.univ (fun w => ℓ w (σ w)) hθ hθ1
    (fun w _ => hℓ w (σ w))
  have hp : (2 : ℝ) ^ Fintype.card W ≤ (2 : ℝ)^B :=
    pow_le_pow_right₀ (by norm_num) hB
  simp only [Finset.card_univ] at h
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hθ)

theorem supportedFieldPartition_error (T : Finset A) (σ : A → W → C)
    (ℓ : W → C → ℂ) {B : ℕ} (hB : Fintype.card W ≤ B)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hℓ : ∀ w c, ‖ℓ w c - 1‖ ≤ θ) :
    ‖supportedFieldPartition T σ ℓ - supportedFieldPartition T σ (fun _ _ => 1)‖ ≤
      (T.card : ℝ) * ((2 : ℝ)^B * θ) := by
  simp only [supportedFieldPartition, Finset.prod_const_one, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ T, ‖(∏ w, ℓ w (σ a w)) - 1‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ T, (2 : ℝ)^B * θ := Finset.sum_le_sum
      (fun a _ => norm_local_monomial_sub_one_le (σ a) ℓ hB hθ hθ1 hℓ)
    _ = _ := by simp

/-- The admissible-state count cancels from the relative error. -/
theorem supportedFieldPartition_relative (T : Finset A) (σ : A → W → C)
    (hT : T.Nonempty) (ℓ : W → C → ℂ) {B : ℕ} (hB : Fintype.card W ≤ B)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (hℓ : ∀ w c, ‖ℓ w c - 1‖ ≤ θ) :
    ‖supportedFieldPartition T σ ℓ / supportedFieldPartition T σ (fun _ _ => 1) - 1‖ ≤
      (2 : ℝ)^B * θ := by
  rw [div_sub_one (supportedFieldPartition_one_ne_zero T σ hT), norm_div]
  have hbase : ‖supportedFieldPartition T σ (fun _ _ => 1)‖ = (T.card : ℝ) := by simp
  rw [hbase]
  apply (div_le_iff₀ (by exact_mod_cast hT.card_pos : (0 : ℝ) < T.card)).mpr
  simpa only [mul_comm] using supportedFieldPartition_error T σ ℓ hB hθ hθ1 hℓ

/-- A concrete common field radius for the local logarithmic budget. -/
def localFieldRadius (B : ℕ) (α : ℝ) : ℝ :=
  min (1 / 2) (min (1 / 2) (α / 12) / (2 : ℝ)^B)

theorem localFieldRadius_pos (B : ℕ) {α : ℝ} (hα : 0 < α) :
    0 < localFieldRadius B α := by unfold localFieldRadius; positivity

theorem localFieldRadius_le_half (B : ℕ) (α : ℝ) : localFieldRadius B α ≤ 1 / 2 :=
  min_le_left _ _

theorem localFieldRadius_budget (B : ℕ) (α : ℝ) :
    (2 : ℝ)^B * localFieldRadius B α ≤ min (1 / 2) (α / 12) := by
  have h := min_le_right (1 / 2 : ℝ) (min (1 / 2) (α / 12) / (2 : ℝ)^B)
  simpa only [localFieldRadius, mul_comm] using
    (le_div_iff₀ (by positivity : (0 : ℝ) < 2^B)).mp h

theorem supportedFieldPartition_local_control (T : Finset A) (σ : A → W → C)
    (hT : T.Nonempty) {B : ℕ} (hB : Fintype.card W ≤ B) {α : ℝ} (hα : 0 < α)
    (ℓ : W → C → ℂ) (hℓ : ∀ w c, ‖ℓ w c - 1‖ ≤ localFieldRadius B α) :
    ‖supportedFieldPartition T σ ℓ / supportedFieldPartition T σ (fun _ _ => 1) - 1‖ ≤
      min (1 / 2) (α / 12) :=
  (supportedFieldPartition_relative T σ hT ℓ hB (localFieldRadius_pos B hα).le
    (le_trans (localFieldRadius_le_half B α) (by norm_num)) hℓ).trans (localFieldRadius_budget B α)

/-- Local field sums are holomorphic along every holomorphic field path. -/
theorem supportedFieldPartition_differentiableOn (T : Finset A) (σ : A → W → C)
    (ℓ : ℂ → W → C → ℂ) (D : Set ℂ)
    (hℓ : ∀ w c, DifferentiableOn ℂ (fun z => ℓ z w c) D) :
    DifferentiableOn ℂ (fun z => supportedFieldPartition T σ (ℓ z)) D := by
  unfold supportedFieldPartition
  apply DifferentiableOn.fun_sum
  intro a _
  exact DifferentiableOn.fun_finsetProd (fun w _ => hℓ w (σ a w))

/-- A canonical normalized local logarithm, with its analytic branch and
uniform budget proved from the explicit product estimate. -/
theorem supportedFieldPartition_log_control (T : Finset A) (σ : A → W → C)
    (hT : T.Nonempty) {B : ℕ} (hB : Fintype.card W ≤ B) {α r : ℝ} (hα : 0 < α)
    (ℓ : ℂ → W → C → ℂ) (hzero : ℓ 0 = fun _ _ => 1)
    (hℓ : ∀ w c, DifferentiableOn ℂ (fun z => ℓ z w c) (Metric.ball 0 r))
    (hnear : ∀ z ∈ Metric.ball 0 r, ∀ w c, ‖ℓ z w c - 1‖ ≤ localFieldRadius B α) :
    let F := fun z => supportedFieldPartition T σ (ℓ z)
    principalResponseLog F 0 0 = 0 ∧
      DifferentiableOn ℂ (principalResponseLog F 0) (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, Complex.exp (principalResponseLog F 0 z) = F z / F 0) ∧
      ∀ z ∈ Metric.ball 0 r, ‖principalResponseLog F 0 z‖ ≤ α / 8 := by
  apply principalResponseLog_control
  · exact supportedFieldPartition_differentiableOn T σ ℓ _ hℓ
  · rw [hzero]
    exact supportedFieldPartition_one_ne_zero T σ hT
  · intro z hz
    rw [hzero]
    exact supportedFieldPartition_local_control T σ hT hB hα (ℓ z) (hnear z hz)

end
end CI2ZF.LeeYang
