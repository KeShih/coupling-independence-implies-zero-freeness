import CI2ZF.Coupling.CV.CorrectedCharge

/-!
# Lemma `lem:cv-high` (companion appendix CV, Lemma 5.21)

Here `H_c` is the actual per-colour charge `canonicalColourCharge` of the
coupling (for the chosen root/off-root partners), `k_c` is
`(rootNeighbours FX X v c).card`, `N₁₁(c)` is `safety11Count`, and
`γ_loss = gammaLoss ρ Δ θ φ` is the actual coefficient of `eq:cv-gammas` on
the paper's domain `ρ ≥ 1809/1000`, `Δ ≥ 125`, `θ, φ ∈ [0,1]`;
`Λ_bulk = bulk = 1331/750`.

* `cv_high_bulk`: for `k_c ≥ 3`, `H_c + γ_loss N₁₁(c) ≤ -1 + Λ_bulk k_c`
  (the root-allowed hypothesis of the paper is not needed).
* `cv_high_missing`: for `c` absent from the active root list,
  `H_c + γ_loss k_c ≤ (39743/27000) k_c ≤ Λ_bulk k_c`, the second inequality
  strict when `k_c > 0`.
* `cv_high_missing_corrected`: the same bound for the library's corrected
  charge `correctedRegularCharge`, which for a missing colour is exactly
  `H_c + γ_loss k_c` (for every gain coefficient).
-/

namespace CI2ZF.Appendix.CV

open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]

lemma bulk_value : bulk = 1331 / 750 := rfl

/-- First display of `lem:cv-high`. -/
theorem cv_high_bulk
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hm : 3 ≤ (rootNeighbours FX X v c).card)
    {ρ Δ θ φ : ℝ} (hρ : 1809 / 1000 ≤ ρ) (hΔ : 125 ≤ Δ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    canonicalColourCharge h hca hcb (choice.left c) (choice.right c) +
        gammaLoss ρ Δ θ φ * safety11Count FX FY X Y v c ≤
      -1 + bulk * (rootNeighbours FX X v c).card := by
  obtain ⟨-, -, -, hl⟩ := geometric_coefficients_box hρ hΔ hθ hφ
  have hb := canonicalColourCharge_high_corrected h choice hca hcb hm (gain := 0)
    (loss := gammaLoss ρ Δ θ φ) le_rfl (by linarith)
  simpa only [zero_mul, sub_zero] using hb

/-- Second display of `lem:cv-high`: a missing colour. -/
theorem cv_high_missing
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (hca : c ≠ a) (hcb : c ≠ b) (u w : V)
    (hc : c ∉ FX.list v)
    {ρ Δ θ φ : ℝ} (hρ : 1809 / 1000 ≤ ρ) (hΔ : 125 ≤ Δ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    canonicalColourCharge h hca hcb u w +
        gammaLoss ρ Δ θ φ * (rootNeighbours FX X v c).card ≤
      (39743 / 27000 : ℝ) * (rootNeighbours FX X v c).card ∧
    (39743 / 27000 : ℝ) * (rootNeighbours FX X v c).card ≤
      bulk * (rootNeighbours FX X v c).card ∧
    (0 < (rootNeighbours FX X v c).card →
      (39743 / 27000 : ℝ) * (rootNeighbours FX X v c).card <
        bulk * (rootNeighbours FX X v c).card) := by
  obtain ⟨-, -, -, hl⟩ := geometric_coefficients_box hρ hΔ hθ hφ
  have hb := canonicalColourCharge_le_of_unavailable h hca hcb u w hc
  have hk : (0 : ℝ) ≤ (rootNeighbours FX X v c).card := Nat.cast_nonneg _
  have hlk := mul_le_mul_of_nonneg_right hl hk
  refine ⟨by linarith, ?_, fun hpos => ?_⟩
  · rw [bulk_value]
    exact mul_le_mul_of_nonneg_right (by norm_num) hk
  · rw [bulk_value]
    have hk' : (0 : ℝ) < (rootNeighbours FX X v c).card := by exact_mod_cast hpos
    exact mul_lt_mul_of_pos_right (by norm_num) hk'

/-- The missing-colour bound for the library's corrected charge. -/
theorem cv_high_missing_corrected
    {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b c : C}
    (h : RootLocalPair FX FY X Y v a b) (choice : GlobalChoice h)
    (hca : c ≠ a) (hcb : c ≠ b) (hc : c ∉ FX.list v) (gain : ℝ)
    {ρ Δ θ φ : ℝ} (hρ : 1809 / 1000 ≤ ρ) (hΔ : 125 ≤ Δ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) :
    correctedRegularCharge h choice c hca hcb gain (gammaLoss ρ Δ θ φ) =
      canonicalColourCharge h hca hcb (choice.left c) (choice.right c) +
        gammaLoss ρ Δ θ φ * (rootNeighbours FX X v c).card ∧
    correctedRegularCharge h choice c hca hcb gain (gammaLoss ρ Δ θ φ) ≤
      (39743 / 27000 : ℝ) * (rootNeighbours FX X v c).card := by
  have he : correctedRegularCharge h choice c hca hcb gain (gammaLoss ρ Δ θ φ) =
      canonicalColourCharge h hca hcb (choice.left c) (choice.right c) +
        gammaLoss ρ Δ θ φ * (rootNeighbours FX X v c).card := by
    simp only [correctedRegularCharge, if_neg hc, mul_zero, sub_zero]
  refine ⟨he, ?_⟩
  rw [he]
  exact (cv_high_missing h hca hcb _ _ hc hρ hΔ hθ hφ).1

end

end CI2ZF.Appendix.CV
