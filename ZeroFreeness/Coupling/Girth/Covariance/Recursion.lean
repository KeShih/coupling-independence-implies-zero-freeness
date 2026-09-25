import ZeroFreeness.Coupling.Girth.Analysis.Covariance

/-! Exact simultaneous supersolutions for the two source-response norms. -/
namespace ZeroFreeness.Appendix.Girth
noncomputable section

def covarianceAU (r a ε χ : ℝ) : ℝ := r * χ + a * ε * χ ^ 2
def covarianceAV (r χ : ℝ) : ℝ := r * χ
def covarianceUStar (r a ε χ ℓ : ℝ) : ℝ := a * (1 + ℓ * χ) / (1 - covarianceAU r a ε χ)
def covarianceVStar (r a ε χ ℓ K : ℝ) : ℝ :=
  ((covarianceAV r χ + 2 * a * K * χ ^ 2) * covarianceUStar r a ε χ ℓ +
    2 * a * (1 + ℓ * χ)) / (1 - covarianceAV r χ)
def covarianceMStar (r a ε χ ℓ K A : ℝ) : ℝ :=
  2 * (1 + ℓ * χ + K * χ ^ 2 * covarianceUStar r a ε χ ℓ) +
    2 * A * χ * covarianceVStar r a ε χ ℓ K

theorem covariance_supersolution {r a ε χ ℓ K : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (_hε : 0 ≤ ε) (hχ : 0 ≤ χ) (hℓ : 0 ≤ ℓ) (hK : 0 ≤ K)
    (hAU : covarianceAU r a ε χ < 1) (hAV : covarianceAV r χ < 1) :
    0 ≤ covarianceUStar r a ε χ ℓ ∧ 0 ≤ covarianceVStar r a ε χ ℓ K ∧
    covarianceAU r a ε χ * covarianceUStar r a ε χ ℓ + a * (1 + ℓ * χ) = covarianceUStar r a ε χ ℓ ∧
    covarianceAV r χ * covarianceVStar r a ε χ ℓ K +
      (covarianceAV r χ + 2 * a * K * χ ^ 2) * covarianceUStar r a ε χ ℓ +
      2 * a * (1 + ℓ * χ) = covarianceVStar r a ε χ ℓ K := by
  have hu : 0 ≤ covarianceUStar r a ε χ ℓ := by unfold covarianceUStar; positivity
  have hv : 0 ≤ covarianceVStar r a ε χ ℓ K := by
    unfold covarianceVStar
    exact div_nonneg (add_nonneg (mul_nonneg (add_nonneg (mul_nonneg hr hχ)
      (by positivity)) hu) (by positivity)) (by linarith)
  refine ⟨hu, hv, ?_, ?_⟩
  · unfold covarianceUStar
    field_simp [ne_of_gt (sub_pos.mpr hAU)]
    ring
  · unfold covarianceVStar
    field_simp [ne_of_gt (sub_pos.mpr hAV)]
    ring

theorem covariance_recursion_bounded {r a ε χ ℓ K : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hε : 0 ≤ ε) (hχ : 0 ≤ χ) (hℓ : 0 ≤ ℓ) (hK : 0 ≤ K)
    (hAU : covarianceAU r a ε χ < 1) (hAV : covarianceAV r χ < 1)
    (U V : ℕ → ℝ) (hU0 : U 0 = 0) (hV0 : V 0 = 0)
    (hU : ∀ n, U (n+1) ≤ covarianceAU r a ε χ * U n + a * (1 + ℓ * χ))
    (hV : ∀ n, V (n+1) ≤ covarianceAV r χ * V n +
      (covarianceAV r χ + 2 * a * K * χ ^ 2) * U n + 2 * a * (1 + ℓ * χ)) :
    ∀ n, U n ≤ covarianceUStar r a ε χ ℓ ∧ V n ≤ covarianceVStar r a ε χ ℓ K := by
  have hs := covariance_supersolution hr ha hε hχ hℓ hK hAU hAV
  have hAU0 : 0 ≤ covarianceAU r a ε χ := by unfold covarianceAU; positivity
  have hAV0 : 0 ≤ covarianceAV r χ := mul_nonneg hr hχ
  have hcross : 0 ≤ covarianceAV r χ + 2 * a * K * χ ^ 2 := by positivity
  intro n
  induction n with
  | zero => simpa only [hU0, hV0] using And.intro hs.1 hs.2.1
  | succ n ih =>
    constructor
    · calc
        _ ≤ _ := hU n
        _ ≤ covarianceAU r a ε χ * covarianceUStar r a ε χ ℓ + a * (1 + ℓ * χ) :=
          add_le_add (mul_le_mul_of_nonneg_left ih.1 hAU0) le_rfl
        _ = _ := hs.2.2.1
    · calc
        _ ≤ _ := hV n
        _ ≤ covarianceAV r χ * covarianceVStar r a ε χ ℓ K +
            (covarianceAV r χ + 2 * a * K * χ ^ 2) * covarianceUStar r a ε χ ℓ + 2 * a * (1 + ℓ * χ) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left ih.2 hAV0)
            (mul_le_mul_of_nonneg_left ih.1 hcross)) le_rfl
        _ = _ := hs.2.2.2

theorem covariance_oscillation_bounded {r a ε χ ℓ K A u v m : ℝ}
    (hχ : 0 ≤ χ) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hu : u ≤ covarianceUStar r a ε χ ℓ) (hv : v ≤ covarianceVStar r a ε χ ℓ K)
    (hm : m ≤ 2 * (1 + ℓ * χ + K * χ ^ 2 * u) + 2 * A * χ * v) :
    m ≤ covarianceMStar r a ε χ ℓ K A := by
  apply hm.trans
  unfold covarianceMStar
  gcongr

end
end ZeroFreeness.Appendix.Girth
