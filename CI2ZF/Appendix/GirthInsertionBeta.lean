import CI2ZF.Appendix.GirthInsertionScalar

namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω U : Type*} [Fintype Ω] [Fintype U] [DecidableEq U]

namespace ScalarInsertion
variable (I : ScalarInsertion Ω U)

def aB : ℝ := 1 / (1 - I.B)
def phi (ω : Ω) : ℝ := Real.exp (-I.s * I.X ω)
def beta (u : U) (ω : Ω) : ℝ :=
  I.s / (1 - I.s * I.p u) - (I.s / I.T) * ∏ j ∈ Finset.univ.erase u, (1 - I.s * I.π j ω)
def betaBound (Vπ VM : ℝ) : ℝ :=
  I.aB ^ 2 * Real.sqrt Vπ + I.aB * Real.exp (I.amplitude + 2 * I.remainderBudget) *
    (Real.sqrt VM + I.remainderBudget)

theorem aB_pos : 0 < I.aB := one_div_pos.mpr (sub_pos.mpr I.B_lt_one)

theorem Y_phi_close (ω : Ω) : |I.Y ω - I.phi ω| ≤ I.remainderBudget := by
  have hx : -I.s * I.X ω ≤ 0 := by nlinarith [mul_nonneg I.s_nonneg (I.X_bounds ω).1]
  have he := exp_nonpos_lipschitz (by linarith [(I.logError_bounds ω).1] :
    -I.s * I.X ω - I.logError ω ≤ 0) hx
  rw [← I.log_Y, Real.exp_log (I.Y_pos ω)] at he
  change |I.Y ω - I.phi ω| ≤ _ at he
  have hnorm : |(-I.s * I.X ω - I.logError ω) - -I.s * I.X ω| = I.logError ω := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (I.logError_bounds ω).1]
  exact he.trans (by rw [I.log_Y, hnorm]; exact (I.logError_bounds ω).2)

theorem sqrt_variance_phi {V : ℝ} (hV : variance I.μ I.M ≤ V) :
    Real.sqrt (variance I.μ I.phi) ≤ Real.sqrt V := by
  have hμ0 : 0 ≤ expectReal I.μ I.X := by
    simpa only [expectReal_const] using expectReal_mono I.μ fun ω => (I.X_bounds ω).1
  have hp (ω : Ω) : |I.phi ω - Real.exp (-I.s * expectReal I.μ I.X)| ≤ |I.M ω| := by
    have he := exp_nonpos_lipschitz
      (show -I.s * I.X ω ≤ 0 by nlinarith [mul_nonneg I.s_nonneg (I.X_bounds ω).1])
      (show -I.s * expectReal I.μ I.X ≤ 0 by nlinarith [mul_nonneg I.s_nonneg hμ0])
    change |I.phi ω - Real.exp (-I.s * expectReal I.μ I.X)| ≤ _ at he
    have hid : -I.s * I.X ω - -I.s * expectReal I.μ I.X = -I.s * I.M ω := by rw [I.M_eq]; ring
    rw [hid, abs_mul, abs_neg, abs_of_nonneg I.s_nonneg] at he
    exact he.trans ((mul_le_mul_of_nonneg_right I.s_le_one (abs_nonneg _)).trans_eq (one_mul _))
  calc
    _ ≤ finiteL2 I.μ (fun ω => I.phi ω - Real.exp (-I.s * expectReal I.μ I.X)) :=
      sqrt_variance_le_error I.μ I.phi _
    _ ≤ finiteL2 I.μ I.M := by
      have hh := finiteL2_pointwise I.μ
        (fun ω => I.phi ω - Real.exp (-I.s * expectReal I.μ I.X)) I.M zero_le_one
        (by simpa only [one_mul] using hp)
      simpa only [one_mul] using hh
    _ = Real.sqrt (variance I.μ I.M) := by
      have hh := finiteL2_centered I.μ I.M
      simpa only [I.M_mean, sub_zero] using hh
    _ ≤ _ := Real.sqrt_le_sqrt hV

theorem sqrt_variance_Y {V : ℝ} (hV : variance I.μ I.M ≤ V) :
    Real.sqrt (variance I.μ I.Y) ≤ Real.sqrt V + I.remainderBudget := by
  exact (sqrt_variance_add_error I.μ I.Y I.phi I.remainderBudget_nonneg I.Y_phi_close).trans
    (add_le_add (I.sqrt_variance_phi hV) le_rfl)

theorem reciprocal_scaled_bound {x : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ I.B) :
    0 ≤ I.s / (1 - I.s * x) ∧ I.s / (1 - I.s * x) ≤ I.aB := by
  have hx := I.scaled_bounds hx0 hxB
  have hd : 0 < 1 - I.s * x := by linarith [I.B_lt_one]
  constructor
  · exact div_nonneg I.s_nonneg hd.le
  · exact (div_le_div_of_nonneg_right I.s_le_one hd.le).trans
      (one_div_le_one_div_of_le (sub_pos.mpr I.B_lt_one) (by linarith))

theorem reciprocal_difference_bound (u : U) (ω : Ω) :
    |I.s * (1 / (1 - I.s * I.p u) - 1 / (1 - I.s * I.π u ω))| ≤
      I.aB ^ 2 * |I.π u ω - I.p u| := by
  have hp := I.reciprocal_scaled_bound (I.p_bounds u).1 (I.p_bounds u).2
  have hπ := I.reciprocal_scaled_bound (I.π_nonneg u ω) (I.π_le u ω)
  have hdp : 1 - I.s * I.p u ≠ 0 := ne_of_gt (by
    have hh := I.scaled_bounds (I.p_bounds u).1 (I.p_bounds u).2
    linarith [I.B_lt_one])
  have hdπ : 1 - I.s * I.π u ω ≠ 0 := ne_of_gt (by
    have hh := I.scaled_bounds (I.π_nonneg u ω) (I.π_le u ω)
    linarith [I.B_lt_one])
  have he : I.s * (1 / (1 - I.s * I.p u) - 1 / (1 - I.s * I.π u ω)) =
      (I.s / (1 - I.s * I.p u)) * (I.s / (1 - I.s * I.π u ω)) * (I.p u - I.π u ω) := by
    field_simp
    ring
  rw [he, abs_mul, abs_mul, abs_of_nonneg hp.1, abs_of_nonneg hπ.1, abs_sub_comm]
  exact mul_le_mul_of_nonneg_right (by simpa only [pow_two] using mul_le_mul hp.2 hπ.2 hπ.1 I.aB_pos.le)
    (abs_nonneg _)

theorem beta_decomposition (u : U) (ω : Ω) : I.beta u ω =
    I.s * (1 / (1 - I.s * I.p u) - 1 / (1 - I.s * I.π u ω)) +
      (I.s / (1 - I.s * I.π u ω)) * (1 - I.Y ω / I.T) := by
  have hd : 1 - I.s * I.π u ω ≠ 0 := ne_of_gt (by
    have hh := I.scaled_bounds (I.π_nonneg u ω) (I.π_le u ω)
    linarith [I.B_lt_one])
  have hh := Finset.mul_prod_erase (Finset.univ : Finset U) (fun j => 1 - I.s * I.π j ω) (Finset.mem_univ u)
  change (1 - I.s * I.π u ω) * (∏ j ∈ Finset.univ.erase u, (1 - I.s * I.π j ω)) = I.Y ω at hh
  dsimp only [beta]
  rw [← hh]
  field_simp
  ring

theorem beta_second_pointwise (u : U) (ω : Ω) :
    |(I.s / (1 - I.s * I.π u ω)) * (1 - I.Y ω / I.T)| ≤
      (I.aB / I.T) * |I.Y ω - I.T| := by
  have hπ := I.reciprocal_scaled_bound (I.π_nonneg u ω) (I.π_le u ω)
  have he : 1 - I.Y ω / I.T = (I.T - I.Y ω) / I.T := by field_simp [I.T_pos.ne']
  rw [he, abs_mul, abs_of_nonneg hπ.1, abs_div, abs_of_pos I.T_pos, abs_sub_comm]
  calc
    _ ≤ I.aB * (|I.Y ω - I.T| / I.T) := mul_le_mul_of_nonneg_right hπ.2
      (div_nonneg (abs_nonneg _) I.T_pos.le)
    _ = _ := by ring

theorem beta_finiteL2_bound {Vπ VM : ℝ} (hVπ : ∀ u, variance I.μ (I.π u) ≤ Vπ)
    (hVM : variance I.μ I.M ≤ VM) (u : U) : finiteL2 I.μ (I.beta u) ≤ I.betaBound Vπ VM := by
  let f : Ω → ℝ := fun ω => I.s * (1 / (1 - I.s * I.p u) - 1 / (1 - I.s * I.π u ω))
  let g : Ω → ℝ := fun ω => (I.s / (1 - I.s * I.π u ω)) * (1 - I.Y ω / I.T)
  have hf : finiteL2 I.μ f ≤ I.aB ^ 2 * Real.sqrt Vπ := by
    calc
      _ ≤ I.aB ^ 2 * finiteL2 I.μ (fun ω => I.π u ω - I.p u) :=
        finiteL2_pointwise I.μ f _ (sq_nonneg _) (I.reciprocal_difference_bound u)
      _ = I.aB ^ 2 * Real.sqrt (variance I.μ (I.π u)) := by rw [p, finiteL2_centered]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hVπ u)) (sq_nonneg _)
  have hg : finiteL2 I.μ g ≤ I.aB * Real.exp (I.amplitude + 2 * I.remainderBudget) *
      (Real.sqrt VM + I.remainderBudget) := by
    calc
      _ ≤ (I.aB / I.T) * finiteL2 I.μ (fun ω => I.Y ω - I.T) :=
        finiteL2_pointwise I.μ g _ (div_nonneg I.aB_pos.le I.T_pos.le) (I.beta_second_pointwise u)
      _ = (I.aB / I.T) * Real.sqrt (variance I.μ I.Y) := by rw [T, finiteL2_centered]
      _ ≤ (I.aB / I.T) * (Real.sqrt VM + I.remainderBudget) :=
        mul_le_mul_of_nonneg_left (I.sqrt_variance_Y hVM) (div_nonneg I.aB_pos.le I.T_pos.le)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (add_nonneg (Real.sqrt_nonneg _) I.remainderBudget_nonneg)
        have ht : 1 / I.T ≤ Real.exp (I.amplitude + 2 * I.remainderBudget) := by
          calc
            _ ≤ 1 / Real.exp (-I.amplitude - I.remainderBudget) :=
              one_div_le_one_div_of_le (Real.exp_pos _) I.T_lower
            _ = Real.exp (I.amplitude + I.remainderBudget) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
            _ ≤ _ := Real.exp_le_exp.mpr (by linarith [I.remainderBudget_nonneg])
        simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left ht I.aB_pos.le
  calc
    _ = finiteL2 I.μ (fun ω => f ω + g ω) := by congr 1; funext ω; exact I.beta_decomposition u ω
    _ ≤ _ := finiteL2_add_le I.μ f g
    _ ≤ _ := add_le_add hf hg

theorem beta_mean_square_bound {Vπ VM : ℝ} (hVπ : ∀ u, variance I.μ (I.π u) ≤ Vπ)
    (hVM : variance I.μ I.M ≤ VM) (u : U) :
    expectReal I.μ (fun ω => I.beta u ω ^ 2) ≤ I.betaBound Vπ VM ^ 2 := by
  rw [← finiteL2_sq]
  exact pow_le_pow_left₀ (finiteL2_nonneg I.μ (I.beta u)) (I.beta_finiteL2_bound hVπ hVM u) 2

end ScalarInsertion
end
end CI2ZF.Appendix.Girth
