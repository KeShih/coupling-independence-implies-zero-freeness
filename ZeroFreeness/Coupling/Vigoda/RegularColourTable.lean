import ZeroFreeness.Coupling.Vigoda.RegularColourTwo

/-!
# The regular-colour table of `main.tex`, Section 4 (rows `h = 0, …, 4`)

For a regular colour with two root neighbours in distinct components of
both families, with sizes `r₁, r₂` (family `𝒞`) and `s₁, s₂` (family `𝒟`)
and feasibility bits `f₁, f₂, g₁, g₂`, the paper defines

* `H₀ = ∑ᵢ g_{rᵢ,sᵢ}(fᵢ p_{rᵢ}, gᵢ p_{sᵢ})`, the off-root bound before the
  root matches (`H0` below);
* the total correction `(1 - max rᵢ + min rᵢ) P + (1 - max sᵢ + min sᵢ) P'`,
  `P = f₁f₂ p_{1+r₁+r₂}`, `P' = g₁g₂ p_{1+s₁+s₂}` (`correction` below);

proves `Q_c ≤ H₀ + correction` (`eq:two-neighbour-reduction`) and tabulates
upper bounds by the number `h` of singletons among the four sizes:

| `h` | arrangement | `H₀` | correction | `Q_c` |
| 0 | any | 52/21 | 2/21 | 18/7 |
| 1 | any | 4/3 + 26/21 | 1/21 | 55/21 |
| 2 | one singleton in each family | 2·4/3 | 0 | 8/3 |
| 3 | any | 1 + 4/3 | 1/6 | 5/2 |
| 4 | any | 2 | 2·1/6 | 7/3 |

Here `Q_c` is the library's `flexibleFormula`, the exact per-colour charge
(`RegularColourTwo.two_piece_formulas`,
`RegularColourTwo.perColourCharge_le_two_distinct`).  Each row is proved as
stated (`table_row_zero`, …, `table_row_four`), together with the reduction
inequality (`two_neighbour_reduction`).  The entries are upper bounds, as in
the paper; computation shows the rows `h = 0, 1, 2` are not attained for
`Q_c` (the maxima are `41/21`, `16/7`, `55/21`), while `8/3` is attained in
the remaining case `h = 2` with both singletons in one family.

The finite check uses the library's integer profile `scaledP = 84 p` and
the component-size truncation at `7` (`p_s = 0` for `s ≥ 7`).
-/

namespace ZeroFreeness.RegularColourCharge
open ZeroFreeness.VigodaArithmetic PottsCI.Vigoda

/-! ## Scaled integer quantities -/

def scaledPair (r s : ℕ) (u w : ℤ) : ℤ := r * u + s * w - min u w

def h0Scaled (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : ℤ :=
  scaledPair r₁ s₁ (if f₁ then scaledP r₁ else 0) (if g₁ then scaledP s₁ else 0) +
  scaledPair r₂ s₂ (if f₂ then scaledP r₂ else 0) (if g₂ then scaledP s₂ else 0)

def rateScaled (r s : ℕ) (f g : Bool) : ℤ := if f && g then scaledP (1 + r + s) else 0

def corrScaled (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : ℤ :=
  (1 - ((max r₁ r₂ : ℕ) : ℤ) + ((min r₁ r₂ : ℕ) : ℤ)) * rateScaled r₁ r₂ f₁ f₂ +
  (1 - ((max s₁ s₂ : ℕ) : ℤ) + ((min s₁ s₂ : ℕ) : ℤ)) * rateScaled s₁ s₂ g₁ g₂

/-- The number `h` of singletons among the four sizes. -/
def singletons (r₁ r₂ s₁ s₂ : ℕ) : ℕ :=
  (if r₁ = 1 then 1 else 0) + (if r₂ = 1 then 1 else 0) +
    (if s₁ = 1 then 1 else 0) + (if s₂ = 1 then 1 else 0)

/-- Both singletons of an `h = 2` configuration lie in one family: the case
treated separately after the table. -/
def bothInOneFamily (r₁ r₂ s₁ s₂ : ℕ) : Prop := (r₁ = 1 ∧ r₂ = 1) ∨ (s₁ = 1 ∧ s₂ = 1)

instance decidableBothInOneFamily (r₁ r₂ s₁ s₂ : ℕ) :
    Decidable (bothInOneFamily r₁ r₂ s₁ s₂) := by
  unfold bothInOneFamily; infer_instance

/-- The table rows, scaled by `84`. -/
def rowH0 : ℕ → ℤ
  | 0 => 208 | 1 => 216 | 2 => 224 | 3 => 196 | _ => 168

def rowCorr : ℕ → ℤ
  | 0 => 8 | 1 => 4 | 2 => 0 | 3 => 14 | _ => 28

/-- Boolean row check, `true` in the excluded `h = 2` arrangement. -/
def rowOK (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : Bool :=
  if singletons r₁ r₂ s₁ s₂ = 2 ∧ bothInOneFamily r₁ r₂ s₁ s₂ then true
  else decide (h0Scaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ rowH0 (singletons r₁ r₂ s₁ s₂)) &&
    decide (corrScaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ rowCorr (singletons r₁ r₂ s₁ s₂))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reduction_small (r₁ r₂ s₁ s₂ : Fin 7) (f₁ f₂ g₁ g₂ pickA pickB : Bool) :
    (if pickA then r₂.val ≤ r₁.val else r₁.val ≤ r₂.val) →
    (if pickB then s₂.val ≤ s₁.val else s₁.val ≤ s₂.val) →
    flexibleCharge (r₁.val + 1) (r₂.val + 1) (s₁.val + 1) (s₂.val + 1)
      f₁ f₂ g₁ g₂ pickA pickB ≤
    h0Scaled (r₁.val + 1) (r₂.val + 1) (s₁.val + 1) (s₂.val + 1) f₁ f₂ g₁ g₂ +
      corrScaled (r₁.val + 1) (r₂.val + 1) (s₁.val + 1) (s₂.val + 1) f₁ f₂ g₁ g₂ := by
  fin_cases r₁ <;> revert r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rows_small (r₁ r₂ s₁ s₂ : Fin 7) (f₁ f₂ g₁ g₂ : Bool) :
    rowOK (r₁.val + 1) (r₂.val + 1) (s₁.val + 1) (s₂.val + 1) f₁ f₂ g₁ g₂ = true := by
  fin_cases r₁ <;> revert r₂ s₁ s₂ f₁ f₂ g₁ g₂ <;> decide

/-! ## Truncation of component sizes at `7` -/

theorem scaledP_cap (r : ℕ) : scaledP (min r 7) = scaledP r := by
  by_cases hr : r ≤ 7
  · rw [Nat.min_eq_left hr]
  · rw [Nat.min_eq_right (by omega), scaledP_zero_of_seven_le r (by omega)]
    rfl

theorem mul_scaledP_cap (r : ℕ) (f : Bool) :
    ((min r 7 : ℕ) : ℤ) * (if f then scaledP (min r 7) else 0) =
      (r : ℤ) * (if f then scaledP r else 0) := by
  by_cases hr : r ≤ 7
  · rw [Nat.min_eq_left hr]
  · rw [scaledP_cap, scaledP_zero_of_seven_le r (by omega)]
    simp

theorem scaledPair_cap (r s : ℕ) (f g : Bool) :
    scaledPair (min r 7) (min s 7) (if f then scaledP (min r 7) else 0)
        (if g then scaledP (min s 7) else 0) =
      scaledPair r s (if f then scaledP r else 0) (if g then scaledP s else 0) := by
  unfold scaledPair
  rw [mul_scaledP_cap, mul_scaledP_cap, scaledP_cap, scaledP_cap]

theorem h0Scaled_cap (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) :
    h0Scaled (min r₁ 7) (min r₂ 7) (min s₁ 7) (min s₂ 7) f₁ f₂ g₁ g₂ =
      h0Scaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  unfold h0Scaled
  rw [scaledPair_cap, scaledPair_cap]

theorem rateScaled_cap_term (r s : ℕ) (f g : Bool) :
    (1 - ((max (min r 7) (min s 7) : ℕ) : ℤ) + ((min (min r 7) (min s 7) : ℕ) : ℤ)) *
        rateScaled (min r 7) (min s 7) f g =
      (1 - ((max r s : ℕ) : ℤ) + ((min r s : ℕ) : ℤ)) * rateScaled r s f g := by
  by_cases h : r ≤ 7 ∧ s ≤ 7
  · rw [Nat.min_eq_left h.1, Nat.min_eq_left h.2]
  · have h1 : rateScaled r s f g = 0 := by
      unfold rateScaled
      rw [scaledP_zero_of_seven_le _ (by omega)]
      simp
    have h2 : rateScaled (min r 7) (min s 7) f g = 0 := by
      unfold rateScaled
      rw [scaledP_zero_of_seven_le _ (by omega)]
      simp
    rw [h1, h2, mul_zero, mul_zero]

theorem corrScaled_cap (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) :
    corrScaled (min r₁ 7) (min r₂ 7) (min s₁ 7) (min s₂ 7) f₁ f₂ g₁ g₂ =
      corrScaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  unfold corrScaled
  rw [rateScaled_cap_term, rateScaled_cap_term]

theorem cap_eq_one_iff (r : ℕ) : min r 7 = 1 ↔ r = 1 := by omega

theorem singletons_cap (r₁ r₂ s₁ s₂ : ℕ) :
    singletons (min r₁ 7) (min r₂ 7) (min s₁ 7) (min s₂ 7) = singletons r₁ r₂ s₁ s₂ := by
  simp only [singletons, cap_eq_one_iff]

theorem bothInOneFamily_cap (r₁ r₂ s₁ s₂ : ℕ) :
    bothInOneFamily (min r₁ 7) (min r₂ 7) (min s₁ 7) (min s₂ 7) ↔
      bothInOneFamily r₁ r₂ s₁ s₂ := by
  simp only [bothInOneFamily, cap_eq_one_iff]

theorem rowOK_cap (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) :
    rowOK (min r₁ 7) (min r₂ 7) (min s₁ 7) (min s₂ 7) f₁ f₂ g₁ g₂ =
      rowOK r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  unfold rowOK
  rw [singletons_cap, h0Scaled_cap, corrScaled_cap]
  simp only [bothInOneFamily_cap]

/-- Reduce four positive sizes to `Fin 7` indices. -/
theorem cap_index (r : ℕ) (hr : 1 ≤ r) : min r 7 - 1 + 1 = min r 7 := by omega

/-! ## All component sizes -/

theorem reduction_scaled (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ pickA pickB : Bool)
    (hA : if pickA then r₂ ≤ r₁ else r₁ ≤ r₂)
    (hB : if pickB then s₂ ≤ s₁ else s₁ ≤ s₂) :
    flexibleCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤
      h0Scaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ + corrScaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  let R₁ : Fin 7 := ⟨min r₁ 7 - 1, by omega⟩
  let R₂ : Fin 7 := ⟨min r₂ 7 - 1, by omega⟩
  let S₁ : Fin 7 := ⟨min s₁ 7 - 1, by omega⟩
  let S₂ : Fin 7 := ⟨min s₂ 7 - 1, by omega⟩
  have hA' : if pickA then R₂.val ≤ R₁.val else R₁.val ≤ R₂.val := by
    dsimp [R₁, R₂]
    cases pickA <;> simp at hA ⊢ <;> omega
  have hB' : if pickB then S₂.val ≤ S₁.val else S₁.val ≤ S₂.val := by
    dsimp [S₁, S₂]
    cases pickB <;> simp at hB ⊢ <;> omega
  have hc := reduction_small R₁ R₂ S₁ S₂ f₁ f₂ g₁ g₂ pickA pickB hA' hB'
  dsimp [R₁, R₂, S₁, S₂] at hc
  rw [cap_index r₁ hr₁, cap_index r₂ hr₂, cap_index s₁ hs₁, cap_index s₂ hs₂,
    flexibleCharge_cap, h0Scaled_cap, corrScaled_cap] at hc
  exact hc

theorem rowOK_all (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (f₁ f₂ g₁ g₂ : Bool) :
    rowOK r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ = true := by
  have hc := rows_small ⟨min r₁ 7 - 1, by omega⟩ ⟨min r₂ 7 - 1, by omega⟩
    ⟨min s₁ 7 - 1, by omega⟩ ⟨min s₂ 7 - 1, by omega⟩ f₁ f₂ g₁ g₂
  dsimp only at hc
  rw [cap_index r₁ hr₁, cap_index r₂ hr₂, cap_index s₁ hs₁, cap_index s₂ hs₂, rowOK_cap] at hc
  exact hc

theorem rows_scaled (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂) (f₁ f₂ g₁ g₂ : Bool)
    (hrow : ¬ (singletons r₁ r₂ s₁ s₂ = 2 ∧ bothInOneFamily r₁ r₂ s₁ s₂)) :
    h0Scaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ rowH0 (singletons r₁ r₂ s₁ s₂) ∧
      corrScaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ rowCorr (singletons r₁ r₂ s₁ s₂) := by
  have h := rowOK_all r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂
  unfold rowOK at h
  rw [if_neg hrow, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at h
  exact h

/-! ## The paper's real quantities -/

noncomputable section

/-- `H₀ = ∑ᵢ g_{rᵢ,sᵢ}(fᵢ p_{rᵢ}, gᵢ p_{sᵢ})`. -/
def H0 (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : ℝ :=
  pairCharge r₁ s₁ (if f₁ then vigodaMass r₁ else 0) (if g₁ then vigodaMass s₁ else 0) +
  pairCharge r₂ s₂ (if f₂ then vigodaMass r₂ else 0) (if g₂ then vigodaMass s₂ else 0)

/-- The total correction `(1 - max rᵢ + min rᵢ) P + (1 - max sᵢ + min sᵢ) P'`. -/
def correction (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) : ℝ :=
  (1 - ((max r₁ r₂ : ℕ) : ℝ) + ((min r₁ r₂ : ℕ) : ℝ)) * familyRootRate r₁ r₂ f₁ f₂ +
  (1 - ((max s₁ s₂ : ℕ) : ℝ) + ((min s₁ s₂ : ℕ) : ℝ)) * familyRootRate s₁ s₂ g₁ g₂

theorem ite_scaledP_cast (f : Bool) (r : ℕ) :
    (if f = true then ((scaledP r : ℤ) : ℝ) else 0) = 84 * (if f then vigodaMass r else 0) := by
  cases f <;> simp [scaledP_eq_profile]

theorem scaledPair_cast (r s : ℕ) (f g : Bool) :
    (scaledPair r s (if f then scaledP r else 0) (if g then scaledP s else 0) : ℝ) =
      84 * pairCharge r s (if f then vigodaMass r else 0) (if g then vigodaMass s else 0) := by
  unfold scaledPair pairCharge
  push_cast
  rw [ite_scaledP_cast, ite_scaledP_cast, ← mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 84)]
  ring

theorem h0Scaled_cast (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) :
    (h0Scaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) = 84 * H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  unfold h0Scaled H0
  push_cast
  rw [scaledPair_cast, scaledPair_cast]
  ring

theorem rateScaled_cast (r s : ℕ) (f g : Bool) :
    (rateScaled r s f g : ℝ) = 84 * familyRootRate r s f g := by
  unfold rateScaled familyRootRate
  split_ifs <;> simp [scaledP_eq_profile]

theorem corrScaled_cast (r₁ r₂ s₁ s₂ : ℕ) (f₁ f₂ g₁ g₂ : Bool) :
    (corrScaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) = 84 * correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  unfold corrScaled correction
  push_cast
  rw [rateScaled_cast, rateScaled_cast]
  ring

/-- **`eq:two-neighbour-reduction`**: `Q_c ≤ H₀ + correction`, for all
positive component sizes, all feasibility bits and every admissible
choice of largest components. -/
theorem two_neighbour_reduction (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ pickA pickB : Bool)
    (hA : if pickA then r₂ ≤ r₁ else r₁ ≤ r₂)
    (hB : if pickB then s₂ ≤ s₁ else s₁ ≤ s₂) :
    flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤
      H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ + correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ := by
  have h := reduction_scaled r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB
  have hR : (flexibleCharge r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB : ℝ) ≤
      (h0Scaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) + (corrScaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) := by
    exact_mod_cast h
  rw [flexibleCharge_eq_formula, h0Scaled_cast, corrScaled_cast] at hR
  linarith

/-- Generic row statement: in each of the five tabulated arrangements,
`H₀`, the correction and `Q_c` are at most the row entries. -/
theorem table_row (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ pickA pickB : Bool)
    (hA : if pickA then r₂ ≤ r₁ else r₁ ≤ r₂)
    (hB : if pickB then s₂ ≤ s₁ else s₁ ≤ s₂)
    (hrow : ¬ (singletons r₁ r₂ s₁ s₂ = 2 ∧ bothInOneFamily r₁ r₂ s₁ s₂)) :
    H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ (rowH0 (singletons r₁ r₂ s₁ s₂) : ℝ) / 84 ∧
      correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ (rowCorr (singletons r₁ r₂ s₁ s₂) : ℝ) / 84 ∧
      flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤
        ((rowH0 (singletons r₁ r₂ s₁ s₂) : ℝ) + rowCorr (singletons r₁ r₂ s₁ s₂)) / 84 := by
  obtain ⟨h1, h2⟩ := rows_scaled r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ hrow
  have h1' : (h0Scaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) ≤ rowH0 (singletons r₁ r₂ s₁ s₂) := by
    exact_mod_cast h1
  have h2' : (corrScaled r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ : ℝ) ≤ rowCorr (singletons r₁ r₂ s₁ s₂) := by
    exact_mod_cast h2
  rw [h0Scaled_cast] at h1'
  rw [corrScaled_cast] at h2'
  have hred := two_neighbour_reduction r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ## The five rows, as printed -/

section Rows
variable (r₁ r₂ s₁ s₂ : ℕ)
    (hr₁ : 1 ≤ r₁) (hr₂ : 1 ≤ r₂) (hs₁ : 1 ≤ s₁) (hs₂ : 1 ≤ s₂)
    (f₁ f₂ g₁ g₂ pickA pickB : Bool)
    (hA : if pickA then r₂ ≤ r₁ else r₁ ≤ r₂)
    (hB : if pickB then s₂ ≤ s₁ else s₁ ≤ s₂)
include hr₁ hr₂ hs₁ hs₂ hA hB

/-- Row `h = 0`: `H₀ ≤ 52/21`, correction `≤ 2/21`, `Q_c ≤ 18/7`. -/
theorem table_row_zero (hh : singletons r₁ r₂ s₁ s₂ = 0) :
    H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 52 / 21 ∧
      correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 2 / 21 ∧
      flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 18 / 7 := by
  have h := table_row r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB (by omega)
  rw [hh] at h
  norm_num [rowH0, rowCorr] at h ⊢
  exact h

/-- Row `h = 1`: `H₀ ≤ 4/3 + 26/21`, correction `≤ 1/21`, `Q_c ≤ 55/21`. -/
theorem table_row_one (hh : singletons r₁ r₂ s₁ s₂ = 1) :
    H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 4 / 3 + 26 / 21 ∧
      correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 1 / 21 ∧
      flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 55 / 21 := by
  have h := table_row r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB (by omega)
  rw [hh] at h
  norm_num [rowH0, rowCorr] at h ⊢
  exact h

/-- Row `h = 2`, one singleton in each family: `H₀ ≤ 2·4/3`,
correction `≤ 0`, `Q_c ≤ 8/3`. -/
theorem table_row_two (hh : singletons r₁ r₂ s₁ s₂ = 2)
    (heach : ¬ bothInOneFamily r₁ r₂ s₁ s₂) :
    H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 2 * (4 / 3) ∧
      correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 0 ∧
      flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 8 / 3 := by
  have h := table_row r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB
    (fun h => heach h.2)
  rw [hh] at h
  norm_num [rowH0, rowCorr] at h ⊢
  exact h

/-- Row `h = 3`: `H₀ ≤ 1 + 4/3`, correction `≤ 1/6`, `Q_c ≤ 5/2`. -/
theorem table_row_three (hh : singletons r₁ r₂ s₁ s₂ = 3) :
    H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 1 + 4 / 3 ∧
      correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 1 / 6 ∧
      flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 5 / 2 := by
  have h := table_row r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB (by omega)
  rw [hh] at h
  norm_num [rowH0, rowCorr] at h ⊢
  exact h

/-- Row `h = 4`: `H₀ ≤ 2`, correction `≤ 2·1/6`, `Q_c ≤ 7/3`. -/
theorem table_row_four (hh : singletons r₁ r₂ s₁ s₂ = 4) :
    H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 2 ∧
      correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ 2 * (1 / 6) ∧
      flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 7 / 3 := by
  have h := table_row r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB (by omega)
  rw [hh] at h
  norm_num [rowH0, rowCorr] at h ⊢
  exact h

/-- The remaining arrangement (`h = 2`, both singletons in one family) and
"every last-column entry is at most `8/3`": in all cases `Q_c ≤ 8/3`. -/
theorem table_last_column_le :
    flexibleFormula r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ pickA pickB ≤ 8 / 3 :=
  flexibleFormula_le r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ f₁ f₂ g₁ g₂ pickA pickB hA hB

end Rows

end

/-! ## Connection with the actual graph charge -/

section Graph
open Finset PottsCI PottsCI.Vigoda RootComponentGeometry ZeroFreeness.RegularColourCharge
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [Fintype C]

/-- In the tabulated case (two root neighbours, distinct components in both
families), the actual per-colour charge is `flexibleFormula` of the actual
component sizes, feasibility bits and largest-component choices. -/
theorem perColourCharge_eq_flexibleFormula {FX FY : HardListInstance V C} {X Y : V → C}
    {v u w : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v) (huw : u ≠ w)
    (hN : rootNeighbours FX X v c = {u, w})
    (hAX : offRootComponent FX X v (X v) c u ≠ offRootComponent FX X v (X v) c w)
    (hBY : offRootComponent FY Y v (Y v) c u ≠ offRootComponent FY Y v (Y v) c w) :
    perColourCharge h hca hcb = flexibleFormula
      (offRootComponent FX X v (X v) c u).card (offRootComponent FX X v (X v) c w).card
      (offRootComponent FY Y v (Y v) c u).card (offRootComponent FY Y v (Y v) c w).card
      (feasibleBool FX X v c (offRootComponent FX X v (X v) c u))
      (feasibleBool FX X v c (offRootComponent FX X v (X v) c w))
      (feasibleBool FY Y v c (offRootComponent FY Y v (Y v) c u))
      (feasibleBool FY Y v c (offRootComponent FY Y v (Y v) c w))
      (picksFirst FX X v u c) (picksFirst FY Y v u c) := by
  have hNY : rootNeighbours FY Y v c = {u, w} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hX := two_piece_formulas FX X v u w c (by rwa [h.X_root]) hav hN hAX
  have hY := two_piece_formulas FY Y v u w c (by rwa [h.Y_root])
    ((h.root_list_regular_iff c hca hcb).mp hav) hNY hBY
  dsimp only at hX hY
  have hNne : (rootNeighbours FX X v c).Nonempty := by rw [hN]; exact insert_nonempty _ _
  rw [perColourCharge, if_pos hNne, offRootCharge_two_distinct h hca hcb huw hN hAX hBY,
    hX.2.1, hY.2.1, hX.2.2.1, hX.2.2.2, hY.2.2.1, hY.2.2.2]
  unfold flexibleFormula
  ring

/-- **The table rows for the actual graph charge.**  In the tabulated case,
if the four actual component sizes fall in row `h` (any row except `h = 2`
with both singletons in one family), then `H₀`, the correction and the
per-colour charge `Q_c` are at most the row entries. -/
theorem perColourCharge_table_row {FX FY : HardListInstance V C} {X Y : V → C}
    {v u w : V} {a b c : C} (h : RootLocalPair FX FY X Y v a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hav : c ∈ FX.list v) (huw : u ≠ w)
    (hN : rootNeighbours FX X v c = {u, w})
    (hAX : offRootComponent FX X v (X v) c u ≠ offRootComponent FX X v (X v) c w)
    (hBY : offRootComponent FY Y v (Y v) c u ≠ offRootComponent FY Y v (Y v) c w)
    (hrow : ¬ (singletons
        (offRootComponent FX X v (X v) c u).card (offRootComponent FX X v (X v) c w).card
        (offRootComponent FY Y v (Y v) c u).card (offRootComponent FY Y v (Y v) c w).card = 2 ∧
      bothInOneFamily
        (offRootComponent FX X v (X v) c u).card (offRootComponent FX X v (X v) c w).card
        (offRootComponent FY Y v (Y v) c u).card (offRootComponent FY Y v (Y v) c w).card)) :
    let r₁ := (offRootComponent FX X v (X v) c u).card
    let r₂ := (offRootComponent FX X v (X v) c w).card
    let s₁ := (offRootComponent FY Y v (Y v) c u).card
    let s₂ := (offRootComponent FY Y v (Y v) c w).card
    let f₁ := feasibleBool FX X v c (offRootComponent FX X v (X v) c u)
    let f₂ := feasibleBool FX X v c (offRootComponent FX X v (X v) c w)
    let g₁ := feasibleBool FY Y v c (offRootComponent FY Y v (Y v) c u)
    let g₂ := feasibleBool FY Y v c (offRootComponent FY Y v (Y v) c w)
    H0 r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ (rowH0 (singletons r₁ r₂ s₁ s₂) : ℝ) / 84 ∧
      correction r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂ ≤ (rowCorr (singletons r₁ r₂ s₁ s₂) : ℝ) / 84 ∧
      perColourCharge h hca hcb ≤
        ((rowH0 (singletons r₁ r₂ s₁ s₂) : ℝ) + rowCorr (singletons r₁ r₂ s₁ s₂)) / 84 := by
  intro r₁ r₂ s₁ s₂ f₁ f₂ g₁ g₂
  have hNY : rootNeighbours FY Y v c = {u, w} := by rwa [← h.rootNeighbours_eq hca hcb]
  have hX := two_piece_formulas FX X v u w c (by rwa [h.X_root]) hav hN hAX
  have hY := two_piece_formulas FY Y v u w c (by rwa [h.Y_root])
    ((h.root_list_regular_iff c hca hcb).mp hav) hNY hBY
  dsimp only at hX hY
  have hpos (F : HardListInstance V C) (Z : V → C) (z : V) :
      1 ≤ (offRootComponent F Z v (Z v) c z).card :=
    card_pos.mpr ⟨z, self_mem_offRootComponent F Z v z (Z v) c⟩
  rw [perColourCharge_eq_flexibleFormula h hca hcb hav huw hN hAX hBY]
  exact table_row _ _ _ _ (hpos FX X u) (hpos FX X w) (hpos FY Y u) (hpos FY Y w)
    _ _ _ _ _ _ hX.1 hY.1 hrow

end Graph

end ZeroFreeness.RegularColourCharge
