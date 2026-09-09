import CI2ZF.Coupling.Foundations.PartialCoupling
import CI2ZF.Coupling.Vigoda.VigodaChargeFormula

/-!
# Incidence allocation for component couplings

Each incidence (an active neighbour of the disagreement vertex) belongs to
one component on each side. Dividing a component's residual mass by its
number of incidences gives a partial matching with no overdrawn row or column.
-/

namespace CI2ZF.IncidenceMatching

open scoped BigOperators
open PottsCI PottsCI.Vigoda CI2ZF.VigodaArithmetic

noncomputable section

variable {I A B : Type*} [Fintype I]
variable [DecidableEq A] [DecidableEq B]

def count (f : I → A) (a : A) : ℕ := (Finset.univ.filter fun i => f i = a).card

lemma count_pos (f : I → A) (i : I) : 0 < count f (f i) := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp⟩

lemma count_pos_of_surjective (f : I → A) (hf : Function.Surjective f) (a : A) :
    0 < count f a := by
  obtain ⟨i, rfl⟩ := hf a
  exact count_pos f i

lemma count_comp_equiv {J : Type*} [Fintype J] (e : I ≃ J) (f : J → A) (a : A) :
    count (fun i => f (e i)) a = count f a := by
  have hc := Fintype.card_congr (e.subtypeEquiv
    (p := fun i => f (e i) = a) (q := fun j => f j = a) (fun _ => Iff.rfl))
  simpa only [Fintype.card_subtype, count] using hc

def share (f : I → A) (r : A → ℝ) (i : I) : ℝ := r (f i) / count f (f i)

def atIncidence (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (i : I) : ℝ :=
  min (share f r i) (share g s i)

def matrix (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (a : A) (b : B) : ℝ :=
  ∑ i, if f i = a ∧ g i = b then atIncidence f g r s i else 0

lemma share_nonneg (f : I → A) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a) (i : I) :
    0 ≤ share f r i := div_nonneg (hr _) (Nat.cast_nonneg _)

lemma atIncidence_nonneg (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b) (i : I) :
    0 ≤ atIncidence f g r s i :=
  le_min (share_nonneg f r hr i) (share_nonneg g s hs i)

lemma matrix_nonneg (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b) (a : A) (b : B) :
    0 ≤ matrix f g r s a b := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact atIncidence_nonneg f g r s hr hs i
  · exact le_rfl

lemma matrix_row [Fintype B] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (a : A) :
    (∑ b, matrix f g r s a b) = ∑ i, if f i = a then atIncidence f g r s i else 0 := by
  unfold matrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : f i = a <;> simp [h]

lemma matrix_col [Fintype A] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (b : B) :
    (∑ a, matrix f g r s a b) = ∑ i, if g i = b then atIncidence f g r s i else 0 := by
  unfold matrix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : g i = b <;> simp [h]

lemma sum_share_fibre (f : I → A) (r : A → ℝ) (a : A) :
    (∑ i, if f i = a then share f r i else 0) =
      (count f a : ℝ) * (r a / count f a) := by
  have hterm (i : I) : (if f i = a then share f r i else 0) =
      if f i = a then r a / count f a else 0 := by
    by_cases h : f i = a <;> simp [share, h]
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rfl

lemma sum_share_fibre_le (f : I → A) (r : A → ℝ) (hr : ∀ a, 0 ≤ r a) (a : A) :
    (∑ i, if f i = a then share f r i else 0) ≤ r a := by
  rw [sum_share_fibre]
  by_cases hc : count f a = 0
  · simpa [hc] using hr a
  · have hcR : (count f a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
    exact le_of_eq (by field_simp)

lemma matrix_row_le [Fintype B] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (a : A) : (∑ b, matrix f g r s a b) ≤ r a := by
  rw [matrix_row]
  calc
    (∑ i, if f i = a then atIncidence f g r s i else 0) ≤
        ∑ i, if f i = a then share f r i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact min_le_left _ _
      · exact le_rfl
    _ ≤ r a := sum_share_fibre_le f r hr a

lemma matrix_col_le [Fintype A] (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hs : ∀ b, 0 ≤ s b) (b : B) : (∑ a, matrix f g r s a b) ≤ s b := by
  rw [matrix_col]
  calc
    (∑ i, if g i = b then atIncidence f g r s i else 0) ≤
        ∑ i, if g i = b then share g s i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact min_le_right _ _
      · exact le_rfl
    _ ≤ s b := sum_share_fibre_le g s hs b

/-- The incidence allocation as an actual partial coupling, whenever the
available residual capacities fit within the desired marginal laws. -/
def partialCoupling [Fintype A] [Fintype B] (μ : FinDist A) (ν : FinDist B)
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b)
    (hrμ : ∀ a, r a ≤ μ.w a) (hsν : ∀ b, s b ≤ ν.w b) : PartialCoupling μ ν where
  w := matrix f g r s
  nonneg := matrix_nonneg f g r s hr hs
  row_le a := (matrix_row_le f g r s hr a).trans (hrμ a)
  col_le b := (matrix_col_le f g r s hs b).trans (hsν b)

lemma total_matrix_mass [Fintype A] [Fintype B]
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) :
    (∑ a, ∑ b, matrix f g r s a b) = ∑ i, atIncidence f g r s i := by
  simp_rw [matrix_row]
  rw [Finset.sum_comm]
  simp

/-- A matrix entry may collect several incidences. Its cost is exactly the
sum of the costs of those incidences, so repeated component pairs are safe. -/
lemma matrix_weighted_sum [Fintype A] [Fintype B]
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ) (d : A → B → ℝ) :
    (∑ a, ∑ b, matrix f g r s a b * d a b) =
      ∑ i, atIncidence f g r s i * d (f i) (g i) := by
  simp_rw [matrix, Finset.sum_mul, ite_mul, zero_mul]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ite_and]
  simp

/-- Complete the actual incidence matrix to a coupling. Any saving proved
for each matched component pair survives the product completion exactly. -/
theorem complete_cost_le_charge_sub_saving [Fintype A] [Fintype B]
    (μ : FinDist A) (ν : FinDist B)
    (f : I → A) (g : I → B) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b)
    (hrμ : ∀ a, r a ≤ μ.w a) (hsν : ∀ b, s b ≤ ν.w b)
    (d : A → B → ℝ) (aCharge : A → ℝ) (bCharge : B → ℝ) (saving : I → ℝ)
    (hd : ∀ a b, d a b ≤ aCharge a + bCharge b)
    (hmatch : ∀ i, d (f i) (g i) ≤ aCharge (f i) + bCharge (g i) - saving i) :
    (partialCoupling μ ν f g r s hr hs hrμ hsν).complete.cost d ≤
      (∑ a, μ.w a * aCharge a) + (∑ b, ν.w b * bCharge b) -
        ∑ i, atIncidence f g r s i * saving i := by
  let κ := partialCoupling μ ν f g r s hr hs hrμ hsν
  have hκcost (c : A → B → ℝ) : κ.cost c =
      ∑ i, atIncidence f g r s i * c (f i) (g i) :=
    matrix_weighted_sum f g r s c
  have hmatchCost : κ.cost d ≤ κ.cost (fun a b => aCharge a + bCharge b) -
      ∑ i, atIncidence f g r s i * saving i := by
    rw [hκcost, hκcost, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_sub] using
      mul_le_mul_of_nonneg_left (hmatch i) (atIncidence_nonneg f g r s hr hs i)
  have haccount : κ.cost (fun a b => aCharge a + bCharge b) +
      (∑ a, κ.leftResidual a * aCharge a) +
      (∑ b, κ.rightResidual b * bCharge b) =
      (∑ a, μ.w a * aCharge a) + (∑ b, ν.w b * bCharge b) := by
    have hleft : (∑ a, ∑ b, κ.w a b * aCharge a) =
        ∑ a, (∑ b, κ.w a b) * aCharge a := by simp_rw [Finset.sum_mul]
    have hright : (∑ a, ∑ b, κ.w a b * bCharge b) =
        ∑ b, (∑ a, κ.w a b) * bCharge b := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    simp only [PartialCoupling.cost, mul_add, Finset.sum_add_distrib,
      PartialCoupling.leftResidual, PartialCoupling.rightResidual,
      sub_mul, Finset.sum_sub_distrib]
    rw [hleft, hright]
    ring
  have hcomplete := κ.complete_cost_le_separable d aCharge bCharge hd
  change κ.complete.cost d ≤ _
  linarith

/-- Every component that is indexed by the family meets an incidence.
Consequently its mass is recovered exactly from its equal shares. -/
lemma sum_share [Fintype A] (f : I → A) (hf : Function.Surjective f) (r : A → ℝ) :
    (∑ i, share f r i) = ∑ a, r a := by
  calc
    (∑ i, share f r i) = ∑ i, ∑ a, if f i = a then share f r i else 0 := by simp
    _ = ∑ a, ∑ i, if f i = a then share f r i else 0 := Finset.sum_comm
    _ = ∑ a, r a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sum_share_fibre]
      have hc : (count f a : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.ne_of_gt (count_pos_of_surjective f hf a))
      field_simp

lemma sum_weighted_share [Fintype A] (f : I → A) (hf : Function.Surjective f)
    (r w : A → ℝ) : (∑ i, w (f i) * share f r i) = ∑ a, w a * r a := by
  have h := sum_share f hf (fun a => w a * r a)
  simpa only [share, mul_div_assoc] using h

/-- The remaining size charges minus the matching saving, written entirely
as a sum over actual incidences. -/
theorem charge_as_incidence_sum [Fintype A] [Fintype B] (f : I → A) (g : I → B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (r aSize : A → ℝ) (s bSize : B → ℝ) :
    (∑ a, aSize a * r a) + (∑ b, bSize b * s b) -
        (∑ i, atIncidence f g r s i) =
      ∑ i, (aSize (f i) * share f r i + bSize (g i) * share g s i -
        atIncidence f g r s i) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_weighted_share f hf, sum_weighted_share g hg]

/-- The `4m/3` off-root bound now follows from the actual incidence
allocation and the Vigoda profile box inequality. -/
theorem incidence_charge_le_four_thirds [Fintype A] [Fintype B] (f : I → A) (g : I → B)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (r : A → ℝ) (s : B → ℝ) (aSize : A → ℕ) (bSize : B → ℕ)
    (hr : ∀ a, 0 ≤ r a) (hs : ∀ b, 0 ≤ s b)
    (hrp : ∀ a, r a ≤ vigodaMass (aSize a))
    (hsp : ∀ b, s b ≤ vigodaMass (bSize b))
    (hcardA : ∀ a, count f a ≤ aSize a) (hcardB : ∀ b, count g b ≤ bSize b) :
    (∑ a, (aSize a : ℝ) * r a) + (∑ b, (bSize b : ℝ) * s b) -
        (∑ i, atIncidence f g r s i) ≤ (4 / 3 : ℝ) * Fintype.card I := by
  rw [charge_as_incidence_sum f g hf hg]
  calc
    (∑ i, ((aSize (f i) : ℝ) * share f r i + (bSize (g i) : ℝ) * share g s i -
        atIncidence f g r s i)) ≤ ∑ _ : I, (4 / 3 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hb := vigoda_port_box_bound (count f (f i)) (aSize (f i))
        (count g (g i)) (bSize (g i)) (count_pos f i) (hcardA _)
        (count_pos g i) (hcardB _) (r (f i)) (s (g i)) (hr _) (hrp _) (hs _) (hsp _)
      simpa only [share, atIncidence, div_mul_eq_mul_div, mul_div_assoc] using hb
    _ = (4 / 3 : ℝ) * Fintype.card I := by simp [mul_comm]

/-- Summing the separate colour bounds gives the conditional hard-estimate
right hand side. The finite set is the intersection of the two root lists. -/
theorem sum_colour_charge_le {C : Type*} [Fintype C] [DecidableEq C]
    (Q : C → ℝ) (m : C → ℕ) (available : Finset C)
    (hQ : ∀ c, Q c ≤ (11 / 6 : ℝ) * m c - if c ∈ available then 1 else 0) :
    (∑ c, Q c) ≤ (11 / 6 : ℝ) * (∑ c, (m c : ℝ)) - available.card := by
  calc
    (∑ c, Q c) ≤ ∑ c, ((11 / 6 : ℝ) * m c - if c ∈ available then 1 else 0) :=
      Finset.sum_le_sum fun c _ => hQ c
    _ = _ := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp

end

end CI2ZF.IncidenceMatching
