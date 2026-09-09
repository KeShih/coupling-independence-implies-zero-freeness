import CI2ZF.Coupling.Girth.Tree.Gibbs

/-!
# Quantitative decay on finite Potts trees

Two rooted trees may differ beyond a prescribed common prefix. The sharp
message bounds at the cut and the proved local finite-difference theorem
give uniform exponential decay through every common interior level.
-/

namespace CI2ZF.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset Set PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C]

def entropy (x : ℝ) (t : CavityTree C) : ℝ :=
  entropyCorrection (messageOddsBound t.degree (t.palette x))

def weightSquare (x : ℝ) (t : CavityTree C) : ℝ := 1 / (1 - t.entropy x)

theorem entropy_lt_one {t : CavityTree C} {Δ : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hq : Δ + 3 ≤ Fintype.card C) (hbudget : t.DegreeBudget Δ) :
    t.entropy x < 1 := entropyCorrection_lt_one
      (messageOddsBound_pos (t.palette_slack hx hq hbudget))
      (messageOddsBound_le_third (t.palette_slack hx hq hbudget))

theorem weightSquare_nonneg {t : CavityTree C} {Δ : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hq : Δ + 3 ≤ Fintype.card C) (hbudget : t.DegreeBudget Δ) :
    0 ≤ t.weightSquare x := div_nonneg zero_le_one (by linarith [entropy_lt_one hx hq hbudget])

theorem weightSquare_upper {t : CavityTree C} {Δ : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hq : Δ + 3 ≤ Fintype.card C) (hbudget : t.DegreeBudget Δ) :
    t.weightSquare x ≤ Real.exp (1 / 6) := by
  have hslack := t.palette_slack hx hq hbudget
  exact (entropy_weight_inverse_bound (messageOddsBound_pos hslack)
    (messageOddsBound_le_third hslack)).trans
      (Real.exp_le_exp.mpr (by linarith [messageOddsBound_le_third hslack]))

def localData (x : ℝ) (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    {Δ : ℕ} (hx : 0 < x) (hx1 : x ≤ 1) (hq : Δ + 3 ≤ Fintype.card C)
    (hbudget : (CavityTree.node d b child).DegreeBudget Δ) : LocalRecursion C (Fin d) where
  unary := paletteWeight x b
  unary_pos := fun c => pow_pos hx (b c)
  unary_le_one := paletteWeight_le_one hx.le hx1 b
  input := fun i c => (1 - x) * (child i).probability x c
  childDegree := fun i => (child i).degree
  childPalette := fun i => (child i).palette x
  child_slack := fun i => (child i).palette_slack hx.le hq (hbudget.2 i)
  input_nonneg := fun i c => mul_nonneg (by linarith)
    (((child i).probability_facts hx hx1 hq (hbudget.2 i)).1 c).1.le
  input_cap := fun i c =>
    (mul_le_of_le_one_left
      (((child i).probability_facts hx hx1 hq (hbudget.2 i)).1 c).1.le (by linarith)).trans
      (((child i).probability_facts hx hx1 hq (hbudget.2 i)).1 c).2
  input_mass := fun i => by
    rw [← Finset.mul_sum, ((child i).probability_facts hx hx1 hq (hbudget.2 i)).2, mul_one]
    linarith
  palette := (CavityTree.node d b child).palette x
  palette_lower := palette_mass_lower hx.le b
  parent_slack := by simpa only [Fintype.card_fin, degree] using
    (CavityTree.node d b child).palette_slack hx.le hq hbudget

/-- At the cut the top degree and total pinned count agree. Each successor
requires the whole local colour weight to agree for one further level. -/
inductive Agreement : ℕ → CavityTree C → CavityTree C → Prop where
  | zero (t u : CavityTree C) (hd : t.degree = u.degree)
      (hb : (∑ c, t.boundary c) = ∑ c, u.boundary c) : Agreement 0 t u
  | succ (k d : ℕ) (b : C → ℕ) (t u : Fin d → CavityTree C)
      (h : ∀ i, Agreement k (t i) (u i)) :
      Agreement (k + 1) (.node d b t) (.node d b u)

theorem Agreement.degree_eq {k : ℕ} {t u : CavityTree C} (h : Agreement k t u) :
    t.degree = u.degree := by
  cases h with
  | zero _ _ hd _ => exact hd
  | succ => rfl

theorem Agreement.palette_eq {k : ℕ} {t u : CavityTree C} (h : Agreement k t u) (x : ℝ) :
    t.palette x = u.palette x := by
  cases h with
  | zero t u hd hb =>
    unfold palette
    congr 2
    exact_mod_cast hb
  | succ => rfl

def cutEnergy (q : ℝ) : ℝ := Real.exp (1 / 6) * q * (Real.log 3) ^ 2

theorem cutEnergy_nonneg {q : ℝ} (hq : 0 ≤ q) : 0 ≤ cutEnergy q := by unfold cutEnergy; positivity

theorem potential_cut_energy (t u : CavityTree C) {Δ : ℕ} {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hq : Δ + 3 ≤ Fintype.card C)
    (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ) :
    t.weightSquare x *
      (∑ c, (messagePotential ((1 - x) * u.probability x c) -
        messagePotential ((1 - x) * t.probability x c)) ^ 2) ≤
      cutEnergy (Fintype.card C) := by
  have ht' := t.scaled_probability_domain hx hx1 hq ht
  have hu' := u.scaled_probability_domain hx hx1 hq hu
  have hpoint (c : C) :
      (messagePotential ((1 - x) * u.probability x c) -
        messagePotential ((1 - x) * t.probability x c)) ^ 2 ≤ (Real.log 3) ^ 2 := by
    have h1 := messagePotential_mem (ht'.1 c)
    have h2 := messagePotential_mem (hu'.1 c)
    nlinarith [h1.1, h1.2, h2.1, h2.2,
      mul_nonneg h1.1 h2.1, mul_nonneg (sub_nonneg.mpr h1.2) (sub_nonneg.mpr h2.2)]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset C)) (fun c _ => hpoint c)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  calc
    _ ≤ t.weightSquare x * ((Fintype.card C : ℝ) * (Real.log 3) ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (weightSquare_nonneg hx.le hq ht)
    _ ≤ Real.exp (1 / 6) * ((Fintype.card C : ℝ) * (Real.log 3) ^ 2) :=
      mul_le_mul_of_nonneg_right (weightSquare_upper hx.le hq ht) (by positivity)
    _ = _ := by unfold cutEnergy; ring

/-- Every common interior level supplies the strict squared contraction
factor `exp(-8/(81q))`. -/
theorem potential_decay {k : ℕ} {t u : CavityTree C} (hag : Agreement k t u)
    {Δ : ℕ} {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hq : Δ + 3 ≤ Fintype.card C)
    (ht : t.DegreeBudget Δ) (hu : u.DegreeBudget Δ) :
    t.weightSquare x *
      (∑ c, (messagePotential ((1 - x) * u.probability x c) -
        messagePotential ((1 - x) * t.probability x c)) ^ 2) ≤
      Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k * cutEnergy (Fintype.card C) := by
  induction hag with
  | zero t u hd hb => simpa only [pow_zero, one_mul] using potential_cut_energy t u hx hx1.le hq ht hu
  | succ k d b t u hag ih =>
    let I := localData x d b t hx hx1.le hq ht
    let n : Fin d → C → ℝ := fun i c => (1 - x) * (u i).probability x c
    let T := Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ k * cutEnergy (Fintype.card C)
    have hn0 (i : Fin d) (c : C) : 0 ≤ n i c := mul_nonneg (by linarith)
      (((u i).probability_facts hx hx1.le hq (hu.2 i)).1 c).1.le
    have hncap (i : Fin d) (c : C) : n i c ≤ messageCap (I.childDegree i) (I.childPalette i) := by
      change n i c ≤ messageCap (t i).degree ((t i).palette x)
      rw [(hag i).degree_eq, (hag i).palette_eq]
      exact (mul_le_of_le_one_left
        (((u i).probability_facts hx hx1.le hq (hu.2 i)).1 c).1.le (by linarith)).trans
          (((u i).probability_facts hx hx1.le hq (hu.2 i)).1 c).2
    have hnmass (i : Fin d) : ∑ c, n i c ≤ 1 := by
      simp only [n, ← Finset.mul_sum, ((u i).probability_facts hx hx1.le hq (hu.2 i)).2, mul_one]
      linarith
    have hT : 0 ≤ T := mul_nonneg (pow_nonneg (Real.exp_pos _).le _)
      (cutEnergy_nonneg (Nat.cast_nonneg _))
    have hh (i : Fin d) :
        (∑ c, (messagePotential (n i c) - messagePotential (I.input i c)) ^ 2) ≤
          T * (1 - I.childEntropy i) := by
      have hi := ih i (ht.2 i) (hu.2 i)
      change (1 / (1 - (t i).entropy x)) * _ ≤ T at hi
      have he : 0 < 1 - (t i).entropy x := sub_pos.mpr (entropy_lt_one hx.le hq (ht.2 i))
      have hi' := (div_le_iff₀ he).mp (show
        (∑ c, (messagePotential ((1 - x) * (u i).probability x c) -
          messagePotential ((1 - x) * (t i).probability x c)) ^ 2) /
          (1 - (t i).entropy x) ≤ T by simpa only [one_div_mul_eq_div] using hi)
      exact hi'
    have h := I.weighted_finite_difference n hn0 hncap hnmass
      (show 0 < 1 - x by linarith) (show 1 - x ≤ 1 by linarith)
      ((CavityTree.node d b t).palette_le_card hx1.le) hT hh
    have heq : Real.exp (-8 / (81 * (Fintype.card C : ℝ))) * T =
        Real.exp (-8 / (81 * (Fintype.card C : ℝ))) ^ (k + 1) * cutEnergy (Fintype.card C) := by
      unfold T
      rw [pow_succ]
      ring
    rw [heq] at h
    simpa only [I, localData, LocalRecursion.parentEntropy, LocalRecursion.parentOdds,
      Fintype.card_fin, weightSquare, entropy, degree, probability, n,
      LocalRecursion.law, messageLaw_apply] using h

end

end CI2ZF.Appendix.Girth.CavityTree
