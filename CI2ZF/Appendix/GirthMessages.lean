import CI2ZF.PottsModel

/-!
# Weighted tree messages for the large-girth appendix

This file proves the palette lower bound and the invariant message domain in
`appendices/high-girth.tex`, directly for the displayed weighted Potts recursion.
In particular, the normalization is proved positive from the degree budget;
it is not supplied as a hypothesis. The contraction and large-girth transfer
are separate, still unproved steps.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

noncomputable section

variable {C D : Type*} [Fintype C] [Fintype D]

/-- A scaled message lies in the closed quarter-cube and has mass at most `s`. -/
def MessageDomain (s : ℝ) (m : C → ℝ) : Prop :=
  (∀ c, 0 ≤ m c ∧ m c ≤ 1 / 4) ∧ ∑ c, m c ≤ s

/-- The actual unary weights supplied by pinned neighbours. -/
def paletteWeight (x : ℝ) (b : C → ℕ) (c : C) : ℝ := x ^ b c

def messageWeight (a : C → ℝ) (m : D → C → ℝ) (c : C) : ℝ :=
  a c * ∏ i, (1 - m i c)

def messagePartition (a : C → ℝ) (m : D → C → ℝ) : ℝ :=
  ∑ c, messageWeight a m c

def messageMarginal (a : C → ℝ) (m : D → C → ℝ) (c : C) : ℝ :=
  messageWeight a m c / messagePartition a m

theorem paletteWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (b : C → ℕ) (c : C) :
    0 ≤ paletteWeight x b c := pow_nonneg hx _

theorem paletteWeight_le_one {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (b : C → ℕ) (c : C) : paletteWeight x b c ≤ 1 := by
  exact pow_le_one₀ hx hx1

/-- Bernoulli's inequality with the number of pinned neighbours counted with
multiplicity, including activity zero. -/
theorem palette_mass_lower {x : ℝ} (hx : 0 ≤ x) (b : C → ℕ) :
    (Fintype.card C : ℝ) - (1 - x) * ∑ c, (b c : ℝ) ≤
      ∑ c, paletteWeight x b c := by
  calc
    (Fintype.card C : ℝ) - (1 - x) * ∑ c, (b c : ℝ) =
        ∑ c, (1 + (b c : ℝ) * (x - 1)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one, ← Finset.sum_mul]
          ring
    _ ≤ ∑ c, paletteWeight x b c := by
      exact Finset.sum_le_sum fun c _ => one_add_mul_sub_le_pow (by linarith) (b c)

/-- The finite union bound in product form. -/
theorem one_sub_sum_le_prod {ι : Type*} (t : Finset ι) (y : ι → ℝ)
    (hy : ∀ i ∈ t, 0 ≤ y i ∧ y i ≤ 1) :
    1 - ∑ i ∈ t, y i ≤ ∏ i ∈ t, (1 - y i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    have hit := hy i (Finset.mem_insert_self _ _)
    have hyt : ∀ j ∈ t, 0 ≤ y j ∧ y j ≤ 1 :=
      fun j hj => hy j (Finset.mem_insert_of_mem hj)
    have hsum : 0 ≤ ∑ j ∈ t, y j := Finset.sum_nonneg fun j hj => (hyt j hj).1
    have hmul := mul_le_mul_of_nonneg_left (ih hyt) (sub_nonneg.mpr hit.2)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith [mul_nonneg hit.1 hsum]

theorem messageWeight_nonneg {a : C → ℝ} {m : D → C → ℝ}
    (ha : ∀ c, 0 ≤ a c) (hm : ∀ i c, m i c ≤ 1) (c : C) :
    0 ≤ messageWeight a m c := by
  exact mul_nonneg (ha c) (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hm i c))

theorem messageWeight_le_one {a : C → ℝ} {m : D → C → ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ 1) (c : C) :
    messageWeight a m c ≤ 1 := by
  have hprod : (∏ i, (1 - m i c)) ≤ 1 :=
    Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hm i c).2)
      (fun i _ => by linarith [(hm i c).1])
  exact mul_le_one₀ (ha c).2
    (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hm i c).2) hprod

/-- Every child contributes at most its total message mass to the loss in the
normalizing denominator. -/
theorem messagePartition_lower {a : C → ℝ} {m : D → C → ℝ} {s : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1)
    (hm : ∀ i c, 0 ≤ m i c ∧ m i c ≤ 1)
    (hmass : ∀ i, ∑ c, m i c ≤ s) :
    (∑ c, a c) - (Fintype.card D : ℝ) * s ≤ messagePartition a m := by
  have hpoint (c : C) : a c - ∑ i, m i c ≤ messageWeight a m c := by
    have hp := one_sub_sum_le_prod (Finset.univ : Finset D) (fun i => m i c)
      (fun i _ => hm i c)
    have hsum : 0 ≤ ∑ i, m i c := Finset.sum_nonneg fun i _ => (hm i c).1
    have hmul := mul_le_mul_of_nonneg_left hp (ha c).1
    have hloss := mul_le_mul_of_nonneg_right (ha c).2 hsum
    dsimp [messageWeight]
    nlinarith
  have hmass' : (∑ c, ∑ i, m i c) ≤ (Fintype.card D : ℝ) * s := by
    rw [Finset.sum_comm]
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset D)) (fun i _ => hmass i)
  calc
    (∑ c, a c) - (Fintype.card D : ℝ) * s ≤ (∑ c, a c) - ∑ c, ∑ i, m i c := by
      linarith
    _ = ∑ c, (a c - ∑ i, m i c) := by rw [Finset.sum_sub_distrib]
    _ ≤ messagePartition a m := Finset.sum_le_sum fun c _ => hpoint c

/-- A four-unit palette slack forces the actual tree denominator to be at
least four, even for interpolation messages whose mass is only bounded. -/
theorem messagePartition_ge_four {a : C → ℝ} {m : D → C → ℝ} {s A : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA : A ≤ ∑ c, a c)
    (hs : s ≤ 1) (hm : ∀ i, MessageDomain s (m i))
    (hslack : 4 ≤ A - (Fintype.card D : ℝ)) :
    4 ≤ messagePartition a m := by
  have hlow := messagePartition_lower ha
    (fun i c => ⟨(hm i).1 c |>.1, by linarith [(hm i).1 c |>.2]⟩)
    (fun i => (hm i).2)
  have hds := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card D) :
    (0 : ℝ) ≤ Fintype.card D)
  nlinarith

theorem sum_messageMarginal {a : C → ℝ} {m : D → C → ℝ}
    (hZ : messagePartition a m ≠ 0) : ∑ c, messageMarginal a m c = 1 := by
  simp only [messageMarginal, ← Finset.sum_div]
  exact div_self hZ

/-- The normalized weighted recursion as an actual finite probability law. -/
def messageLaw (a : C → ℝ) (m : D → C → ℝ)
    (hw : ∀ c, 0 ≤ messageWeight a m c) (hZ : 0 < messagePartition a m) :
    PottsCI.FinDist C where
  w := messageMarginal a m
  nonneg c := div_nonneg (hw c) hZ.le
  sum_one := sum_messageMarginal hZ.ne'

@[simp] theorem messageLaw_apply (a : C → ℝ) (m : D → C → ℝ)
    (hw : ∀ c, 0 ≤ messageWeight a m c) (hZ : 0 < messagePartition a m) (c : C) :
    (messageLaw a m hw hZ).w c = messageMarginal a m c := rfl

theorem messageMarginal_pos {a : C → ℝ} {m : D → C → ℝ}
    (ha : ∀ c, 0 < a c) (hm : ∀ i c, m i c < 1)
    (hZ : 0 < messagePartition a m) (c : C) : 0 < messageMarginal a m c := by
  exact div_pos (mul_pos (ha c) (Finset.prod_pos fun i _ => sub_pos.mpr (hm i c))) hZ

/-- Invariance of `D_s` for the weighted tree recursion, including the empty
child set and both activity endpoints. -/
theorem messageDomain_invariant {a : C → ℝ} {m : D → C → ℝ} {s A : ℝ}
    (ha : ∀ c, 0 ≤ a c ∧ a c ≤ 1) (hA : A ≤ ∑ c, a c)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hm : ∀ i, MessageDomain s (m i))
    (hslack : 4 ≤ A - (Fintype.card D : ℝ)) :
    (∀ c, 0 ≤ messageMarginal a m c ∧ messageMarginal a m c ≤ 1 / 4) ∧
      MessageDomain s (fun c => s * messageMarginal a m c) ∧
      ∑ c, s * messageMarginal a m c = s := by
  have hZ4 := messagePartition_ge_four ha hA hs1 hm hslack
  have hZ : 0 < messagePartition a m := by linarith
  have hm' : ∀ i c, 0 ≤ m i c ∧ m i c ≤ 1 :=
    fun i c => ⟨(hm i).1 c |>.1, by linarith [(hm i).1 c |>.2]⟩
  have hp (c : C) : 0 ≤ messageMarginal a m c ∧ messageMarginal a m c ≤ 1 / 4 := by
    refine ⟨div_nonneg (messageWeight_nonneg (fun c => (ha c).1)
      (fun i c => (hm' i c).2) c) hZ.le, ?_⟩
    apply (div_le_iff₀ hZ).mpr
    have hw := messageWeight_le_one ha hm' c
    linarith
  have hmass : ∑ c, s * messageMarginal a m c = s := by
    rw [← Finset.mul_sum, sum_messageMarginal hZ.ne', mul_one]
  refine ⟨hp, ⟨?_, hmass.le⟩, hmass⟩
  intro c
  refine ⟨mul_nonneg hs0 (hp c).1, ?_⟩
  calc
    s * messageMarginal a m c ≤ 1 * messageMarginal a m c :=
      mul_le_mul_of_nonneg_right hs1 (hp c).1
    _ ≤ 1 / 4 := by simpa using (hp c).2

/-- The paper's non-root structural budget gives four units of slack. -/
theorem nonroot_four_slack {q Δ d k : ℕ} {s : ℝ}
    (hcol : Δ + 3 ≤ q) (hbudget : d + k + 1 ≤ Δ)
    (hs : s ≤ 1) : 4 ≤ (q : ℝ) - s * k - d := by
  have hk := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hn : d + k + 4 ≤ q := by omega
  have hn' : (d : ℝ) + k + 4 ≤ q := by exact_mod_cast hn
  nlinarith

/-- The root retains three units, without making a false non-root claim. -/
theorem root_three_slack {q Δ d k : ℕ} {s : ℝ}
    (hcol : Δ + 3 ≤ q) (hbudget : d + k ≤ Δ)
    (hs : s ≤ 1) : 3 ≤ (q : ℝ) - s * k - d := by
  have hk := mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hn : d + k + 3 ≤ q := by omega
  have hn' : (d : ℝ) + k + 3 ≤ q := by exact_mod_cast hn
  nlinarith

/-- Specialization to the actual Potts unary weights and `s = 1 - x`.
This is the induction step proving genuine non-root messages lie in `D_s`. -/
theorem potts_messageDomain_invariant {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (b : C → ℕ) (m : D → C → ℝ) {Δ : ℕ}
    (hcol : Δ + 3 ≤ Fintype.card C)
    (hbudget : Fintype.card D + (∑ c, b c) + 1 ≤ Δ)
    (hm : ∀ i, MessageDomain (1 - x) (m i)) :
    MessageDomain (1 - x)
      (fun c => (1 - x) * messageMarginal (paletteWeight x b) m c) := by
  have hslack := nonroot_four_slack (s := 1 - x) hcol hbudget (by linarith)
  have hA := palette_mass_lower hx0 b
  have hslack' : 4 ≤ ((Fintype.card C : ℝ) - (1 - x) * ∑ c, (b c : ℝ)) -
      (Fintype.card D : ℝ) := by
    simpa only [Nat.cast_sum] using hslack
  exact (messageDomain_invariant
    (fun c => ⟨paletteWeight_nonneg hx0 b c, paletteWeight_le_one hx0 hx1 b c⟩)
    hA (by linarith) (by linarith) hm hslack').2.1

end

end CI2ZF.Appendix.Girth
