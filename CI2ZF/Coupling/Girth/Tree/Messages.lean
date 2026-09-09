import CI2ZF.Coupling.Girth.Analysis.FiniteDifference
import CI2ZF.Coupling.Girth.Analysis.InfluenceBounds

/-!
# Actual messages on finite rooted Potts trees

Each vertex carries its boundary colour counts. The degree budget charges
one extra incidence for the deleted parent edge, as required of cavity
messages. All sharp message estimates are proved by induction over the
finite tree from these counts and the Potts activity.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open Finset PottsCI

set_option linter.unusedSectionVars false

noncomputable section

inductive CavityTree (C : Type*) where
  | node (degree : ℕ) (boundary : C → ℕ) (children : Fin degree → CavityTree C)

namespace CavityTree

variable {C : Type*} [Fintype C] [DecidableEq C]

def degree : CavityTree C → ℕ
  | .node d _ _ => d

def boundary : CavityTree C → C → ℕ
  | .node _ b _ => b

def palette (x : ℝ) (t : CavityTree C) : ℝ :=
  (Fintype.card C : ℝ) - (1 - x) * ∑ c, (t.boundary c : ℝ)

def DegreeBudget (Δ : ℕ) : CavityTree C → Prop
  | .node d b child => d + (∑ c, b c) + 1 ≤ Δ ∧ ∀ i, DegreeBudget Δ (child i)

def probability (x : ℝ) : CavityTree C → C → ℝ
  | .node _ b child => messageMarginal (paletteWeight x b)
      (fun i c => (1 - x) * probability x (child i) c)

theorem palette_slack (t : CavityTree C) {Δ : ℕ} {x : ℝ}
    (hx : 0 ≤ x) (hq : Δ + 3 ≤ Fintype.card C) (hbudget : t.DegreeBudget Δ) :
    (t.degree : ℝ) + 4 ≤ t.palette x := by
  cases t with
  | node d b child =>
    have h := nonroot_four_slack (s := 1 - x) hq hbudget.1 (by linarith)
    simp only [degree, palette, boundary, Nat.cast_sum] at *
    linarith

theorem palette_le_card (t : CavityTree C) {x : ℝ} (hx : x ≤ 1) :
    t.palette x ≤ Fintype.card C := by
  unfold palette
  have hs : 0 ≤ ∑ c, (t.boundary c : ℝ) := Finset.sum_nonneg fun c _ => Nat.cast_nonneg _
  nlinarith

/-- Sharp cavity probabilities and exact normalization, derived on the
entire finite tree without any input-message hypothesis. -/
theorem probability_facts (t : CavityTree C) {Δ : ℕ} {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hq : Δ + 3 ≤ Fintype.card C)
    (hbudget : t.DegreeBudget Δ) :
    (∀ c, 0 < t.probability x c ∧
      t.probability x c ≤ messageCap t.degree (t.palette x)) ∧
      ∑ c, t.probability x c = 1 := by
  induction t with
  | node d b child ih =>
    have hchild := fun i => ih i (hbudget.2 i)
    let m : Fin d → C → ℝ := fun i c => (1 - x) * (child i).probability x c
    have hm0 (i : Fin d) (c : C) : 0 ≤ m i c :=
      mul_nonneg (by linarith) ((hchild i).1 c).1.le
    have hmcap (i : Fin d) (c : C) :
        m i c ≤ messageCap (child i).degree ((child i).palette x) := by
      calc
        _ ≤ (child i).probability x c := mul_le_of_le_one_left ((hchild i).1 c).1.le (by linarith)
        _ ≤ _ := ((hchild i).1 c).2
    have hmquarter (i : Fin d) (c : C) : m i c ≤ 1 / 4 :=
      (hmcap i c).trans (messageCap_bounds ((child i).palette_slack hx.le hq (hbudget.2 i))).2
    have hmass (i : Fin d) : ∑ c, m i c ≤ 1 := by
      simp only [m, ← Finset.mul_sum, (hchild i).2, mul_one]
      linarith
    let I : LocalRecursion C (Fin d) := {
      unary := paletteWeight x b
      unary_pos := fun c => pow_pos hx _
      unary_le_one := paletteWeight_le_one hx.le hx1 b
      input := m
      childDegree := fun i => (child i).degree
      childPalette := fun i => (child i).palette x
      child_slack := fun i => (child i).palette_slack hx.le hq (hbudget.2 i)
      input_nonneg := hm0
      input_cap := hmcap
      input_mass := hmass
      palette := (CavityTree.node d b child).palette x
      palette_lower := palette_mass_lower hx.le b
      parent_slack := by simpa only [Fintype.card_fin, degree] using
        (CavityTree.node d b child).palette_slack hx.le hq hbudget }
    refine ⟨fun c => ⟨I.law_pos c, ?_⟩, ?_⟩
    · have h := sharp_message_marginal I.unary I.input
        (fun b => ⟨(I.unary_pos b).le, I.unary_le_one b⟩) I.palette_lower I.parent_slack
        (fun i b => ⟨I.input_nonneg i b, I.input_quarter i b⟩) I.input_mass c
      simpa only [I, probability, degree, Fintype.card_fin] using h.2.2.2
    · exact I.law.sum_one

theorem scaled_probability_domain (t : CavityTree C) {Δ : ℕ} {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hq : Δ + 3 ≤ Fintype.card C)
    (hbudget : t.DegreeBudget Δ) :
    MessageDomain (1 - x) (fun c => (1 - x) * t.probability x c) := by
  have h := t.probability_facts hx hx1 hq hbudget
  have hcap := messageCap_bounds (t.palette_slack hx.le hq hbudget)
  refine ⟨fun c => ⟨mul_nonneg (by linarith) (h.1 c).1.le, ?_⟩, ?_⟩
  · exact (mul_le_of_le_one_left (h.1 c).1.le (by linarith)).trans ((h.1 c).2.trans hcap.2)
  · simp only [← Finset.mul_sum, h.2, mul_one, le_refl]

end CavityTree

end

end CI2ZF.Appendix.Girth
