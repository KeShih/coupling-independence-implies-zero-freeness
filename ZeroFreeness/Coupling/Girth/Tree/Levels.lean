import ZeroFreeness.Coupling.Girth.Tree.Spatial

/-!
# Levels and conditional laws of finite rooted Potts trees

These definitions retain the actual finite configuration distributions.
Influence blocks compare the one-site marginal after fixing the root to a
colour with the unconditional marginal.
-/

namespace ZeroFreeness.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset Set PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

def probabilityLaw (x : ℝ) (hx : 0 < x) (t : CavityTree C) : FinDist C where
  w := t.probability x
  nonneg c := by rw [t.probability_eq_gibbs hx c]; exact div_nonneg (t.rootWeight_nonneg hx c) (t.partition_pos hx).le
  sum_one := by
    simp_rw [t.probability_eq_gibbs hx]
    rw [← Finset.sum_div, t.sum_rootWeight, div_self (t.partition_pos hx).ne']

theorem rootWeight_pos {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    0 < t.rootWeight x c := by
  cases t with
  | node d b child =>
    let σ : (CavityTree.node d b child).Configuration :=
      (c, fun i => Classical.choice ((child i).configurationNonempty))
    have hle : (CavityTree.node d b child).configurationWeight x σ ≤
        (CavityTree.node d b child).rootWeight x c := by
      have h := Finset.single_le_sum
        (f := fun τ : (CavityTree.node d b child).Configuration =>
          if (CavityTree.node d b child).rootColour τ = c then
            (CavityTree.node d b child).configurationWeight x τ else 0)
        (fun τ _ => by split_ifs; exact ((CavityTree.node d b child).configurationWeight_pos hx τ).le; exact le_rfl)
        (Finset.mem_univ σ)
      simpa only [σ, rootColour, if_true, rootWeight] using h
    exact ((CavityTree.node d b child).configurationWeight_pos hx σ).trans_le hle

def rootConditionalLaw (x : ℝ) (hx : 0 < x) (t : CavityTree C) (a : C) : FinDist t.Configuration where
  w σ := (if t.rootColour σ = a then t.configurationWeight x σ else 0) / t.rootWeight x a
  nonneg σ := div_nonneg (by split_ifs; exact (t.configurationWeight_pos hx σ).le; exact le_rfl)
    (t.rootWeight_pos hx a).le
  sum_one := by rw [← Finset.sum_div]; exact div_self (t.rootWeight_pos hx a).ne'

def Level (t : CavityTree C) (k : ℕ) : Type :=
  Nat.rec (motive := fun _ => CavityTree C → Type) (fun _ => Unit)
    (fun _ previous t => match t with
      | .node d _ child => (i : Fin d) × previous (child i)) k t

instance levelFintype (t : CavityTree C) (k : ℕ) : Fintype (t.Level k) := by
  induction k generalizing t with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ k ih =>
    cases t with
    | node d b child =>
      letI : ∀ i, Fintype ((child i).Level k) := fun i => ih (child i)
      exact inferInstanceAs (Fintype ((i : Fin d) × (child i).Level k))

def levelColour : (t : CavityTree C) → (k : ℕ) → t.Level k → t.Configuration → C
  | t, 0, _, σ => t.rootColour σ
  | .node _ _ child, k + 1, v, σ => levelColour (child v.1) k v.2 (σ.2 v.1)

def levelMarginal (t : CavityTree C) (k : ℕ) (μ : FinDist t.Configuration)
    (v : t.Level k) (c : C) : ℝ := ∑ σ, if t.levelColour k v σ = c then μ.w σ else 0

def influenceBlock (x : ℝ) (hx : 0 < x) (t : CavityTree C) (k : ℕ)
    (v : t.Level k) (a c : C) : ℝ :=
  t.levelMarginal k (t.rootConditionalLaw x hx a) v c -
    t.levelMarginal k (t.gibbs x hx) v c

def levelTotalVariation (x : ℝ) (hx : 0 < x) (t : CavityTree C) (k : ℕ) (a b : C) : ℝ :=
  ∑ v : t.Level k, (1 / 2 : ℝ) * ∑ c,
    |t.levelMarginal k (t.rootConditionalLaw x hx a) v c -
      t.levelMarginal k (t.rootConditionalLaw x hx b) v c|

end

end ZeroFreeness.Appendix.Girth.CavityTree
