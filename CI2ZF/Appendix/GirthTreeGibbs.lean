import CI2ZF.Appendix.GirthTreeMessages

/-!
# Gibbs semantics of the finite-tree recursion

Configurations assign a colour at every node. Their weight includes all
boundary counts and the Potts factor on every parent--child edge. The
recursively defined probability is proved equal to the corresponding
normalized finite configuration marginal.
-/

namespace CI2ZF.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset PottsCI

set_option linter.unusedSectionVars false

noncomputable section

universe u

variable {C : Type u} [Fintype C] [DecidableEq C]

def Configuration : CavityTree C → Type u
  | .node d _ child => C × ((i : Fin d) → Configuration (child i))

instance configurationFintype (t : CavityTree C) : Fintype t.Configuration := by
  induction t with
  | node d b child ih =>
    letI : ∀ i, Fintype (child i).Configuration := ih
    exact inferInstanceAs (Fintype (C × ((i : Fin d) → (child i).Configuration)))

instance configurationNonempty [Nonempty C] (t : CavityTree C) : Nonempty t.Configuration := by
  induction t with
  | node d b child ih =>
    let : ∀ i, Nonempty (child i).Configuration := ih
    exact inferInstanceAs (Nonempty (C × ((i : Fin d) → (child i).Configuration)))

def rootColour : (t : CavityTree C) → t.Configuration → C
  | .node _ _ _, σ => σ.1

def configurationWeight (x : ℝ) : (t : CavityTree C) → t.Configuration → ℝ
  | .node _ b child, σ => x ^ b σ.1 * ∏ i,
      ((if σ.1 = (child i).rootColour (σ.2 i) then x else 1) *
        configurationWeight x (child i) (σ.2 i))

def partition (x : ℝ) (t : CavityTree C) : ℝ := ∑ σ, t.configurationWeight x σ

def rootWeight (x : ℝ) (t : CavityTree C) (c : C) : ℝ :=
  ∑ σ, if t.rootColour σ = c then t.configurationWeight x σ else 0

theorem sum_rootWeight (x : ℝ) (t : CavityTree C) :
    ∑ c, t.rootWeight x c = t.partition x := by
  unfold rootWeight partition
  rw [Finset.sum_comm]
  simp

theorem configurationWeight_pos {x : ℝ} (hx : 0 < x) (t : CavityTree C) :
    ∀ σ, 0 < t.configurationWeight x σ := by
  induction t with
  | node d b child ih =>
    intro σ
    apply mul_pos (pow_pos hx _)
    apply Finset.prod_pos
    intro i _
    exact mul_pos (by split_ifs <;> positivity) (ih i _)

theorem partition_pos [Nonempty C] {x : ℝ} (hx : 0 < x) (t : CavityTree C) :
    0 < t.partition x :=
  Finset.sum_pos (fun σ _ => t.configurationWeight_pos hx σ) Finset.univ_nonempty

theorem rootWeight_nonneg {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    0 ≤ t.rootWeight x c := by
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact (t.configurationWeight_pos hx σ).le
  · exact le_rfl

theorem edge_partition (x : ℝ) (t : CavityTree C) (c : C) :
    (∑ σ, (if c = t.rootColour σ then x else 1) * t.configurationWeight x σ) =
      t.partition x - (1 - x) * t.rootWeight x c := by
  unfold partition rootWeight
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases h : c = t.rootColour σ
  · simp only [h, if_true]
    ring
  · simp only [h, Ne.symm h, if_false, one_mul, mul_zero, sub_zero]

theorem rootWeight_node (x : ℝ) (d : ℕ) (b : C → ℕ)
    (child : Fin d → CavityTree C) (c : C) :
    (CavityTree.node d b child).rootWeight x c = x ^ b c *
      ∏ i, ((child i).partition x - (1 - x) * (child i).rootWeight x c) := by
  change (∑ σ : C × ((i : Fin d) → (child i).Configuration),
    if σ.1 = c then x ^ b σ.1 *
      ∏ i, ((if σ.1 = (child i).rootColour (σ.2 i) then x else 1) *
        (child i).configurationWeight x (σ.2 i)) else 0) = _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.mul_sum, ← Fintype.prod_sum
    (fun i (σ : (child i).Configuration) =>
      (if c = (child i).rootColour σ then x else 1) * (child i).configurationWeight x σ)]
  simp_rw [edge_partition]

/-- The recursive message is precisely the normalized Gibbs marginal. -/
theorem probability_eq_gibbs [Nonempty C] {x : ℝ} (hx : 0 < x)
    (t : CavityTree C) (c : C) :
    t.probability x c = t.rootWeight x c / t.partition x := by
  induction t generalizing c with
  | node d b child ih =>
    let m : Fin d → C → ℝ := fun i c => (1 - x) * (child i).probability x c
    let Z : ℝ := ∏ i, (child i).partition x
    have hZ : 0 < Z := Finset.prod_pos fun i _ => (child i).partition_pos hx
    have hweight (c : C) : (CavityTree.node d b child).rootWeight x c =
        Z * messageWeight (paletteWeight x b) m c := by
      rw [rootWeight_node]
      have hpoint (i : Fin d) :
          (child i).partition x - (1 - x) * (child i).rootWeight x c =
            (child i).partition x * (1 - m i c) := by
        dsimp [m]
        rw [ih i c]
        field_simp [(child i).partition_pos hx |>.ne']
      simp_rw [hpoint]
      rw [Finset.prod_mul_distrib]
      unfold messageWeight paletteWeight
      ring
    have hpart : (CavityTree.node d b child).partition x =
        Z * messagePartition (paletteWeight x b) m := by
      rw [← sum_rootWeight]
      simp_rw [hweight]
      rw [← Finset.mul_sum]
      rfl
    rw [hweight, hpart]
    change messageMarginal (paletteWeight x b) m c = _
    unfold messageMarginal
    exact (mul_div_mul_left _ _ hZ.ne').symm

def gibbs [Nonempty C] (x : ℝ) (hx : 0 < x) (t : CavityTree C) : FinDist t.Configuration where
  w σ := t.configurationWeight x σ / t.partition x
  nonneg σ := div_nonneg (t.configurationWeight_pos hx σ).le (t.partition_pos hx).le
  sum_one := by rw [← Finset.sum_div]; exact div_self (t.partition_pos hx).ne'

theorem probability_eq_gibbs_marginal [Nonempty C] {x : ℝ} (hx : 0 < x)
    (t : CavityTree C) (c : C) :
    t.probability x c = ∑ σ, if t.rootColour σ = c then (t.gibbs x hx).w σ else 0 := by
  rw [t.probability_eq_gibbs hx c]
  unfold rootWeight gibbs
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

end

end CI2ZF.Appendix.Girth.CavityTree
