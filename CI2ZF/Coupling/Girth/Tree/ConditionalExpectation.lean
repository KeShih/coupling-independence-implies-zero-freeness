import CI2ZF.Coupling.Girth.Tree.Levels

/-!
# Conditional expectations of the actual finite-tree Gibbs law

The root disintegration and the child recursion below are finite-sum
identities. In particular, they do not assume an influence factorization
or a literature input.
-/

namespace CI2ZF.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset PottsCI

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

def mean (x : ℝ) (hx : 0 < x) (t : CavityTree C) (F : t.Configuration → ℝ) : ℝ :=
  ∑ σ, (t.gibbs x hx).w σ * F σ

def conditionalMean (x : ℝ) (hx : 0 < x) (t : CavityTree C)
    (F : t.Configuration → ℝ) (a : C) : ℝ :=
  ∑ σ, (t.rootConditionalLaw x hx a).w σ * F σ

theorem mean_eq_sum_div (x : ℝ) (hx : 0 < x) (t : CavityTree C)
    (F : t.Configuration → ℝ) :
    t.mean x hx F = (∑ σ, t.configurationWeight x σ * F σ) / t.partition x := by
  simp only [mean, gibbs, div_mul_eq_mul_div, Finset.sum_div]

theorem conditionalMean_eq_sum_div (x : ℝ) (hx : 0 < x) (t : CavityTree C)
    (F : t.Configuration → ℝ) (a : C) :
    t.conditionalMean x hx F a =
      (∑ σ, (if t.rootColour σ = a then t.configurationWeight x σ else 0) * F σ) /
        t.rootWeight x a := by
  simp only [conditionalMean, rootConditionalLaw, div_mul_eq_mul_div, Finset.sum_div]

theorem mean_eq_sum_probability_conditionalMean (x : ℝ) (hx : 0 < x)
    (t : CavityTree C) (F : t.Configuration → ℝ) :
    t.mean x hx F = ∑ a, t.probability x a * t.conditionalMean x hx F a := by
  simp_rw [mean_eq_sum_div, conditionalMean_eq_sum_div, probability_eq_gibbs hx]
  have hterm (a : C) :
      t.rootWeight x a / t.partition x *
        ((∑ σ, (if t.rootColour σ = a then t.configurationWeight x σ else 0) * F σ) /
          t.rootWeight x a) =
        (∑ σ, (if t.rootColour σ = a then t.configurationWeight x σ else 0) * F σ) /
          t.partition x := by
    field_simp [(t.rootWeight_pos hx a).ne']
  simp_rw [hterm]
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp [ite_mul]

theorem mean_sum (x : ℝ) (hx : 0 < x) (t : CavityTree C)
    {ι : Type*} [Fintype ι] (F : ι → t.Configuration → ℝ) :
    t.mean x hx (fun σ => ∑ i, F i σ) = ∑ i, t.mean x hx (F i) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem conditionalMean_sum (x : ℝ) (hx : 0 < x) (t : CavityTree C)
    {ι : Type*} [Fintype ι] (F : ι → t.Configuration → ℝ) (a : C) :
    t.conditionalMean x hx (fun σ => ∑ i, F i σ) a =
      ∑ i, t.conditionalMean x hx (F i) a := by
  simp only [conditionalMean, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite product weights factor when the observable uses one coordinate. -/
private theorem sum_prod_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (w : ∀ i, κ i → ℝ)
    (i : ι) (F : κ i → ℝ) :
    (∑ σ : (j : ι) → κ j, (∏ j, w j (σ j)) * F (σ i)) =
      (∑ s, w i s * F s) * ∏ j ∈ Finset.univ.erase i, ∑ s, w j s := by
  classical
  let w' := Function.update w i (fun s => w i s * F s)
  have hpoint (σ : (j : ι) → κ j) :
      (∏ j, w' j (σ j)) = (∏ j, w j (σ j)) * F (σ i) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have he : (∏ j ∈ Finset.univ.erase i, w' j (σ j)) =
        ∏ j ∈ Finset.univ.erase i, w j (σ j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [w', Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    rw [he]
    simp only [w', Function.update_self]
    ring
  simp_rw [← hpoint]
  rw [← Fintype.prod_sum, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [w', Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Conditioning on the root leaves the explicit product of edge-weighted
child configuration laws; the root unary factor cancels. -/
theorem conditionalMean_node_eq (x : ℝ) (hx : 0 < x) (d : ℕ)
    (b : C → ℕ) (child : Fin d → CavityTree C)
    (F : ((i : Fin d) → (child i).Configuration) → ℝ) (a : C) :
    (CavityTree.node d b child).conditionalMean x hx (fun σ => F σ.2) a =
      (∑ σ : (i : Fin d) → (child i).Configuration,
        (∏ i, (if a = (child i).rootColour (σ i) then x else 1) *
          (child i).configurationWeight x (σ i)) * F σ) /
        (∏ i : Fin d, ((child i).partition x - (1 - x) * (child i).rootWeight x a)) := by
  classical
  rw [conditionalMean_eq_sum_div]
  change (∑ σ : C × ((i : Fin d) → (child i).Configuration),
    (if σ.1 = a then x ^ b σ.1 * ∏ i,
      (if σ.1 = (child i).rootColour (σ.2 i) then x else 1) *
        (child i).configurationWeight x (σ.2 i) else 0) * F σ.2) / _ = _
  simp_rw [ite_mul, zero_mul]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, rootWeight_node]
  exact mul_div_mul_left _ _ (pow_pos hx (b a)).ne'

/-- The conditional law of one child subtree is its Gibbs law reweighted
by the single edge joining it to the fixed root colour. -/
theorem conditionalMean_child_eq_ratio (x : ℝ) (hx : 0 < x) (d : ℕ)
    (b : C → ℕ) (child : Fin d → CavityTree C) (i : Fin d)
    (F : (child i).Configuration → ℝ) (a : C) :
    (CavityTree.node d b child).conditionalMean x hx (fun σ => F (σ.2 i)) a =
      (∑ σ, ((if a = (child i).rootColour σ then x else 1) *
        (child i).configurationWeight x σ) * F σ) /
          ((child i).partition x - (1 - x) * (child i).rootWeight x a) := by
  classical
  have hZ (j : Fin d) :
      0 < ∑ σ, (if a = (child j).rootColour σ then x else 1) *
        (child j).configurationWeight x σ := by
    apply Finset.sum_pos _ Finset.univ_nonempty
    intro σ _
    exact mul_pos (by split_ifs <;> positivity) ((child j).configurationWeight_pos hx σ)
  rw [conditionalMean_node_eq x hx d b child (fun σ => F (σ i)) a]
  simp_rw [← edge_partition]
  rw [sum_prod_coordinate
    (fun (j : Fin d) (σ : (child j).Configuration) =>
      (if a = (child j).rootColour σ then x else 1) * (child j).configurationWeight x σ) i F,
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_div_mul_right _ _ (Finset.prod_pos (fun j _ => hZ j)).ne'

/-- Exact normalized conditional-expectation recursion for a child subtree.
Only positivity of the activity is needed. -/
theorem conditionalMean_child (x : ℝ) (hx : 0 < x) (d : ℕ)
    (b : C → ℕ) (child : Fin d → CavityTree C) (i : Fin d)
    (F : (child i).Configuration → ℝ) (a : C) :
    (CavityTree.node d b child).conditionalMean x hx (fun σ => F (σ.2 i)) a =
      ((child i).mean x hx F - (1 - x) * (child i).probability x a *
        (child i).conditionalMean x hx F a) /
          (1 - (1 - x) * (child i).probability x a) := by
  rw [conditionalMean_child_eq_ratio, mean_eq_sum_div, conditionalMean_eq_sum_div,
    probability_eq_gibbs hx]
  have hnum :
      (∑ σ, ((if a = (child i).rootColour σ then x else 1) *
        (child i).configurationWeight x σ) * F σ) =
      (∑ σ, (child i).configurationWeight x σ * F σ) - (1 - x) *
        ∑ σ, (if (child i).rootColour σ = a then (child i).configurationWeight x σ else 0) *
          F σ := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases h : a = (child i).rootColour σ
    · rw [if_pos h, if_pos h.symm]
      ring
    · rw [if_neg h, if_neg (Ne.symm h)]
      ring
  have hZ : (child i).partition x ≠ 0 := ((child i).partition_pos hx).ne'
  have hR : (child i).rootWeight x a ≠ 0 := ((child i).rootWeight_pos hx a).ne'
  rw [hnum]
  field_simp [hZ, hR]

end

end CI2ZF.Appendix.Girth.CavityTree
