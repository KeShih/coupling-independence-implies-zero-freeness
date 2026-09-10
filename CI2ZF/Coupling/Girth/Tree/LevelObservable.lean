import CI2ZF.Coupling.Girth.Tree.Levels

/-! Additive observables on a tree level and their actual Gibbs expectations.
The finite sums below identify an influence row with a conditional-minus-
unconditional expectation, including the root level and empty levels. -/
namespace CI2ZF.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset PottsCI

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

def levelObservable (t : CavityTree C) (k : ℕ) (h : t.Level k → C → ℝ)
    (σ : t.Configuration) : ℝ :=
  ∑ v, h v (t.levelColour k v σ)

omit [Fintype C] [DecidableEq C] [Nonempty C] in
theorem levelObservable_zero (t : CavityTree C) (h : t.Level 0 → C → ℝ)
    (σ : t.Configuration) : t.levelObservable 0 h σ = h () (t.rootColour σ) := by
  cases t with
  | node d b child =>
    change (∑ v : Unit, h v σ.1) = h () σ.1
    simp

omit [Fintype C] [DecidableEq C] [Nonempty C] in
theorem levelObservable_succ (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    (k : ℕ) (h : (CavityTree.node d b child).Level (k + 1) → C → ℝ)
    (σ : (CavityTree.node d b child).Configuration) :
    (CavityTree.node d b child).levelObservable (k + 1) h σ =
      ∑ i, (child i).levelObservable k (fun v => h ⟨i, v⟩) (σ.2 i) := by
  change (∑ v : (i : Fin d) × (child i).Level k,
    h v ((child v.1).levelColour k v.2 (σ.2 v.1))) = _
  rw [Fintype.sum_sigma]
  rfl

omit [Nonempty C] in
theorem sum_levelMarginal_mul (t : CavityTree C) (k : ℕ)
    (μ : FinDist t.Configuration) (h : t.Level k → C → ℝ) :
    (∑ v, ∑ c, t.levelMarginal k μ v c * h v c) =
      ∑ σ, μ.w σ * t.levelObservable k h σ := by
  classical
  have hv (v : t.Level k) :
      (∑ c, t.levelMarginal k μ v c * h v c) =
        ∑ σ, μ.w σ * h v (t.levelColour k v σ) := by
    unfold levelMarginal
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro σ _
    simp only [ite_mul, zero_mul]
    simp
  simp_rw [hv]
  rw [Finset.sum_comm]
  simp only [levelObservable, Finset.mul_sum]

theorem level_influence_eq_observable_difference (x : ℝ) (hx : 0 < x)
    (t : CavityTree C) (k : ℕ) (h : t.Level k → C → ℝ) (a : C) :
    (∑ v, ∑ c, t.influenceBlock x hx k v a c * h v c) =
      (∑ σ, (t.rootConditionalLaw x hx a).w σ * t.levelObservable k h σ) -
        ∑ σ, (t.gibbs x hx).w σ * t.levelObservable k h σ := by
  simp only [influenceBlock, sub_mul, Finset.sum_sub_distrib]
  rw [sum_levelMarginal_mul, sum_levelMarginal_mul]

theorem rootConditionalLaw_mean_root (x : ℝ) (hx : 0 < x)
    (t : CavityTree C) (f : C → ℝ) (a : C) :
    (∑ σ, (t.rootConditionalLaw x hx a).w σ * f (t.rootColour σ)) = f a := by
  classical
  calc
    _ = ∑ σ, (t.rootConditionalLaw x hx a).w σ * f a := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hσ : t.rootColour σ = a
      · rw [hσ]
      · simp only [rootConditionalLaw, hσ, if_false, zero_div, zero_mul]
    _ = f a := by
      rw [← Finset.sum_mul, (t.rootConditionalLaw x hx a).sum_one, one_mul]

theorem gibbs_mean_root (x : ℝ) (hx : 0 < x)
    (t : CavityTree C) (f : C → ℝ) :
    (∑ σ, (t.gibbs x hx).w σ * f (t.rootColour σ)) =
      ∑ c, t.probability x c * f c := by
  classical
  symm
  simp_rw [t.probability_eq_gibbs_marginal hx, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [ite_mul, zero_mul]
  simp

end
end CI2ZF.Appendix.Girth.CavityTree
