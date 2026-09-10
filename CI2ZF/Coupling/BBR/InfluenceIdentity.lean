import CI2ZF.Coupling.Girth.Tree.ConditionalExpectation
import CI2ZF.Coupling.Girth.Tree.LevelObservable
import CI2ZF.Coupling.BBR.InfluenceAlgebra
import CI2ZF.Coupling.BBR.Response

/-! The influence--Jacobian identity for the actual finite-tree Gibbs law.

Conditioning the parent root gives the explicit edge-weighted child law.
Its centered expectation is exactly the normalized Jacobian block. Tree
induction and centering at the root therefore identify the full level
response with the actual conditional-minus-unconditional observable.
No literature theorem or influence identity is assumed. -/
namespace CI2ZF.Appendix.BBR

open scoped BigOperators
open Finset PottsCI
open CI2ZF.Appendix.Girth

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- The projected message response is the actual centered conditional
expectation of any additive observable on a level, including level zero. -/
theorem projected_level_response {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (k : ℕ) (t : CavityTree C) (h : t.Level k → C → ℝ) (a : C) :
    projection (t.message x) (response x t k h) a / t.message x a =
      t.conditionalMean x hx (t.levelObservable k h) a -
        t.mean x hx (t.levelObservable k h) := by
  classical
  induction k generalizing t a with
  | zero =>
    rw [response, terminal_projection_div_message hx]
    simp only [CavityTree.conditionalMean, CavityTree.mean, CavityTree.levelObservable_zero]
    rw [CavityTree.rootConditionalLaw_mean_root, CavityTree.gibbs_mean_root]
  | succ k ih =>
    cases t with
    | node d b child =>
      let T := CavityTree.node d b child
      let F (i : Fin d) : (child i).Configuration → ℝ :=
        (child i).levelObservable k (fun v => h ⟨i, v⟩)
      let base : ℝ := ∑ i, (child i).mean x hx (F i)
      have hi (i : Fin d) (c : C) :
          T.conditionalMean x hx (fun σ => F i (σ.2 i)) c =
            (child i).mean x hx (F i) +
              jacobianBlock x (T.message x) ((child i).message x)
                (response x (child i) k (fun v => h ⟨i, v⟩)) c / T.message x c := by
        rw [CavityTree.conditionalMean_child x hx, jacobianBlock_div_message hx hx1,
          ih (child i) (fun v => h ⟨i, v⟩) c]
        have hden : 1 - (1 - x) * (child i).probability x c ≠ 0 :=
          (hx.trans_le ((child i).edgeFactor_mem hx hx1 c).1).ne'
        dsimp only [F]
        field_simp [hden]
        ring
      have hs (c : C) :
          T.conditionalMean x hx (T.levelObservable (k + 1) h) c =
            base + response x T (k + 1) h c / T.message x c := by
        calc
          _ = ∑ i, T.conditionalMean x hx (fun σ => F i (σ.2 i)) c := by
            simp only [CavityTree.conditionalMean, T, CavityTree.levelObservable_succ,
              F, Finset.mul_sum]
            rw [Finset.sum_comm]
          _ = _ := by
            simp_rw [hi]
            rw [Finset.sum_add_distrib, ← Finset.sum_div]
            rfl
      have hp : (∑ c, T.probability x c) = 1 := (T.probabilityLaw x hx).sum_one
      have hm : T.mean x hx (T.levelObservable (k + 1) h) =
          base + ∑ c, T.probability x c * (response x T (k + 1) h c / T.message x c) := by
        rw [CavityTree.mean_eq_sum_probability_conditionalMean]
        simp_rw [hs, mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hp, one_mul]
      change projection (T.message x) (response x T (k + 1) h) a / T.message x a =
        T.conditionalMean x hx (T.levelObservable (k + 1) h) a -
          T.mean x hx (T.levelObservable (k + 1) h)
      rw [projection_div_message hx, hs a, hm]
      ring

/-- The paper's level influence--Jacobian formula, proved from the actual
finite Gibbs marginals for every finite tree and every level. -/
theorem level_influence_factorization {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (t : CavityTree C) (k : ℕ) (h : t.Level k → C → ℝ) (a : C) :
    (∑ v, ∑ c, t.influenceBlock x hx k v a c * h v c) =
      projection (t.message x) (response x t k h) a / t.message x a := by
  rw [t.level_influence_eq_observable_difference x hx k h a]
  exact (projected_level_response hx hx1 k t h a).symm

/-- The formerly external interface, retained as a proved proposition for
clients that use its named factorization field. -/
structure InfluenceIdentity (C : Type*) [Fintype C] [DecidableEq C] [Nonempty C] : Prop where
  factorization : ∀ (x : ℝ) (hx : 0 < x) (_hx1 : x ≤ 1) (t : CavityTree C)
    (k : ℕ) (h : t.Level (k + 1) → C → ℝ) (a : C),
    (∑ v, ∑ c, t.influenceBlock x hx (k + 1) v a c * h v c) =
      projection (t.message x) (response x t (k + 1) h) a / t.message x a

/-- An internal witness of the complete BBR influence identity. -/
theorem influenceIdentity (C : Type*) [Fintype C] [DecidableEq C] [Nonempty C] :
    InfluenceIdentity C := by
  exact ⟨fun _ hx hx1 t k h a => level_influence_factorization hx hx1 t (k + 1) h a⟩

end
end CI2ZF.Appendix.BBR
