import ZeroFreeness.Coupling.Girth.Tree.TotalInfluence
import ZeroFreeness.Coupling.Girth.Tree.ConditionalExpectation
import ZeroFreeness.Coupling.Girth.Tree.LevelObservable

/-! CLMM2023 Lemma 8.7, the tree influence–Jacobian factorization behind
`CLMMInfluenceIdentity`, proved from the actual finite-tree Gibbs law.
The level influence is a difference of conditional expectations, and the
CLMM level response is that difference times the scaled potential
diagonal, by induction on the level. -/

namespace ZeroFreeness.Appendix.Girth.CavityTree

open scoped BigOperators
open Finset PottsCI

set_option linter.unusedSectionVars false

noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Conditional-minus-unconditional expectation of an observable. -/
def centeredMean (x : ℝ) (hx : 0 < x) (t : CavityTree C) (F : t.Configuration → ℝ)
    (a : C) : ℝ :=
  t.conditionalMean x hx F a - t.mean x hx F

/-- The edge-weighted centered child expectation `m/(1-m) * D`. -/
def edgeCentered (x : ℝ) (hx : 0 < x) (t : CavityTree C) (F : t.Configuration → ℝ)
    (c : C) : ℝ :=
  (1 - x) * t.probability x c / (1 - (1 - x) * t.probability x c) * t.centeredMean x hx F c

theorem probability_pos' {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    0 < t.probability x c := by
  rw [t.probability_eq_gibbs hx c]
  exact div_pos (t.rootWeight_pos hx c) (t.partition_pos hx)

theorem probability_le_one' {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    t.probability x c ≤ 1 := (t.probabilityLaw x hx).le_one c

theorem edge_den_pos {x : ℝ} (hx : 0 < x) (t : CavityTree C) (c : C) :
    0 < 1 - (1 - x) * t.probability x c := by
  have h1 := probability_pos' hx t c
  have h2 := probability_le_one' hx t c
  nlinarith [mul_pos hx h1]

theorem sqrt_mul_sqrt_div {m : ℝ} (hm : 0 ≤ m) (e D : ℝ) :
    Real.sqrt m * (Real.sqrt m / e * D) = m / e * D := by
  rw [← mul_assoc, mul_div_assoc', Real.mul_self_sqrt hm]

omit [Nonempty C] in
theorem sum_center_ite (P ψ : C → ℝ) (K : ℝ) (a : C) :
    (∑ b, K * (P b - if b = a then 1 else 0) * ψ b) = K * ((∑ b, P b * ψ b) - ψ a) := by
  have hpt (b : C) : K * (P b - if b = a then 1 else 0) * ψ b =
      K * (P b * ψ b) - if b = a then K * ψ a else 0 := by
    split_ifs with hb
    · subst hb; ring
    · ring
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

/-- Root disintegration of an additive child observable at any node. -/
theorem node_centeredMean (x : ℝ) (hx : 0 < x) (d : ℕ) (b : C → ℕ)
    (child : Fin d → CavityTree C) (F : ∀ i, (child i).Configuration → ℝ) (a : C) :
    (CavityTree.node d b child).centeredMean x hx (fun σ => ∑ i, F i (σ.2 i)) a =
      ∑ i, ((∑ c, (CavityTree.node d b child).probability x c *
        (child i).edgeCentered x hx (F i) c) - (child i).edgeCentered x hx (F i) a) := by
  let T := CavityTree.node d b child
  have hc (c : C) : T.conditionalMean x hx (fun σ => ∑ i, F i (σ.2 i)) c =
      ∑ i, ((child i).mean x hx (F i) - (child i).edgeCentered x hx (F i) c) := by
    rw [conditionalMean_sum x hx T (fun i σ => F i (σ.2 i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [conditionalMean_child x hx d b child i (F i) c]
    have hden := (edge_den_pos hx (child i) c).ne'
    unfold edgeCentered centeredMean
    field_simp
    ring
  have hp : (∑ c, T.probability x c) = 1 := (T.probabilityLaw x hx).sum_one
  have hm : T.mean x hx (fun σ => ∑ i, F i (σ.2 i)) =
      ∑ i, ((child i).mean x hx (F i) -
        ∑ c, T.probability x c * (child i).edgeCentered x hx (F i) c) := by
    rw [mean_eq_sum_probability_conditionalMean]
    simp_rw [hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hp, one_mul]
  change T.conditionalMean x hx _ a - T.mean x hx _ = _
  rw [hc a, hm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The level-`k+1` observable at a node, as a sum of child observables. -/
theorem levelObservable_succ_fun (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    (k : ℕ) (h : (CavityTree.node d b child).Level (k + 1) → C → ℝ) :
    (CavityTree.node d b child).levelObservable (k + 1) h =
      fun σ => ∑ i, (child i).levelObservable k (fun v => h ⟨i, v⟩) (σ.2 i) :=
  funext (levelObservable_succ d b child k h)

/-- The CLMM level response of a non-root subtree is the centered actual
conditional expectation, times the scaled potential diagonal. -/
theorem levelResponse_eq {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hq : Δ + 3 ≤ Fintype.card C) (k : ℕ) (t : CavityTree C) (ht : t.DegreeBudget Δ)
    (h : t.Level k → C → ℝ) (a : C) :
    levelResponse x hx hx1 hq t ht k h a =
      Real.sqrt ((1 - x) * t.probability x a) / (1 - (1 - x) * t.probability x a) *
        t.centeredMean x hx (t.levelObservable k h) a := by
  induction k generalizing t a with
  | zero =>
    simp only [levelResponse, terminalInfluenceAction, centerByLaw, expectReal]
    congr 1
    simp only [centeredMean, conditionalMean, mean, levelObservable_zero]
    rw [rootConditionalLaw_mean_root, gibbs_mean_root]
    rfl
  | succ k ih =>
    cases t with
    | node d b child =>
      let I := localData x d b child hx hx1 hq ht
      let P : C → ℝ := (CavityTree.node d b child).probability x
      let F : ∀ i, (child i).Configuration → ℝ := fun i =>
        (child i).levelObservable k (fun v => h ⟨i, v⟩)
      let ψ : Fin d → C → ℝ := fun i => (child i).edgeCentered x hx (F i)
      have hPa : P a < 1 := I.law_lt_one a
      have hPa0 : 0 < P a := probability_pos' hx _ a
      have hx0 : 0 ≤ 1 - x := by linarith
      change scaledRowFactor (1 - x) (P a) *
          blockAction I.law (fun i c => (1 - x) * (child i).probability x c)
            (fun i => levelResponse x hx hx1 hq (child i) (ht.2 i) k (fun v => h ⟨i, v⟩)) a = _
      have hblock : blockAction I.law (fun i c => (1 - x) * (child i).probability x c)
            (fun i => levelResponse x hx hx1 hq (child i) (ht.2 i) k (fun v => h ⟨i, v⟩)) a =
          ∑ i, Real.sqrt (P a) / (1 - P a) * ((∑ c, P c * ψ i c) - ψ i a) := by
        unfold blockAction
        apply Finset.sum_congr rfl
        intro i _
        rw [← sum_center_ite P (ψ i) (Real.sqrt (P a) / (1 - P a)) a]
        apply Finset.sum_congr rfl
        intro c _
        beta_reduce
        rw [ih (child i) (ht.2 i) (fun v => h ⟨i, v⟩) c]
        have hm0 : 0 ≤ (1 - x) * (child i).probability x c :=
          mul_nonneg hx0 (probability_pos' hx (child i) c).le
        simp only [transformedBlock, potentialDiagonal, ψ, edgeCentered, F]
        change Real.sqrt (P a) / (1 - P a) * (P c - if c = a then 1 else 0) *
            Real.sqrt ((1 - x) * (child i).probability x c) *
            (Real.sqrt ((1 - x) * (child i).probability x c) /
              (1 - (1 - x) * (child i).probability x c) * _) = _
        rw [mul_assoc _ (Real.sqrt _), sqrt_mul_sqrt_div hm0]
      rw [hblock, ← Finset.mul_sum, levelObservable_succ_fun,
        node_centeredMean x hx d b child F a]
      have hne : 1 - P a ≠ 0 := by linarith
      unfold scaledRowFactor
      rw [Real.sqrt_mul hx0]
      field_simp
      rfl

/-- The root-level CLMM response is the centered actual conditional expectation. -/
theorem rootLevelResponse_eq {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hq : Δ + 3 ≤ Fintype.card C) (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    (ht : ∀ i, (child i).DegreeBudget Δ) (k : ℕ)
    (h : (CavityTree.node d b child).Level (k + 1) → C → ℝ) (a : C) :
    rootLevelResponse x hx hx1 hq ((CavityTree.node d b child).probabilityLaw x hx)
        d child ht k h a =
      (CavityTree.node d b child).centeredMean x hx
        ((CavityTree.node d b child).levelObservable (k + 1) h) a := by
  rw [levelObservable_succ_fun, node_centeredMean]
  unfold rootLevelResponse
  apply Finset.sum_congr rfl
  intro i _
  have hsq (c : C) : Real.sqrt ((1 - x) * (child i).probability x c) *
      levelResponse x hx hx1 hq (child i) (ht i) k (fun v => h ⟨i, v⟩) c =
      (child i).edgeCentered x hx ((child i).levelObservable k (fun v => h ⟨i, v⟩)) c := by
    rw [levelResponse_eq]
    have hm0 : 0 ≤ (1 - x) * (child i).probability x c :=
      mul_nonneg (by linarith) (probability_pos' hx (child i) c).le
    unfold edgeCentered
    exact sqrt_mul_sqrt_div hm0 _ _
  have hfun : (fun c => Real.sqrt ((1 - x) * (child i).probability x c) *
      levelResponse x hx hx1 hq (child i) (ht i) k (fun v => h ⟨i, v⟩) c) =
      fun c => (child i).edgeCentered x hx
        ((child i).levelObservable k (fun v => h ⟨i, v⟩)) c := funext hsq
  change -centerByLaw ((CavityTree.node d b child).probabilityLaw x hx)
    (fun c => Real.sqrt ((1 - x) * (child i).probability x c) *
      levelResponse x hx hx1 hq (child i) (ht i) k (fun v => h ⟨i, v⟩) c) a = _
  rw [hfun]
  unfold centerByLaw expectReal
  change -(_ - ∑ c, (CavityTree.node d b child).probability x c * _) = _
  ring

/-- CLMM2023, Lemma 8.7, in the library's finite-tree coordinates. -/
theorem clmmInfluenceIdentity (C : Type*) [Fintype C] [DecidableEq C] [Nonempty C] :
    CLMMInfluenceIdentity C := by
  refine ⟨fun {Δ} x hx hx1 hq d b child _hroot ht k h a => ?_⟩
  rw [level_influence_eq_observable_difference, rootLevelResponse_eq]
  rfl

end

end ZeroFreeness.Appendix.Girth.CavityTree
