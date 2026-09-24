import CI2ZF.Coupling.BBR.Certificate
import CI2ZF.Coupling.BBR.Jacobian

/-! BBR Theorem 2.5, the squared-norm contraction of the square-root
message recursion, proved as in BBR Section 3: the mean value theorem
along the segment `s R + (1 - s) R'`, Cauchy–Schwarz, and the pointwise
Jacobian bound `differential_contraction`. -/
namespace CI2ZF.Appendix.BBR
open scoped BigOperators
open Finset Set PottsCI
open CI2ZF.Appendix.Girth
noncomputable section
set_option linter.unusedSectionVars false

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

theorem hasDerivAt_segment_coord (R R' : C → ℝ) (s : ℝ) (c : C) :
    HasDerivAt (fun t => segment t R R' c) (R c - R' c) s := by
  unfold segment
  have h1 := (hasDerivAt_id s).mul_const (R c)
  have h2 := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const (R' c)
  refine (h1.add h2).congr_deriv ?_
  ring

theorem segment_one' (R R' : C → ℝ) : segment 1 R R' = R := by
  funext c
  simp [segment]

/-- Product rule for the square-root recursion along a differentiable family of
child vectors: the derivative is the sum of the explicit Jacobian blocks. -/
theorem hasDerivAt_localRoot {D : Type*} [Fintype D] [DecidableEq D] {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (B : C → ℝ) {y : ℝ → D → C → ℝ} {z : D → C → ℝ} {a : ℝ}
    (hy : ∀ i c, HasDerivAt (fun t => y t i c) (z i c) a)
    (hS : ∀ i, 0 < squareMass (y a i)) (c : C) :
    HasDerivAt (fun t => localRoot x B (y t) c)
      (∑ i, jacobianBlock x (localRoot x B (y a)) (y a i) (z i) c) a := by
  have hL (i : D) := hasDerivAt_localFactor hx hx1 (y := fun t => y t i) (z := z i) (hy i) (hS i) c
  have hP := HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hL i)
  have h := hP.const_mul (B c)
  unfold localRoot
  apply h.congr_deriv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hden := excludedMass_pos hx hx1 (y a i) (hS i) c
  have hratio := div_pos hden (hS i)
  have hF : 0 < localFactor x (y a i) c := Real.sqrt_pos.2 hratio
  have hFsq : localFactor x (y a i) c ^ 2 * squareMass (y a i) = excludedMass x (y a i) c := by
    unfold localFactor
    rw [Real.sq_sqrt hratio.le]
    field_simp [(hS i).ne']
  unfold jacobianBlock
  dsimp only
  rw [← Finset.mul_prod_erase Finset.univ (fun j => localFactor x (y a j) c) (Finset.mem_univ i),
    ← hFsq, smul_eq_mul]
  field_simp [hF.ne', (hS i).ne']

theorem pointWeight_segment_le {x m : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hm : 0 < m)
    (R R' : C → ℝ) (hR : ∀ c, m ≤ R c) (hR' : ∀ c, m ≤ R' c) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pointWeightSquare x (segment s R R') ≤ segmentWeightSquare x R R' := by
  apply Finset.sup'_le
  intro c _
  exact le_csSup (segmentWeightSet_bddAbove hx hx1 hm R R' hR hR') ⟨s, hs, c, rfl⟩

/-- BBR Theorem 2.5 for the abstract recursion `localRoot`, via the mean value
theorem along the segment `s R + (1 - s) R'` and the pointwise Jacobian bound. -/
theorem segment_contraction {D : Type*} [Fintype D] [DecidableEq D] {x m : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) (hm : 0 < m)
    (B : C → ℝ) (hB : ∀ c, B c ^ 2 ≤ 1) (R R' : D → C → ℝ)
    (hR : ∀ i c, m ≤ R i c) (hR' : ∀ i c, m ≤ R' i c) :
    squareMass (fun c => localRoot x B R c - localRoot x B R' c) ≤
      ∑ i, ((1 - x) / Real.exp 1 * segmentWeightSquare x (R i) (R' i)) *
        squareMass (fun c => R i c - R' i c) := by
  let γ : ℝ → D → C → ℝ := fun s i => segment s (R i) (R' i)
  let z : D → C → ℝ := fun i c => R i c - R' i c
  let w : C → ℝ := fun c => localRoot x B R c - localRoot x B R' c
  have hγ1 : γ 1 = R := funext fun i => segment_one' (R i) (R' i)
  have hγ0 : γ 0 = R' := funext fun i => segment_zero (R i) (R' i)
  have hq : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hS (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (i : D) : 0 < squareMass (γ s i) :=
    lt_of_lt_of_le (by positivity) (segment_mass_lower hm.le (R i) (R' i) (hR i) (hR' i) hs)
  let J : ℝ → C → ℝ := fun s c => ∑ i, jacobianBlock x (localRoot x B (γ s)) (γ s i) (z i) c
  let φ : ℝ → ℝ := fun s => ∑ c, localRoot x B (γ s) c * w c
  let φ' : ℝ → ℝ := fun s => ∑ c, J s c * w c
  have hder (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt φ (φ' s) s := by
    have hc (c : C) : HasDerivAt (fun t => localRoot x B (γ t) c * w c) (J s c * w c) s :=
      (hasDerivAt_localRoot hx hx1 B (y := γ) (z := z)
        (fun i c => hasDerivAt_segment_coord (R i) (R' i) s c) (hS s hs) c).mul_const (w c)
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun c _ => hc c)
  have hcont : ContinuousOn φ (Icc 0 1) := fun s hs => (hder s hs).continuousAt.continuousWithinAt
  obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope φ φ' zero_lt_one hcont
    (fun s hs => hder s (Ioo_subset_Icc_self hs))
  have hs' : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
  have hdiff : φ 1 - φ 0 = squareMass w := by
    simp only [φ, hγ1, hγ0, ← Finset.sum_sub_distrib, squareMass]
    exact Finset.sum_congr rfl fun c _ => by simp only [w]; ring
  have hφ' : φ' s = squareMass w := by rw [hslope, hdiff]; simp
  have hcs : φ' s ^ 2 ≤ squareMass (J s) * squareMass w := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (J s) w
    simpa only [φ', squareMass] using this
  have hJ : squareMass w ≤ squareMass (J s) := by
    rw [hφ'] at hcs
    rcases (squareMass_nonneg w).lt_or_eq with hpos | hzero
    · nlinarith
    · rw [← hzero]; exact squareMass_nonneg _
  have hdc := differential_contraction hx hx1 B hB (γ s) z (hS s hs')
  refine hJ.trans (hdc.trans ?_)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (squareMass_nonneg _)
  exact mul_le_mul_of_nonneg_left (pointWeight_segment_le hx hx1 hm (R i) (R' i) (hR i) (hR' i) hs')
    (div_nonneg (sub_nonneg.mpr hx1) (Real.exp_pos _).le)

/-- BBR Theorem 2.5, exactly the `theorem_2_5` field of `Literature`. -/
theorem theorem_2_5_holds : ∀ (Δ : ℕ) (_hΔ : 3 ≤ Δ) (_hq : 2 ≤ Fintype.card C) (x : ℝ), 0 < x → x < 1 →
    ∀ (d : ℕ) (b : C → ℕ) (t u : Fin d → Girth.CavityTree C),
      d + (∑ c, b c) ≤ Δ → (∀ i, (t i).DegreeBudget Δ) → (∀ i, (u i).DegreeBudget Δ) →
      (∀ i, CLMM.SameDomain (t i) (u i)) →
      squareMass (fun c => (Girth.CavityTree.node d b t).message x c -
        (Girth.CavityTree.node d b u).message x c) ≤
        ∑ i, ((1 - x) / Real.exp 1 * segmentWeightSquare x ((t i).message x) ((u i).message x)) *
          squareMass (fun c => (t i).message x c - (u i).message x c) := by
  intro Δ _ _ x hx hx1 d b t u _ ht hu _
  let B : C → ℝ := fun c => Real.sqrt (x ^ b c)
  have hB (c : C) : B c ^ 2 ≤ 1 := by
    dsimp [B]
    rw [Real.sq_sqrt (pow_nonneg hx.le _)]
    exact pow_le_one₀ hx.le hx1.le
  have hnode (v : Fin d → Girth.CavityTree C) :
      (Girth.CavityTree.node d b v).message x = localRoot x B (fun i => (v i).message x) :=
    funext fun c => Girth.CavityTree.message_node hx hx1.le d b v c
  have hfloor (v : Girth.CavityTree C) (hv : v.DegreeBudget Δ) (c : C) :
      Real.sqrt (x ^ (Δ - 1)) ≤ v.message x c :=
    CavityTree.message_uniform_lower hx le_rfl hx1.le v (Δ - 1) (cavity_total_degree v hv) c
  rw [hnode t, hnode u]
  exact segment_contraction hx hx1.le (Real.sqrt_pos.2 (pow_pos hx (Δ - 1))) B hB _ _
    (fun i c => hfloor (t i) (ht i) c) (fun i c => hfloor (u i) (hu i) c)

end
end CI2ZF.Appendix.BBR
