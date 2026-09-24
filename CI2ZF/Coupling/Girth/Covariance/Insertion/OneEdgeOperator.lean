import CI2ZF.Coupling.Girth.Covariance.Insertion.Edge
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The one-edge colour operator (companion Lemma 9.2, `lem:girth5-one-edge`)

For a cavity colour law `r` obtained after deleting one incident
constraint and `s = 1 - x`, the paper's operator is
`(T_r h)(t) = (⟨r,h⟩ - s r(t) h(t)) / (1 - s r(t))`, which is the library's
`edgeResponse s r h t`. With `m = q - Δ`, `B = 1/m` and
`L_Δ = (1 + √(q/(m+1)))/m`, the lemma asserts

1. `r(c) ≤ (m+1)⁻¹`, for every `x ∈ [0,1]` (including the hard endpoint);
2. `‖Π T_r Π‖_{2→2} ≤ L_Δ`, where `Π = I - q⁻¹ 𝟙𝟙ᵀ`;
3. `Var_{t∼ϱ}((T_r h)(t)) ≤ B L_Δ² ‖h‖₂²` whenever `ϱ` has atoms at most `B`.

Item 1 is proved here for `0 ≤ x ≤ 1` from the degree budget (the library's
`cavityLaw` and `cavityLaw_atom_le` require `0 < x`). Item 2 is proved both
as a pointwise Euclidean estimate and as an operator-norm bound for the
continuous linear map on `EuclideanSpace ℝ C`. Item 3 is the library's
`one_edge_variance_bound`, restated for the actual cavity law. The final
theorems package all three for the actual cavity law, first with a general
slack `0 < m ≤ q - Δ` and then exactly with the paper's `m = q - Δ`,
`m ≥ δΔ`, `B = m⁻¹`.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI CI2ZF.Appendix.Girth WithLp

noncomputable section

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C]

/-! ## The projection `Π` orthogonal to constants -/

/-- `Π h = h - q⁻¹ (∑ h) 𝟙`. -/
def centre (h : C → ℝ) : C → ℝ := fun c => h c - (∑ d, h d) / Fintype.card C

theorem centre_add_const [Nonempty C] (h : C → ℝ) (k : ℝ) :
    centre (fun c => k + h c) = centre h := by
  have hq : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  funext c
  simp only [centre, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem centre_sq_le [Nonempty C] (h : C → ℝ) :
    (∑ c, centre h c ^ 2) ≤ ∑ c, h c ^ 2 := by
  have hq : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  set A := ∑ d, h d
  have hid : (∑ c, centre h c ^ 2) = (∑ c, h c ^ 2) - A ^ 2 / Fintype.card C := by
    simp only [centre, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    field_simp
    ring
  rw [hid]
  have : 0 ≤ A ^ 2 / Fintype.card C := by positivity
  linarith

theorem centre_add (h g : C → ℝ) : centre (h + g) = centre h + centre g := by
  funext c
  simp only [centre, Pi.add_apply, Finset.sum_add_distrib]
  ring

theorem centre_smul (a : ℝ) (h : C → ℝ) : centre (a • h) = a • centre h := by
  funext c
  simp only [centre, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem edgeResponse_add (s : ℝ) (r : FinDist C) (h g : C → ℝ) :
    edgeResponse s r (h + g) = edgeResponse s r h + edgeResponse s r g := by
  funext t
  simp only [edgeResponse, expectReal, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem edgeResponse_smul (s a : ℝ) (r : FinDist C) (h : C → ℝ) :
    edgeResponse s r (a • h) = a • edgeResponse s r h := by
  funext t
  simp only [edgeResponse, expectReal, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ c, r.w c * (a * h c)) = a * ∑ c, r.w c * h c by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring]
  ring

/-- The paper's constant `L_Δ = (1 + √(q/(m+1)))/m`. -/
def oneEdgeConstant (q m : ℝ) : ℝ := (1 + Real.sqrt (q / (m + 1))) / m

theorem oneEdgeConstant_nonneg {q m : ℝ} (hm : 0 < m) : 0 ≤ oneEdgeConstant q m := by
  unfold oneEdgeConstant
  positivity

/-! ## `‖Π T_r Π‖_{2→2} ≤ L_Δ` -/

/-- Squared form of `‖Π T_r Π h‖₂ ≤ L_Δ ‖h‖₂`. -/
theorem projected_edge_sq_bound [Nonempty C] {s m : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hm : 0 < m) (r : FinDist C) (hr : ∀ c, r.w c ≤ 1 / (m + 1)) (h : C → ℝ) :
    (∑ t, centre (edgeResponse s r (centre h)) t ^ 2) ≤
      oneEdgeConstant (Fintype.card C) m ^ 2 * ∑ c, h c ^ 2 := by
  set h' := centre h
  set E := expectReal r h'
  let θ : C → ℝ := fun t => s * r.w t / (1 - s * r.w t)
  let k : C → ℝ := fun t => -(θ t) * (h' t - E)
  have hresp : edgeResponse s r h' = fun t => E + k t := by
    funext t
    obtain ⟨hd, _, _⟩ := edge_occupancy_bound hs0 hs1 hm r hr t
    have := edgeResponse_centered r h' t hd.ne'
    simp only [k, θ]
    linarith
  have hk (t : C) : k t ^ 2 ≤ (1 / m) ^ 2 * (h' t - E) ^ 2 := by
    obtain ⟨_, ht0, ht1⟩ := edge_occupancy_bound hs0 hs1 hm r hr t
    simp only [k, mul_pow, neg_sq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht0 ht1 2) (sq_nonneg _)
  have hp0 : (0 : ℝ) ≤ 1 / (m + 1) := by positivity
  have hc := centered_energy_bound r h' hp0 hr
  have hqp : (Fintype.card C : ℝ) * (1 / (m + 1)) = Fintype.card C / (m + 1) := by ring
  rw [hqp] at hc
  calc
    (∑ t, centre (edgeResponse s r h') t ^ 2) = ∑ t, centre k t ^ 2 := by
      rw [hresp, centre_add_const]
    _ ≤ ∑ t, k t ^ 2 := centre_sq_le k
    _ ≤ ∑ t, (1 / m) ^ 2 * (h' t - E) ^ 2 := Finset.sum_le_sum fun t _ => hk t
    _ = (1 / m) ^ 2 * ∑ t, (h' t - E) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / m) ^ 2 * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m + 1))) ^ 2 *
          ∑ c, h' c ^ 2) := mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ ≤ (1 / m) ^ 2 * ((1 + Real.sqrt ((Fintype.card C : ℝ) / (m + 1))) ^ 2 *
          ∑ c, h c ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left (centre_sq_le h) (sq_nonneg _)
    _ = oneEdgeConstant (Fintype.card C) m ^ 2 * ∑ c, h c ^ 2 := by
      unfold oneEdgeConstant
      ring

/-- Euclidean-norm form: `‖Π T_r Π h‖₂ ≤ L_Δ ‖h‖₂`. -/
theorem projected_edge_norm_bound [Nonempty C] {s m : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hm : 0 < m) (r : FinDist C) (hr : ∀ c, r.w c ≤ 1 / (m + 1)) (h : C → ℝ) :
    Real.sqrt (∑ t, centre (edgeResponse s r (centre h)) t ^ 2) ≤
      oneEdgeConstant (Fintype.card C) m * Real.sqrt (∑ c, h c ^ 2) := by
  have hL := oneEdgeConstant_nonneg (q := (Fintype.card C : ℝ)) hm
  calc
    _ ≤ Real.sqrt (oneEdgeConstant (Fintype.card C) m ^ 2 * ∑ c, h c ^ 2) :=
      Real.sqrt_le_sqrt (projected_edge_sq_bound hs0 hs1 hm r hr h)
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hL]

/-- The operator `Π T_r Π` on `EuclideanSpace ℝ C`. -/
def projectedEdgeOperator [Nonempty C] (s : ℝ) (r : FinDist C) :
    EuclideanSpace ℝ C →L[ℝ] EuclideanSpace ℝ C :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => toLp 2 (centre (edgeResponse s r (centre (ofLp h))))
      map_add' := by
        intro h g
        ext t
        simp only [ofLp_add, centre_add, edgeResponse_add, PiLp.add_apply, Pi.add_apply]
      map_smul' := by
        intro a h
        ext t
        simp only [ofLp_smul, centre_smul, edgeResponse_smul, PiLp.smul_apply,
          Pi.smul_apply, RingHom.id_apply] }

theorem projectedEdgeOperator_apply [Nonempty C] (s : ℝ) (r : FinDist C)
    (h : EuclideanSpace ℝ C) (t : C) :
    projectedEdgeOperator s r h t = centre (edgeResponse s r (centre (ofLp h))) t := rfl

/-- Operator-norm form: `‖Π T_r Π‖_{2→2} ≤ L_Δ`. -/
theorem projectedEdgeOperator_norm_le [Nonempty C] {s m : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hm : 0 < m) (r : FinDist C) (hr : ∀ c, r.w c ≤ 1 / (m + 1)) :
    ‖projectedEdgeOperator s r‖ ≤ oneEdgeConstant (Fintype.card C) m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (oneEdgeConstant_nonneg hm)
  intro h
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [Real.norm_eq_abs, sq_abs, projectedEdgeOperator_apply]
  exact projected_edge_norm_bound hs0 hs1 hm r hr (ofLp h)

/-! ## The actual cavity law on the closed interval `[0,1]` -/

section Cavity

variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableEq C] [Nonempty C]
variable (I : PinningData V C)

/-- The cavity partition after deleting the incident constraint `vw` is at
least `m + 1`, for every `x ≥ 0`. -/
theorem cavityPartition_lower {x : ℝ} (hx0 : 0 ≤ x) {Δ : ℕ}
    (hd : I.DegreeBound Δ) {m : ℝ} (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) :
    m + 1 ≤ GraphHeatBath.cavityPartition I x σ v w := by
  have hb := palette_mass_lower hx0 (GraphHeatBath.cavityCount I σ v w)
  have hs : (∑ c, (GraphHeatBath.cavityCount I σ v w c : ℝ)) + 1 ≤ (Δ : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast (by rw [GraphHeatBath.cavityCount_sum I σ v w hvw]; exact hd v)
  have hn : 0 ≤ ∑ c, (GraphHeatBath.cavityCount I σ v w c : ℝ) :=
    Finset.sum_nonneg fun c _ => Nat.cast_nonneg _
  change (Fintype.card C : ℝ) - (1 - x) * ∑ c, (GraphHeatBath.cavityCount I σ v w c : ℝ) ≤
    GraphHeatBath.cavityPartition I x σ v w at hb
  nlinarith

/-- The cavity colour law after deleting one incident constraint, defined
for every nonnegative activity with positive cavity partition (in
particular at `x = 0`). -/
def cavityLawNN {x : ℝ} (hx0 : 0 ≤ x) (σ : V → C) (v w : V)
    (hZ : 0 < GraphHeatBath.cavityPartition I x σ v w) : FinDist C where
  w c := GraphHeatBath.cavityWeight I x σ v w c / GraphHeatBath.cavityPartition I x σ v w
  nonneg c := div_nonneg (pow_nonneg hx0 _) hZ.le
  sum_one := by rw [← Finset.sum_div]; exact div_self hZ.ne'

/-- For `x > 0` this is the library's `cavityLaw`. -/
theorem cavityLawNN_eq {x : ℝ} (hx : 0 < x) (σ : V → C) (v w : V)
    (hZ : 0 < GraphHeatBath.cavityPartition I x σ v w) :
    cavityLawNN I hx.le σ v w hZ = GraphHeatBath.cavityLaw I x hx σ v w := rfl

/-- `r(c) ≤ (m+1)⁻¹` on the closed interval `0 ≤ x ≤ 1`. -/
theorem cavityLawNN_atom_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) {m : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (σ : V → C) (v w : V) (hvw : I.graph.Adj v w)
    (hZ : 0 < GraphHeatBath.cavityPartition I x σ v w) (c : C) :
    (cavityLawNN I hx0 σ v w hZ).w c ≤ 1 / (m + 1) := by
  have hlow := cavityPartition_lower I hx0 hd hq σ v w hvw
  have hnum : GraphHeatBath.cavityWeight I x σ v w c ≤ 1 := pow_le_one₀ hx0 hx1
  change GraphHeatBath.cavityWeight I x σ v w c / GraphHeatBath.cavityPartition I x σ v w ≤
    1 / (m + 1)
  apply (div_le_div_iff₀ hZ (by linarith)).mpr
  have h0 : 0 ≤ GraphHeatBath.cavityWeight I x σ v w c := pow_nonneg hx0 _
  nlinarith

/-- Companion Lemma 9.2 (`lem:girth5-one-edge`) for the actual cavity law
of `v` after deleting the edge `vw`, for every `x ∈ [0,1]`, `s = 1 - x`, and
any slack `0 < m ≤ q - Δ`: the atom bound, the projected operator bound
`‖Π T_r Π‖_{2→2} ≤ L`, its pointwise Euclidean form, and the variance bound
`Var_ϱ(T_r h) ≤ B L² ‖h‖₂²` for every law `ϱ` with atoms at most `B`. -/
theorem one_edge_operator {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {Δ : ℕ}
    (hd : I.DegreeBound Δ) {m : ℝ} (hm : 0 < m) (hq : m ≤ (Fintype.card C : ℝ) - Δ)
    (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) :
    ∃ hZ : 0 < GraphHeatBath.cavityPartition I x σ v w,
      (∀ c, (cavityLawNN I hx0 σ v w hZ).w c ≤ 1 / (m + 1)) ∧
      ‖projectedEdgeOperator (1 - x) (cavityLawNN I hx0 σ v w hZ)‖ ≤
        oneEdgeConstant (Fintype.card C) m ∧
      (∀ h : C → ℝ,
        Real.sqrt (∑ t, centre (edgeResponse (1 - x) (cavityLawNN I hx0 σ v w hZ)
            (centre h)) t ^ 2) ≤
          oneEdgeConstant (Fintype.card C) m * Real.sqrt (∑ c, h c ^ 2)) ∧
      ∀ {B : ℝ}, 0 ≤ B → ∀ ϱ : FinDist C, (∀ c, ϱ.w c ≤ B) → ∀ h : C → ℝ,
        variance ϱ (edgeResponse (1 - x) (cavityLawNN I hx0 σ v w hZ) h) ≤
          B * oneEdgeConstant (Fintype.card C) m ^ 2 * ∑ c, h c ^ 2 := by
  have hZ : 0 < GraphHeatBath.cavityPartition I x σ v w :=
    by linarith [cavityPartition_lower I hx0 hd hq σ v w hvw]
  have hr := cavityLawNN_atom_le I hx0 hx1 hd hm hq σ v w hvw hZ
  have hs0 : 0 ≤ 1 - x := by linarith
  have hs1 : 1 - x ≤ 1 := by linarith
  refine ⟨hZ, hr, projectedEdgeOperator_norm_le hs0 hs1 hm _ hr,
    fun h => projected_edge_norm_bound hs0 hs1 hm _ hr h, ?_⟩
  intro B hB ϱ hϱ h
  have := one_edge_variance_bound hs0 hs1 hm hB _ ϱ hr hϱ h
  simpa only [oneEdgeConstant] using this

/-- The paper's exact instantiation: `m = q - Δ ≥ δΔ` with `δ > 0` and
`Δ ≥ 1`, `B = m⁻¹`, `L_Δ = (1 + √(q/(m+1)))/m`, for every `x ∈ [0,1]`. -/
theorem girth5_one_edge {δ : ℝ} (hδ : 0 < δ) {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hm : δ * Δ ≤ (Fintype.card C : ℝ) - Δ)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hd : I.DegreeBound Δ)
    (σ : V → C) (v w : V) (hvw : I.graph.Adj v w) :
    ∃ hZ : 0 < GraphHeatBath.cavityPartition I x σ v w,
      (∀ c, (cavityLawNN I hx0 σ v w hZ).w c ≤ 1 / (((Fintype.card C : ℝ) - Δ) + 1)) ∧
      ‖projectedEdgeOperator (1 - x) (cavityLawNN I hx0 σ v w hZ)‖ ≤
        oneEdgeConstant (Fintype.card C) ((Fintype.card C : ℝ) - Δ) ∧
      ∀ ϱ : FinDist C, (∀ c, ϱ.w c ≤ 1 / ((Fintype.card C : ℝ) - Δ)) → ∀ h : C → ℝ,
        variance ϱ (edgeResponse (1 - x) (cavityLawNN I hx0 σ v w hZ) h) ≤
          1 / ((Fintype.card C : ℝ) - Δ) *
            oneEdgeConstant (Fintype.card C) ((Fintype.card C : ℝ) - Δ) ^ 2 *
              ∑ c, h c ^ 2 := by
  have hΔ' : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hmpos : 0 < (Fintype.card C : ℝ) - Δ := by nlinarith
  obtain ⟨hZ, hr, hop, -, hvar⟩ :=
    one_edge_operator I hx0 hx1 hd hmpos le_rfl σ v w hvw
  exact ⟨hZ, hr, hop, fun ϱ hϱ h => hvar (by positivity) ϱ hϱ h⟩

end Cavity

end

end CI2ZF.Appendix.Girth
