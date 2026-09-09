import CI2ZF.Coupling.CV.SoftEndgame
import CI2ZF.Coupling.CV.GeometricDrift
import CI2ZF.Coupling.Vigoda.OptionCI

/-! Complete CV coupling independence for the actual normalized root
children, including empty remaining graphs and both real endpoints. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.FinDist CI2ZF.Potts
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]
local instance cvRootCIConfigDecEq : DecidableEq (V → C) := Classical.decEq _

def ciConstant : ℝ := 2 / (metricLower * gap)

lemma ciConstant_bounds : 0 < ciConstant ∧ ciConstant = 409060125 / 50858 ∧
    ciConstant < 804319 / 100 := by norm_num [ciConstant, metricLower, gap]

lemma colours_slack {Δ : ℕ} (hΔ : 125 ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) : Δ + 2 ≤ Fintype.card C := by
  have hd : (125 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have h : (Δ : ℝ) + 2 ≤ Fintype.card C := by linarith
  exact_mod_cast h

/-- All concrete adjacent-drift hypotheses are discharged. -/
theorem soft_adjacent_contraction [Nonempty V]
    (I : PinningData V C) {Δ : ℕ} (hΔ : 125 ≤ Δ) (hd : I.DegreeBound Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : AdjacentSoftContraction I Δ x hx0 hx1 := by
  intro X Y hXY
  obtain ⟨v, hv, hagree⟩ := CI2ZF.exists_unique_disagreement hXY
  have hd0 : 0 < Δ := by omega
  have hfree (u : V) : I.graph.degree u ≤ Δ := (Nat.le_add_right _ _).trans (hd u)
  have hh := (soft_W_le_averagedCost I X Y v hv hagree
    (optimizedAdjacentChoices I X Y v hv hagree) x hx0 hx1 (geometricMetric I x)
    (geometricMetric_nonneg I ⟨hx0.le, hx1.le⟩ hd0 hfree hq)).trans
      (averaged_geometric_contract I X Y v hv hagree x ⟨hx0.le, hx1.le⟩ hΔ hd hq)
  rwa [geometricMetric_adjacent I ⟨hx0.le, hx1.le⟩ hd0 hfree hq hXY] at hh

variable {O : Type*} [Fintype O]

theorem optionChild_soft_boundary_W_le [Nonempty O]
    (I : PinningData (Option O) C) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (a : C) (X : O → C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham (softCVKernel (optionChildData I a) x hx0 hx1 X)
      (softCVKernel (optionMiddleData I) x hx0 hx1 X) ≤
        (1 - x) * Δ / ((Fintype.card O : ℝ) * Fintype.card C) := by
  apply (softCVKernel_addBoundarySet_W_le
    (optionMiddleData I) (optionRootNeighbours I) a X x hx0 hx1).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  exact_mod_cast optionRootNeighbours_card_le I hd

/-- The exact interior bound has an extra factor `1-x`. -/
theorem option_root_ci_open [Nonempty O]
    (I : PinningData (Option O) C) {Δ : ℕ} (hΔ : 125 ≤ Δ) (hd : I.DegreeBound Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (a b : C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W ham ((optionChildData I a).gibbs x hx0.le ((optionChildData I a).partition_pos_of_parameter_pos hx0))
      ((optionChildData I b).gibbs x hx0.le ((optionChildData I b).partition_pos_of_parameter_pos hx0)) ≤
        2 * (1 - x) / (metricLower * gap) := by
  have hd0 : 0 < Δ := by omega
  have hchild (c : C) := optionChildData_degreeBound I hd c
  have hcomp (c : C) := gibbs_comparison_of_adjacent
    (optionChildData I c) (optionMiddleData I) hd0
    (fun u => (Nat.le_add_right _ _).trans (hchild c u)) hq x hx0 hx1
    (soft_adjacent_contraction _ hΔ (hchild c) hq x hx0 hx1)
    (fun X => optionChild_soft_boundary_W_le I hd c X x hx0 hx1)
  have ht := W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle
    ((optionChildData I a).gibbs x hx0.le ((optionChildData I a).partition_pos_of_parameter_pos hx0))
    ((optionMiddleData I).gibbs x hx0.le ((optionMiddleData I).partition_pos_of_parameter_pos hx0))
    ((optionChildData I b).gibbs x hx0.le ((optionChildData I b).partition_pos_of_parameter_pos hx0))
  rw [W_ham_comm ((optionMiddleData I).gibbs x hx0.le _) _] at ht
  exact (ht.trans (add_le_add (hcomp a) (hcomp b))).trans_eq (by ring)

/-- A useful finite-state endpoint lemma: uniform open-interval transport
bounds pass to activity zero, and activity one is the common product law. -/
theorem closed_gibbs_bound_of_open
    (I J : PinningData V C) {Δ : ℕ} (hI : I.DegreeBound Δ) (hJ : J.DegreeBound Δ)
    (hq : Δ + 2 ≤ Fintype.card C) {K : ℝ} (hK : 0 ≤ K)
    (hopen : ∀ (x : ℝ) (hx : 0 < x), x < 1 →
      W ham (I.gibbs x hx.le (I.partition_pos_of_parameter_pos hx))
        (J.gibbs x hx.le (J.partition_pos_of_parameter_pos hx)) ≤ K)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham (I.nonnegativeGibbs hI hq x) (J.nonnegativeGibbs hJ hq x) ≤ K := by
  have hpos : ∀ y : PinningData.NonnegativeParameter, 0 < (y : ℝ) → (y : ℝ) ≤ 1 →
      W ham (I.nonnegativeGibbs hI hq y) (J.nonnegativeGibbs hJ hq y) ≤ K := by
    intro y hy hy1
    rcases lt_or_eq_of_le hy1 with hylt | hyeq
    · exact hopen y hy hylt
    · have hyeq' : y = ⟨1, by norm_num⟩ := Subtype.ext hyeq
      subst y
      rw [PinningData.nonnegativeGibbs, PinningData.nonnegativeGibbs, W_ham_gibbs_one]
      exact hK
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x from x.property) with hxzero | hxpos
  · have hxeq : x = PinningData.hardParameter := Subtype.ext hxzero.symm
    subst x
    exact I.hard_W_le_of_positive_parameter_bound J hI hJ hq hardApproach tendsto_hardApproach
      (Filter.Eventually.of_forall hardApproach_pos)
      (Filter.Eventually.of_forall hardApproach_le_one)
      ham_nonneg ham_self ham_triangle ham_le_card hpos
  · exact hpos x hxpos hx1

/-- The appendix's full-interval CV root CI theorem, on actual finite
Gibbs laws, with no external coupling or contraction premise. -/
theorem option_root_ci
    (I : PinningData (Option O) C) {Δ : ℕ} (hΔ : 125 ≤ Δ) (hd : I.DegreeBound Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (a b : C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    W ham
      ((optionChildData I a).nonnegativeGibbs (optionChildData_degreeBound I hd a) (colours_slack hΔ hq) x)
      ((optionChildData I b).nonnegativeGibbs (optionChildData_degreeBound I hd b) (colours_slack hΔ hq) x) ≤
        ciConstant := by
  apply closed_gibbs_bound_of_open _ _ (optionChildData_degreeBound I hd a)
    (optionChildData_degreeBound I hd b) (colours_slack hΔ hq) ciConstant_bounds.1.le _ x hx1
  intro y hy0 hy1
  cases isEmpty_or_nonempty O with
  | inl h =>
    let := h
    rw [W_ham_eq_zero_of_isEmpty]
    exact ciConstant_bounds.1.le
  | inr h =>
    let := h
    apply (option_root_ci_open I hΔ hd hq a b y hy0 hy1).trans
    unfold ciConstant
    apply div_le_div_of_nonneg_right _ (by norm_num [metricLower, gap])
    linarith

end
end CI2ZF.Appendix.CV
