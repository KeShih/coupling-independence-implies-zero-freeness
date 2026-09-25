import ZeroFreeness.Coupling.CV.DiscountTotal
import ZeroFreeness.Coupling.CV.Boundary
import ZeroFreeness.Coupling.Foundations.TwoMetric
import ZeroFreeness.Coupling.Vigoda.CouplingIndependence

/-! Actual common-coin averaging, weighted path coupling and two-metric
stationary comparison for the CV kernel. The adjacent estimate is isolated
here and discharged by the geometric-drift module in the final CI theorem. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.FinDist ZeroFreeness.Potts
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvSoftEndgameConfigDecEq : DecidableEq (V → C) := Classical.decEq _

def contractionFactor (V C : Type*) [Fintype V] [Fintype C] (Δ : ℕ) : ℝ :=
  1 - gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C)

lemma contractionFactor_mem [Nonempty V] [Nonempty C] {Δ : ℕ} (hΔ : 0 < Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) :
    contractionFactor V C Δ ∈ Set.Ico (0 : ℝ) 1 := by
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hd : (0 : ℝ) < Δ := Nat.cast_pos.mpr hΔ
  have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hD : 0 < (Fintype.card V : ℝ) * Fintype.card C := by positivity
  have hDΔ : (Δ : ℝ) ≤ (Fintype.card V : ℝ) * Fintype.card C := by nlinarith
  have hg : 0 < gap ∧ gap ≤ 1 := by norm_num [gap]
  have hp : 0 < gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C) :=
    div_pos (mul_pos hg.1 hd) hD
  have hp1 : gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C) ≤ 1 := by
    apply (div_le_one hD).mpr
    exact (mul_le_of_le_one_left hd.le hg.2).trans hDΔ
  exact ⟨by dsimp [contractionFactor]; linarith, by dsimp [contractionFactor]; linarith⟩

lemma geometricMetric_nonneg (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hd : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X Y : V → C) :
    0 ≤ geometricMetric I x X Y :=
  (mul_nonneg (by norm_num [metricLower]) (ham_nonneg X Y)).trans
    (geometricMetric_comparison I hx hΔ hd hq X Y).1

lemma geometricMetric_triangle (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hd : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X Y Z : V → C) :
    geometricMetric I x X Z ≤ geometricMetric I x X Y + geometricMetric I x Y Z :=
  pathMetric_triangle _ (by norm_num [metricLower])
    (fun X Y h => (edgeLength_bounds I hx hΔ hd hq X Y h).1) X Y Z

lemma W_geometric_le_hamming (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hd : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (μ ν : FinDist (V → C)) :
    W (geometricMetric I x) μ ν ≤ W ham μ ν := by
  apply le_W
  intro γ
  exact (W_le_cost (geometricMetric_nonneg I hx hΔ hd hq) γ).trans
    (cost_le_cost γ (fun X Y => (geometricMetric_comparison I hx hΔ hd hq X Y).2))

/-- The explicit completed hard couplings form a coupling of the two
actual soft rows after averaging the shared Bernoulli variables. -/
theorem soft_W_le_averagedCost [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (d : (V → C) → (V → C) → ℝ) (hd : ∀ X Y, 0 ≤ d X Y) :
    W d (softCVKernel I x hx0 hx1 X) (softCVKernel I x hx0 hx1 Y) ≤
      averagedCost I X Y v hroot hagree choice x ⟨hx0.le, hx1.le⟩ d := by
  rw [softCVKernel_eq_coin_mixture, softCVKernel_eq_coin_mixture]
  apply (W_bind_diag hd _ _ _).trans
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left
    (W_le_cost hd (adjacentHardCoupling I X Y v hroot hagree choice ω))
    ((activityCoins I x ⟨hx0.le, hx1.le⟩).nonneg ω)

def AdjacentSoftContraction [Nonempty V] [Nonempty C]
    (I : PinningData V C) (Δ : ℕ) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : Prop :=
  ∀ X Y : V → C, hamCard X Y = 1 →
    W (geometricMetric I x) (softCVKernel I x hx0 hx1 X) (softCVKernel I x hx0 hx1 Y) ≤
      contractionFactor V C Δ * edgeLength I x X Y

theorem soft_rows_contract_of_adjacent [Nonempty V] [Nonempty C]
    (I : PinningData V C) {Δ : ℕ} (hΔ : 0 < Δ)
    (hd : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hadj : AdjacentSoftContraction I Δ x hx0 hx1) (X Y : V → C) :
    W (geometricMetric I x) (softCVKernel I x hx0 hx1 X) (softCVKernel I x hx0 hx1 Y) ≤
      contractionFactor V C Δ * geometricMetric I x X Y :=
  pathMetric_W_contract _ (by norm_num [metricLower])
    (fun X Y h => (edgeLength_bounds I ⟨hx0.le, hx1.le⟩ hΔ hd hq X Y h).1)
    (contractionFactor_mem hΔ hq).1 _ hadj X Y

theorem soft_laws_contract_of_adjacent [Nonempty V] [Nonempty C]
    (I : PinningData V C) {Δ : ℕ} (hΔ : 0 < Δ)
    (hd : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hadj : AdjacentSoftContraction I Δ x hx0 hx1) (μ ν : FinDist (V → C)) :
    W (geometricMetric I x) (μ.bind (softCVKernel I x hx0 hx1)) (ν.bind (softCVKernel I x hx0 hx1)) ≤
      contractionFactor V C Δ * W (geometricMetric I x) μ ν :=
  W_bind_contract (geometricMetric_nonneg I ⟨hx0.le, hx1.le⟩ hΔ hd hq)
    (geometricMetric_nonneg I ⟨hx0.le, hx1.le⟩ hΔ hd hq)
    (contractionFactor_mem hΔ hq).1 _
    (soft_rows_contract_of_adjacent I hΔ hd hq x hx0 hx1 hadj) μ ν

/-- Comparing one root child with the middle law costs at most
`(1-x)/(metricLower*gap)`; the state-space size and degree cancel. -/
theorem gibbs_comparison_of_adjacent [Nonempty V] [Nonempty C]
    (I J : PinningData V C) {Δ : ℕ} (hΔ : 0 < Δ)
    (hd : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hadj : AdjacentSoftContraction I Δ x hx0 hx1)
    (hperturb : ∀ X, W ham (softCVKernel I x hx0 hx1 X) (softCVKernel J x hx0 hx1 X) ≤
      (1 - x) * Δ / ((Fintype.card V : ℝ) * Fintype.card C)) :
    W ham (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0))
      (J.gibbs x hx0.le (J.partition_pos_of_parameter_pos hx0)) ≤
      (1 - x) / (metricLower * gap) := by
  have hcomp := stationary_comparison_two_metric ham_nonneg
    (geometricMetric_nonneg I ⟨hx0.le, hx1.le⟩ hΔ hd hq)
    (geometricMetric_triangle I ⟨hx0.le, hx1.le⟩ hΔ hd hq)
    (softCVKernel I x hx0 hx1) (softCVKernel J x hx0 hx1)
    (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0))
    (J.gibbs x hx0.le (J.partition_pos_of_parameter_pos hx0))
    (softCVKernel_stationary I x hx0 hx1) (softCVKernel_stationary J x hx0 hx1)
    (contractionFactor_mem hΔ hq).1 (contractionFactor_mem hΔ hq).2
    (soft_laws_contract_of_adjacent I hΔ hd hq x hx0 hx1 hadj)
    (by norm_num [metricLower] : 0 < metricLower)
    (fun X Y => (geometricMetric_comparison I ⟨hx0.le, hx1.le⟩ hΔ hd hq X Y).1)
    (fun X => (W_geometric_le_hamming I ⟨hx0.le, hx1.le⟩ hΔ hd hq _ _).trans (hperturb X))
  apply hcomp.trans_eq
  have hd0 : (Δ : ℝ) ≠ 0 := (Nat.cast_pos.mpr hΔ).ne'
  have hn0 : (Fintype.card V : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  have hq0 : (Fintype.card C : ℝ) ≠ 0 := (Nat.cast_pos.mpr Fintype.card_pos).ne'
  dsimp [contractionFactor]
  simp only [sub_sub_cancel]
  field_simp [hd0, hn0, hq0]

end
end ZeroFreeness.Appendix.CV
