import ZeroFreeness.Coupling.CV.Geometry
import ZeroFreeness.Coupling.CV.Boundary
import ZeroFreeness.Coupling.Foundations.TwoMetric

/-! Transport comparison for the actual CV metric, and the child--middle row
bound in that metric. These statements use the original graph's actual children. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.FinDist ZeroFreeness.Potts
attribute [local instance] Classical.propDecidable
noncomputable section
local instance (priority := 2000) cVTransportDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
variable {V C : Type*} [Fintype V] [Fintype C]

lemma geometricMetric_nonneg (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X Y : V → C) :
    0 ≤ geometricMetric I x X Y :=
  (mul_nonneg (by norm_num [metricLower]) (ham_nonneg X Y)).trans
    (geometricMetric_comparison I hx hΔ hdegree hq X Y).1

lemma geometricMetric_triangle (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X Y Z : V → C) :
    geometricMetric I x X Z ≤ geometricMetric I x X Y + geometricMetric I x Y Z :=
  pathMetric_triangle _ (by norm_num [metricLower])
    (fun X Y h => (edgeLength_bounds I hx hΔ hdegree hq X Y h).1) X Y Z

lemma geometricMetric_comm (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X Y : V → C) :
    geometricMetric I x X Y = geometricMetric I x Y X :=
  pathMetric_comm _ (by norm_num [metricLower])
    (fun X Y h => (edgeLength_bounds I hx hΔ hdegree hq X Y h).1) (edgeLength_comm I x) X Y

lemma geometricMetric_self (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X : V → C) :
    geometricMetric I x X X = 0 := by
  apply le_antisymm _ (geometricMetric_nonneg I hx hΔ hdegree hq X X)
  simpa [ham_self] using (geometricMetric_comparison I hx hΔ hdegree hq X X).2

/-- The metric comparison survives optimal transport without an assumed
optimal coupling. -/
theorem geometric_transport_comparison (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (mu nu : FinDist (V → C)) :
    metricLower * W ham mu nu ≤ W (geometricMetric I x) mu nu ∧
      W (geometricMetric I x) mu nu ≤ W ham mu nu := by
  constructor
  · exact mul_W_le_W_of_mul_le (by norm_num [metricLower]) ham_nonneg
      (fun X Y => (geometricMetric_comparison I hx hΔ hdegree hq X Y).1)
  · apply le_W
    intro gamma
    apply (W_le_cost (geometricMetric_nonneg I hx hΔ hdegree hq) gamma).trans
    unfold Coupling.cost
    apply Finset.sum_le_sum
    intro X _
    apply Finset.sum_le_sum
    intro Y _
    exact mul_le_mul_of_nonneg_left
      (geometricMetric_comparison I hx hΔ hdegree hq X Y).2 (gamma.nonneg X Y)

/-- Lemma cv-child-middle, in the actual activity-dependent child metric. -/
theorem rootChild_geometric_boundary_W_le [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (a : C) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (X : RootRemaining tau r → C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    W (geometricMetric (rootChildData tau G r a) x)
      (softCVKernel (rootChildData tau G r a) x hx0 hx1 X)
      (softCVKernel (rootMiddleData tau G r) x hx0 hx1 X) ≤
      (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  have hd (v : RootRemaining tau r) : (rootChildData tau G r a).graph.degree v ≤ Δ :=
    (Nat.le_add_right _ _).trans (rootChildData_degreeBound tau G r a hdegree v)
  apply (geometric_transport_comparison _ ⟨hx0.le, hx1.le⟩ hΔ hd hq _ _).2.trans
  exact rootChild_soft_boundary_W_le tau G r a hdegree X x hx0 hx1

end
end ZeroFreeness.Appendix.CV
