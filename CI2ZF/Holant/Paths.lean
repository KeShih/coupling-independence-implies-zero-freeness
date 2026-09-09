import CI2ZF.Holant.ResidualModel
import CI2ZF.Analysis.AnalyticLog

/-! Activity paths used to state the simultaneous Holant induction.
The complex parameter varies on a disk, while each edge activity can move
independently. A finite-dimensional ray lemma recovers arbitrary points of
the product neighborhood at the end. -/
namespace CI2ZF.Holant
open Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V E : Type*} [Fintype V] [DecidableEq E]
set_option linter.unusedSectionVars false

structure ActivityPath (edges : Finset E) (R ε : ℝ) where
  base : E → ℝ
  radius : ℝ
  radius_pos : 0 < radius
  activity : ℂ → E → ℂ
  realBox : ∀ e ∈ edges, base e ∈ Icc 0 R
  at_zero : ∀ e ∈ edges, activity 0 e = (base e : ℂ)
  differentiable : ∀ e ∈ edges, DifferentiableOn ℂ (fun t => activity t e) (ball 0 radius)
  near : ∀ t ∈ ball 0 radius, ∀ e ∈ edges, ‖activity t e - (base e : ℂ)‖ < ε

namespace ActivityPath

def restrict {edges A : Finset E} {R ε : ℝ} (p : ActivityPath edges R ε) (hA : A ⊆ edges) :
    ActivityPath A R ε where
  base := p.base
  radius := p.radius
  radius_pos := p.radius_pos
  activity := p.activity
  realBox e he := p.realBox e (hA he)
  at_zero e he := p.at_zero e (hA he)
  differentiable e he := p.differentiable e (hA he)
  near t ht e he := p.near t ht e (hA he)

theorem partition_differentiable {edges : Finset E} {R ε : ℝ}
    (p : ActivityPath edges R ε) (inc : E → V → Prop) (f : V → ℕ → ℂ) :
    DifferentiableOn ℂ (fun t => partition inc edges f (p.activity t)) (ball 0 p.radius) := by
  unfold partition weight
  apply DifferentiableOn.fun_sum
  intro S hS
  apply DifferentiableOn.const_mul
  apply DifferentiableOn.fun_finsetProd
  intro e he
  exact p.differentiable e ((Finset.mem_powerset.mp hS) he)

theorem partition_at_zero {edges : Finset E} {R ε : ℝ}
    (p : ActivityPath edges R ε) (inc : E → V → Prop) (f : V → ℕ → ℂ) :
    partition inc edges f (p.activity 0) = partition inc edges f (fun e => (p.base e : ℂ)) := by
  apply Finset.sum_congr rfl
  intro S hS
  unfold weight
  congr 1
  exact Finset.prod_congr rfl (fun e he => p.at_zero e ((Finset.mem_powerset.mp hS) he))

theorem instance_differentiable (H : Instance V E) {R ε : ℝ}
    (p : ActivityPath H.edges R ε) :
    DifferentiableOn ℂ (fun t => H.complexPartition (p.activity t)) (ball 0 p.radius) :=
  p.partition_differentiable H.incidence (complexValues H.signature)

theorem instance_at_zero (H : Instance V E) {R ε : ℝ}
    (p : ActivityPath H.edges R ε) :
    H.complexPartition (p.activity 0) = (H.realPartition p.base : ℂ) := by
  rw [Instance.complexPartition, p.partition_at_zero]
  exact H.complexPartition_ofReal p.base

end ActivityPath

/-- Every point of a coordinatewise tube lies on an admissible analytic
path at parameter one, strictly inside its parameter disk. -/
theorem exists_activity_path_to (edges : Finset E) {R ε : ℝ} (hε : 0 < ε)
    (x : E → ℝ) (z : E → ℂ) (hx : ∀ e ∈ edges, x e ∈ Icc 0 R)
    (hz : ∀ e ∈ edges, ‖z e - (x e : ℂ)‖ < ε) :
    ∃ p : ActivityPath edges R ε, 1 < p.radius ∧ ∀ e ∈ edges, p.activity 1 e = z e := by
  let d : edges → ℂ := fun e => z e - (x e : ℂ)
  let m : ℝ := ‖d‖
  have hm0 : 0 ≤ m := norm_nonneg _
  have hmε : m < ε := (pi_norm_lt_iff hε).mpr (fun e => hz e e.property)
  have hmp : 0 < m + 1 := by linarith
  let r := (ε + 1) / (m + 1)
  have hr1 : 1 < r := by
    apply (lt_div_iff₀ hmp).mpr
    linarith
  have hr0 : 0 < r := zero_lt_one.trans hr1
  have hrm : r * m < ε := by
    dsimp [r]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hmp).mpr
    nlinarith
  let p : ActivityPath edges R ε := {
    base := x
    radius := r
    radius_pos := hr0
    activity := fun t e => (x e : ℂ) + t * (z e - (x e : ℂ))
    realBox := hx
    at_zero := by intros; simp
    differentiable := by intros; fun_prop
    near := by
      intro t ht e he
      simp only [add_sub_cancel_left, norm_mul]
      have ht' : ‖t‖ ≤ r :=
        (show ‖t‖ < r by simpa [mem_ball, dist_eq_norm] using ht).le
      have hd : ‖z e - (x e : ℂ)‖ ≤ m := norm_le_pi_norm d ⟨e, he⟩
      exact (mul_le_mul ht' hd (norm_nonneg _) hr0.le).trans_lt hrm }
  exact ⟨p, hr1, by intros; simp [p]⟩

/-- Two already nonzero analytic child partitions have an actual normalized
response logarithm, without requiring their images to avoid a branch cut. -/
theorem exists_child_response_log (P Q : ℂ → ℂ) {r : ℝ} (hr : 0 < r)
    (hP : DifferentiableOn ℂ P (ball 0 r)) (hQ : DifferentiableOn ℂ Q (ball 0 r))
    (hnP : ∀ t ∈ ball 0 r, P t ≠ 0) (hnQ : ∀ t ∈ ball 0 r, Q t ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball 0 r) ∧ L 0 = 0 ∧
      ∀ t ∈ ball 0 r, Complex.exp (L t) = (P t / P 0) / (Q t / Q 0) := by
  obtain ⟨LP, hLP0, hLP, heP⟩ := exists_normalized_log_on_ball P hr hP hnP
  obtain ⟨LQ, hLQ0, hLQ, heQ⟩ := exists_normalized_log_on_ball Q hr hQ hnQ
  refine ⟨fun t => LP t - LQ t, ?_, by simp [hLP0, hLQ0], ?_⟩
  · apply DifferentiableOn.sub
    · exact fun t ht => (hLP t ht).differentiableAt.differentiableWithinAt
    · exact fun t ht => (hLQ t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [Complex.exp_sub, heP t ht, heQ t ht]

/-- The response property used in strong induction quantifies actual
analytic branches. The accompanying nonvanishing induction guarantees
their existence; this definition cannot replace that obligation. -/
def ResponseBound (H : NormalizedInstance V E) (e : E) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) {R ε : ℝ} (p : ActivityPath H.edges R ε) (α : ℝ) : Prop :=
  ∀ L : ℂ → ℂ, DifferentiableOn ℂ L (ball 0 p.radius) → L 0 = 0 →
    (∀ t ∈ ball 0 p.radius, Complex.exp (L t) =
      ((H.oneChild e he hs).toInstance.complexPartition (p.activity t) /
        ((H.oneChild e he hs).toInstance.realPartition p.base : ℂ)) /
      ((H.zeroChild e).toInstance.complexPartition (p.activity t) /
        ((H.zeroChild e).toInstance.realPartition p.base : ℂ))) →
    ∀ t ∈ ball 0 p.radius, ‖L t‖ ≤ α

end
end CI2ZF.Holant
