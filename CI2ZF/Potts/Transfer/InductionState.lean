import CI2ZF.Potts.Model.OptionPartition
import CI2ZF.Analysis.AnalyticLog

/-! The simultaneous induction predicates, stated for actual partition
functions. These definitions do not assume or assert a transfer theorem. -/
namespace CI2ZF.Potts
open PottsCI Separator
noncomputable section
attribute [local instance] Classical.propDecidable

def HasSmallResponseLog (f g : ℂ → ℂ) (x : ℂ) (r alpha : ℝ) : Prop :=
  ∃ L : ℂ → ℂ, L x = 0 ∧ DifferentiableOn ℂ L (Metric.ball x r) ∧
    (∀ z ∈ Metric.ball x r, Complex.exp (L z) = (f z / f x) / (g z / g x)) ∧
    ∀ z ∈ Metric.ball x r, ‖L z‖ ≤ alpha

def PartitionNonzeroOn {V C : Type*} [Fintype V] [Fintype C]
    (I : PinningData V C) (x : ℂ) (r : ℝ) : Prop :=
  ∀ z ∈ Metric.ball x r, pinningProductPartition I z ≠ 0

def OptionRootResponses {V C : Type*} [Fintype V] [Fintype C]
    (I : PinningData (Option V) C) (x : ℂ) (r alpha : ℝ) : Prop :=
  ∀ a b : C, HasSmallResponseLog (pinningProductPartition (optionChildData I a))
    (pinningProductPartition (optionChildData I b)) x r alpha

universe u v
def SmallerPartitionsNonzero (C : Type v) [Fintype C] (Delta n : ℕ) (x : ℂ) (r : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (I : PinningData V C),
    I.DegreeBound Delta → Fintype.card V < n → PartitionNonzeroOn I x r

def SmallerRootResponses (C : Type v) [Fintype C] (Delta n : ℕ)
    (x : ℂ) (r alpha : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (I : PinningData (Option V) C),
    I.DegreeBound Delta → Fintype.card (Option V) < n → OptionRootResponses I x r alpha

theorem HasSmallResponseLog.mono_radius {f g : ℂ → ℂ} {x : ℂ} {r r' alpha : ℝ}
    (h : HasSmallResponseLog f g x r alpha) (hr : r' ≤ r) : HasSmallResponseLog f g x r' alpha := by
  obtain ⟨L, h0, hd, he, hb⟩ := h
  exact ⟨L, h0, hd.mono (Metric.ball_subset_ball hr),
    fun z hz => he z (Metric.ball_subset_ball hr hz),
    fun z hz => hb z (Metric.ball_subset_ball hr hz)⟩

theorem HasSmallResponseLog.mono_bound {f g : ℂ → ℂ} {x : ℂ} {r alpha beta : ℝ}
    (h : HasSmallResponseLog f g x r alpha) (hab : alpha ≤ beta) :
    HasSmallResponseLog f g x r beta := by
  obtain ⟨L, h0, hd, he, hb⟩ := h
  exact ⟨L, h0, hd, he, fun z hz => (hb z hz).trans hab⟩

end
end CI2ZF.Potts
