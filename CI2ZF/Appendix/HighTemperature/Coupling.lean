import CI2ZF.PottsCITheorem

/-!
# General-graph high-temperature coupling independence

The coupling input of `cor:intro-high-temperature`, for arbitrary colour
counts. Positive activity makes every normalized pinned law well-defined;
no hard-colouring feasibility or lower bound `q ≥ Δ + 2` is imposed.
-/
namespace CI2ZF
open PottsCI PottsCI.FinDist
noncomputable section

theorem ciDenominator_mono {q Δ x y : ℝ} (hΔ : 0 ≤ Δ) (hxy : x ≤ y) :
    ciDenominator q Δ x ≤ ciDenominator q Δ y := by
  unfold ciDenominator
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hΔ]

theorem ciBound_antitone {q Δ x y : ℝ} (hΔ : 0 ≤ Δ) (hxy : x ≤ y)
    (hy : y ≤ 1) (hden : 0 < ciDenominator q Δ x) :
    ciBound q Δ y ≤ ciBound q Δ x := by
  have hd := ciDenominator_mono (q := q) hΔ hxy
  have hn : 2 * (1 - y) * Δ ≤ 2 * (1 - x) * Δ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) hΔ]
  exact (div_le_div_of_nonneg_right hn (hden.trans_le hd).le).trans
    (div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hxy.trans hy))) hΔ)
      hden hd)

namespace Potts
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (A : Type*) : DecidableEq A := Classical.decEq A
set_option maxHeartbeats 800000
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]

/-- Actual normalized root-child law at a positive activity. -/
def positiveRootChildGibbs (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a : C) (x : ℝ) (hx : 0 < x) :
    FinDist (RootRemaining tau r → C) :=
  (rootChildData tau G r a).gibbs x hx.le
    ((rootChildData tau G r a).partition_pos_of_parameter_pos hx)

/-- The positive-activity root bound, proved from the actual common-coin
Vigoda coupling even when `q` is smaller than the degree bound. -/
theorem root_positive_ci (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a b : C) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hq : (11 / 6 : ℝ) * (1 - x) * Δ < Fintype.card C) :
    W ham (positiveRootChildGibbs tau G r a x hx)
      (positiveRootChildGibbs tau G r b x hx) ≤ ciBound (Fintype.card C) Δ x := by
  have hden : 0 < ciDenominator (Fintype.card C) Δ x := by
    unfold ciDenominator
    linarith
  cases isEmpty_or_nonempty (RootRemaining tau r) with
  | inl he =>
    let := he
    have hz := W_ham_eq_zero_of_isEmpty
      (positiveRootChildGibbs tau G r a x hx) (positiveRootChildGibbs tau G r b x hx)
    have hb := (le_of_eq hz).trans (ciBound_nonneg (Nat.cast_nonneg Δ) hx1 hden)
    exact hb
  | inr hn =>
    let := hn
    have hb := gibbs_ci_of_softVigoda_inputs_le_one
      (rootChildData tau G r a) (rootChildData tau G r b) (rootMiddleData tau G r)
      Δ x hx hx1 hden (fun hlt => root_soft_inputs_of_conditional_hard tau G r a b hdegree
        (conditionalHardCouplingEstimate _) (conditionalHardCouplingEstimate _) x hx hlt)
    convert hb using 1
    congr 2

/-- One graph-independent CI constant throughout `[x₀,1]`, exactly the
constant used in `cor:intro-high-temperature`. This is a coupling theorem;
the uniform analytic transfer is a separate proof obligation. -/
theorem root_high_temperature_uniform_ci
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex) (a b : C)
    {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : x ∈ Set.Icc x₀ 1)
    (hq : (11 / 6 : ℝ) * (1 - x₀) * Δ < Fintype.card C) :
    W ham (positiveRootChildGibbs tau G r a x (hx₀.trans_le hx.1))
      (positiveRootChildGibbs tau G r b x (hx₀.trans_le hx.1)) ≤
      2 * (1 - x₀) * Δ / ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x₀) * Δ) := by
  have hd₀ : 0 < ciDenominator (Fintype.card C) Δ x₀ := by
    unfold ciDenominator
    linarith
  have hd := hd₀.trans_le (ciDenominator_mono (Nat.cast_nonneg _) hx.1)
  have hqx : (11 / 6 : ℝ) * (1 - x) * Δ < Fintype.card C := by
    unfold ciDenominator at hd
    linarith
  exact (root_positive_ci tau G r a b hdegree (hx₀.trans_le hx.1) hx.2 hqx).trans
    (ciBound_antitone (Nat.cast_nonneg _) hx.1 hx.2 hd₀)

end Potts
end
end CI2ZF
