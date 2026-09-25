import ZeroFreeness.Coupling.Vigoda.OptionCI

/-! The main text's exact positive-activity CI estimate, including the
critical line and activity one. All concrete coupling inputs are discharged. -/
namespace ZeroFreeness.Potts
open PottsCI PottsCI.FinDist
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty C]
local instance (priority := 2000) positiveExactRemainingDecEq
    (tau : PartialColouring V C) (r : tau.FreeVertex) : DecidableEq (RootRemaining tau r) :=
  Classical.decEq _

theorem root_positive_exact_ci (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a b : C) {Δ : ℕ} (hd : ∀ v, G.degree v ≤ Δ)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hgap : 0 < ciDenominator (Fintype.card C) Δ x) :
    W ham
      ((rootChildData tau G r a).gibbs x hx.le
        ((rootChildData tau G r a).partition_pos_of_parameter_pos hx))
      ((rootChildData tau G r b).gibbs x hx.le
        ((rootChildData tau G r b).partition_pos_of_parameter_pos hx)) ≤
      ciBound (Fintype.card C) Δ x := by
  cases isEmpty_or_nonempty (RootRemaining tau r) with
  | inl h =>
    let := h
    have hz := W_ham_eq_zero_of_isEmpty
      ((rootChildData tau G r a).gibbs x hx.le
        ((rootChildData tau G r a).partition_pos_of_parameter_pos hx))
      ((rootChildData tau G r b).gibbs x hx.le
        ((rootChildData tau G r b).partition_pos_of_parameter_pos hx))
    exact hz.le.trans (ciBound_nonneg (Nat.cast_nonneg _) hx1 hgap)
  | inr h =>
    let := h
    apply gibbs_ci_of_softVigoda_inputs_le_one
      (rootChildData tau G r a) (rootChildData tau G r b) (rootMiddleData tau G r) Δ x hx hx1 hgap
    intro hlt
    exact root_soft_inputs_of_conditional_hard tau G r a b hd
      (conditionalHardCouplingEstimate _) (conditionalHardCouplingEstimate _) x hx hlt

theorem root_critical_exact_ci (tau : PartialColouring V C) (G : SimpleGraph V)
    (r : tau.FreeVertex) (a b : C) {Δ : ℕ} (hΔ : 0 < Δ) (hd : ∀ v, G.degree v ≤ Δ)
    (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    W ham
      ((rootChildData tau G r a).gibbs x hx.le
        ((rootChildData tau G r a).partition_pos_of_parameter_pos hx))
      ((rootChildData tau G r b).gibbs x hx.le
        ((rootChildData tau G r b).partition_pos_of_parameter_pos hx)) ≤
      12 * (1 - x) / (11 * x) := by
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  simpa only [ciBound_critical_eq hΔ' hx hq] using
    root_positive_exact_ci tau G r a b hd hx hx1 (ciDenominator_pos_of_critical hΔ' hx hq)

end
end ZeroFreeness.Potts
