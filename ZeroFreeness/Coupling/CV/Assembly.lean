import ZeroFreeness.Coupling.CV.GeometricDrift
import ZeroFreeness.Coupling.CV.GlobalEnvelope
import ZeroFreeness.Coupling.CV.ExpectedLoss

/-!
# Lemma `lem:cv-assembly` (companion appendix CV, Lemma 5.23), eq. `cv-envelope`

`𝒟 = E[d_x(X₁,Y₁)] - d_x(X,Y)` is the expected one-step drift of the
geometric metric `geometricMetric I x` under the actual averaged coupling
(`averagedCost … optimizedAdjacentChoices`).  With `q = |C|`, `n = |V|`,
`θ = 1 - x`, `L_x = lowAvailabilityMass I X Y v x` (the paper's `L_x`, see
`lowAvailabilityMass_eq_paper` in `ZeroFreeness.Coupling.CV.ExpectedLoss`),
`Λ_bulk = bulk = 1331/750`, and
`Λ_low = low γ_gain γ_loss = max {2 - P₂ + γ_loss, 2 - P₃ - γ_gain, 226/125}`
evaluated at the actual coefficients of `eq:cv-gammas`
(`γ_gain = gammaGain (q/Δ) Δ`, `γ_loss = gammaLoss (q/Δ) Δ θ (L_x/Δ)`):

  `nq 𝒟 ≤ -q + θ Λ_low L_x + Λ_bulk (Δ - L_x)`.

`cv_assembly_1809` is the statement on the paper's domain `Δ ≥ 125`,
`q ≥ 1.809 Δ`; `cv_assembly` holds on the library's two-branch `Regime`.
-/

namespace ZeroFreeness.Appendix.CV

open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]

/-- `Λ_low` is the maximum of the three rates of `eq:cv-lambda-rates`. -/
lemma low_eq_rates (gain loss : ℝ) :
    low gain loss = max (2 - 81 / 250 + loss) (max (2 - 77 / 500 - gain) (226 / 125)) := rfl

/-- eq. `cv-envelope`, on the library's `Regime` (which contains the paper's
domain `Δ ≥ 125`, `q ≥ 1.809Δ`). -/
theorem cv_assembly
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ}
    (hreg : Regime Δ (Fintype.card C)) (hdegree : I.DegreeBound Δ) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
        (averagedCost I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree)
          x hx (geometricMetric I x) - geometricMetric I x X Y) ≤
      -(Fintype.card C : ℝ) +
        (1 - x) * low (gammaGain ((Fintype.card C : ℝ) / Δ) Δ)
            (gammaLoss ((Fintype.card C : ℝ) / Δ) Δ (1 - x) (lowAvailabilityMass I X Y v x / Δ)) *
          lowAvailabilityMass I X Y v x +
        bulk * ((Δ : ℝ) - lowAvailabilityMass I X Y v x) := by
  have hd : (0 : ℝ) < Δ := by exact_mod_cast hreg.degree_pos
  have hθ : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hφ : lowAvailabilityMass I X Y v x / Δ ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (lowAvailabilityMass_nonneg I X Y v hx.1) hd.le
    · apply (div_le_one hd).mpr
      exact (lowAvailabilityMass_le_degree I X Y v hx).trans
        (by exact_mod_cast ((Nat.le_add_right _ _).trans (hdegree v) : I.graph.degree v ≤ Δ))
  obtain ⟨hg, hl0, hl⟩ := hreg.coefficients hθ hφ
  have hactual := averaged_geometric_drift_corrected_le I X Y v hroot hagree x hx
    hreg.degree_pos hdegree hreg.colours (by linarith) hl0 rfl rfl
  have henv := expected_correctedHardCharge_envelope I X Y v hroot hagree x hx hdegree hg hl
  exact hactual.trans henv

/-- eq. `cv-envelope` on the paper's domain. -/
theorem cv_assembly_1809
    (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ}
    (hΔ : 125 ≤ Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (hdegree : I.DegreeBound Δ) :
    ((Fintype.card V : ℝ) * Fintype.card C) *
        (averagedCost I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree)
          x hx (geometricMetric I x) - geometricMetric I x X Y) ≤
      -(Fintype.card C : ℝ) +
        (1 - x) * low (gammaGain ((Fintype.card C : ℝ) / Δ) Δ)
            (gammaLoss ((Fintype.card C : ℝ) / Δ) Δ (1 - x) (lowAvailabilityMass I X Y v x / Δ)) *
          lowAvailabilityMass I X Y v x +
        bulk * ((Δ : ℝ) - lowAvailabilityMass I X Y v x) :=
  cv_assembly I X Y v hroot hagree x hx (Or.inl ⟨hΔ, hq⟩) hdegree

end

end ZeroFreeness.Appendix.CV
