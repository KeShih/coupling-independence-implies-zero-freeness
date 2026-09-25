import ZeroFreeness.Coupling.CV.RootCI
import ZeroFreeness.Potts.Theorems.PottsMainTheorem

/-! The full Carlson–Vigoda appendix region, with every real coupling
input and the uniform complex transfer discharged inside Lean. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI ZeroFreeness.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable (C : Type v) [Fintype C] [Nonempty C]

theorem root_coupling {Δ : ℕ} (hΔ : 125 ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (hcolours : Δ + 1 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    RootCouplingBound.{u,v} C Δ hcolours x ciConstant := by
  intro O _ I hd a b
  exact option_root_ci I hΔ hd hq a b x hx1

theorem transfer_inputs {Δ : ℕ} (hΔ : 125 ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    TransferCouplingInputs.{u,v} C Δ hcolours := by
  constructor
  · exact ⟨ciConstant, root_coupling C hΔ hq hcolours PinningData.hardParameter (by norm_num)⟩
  · intro δ _ _
    exact ⟨ciConstant, fun x hx => root_coupling C hΔ hq hcolours x hx.2⟩

/-- The same root coupling bound in either CV regime, including the
critical line `q ≥ 11Δ/6` for every `Δ ≥ 6`. -/
theorem root_coupling_of_regime {Δ : ℕ} (hreg : Regime Δ (Fintype.card C))
    (hcolours : Δ + 1 ≤ Fintype.card C)
    (x : PinningData.NonnegativeParameter) (hx1 : (x : ℝ) ≤ 1) :
    RootCouplingBound.{u,v} C Δ hcolours x ciConstant := by
  intro O _ I hd a b
  exact option_root_ci_of_regime I hreg hd a b x hx1

theorem transfer_inputs_of_regime {Δ : ℕ} (hreg : Regime Δ (Fintype.card C))
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    TransferCouplingInputs.{u,v} C Δ hcolours := by
  constructor
  · exact ⟨ciConstant, root_coupling_of_regime C hreg hcolours PinningData.hardParameter (by norm_num)⟩
  · intro δ _ _
    exact ⟨ciConstant, fun x hx => root_coupling_of_regime C hreg hcolours x hx.2⟩

/-- Regime (ii): one radius works for every graph size and arbitrary
pinning on the entire physical interval. No literature input remains. -/
theorem zero_free {Δ : ℕ} (hΔ : 125 ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) :
    ∃ eps > 0, UniformPottsZeroFree.{u,v} C Δ eps := by
  have hcolours : Δ + 1 ≤ Fintype.card C := (Nat.le_succ _).trans (colours_slack hΔ hq)
  exact bounded_degree_potts_transfer C Δ hcolours (transfer_inputs C hΔ hq hcolours)

end
end ZeroFreeness.Appendix.CV
