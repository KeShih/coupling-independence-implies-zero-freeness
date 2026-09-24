import CI2ZF.Potts.Regions.Arithmetic
import CI2ZF.Potts.Regions.CV.ZeroFree
import CI2ZF.Potts.Theorems.PottsExternalTheorem

/-! The complete near-Vigoda integer reduction, followed by the actual
proved strict/CV theorems and the explicitly cited critical hard input. -/
namespace CI2ZF.Appendix
open PottsCI CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable (C : Type v) [Fintype C] [Nonempty C]

/-- Both coupling inputs of regime (i): a hard-endpoint constant and a
constant on every `[δ,1]`. The only retained literature input is the
critical hard-colouring theorem at the twenty exceptional integer points. -/
theorem near_vigoda_transfer_inputs {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C)
    (critical : ∀ j : ℕ, 1 ≤ j → j ≤ 20 → Δ = 6 * j → Fintype.card C = 11 * j →
      ExternalCriticalHardColouringTheorem.{u,v} C Δ) :
    ∃ hcolours : Δ + 1 ≤ Fintype.card C, TransferCouplingInputs.{u,v} C Δ hcolours := by
  have hcolours : Δ + 1 ≤ Fintype.card C := colours_succ_of_nearVigoda hΔ hq
  refine ⟨hcolours, ?_⟩
  rcases nearVigoda_regime_cases hΔ hq with ⟨hd, hc⟩ | hs | ⟨j, hj, hj20, hd, hc⟩
  · exact CV.transfer_inputs C hd hc hcolours
  · exact strict_transfer_coupling_inputs C hΔ hs hcolours
  · have he : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ := by
      rw [hd, hc]
      push_cast
      ring
    exact critical_transfer_coupling_inputs C hΔ he hcolours
      ((critical j hj hj20 hd hc).to_normalizedInput (by omega) hcolours)

/-- Away from the twenty critical pairs, one constant works for every
activity in `[0,1]`, with no literature input. -/
theorem near_vigoda_noncritical_uniform_ci {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C)
    (hnc : ¬ ∃ j : ℕ, 1 ≤ j ∧ j ≤ 20 ∧ Δ = 6 * j ∧ Fintype.card C = 11 * j) :
    ∃ hcolours : Δ + 1 ≤ Fintype.card C, ∃ cost : ℝ,
      ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ≤ 1 →
        RootCouplingBound.{u,v} C Δ hcolours x cost := by
  have hcolours : Δ + 1 ≤ Fintype.card C := colours_succ_of_nearVigoda hΔ hq
  refine ⟨hcolours, ?_⟩
  rcases nearVigoda_regime_cases hΔ hq with ⟨hd, hc⟩ | hs | hcrit
  · exact ⟨_, fun x hx => CV.root_coupling C hd hc hcolours x hx⟩
  · refine ⟨2 / ciGap (Fintype.card C) Δ, fun x hx => ?_⟩
    intro O _ I hdI a b
    exact option_root_strict_uniform_ci I hΔ hdI hs a b x hx
  · exact absurd hcrit hnc

/-- The only retained literature input is CFFGZZ Theorem 20 at one of
the twenty exceptional integer points. It is stated on actual original
graph/pinning Gibbs laws, and converted by the proved main-text interface. -/
theorem near_vigoda_zero_free {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C)
    (critical : ∀ j : ℕ, 1 ≤ j → j ≤ 20 → Δ = 6 * j → Fintype.card C = 11 * j →
      ExternalCriticalHardColouringTheorem.{u,v} C Δ) :
    ∃ eps > 0, UniformPottsZeroFree.{u,v} C Δ eps := by
  rcases nearVigoda_regime_cases hΔ hq with ⟨hd, hc⟩ | hs | ⟨j, hj, hj20, hd, hc⟩
  · exact CV.zero_free C hd hc
  · exact strict_potts_zero_free C hΔ hs
  · have he : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ := by
      rw [hd, hc]
      push_cast
      ring
    exact critical_potts_zero_free_from_external C hΔ he (critical j hj hj20 hd hc)

end
end CI2ZF.Appendix
