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
