import CI2ZF.Potts.Transfer.FamilyCouplingInputs
import CI2ZF.Potts.Regions.CV.ZeroFree
import CI2ZF.Potts.Regions.Arithmetic
import CI2ZF.Potts.Theorems.PottsExternalTheorem

/-! The hard coupling bounds used by the two unrestricted vertex-field
regions. The near-Vigoda reduction retains only the twenty stated critical
hard-colouring inputs; the Carlson--Vigoda route is proved internally. -/

namespace CI2ZF.LeeYang
open PottsCI CI2ZF.Potts CI2ZF.Appendix
noncomputable section
universe u v
variable (C : Type v) [Fintype C] [Nonempty C]

def allPinningFamily : PinningFamily.{u,v} C where
  contains := fun _ => True
  restrict_mem := by intros; trivial

theorem cv_hard_coupling {Δ : ℕ} (hΔ : 125 ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    ∃ cost : ℝ, RootCouplingBound.{u,v} C Δ hcolours PinningData.hardParameter cost :=
  (CV.transfer_inputs C hΔ hq hcolours).hard

theorem near_vigoda_hard_coupling {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C)
    (hcolours : Δ + 1 ≤ Fintype.card C)
    (critical : ∀ j : ℕ, 1 ≤ j → j ≤ 20 → Δ = 6 * j → Fintype.card C = 11 * j →
      ExternalCriticalHardColouringTheorem.{u,v} C Δ) :
    ∃ cost : ℝ, RootCouplingBound.{u,v} C Δ hcolours PinningData.hardParameter cost := by
  rcases nearVigoda_regime_cases hΔ hq with ⟨hd, hc⟩ | hs | ⟨j, hj, hj20, hd, hc⟩
  · exact cv_hard_coupling C hd hc hcolours
  · exact (strict_transfer_coupling_inputs C hΔ hs hcolours).hard
  · exact (critical j hj hj20 hd hc).to_normalizedInput (by omega) hcolours

end
end CI2ZF.LeeYang
