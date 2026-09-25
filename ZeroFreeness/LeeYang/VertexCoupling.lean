import ZeroFreeness.Potts.Transfer.FamilyCouplingInputs
import ZeroFreeness.Potts.Regions.CV.ZeroFree
import ZeroFreeness.Potts.Regions.Arithmetic
import ZeroFreeness.Potts.Theorems.PottsExternalTheorem
import ZeroFreeness.Potts.Regions.NearVigoda.Theorem

/-! The hard coupling bounds used by the two unrestricted vertex-field
regions. Both are proved internally: the near-Vigoda reduction ends in the
strict-Vigoda or the Carlson--Vigoda theorem, the latter also on the
critical line. -/

namespace ZeroFreeness.LeeYang
open PottsCI ZeroFreeness.Potts ZeroFreeness.Appendix
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
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    ∃ cost : ℝ, RootCouplingBound.{u,v} C Δ hcolours PinningData.hardParameter cost := by
  obtain ⟨_, hCI⟩ := near_vigoda_transfer_inputs.{u,v} C hΔ hq
  exact hCI.hard

end
end ZeroFreeness.LeeYang
