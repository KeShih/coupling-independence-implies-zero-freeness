import CI2ZF.Potts.Transfer.FamilyCouplingInputs
import CI2ZF.Potts.Regions.CV.ZeroFree
import CI2ZF.Potts.Regions.Arithmetic
import CI2ZF.Potts.Theorems.PottsExternalTheorem
import CI2ZF.Potts.Regions.NearVigoda.Theorem

/-! The hard coupling bounds used by the two unrestricted vertex-field
regions. Both are proved internally: the near-Vigoda reduction ends in the
strict-Vigoda or the Carlson--Vigoda theorem, the latter also on the
critical line. -/

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
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    ∃ cost : ℝ, RootCouplingBound.{u,v} C Δ hcolours PinningData.hardParameter cost := by
  obtain ⟨_, hCI⟩ := near_vigoda_transfer_inputs.{u,v} C hΔ hq
  exact hCI.hard

end
end CI2ZF.LeeYang
