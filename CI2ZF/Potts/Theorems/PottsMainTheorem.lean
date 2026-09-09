import CI2ZF.Potts.Transfer.PositiveUniformTransfer
import CI2ZF.Potts.Transfer.HardUniformTransfer
import CI2ZF.Potts.Transfer.UniformZeroFreePackaging

/-! The main-text Potts conclusion on all bounded-degree graphs. The
strict-line theorem has no external coupling hypothesis. At equality,
the hard colouring theorem is an explicit, documented external input. -/
namespace CI2ZF.Potts
open PottsCI Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

/-- The original graph/pinning conclusion, including exact forced
zeros of the unnormalized polynomial. -/
def UniformPottsZeroFree (C : Type v) [Fintype C] (Δ : ℕ) (eps : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C,
    (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
    (∀ z ∈ thickening eps pottsInterval,
      fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
    (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G

/-- The two actual real CI inputs imply graph-independent complex
zero-freeness. No complex induction premise remains in the statement. -/
theorem bounded_degree_potts_transfer (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C)
    (hCI : TransferCouplingInputs.{u, v} C Δ hq) :
    ∃ eps > 0, UniformPottsZeroFree.{u, v} C Δ eps := by
  apply uniform_original_potts_zero_free_of_endpoint_and_positive.{u, v} C Δ
  · obtain ⟨cost, hc⟩ := hCI.hard
    obtain ⟨r, hr, _, _, hn, _⟩ := hard_uniform_transfer.{u, v} C Δ hq cost hc
    exact ⟨r, hr, hn⟩
  · intro δ hδ hδ1
    obtain ⟨cost, hc⟩ := hCI.positive δ hδ hδ1
    exact positive_interval_uniform_transfer.{u, v} C Δ hq hδ cost hc

/-- Full strict-line theorem: actual coupling independence and both
complex induction branches have been proved in Lean. -/
theorem strict_potts_zero_free (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (11 / 6 : ℝ) * Δ < Fintype.card C) :
    ∃ eps > 0, UniformPottsZeroFree.{u, v} C Δ eps := by
  have hcolours : Δ + 1 ≤ Fintype.card C := by
    have h := colours_slack_of_vigoda_line hΔ hq.le
    omega
  exact bounded_degree_potts_transfer C Δ hcolours
    (strict_transfer_coupling_inputs C hΔ hq hcolours)

/-- Critical equality theorem. `hardInput` is the only external result:
the hard-colouring CI consequence of CFFGZZ Theorem 20. In particular,
neither positive-temperature CI nor the CI-to-zero-free transfer is
assumed here. -/
theorem critical_potts_zero_free (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C)
    (hardInput : CriticalHardColouringInput.{u, v} C Δ hcolours) :
    ∃ eps > 0, UniformPottsZeroFree.{u, v} C Δ eps :=
  bounded_degree_potts_transfer C Δ hcolours
    (critical_transfer_coupling_inputs C hΔ hq hcolours hardInput)

/-- The headline weak inequality, with the external hypothesis needed
only in its equality case. -/
theorem potts_zero_free (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (11 / 6 : ℝ) * Δ ≤ Fintype.card C)
    (hcolours : Δ + 1 ≤ Fintype.card C)
    (hardInput : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ →
      CriticalHardColouringInput.{u, v} C Δ hcolours) :
    ∃ eps > 0, UniformPottsZeroFree.{u, v} C Δ eps := by
  rcases lt_or_eq_of_le hq with hstrict | hcritical
  · exact strict_potts_zero_free C hΔ hstrict
  · exact critical_potts_zero_free C hΔ hcritical.symm hcolours (hardInput hcritical.symm)

end
end CI2ZF.Potts
