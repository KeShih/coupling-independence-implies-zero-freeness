import CI2ZF.PottsMainTheorem
import CI2ZF.BoundedGraphClass
import CI2ZF.GraphClassCoupling
import CI2ZF.PinningLeafRealization
import CI2ZF.CriticalLineArithmetic

/-! The headline theorem with its sole external input stated on actual
original bounded-degree graphs. The conversion to boundary-count data
is a proved leaf realization and exact Gibbs-law transport. -/
namespace CI2ZF.Potts
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem ExternalCriticalHardColouringTheorem.to_normalizedInput
    {C : Type v} [Fintype C] [Nonempty C] {Δ : ℕ} (hΔ : 1 ≤ Δ)
    (hq : Δ + 1 ≤ Fintype.card C)
    (hExternal : ExternalCriticalHardColouringTheorem.{u, v} C Δ) :
    CriticalHardColouringInput.{u, v} C Δ hq := by
  obtain ⟨cost, hc⟩ := hExternal
  refine ⟨cost, ?_⟩
  intro O _ I hd a b
  have hI : ((GraphClass.boundedDegree.{u} Δ).pinningFamily C).contains I :=
    ⟨PinningLeaves.Vertex I, inferInstance, PinningLeaves.graph I,
      PinningLeaves.degree_le I hd hΔ, ⟨PinningLeaves.realization I⟩⟩
  exact hc.to_pinningFamily hq I hI hd a b

theorem critical_potts_zero_free_from_external (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hExternal : ExternalCriticalHardColouringTheorem.{u, v} C Δ) :
    ∃ eps > 0, UniformPottsZeroFree.{u, v} C Δ eps := by
  have hcolours : Δ + 1 ≤ Fintype.card C := by
    have h := colours_slack_of_vigoda_line hΔ hq.ge
    omega
  exact critical_potts_zero_free C hΔ hq hcolours
    (hExternal.to_normalizedInput (by omega) hcolours)

/-- Original-graph form of the complete main-text Potts theorem.
External hard CI is requested only in the equality branch. -/
theorem potts_zero_free_from_external (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (11 / 6 : ℝ) * Δ ≤ Fintype.card C)
    (hExternal : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ →
      ExternalCriticalHardColouringTheorem.{u, v} C Δ) :
    ∃ eps > 0, UniformPottsZeroFree.{u, v} C Δ eps := by
  rcases lt_or_eq_of_le hq with hs | he
  · exact strict_potts_zero_free C hΔ hs
  · exact critical_potts_zero_free_from_external C hΔ he.symm (hExternal he.symm)

/-- Paper-facing statement with the integer parameters and colour set
`Fin q`. Colour nonemptiness and the weaker feasibility threshold are
derived rather than added as hypotheses. -/
theorem potts_main_theorem (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : 11 * Δ ≤ 6 * q)
    (hExternal : 6 * q = 11 * Δ →
      ExternalCriticalHardColouringTheorem.{u, 0} (Fin q) Δ) :
    ∃ eps > 0, UniformPottsZeroFree.{u, 0} (Fin q) Δ eps := by
  let : NeZero q := ⟨by omega⟩
  have hqr : (11 / 6 : ℝ) * Δ ≤ Fintype.card (Fin q) := by
    simp only [Fintype.card_fin]
    have h : (11 : ℝ) * Δ ≤ 6 * q := by exact_mod_cast hq
    linarith
  apply potts_zero_free_from_external (Fin q) hΔ hqr
  intro heq
  apply hExternal
  have h : (6 : ℝ) * q = 11 * Δ := by
    simpa only [Fintype.card_fin] using (show
      (6 : ℝ) * Fintype.card (Fin q) = 11 * Δ by linarith)
  exact_mod_cast h

theorem potts_main_strict (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : 11 * Δ < 6 * q) :
    ∃ eps > 0, UniformPottsZeroFree.{u, 0} (Fin q) Δ eps := by
  let : NeZero q := ⟨by omega⟩
  apply strict_potts_zero_free (Fin q) hΔ
  simp only [Fintype.card_fin]
  have h : (11 : ℝ) * Δ < 6 * q := by exact_mod_cast hq
  linarith

end
end CI2ZF.Potts
