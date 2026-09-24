import CI2ZF.Potts.Theorems.PottsMainTheorem
import CI2ZF.Potts.Geometry.BoundedGraphClass
import CI2ZF.Potts.Geometry.GraphClassCoupling
import CI2ZF.Potts.Geometry.PinningLeafRealization
import CI2ZF.Coupling.Vigoda.CriticalLineArithmetic
import CI2ZF.Coupling.CV.RootCI

/-! The headline theorem. Its equality case `q = 11Δ/6` needs a hard
coupling bound at activity zero. The paper cites CFFGZZ Theorem 20 for it;
here it is proved by the Carlson–Vigoda contraction, which extends to the
critical line for every `Δ ≥ 6`. The cited route, with the input stated on
original graphs and converted by a proved leaf realization, is kept for
comparison, and `external_critical_hard_colouring_theorem` proves its
premise too. -/
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

/-- The hard-colouring coupling bound on the critical line, proved by the
Carlson–Vigoda contraction, which holds for `q ≥ 11Δ/6` once `Δ ≥ 6`.
It replaces the cited CFFGZZ Theorem 20. -/
theorem critical_hard_colouring_input (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 6 ≤ Δ) (hq : (11 / 6 : ℝ) * Δ ≤ Fintype.card C)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    CriticalHardColouringInput.{u, v} C Δ hcolours := by
  refine ⟨Appendix.CV.ciConstant, ?_⟩
  intro O _ I hd a b
  exact Appendix.CV.option_root_ci_critical I hΔ hd hq a b PinningData.hardParameter (by norm_num)

/-- On the critical line both coupling inputs of the transfer theorem hold:
the hard bound by `critical_hard_colouring_input`, and the constant
`12/(11δ)` on `[δ,1]`. -/
theorem critical_line_transfer_coupling_inputs (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (Fintype.card C : ℝ) = (11 / 6 : ℝ) * Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    TransferCouplingInputs.{u, v} C Δ hcolours :=
  critical_transfer_coupling_inputs C hΔ hq hcolours
    (critical_hard_colouring_input C (critical_line_degree_ge_six hΔ hq) hq.ge hcolours)

/-- The complete main-text Potts theorem for `q ≥ 11Δ/6`, with no
literature hypothesis. -/
theorem potts_zero_free_of_vigoda_line (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : (11 / 6 : ℝ) * Δ ≤ Fintype.card C) :
    ∃ eps > 0, UniformPottsZeroFree.{u, v} C Δ eps := by
  rcases lt_or_eq_of_le hq with hs | he
  · exact strict_potts_zero_free C hΔ hs
  · have hcolours : Δ + 1 ≤ Fintype.card C := by
      have h := colours_slack_of_vigoda_line hΔ he.le
      omega
    exact critical_potts_zero_free C hΔ he.symm hcolours
      (critical_hard_colouring_input C (critical_line_degree_ge_six hΔ he.symm) hq hcolours)

/-- Paper-facing statement of Theorem 1.1 with the integer parameters and
colour set `Fin q`. There is no literature hypothesis: the equality case
uses the Carlson–Vigoda contraction on the critical line. -/
theorem potts_main_theorem (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : 11 * Δ ≤ 6 * q) :
    ∃ eps > 0, UniformPottsZeroFree.{u, 0} (Fin q) Δ eps := by
  let : NeZero q := ⟨by omega⟩
  have hqr : (11 / 6 : ℝ) * Δ ≤ Fintype.card (Fin q) := by
    simp only [Fintype.card_fin]
    have h : (11 : ℝ) * Δ ≤ 6 * q := by exact_mod_cast hq
    linarith
  exact potts_zero_free_of_vigoda_line (Fin q) hΔ hqr

theorem potts_main_strict (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : 11 * Δ < 6 * q) :
    ∃ eps > 0, UniformPottsZeroFree.{u, 0} (Fin q) Δ eps := by
  let : NeZero q := ⟨by omega⟩
  apply strict_potts_zero_free (Fin q) hΔ
  simp only [Fintype.card_fin]
  have h : (11 : ℝ) * Δ < 6 * q := by exact_mod_cast hq
  linarith

section Cited
local instance (priority := 3000) externalCriticalDecEq (T : Type*) : DecidableEq T :=
  Classical.decEq T

/-- The cited premise itself, the original-graph form of CFFGZZ Theorem 20
used at `q = 11Δ/6`, holds for every `Δ ≥ 6` and `q ≥ 11Δ/6` by the
Carlson–Vigoda contraction on the critical line. So the cited route
above is also closed. -/
theorem external_critical_hard_colouring_theorem (C : Type v) [Fintype C] [Nonempty C]
    {Δ : ℕ} (hΔ : 6 ≤ Δ) (hq : (11 / 6 : ℝ) * Δ ≤ Fintype.card C) :
    ExternalCriticalHardColouringTheorem.{u, v} C Δ := by
  refine ⟨Appendix.CV.ciConstant, ?_⟩
  intro A _ G hG tau r a b ha hb
  let I := rootOptionData (tau.toPinningData G) r
  have hd : I.DegreeBound Δ :=
    rootOptionData_degreeBound _ r (tau.degreeBound_of_original G hG)
  exact root_W_le_of_option_relabel tau G (rootOptionEquiv r).symm I rfl
    PinningData.hardParameter rfl a b ha hb fun _ _ =>
      Appendix.CV.option_root_ci_critical I hΔ hd hq a b PinningData.hardParameter (by norm_num)

end Cited

end
end CI2ZF.Potts
