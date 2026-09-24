import CI2ZF.Potts.Regions.Arithmetic
import CI2ZF.Potts.Regions.CV.ZeroFree
import CI2ZF.Potts.Theorems.PottsExternalTheorem

/-! The complete near-Vigoda integer reduction to the proved strict-Vigoda
and Carlson–Vigoda theorems. The twenty critical pairs `(6j, 11j)` below
degree 125 use the Carlson–Vigoda contraction on the critical line, so no
literature input remains. -/
namespace CI2ZF.Appendix
open PottsCI CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable (C : Type v) [Fintype C] [Nonempty C]

/-- One coupling constant works for every activity in `[0,1]`. -/
theorem near_vigoda_uniform_ci {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C) :
    ∃ hcolours : Δ + 1 ≤ Fintype.card C, ∃ cost : ℝ,
      ∀ x : PinningData.NonnegativeParameter, (x : ℝ) ≤ 1 →
        RootCouplingBound.{u,v} C Δ hcolours x cost := by
  have hcolours : Δ + 1 ≤ Fintype.card C := colours_succ_of_nearVigoda hΔ hq
  refine ⟨hcolours, ?_⟩
  rcases nearVigoda_regime_cases hΔ hq with ⟨hd, hc⟩ | hs | ⟨j, hj, _, hd, hc⟩
  · exact ⟨_, fun x hx => CV.root_coupling C hd hc hcolours x hx⟩
  · refine ⟨2 / ciGap (Fintype.card C) Δ, fun x hx => ?_⟩
    intro O _ I hdI a b
    exact option_root_strict_uniform_ci I hΔ hdI hs a b x hx
  · have h6 : 6 ≤ Δ := by omega
    have hcrit : (11 / 6 : ℝ) * Δ ≤ Fintype.card C := by
      rw [hd, hc]
      push_cast
      linarith
    refine ⟨CV.ciConstant, fun x hx => ?_⟩
    intro O _ I hdI a b
    exact CV.option_root_ci_critical I h6 hdI hcrit a b x hx

/-- Both coupling inputs of regime (i): a hard-endpoint constant and a
constant on every `[δ,1]`. -/
theorem near_vigoda_transfer_inputs {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C) :
    ∃ hcolours : Δ + 1 ≤ Fintype.card C, TransferCouplingInputs.{u,v} C Δ hcolours := by
  obtain ⟨hcolours, cost, h⟩ := near_vigoda_uniform_ci C hΔ hq
  exact ⟨hcolours, ⟨cost, h PinningData.hardParameter (by norm_num)⟩,
    fun _ _ _ => ⟨cost, fun x hx => h x hx.2⟩⟩

/-- Regime (i): one radius works for every graph size and arbitrary
pinning on the entire physical interval. No literature input remains. -/
theorem near_vigoda_zero_free {Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : ((11 / 6 : ℝ) - 1 / 84000) * Δ ≤ Fintype.card C) :
    ∃ eps > 0, UniformPottsZeroFree.{u,v} C Δ eps := by
  obtain ⟨hcolours, hCI⟩ := near_vigoda_transfer_inputs C hΔ hq
  exact bounded_degree_potts_transfer C Δ hcolours hCI

end
end CI2ZF.Appendix
