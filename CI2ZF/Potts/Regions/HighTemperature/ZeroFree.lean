import CI2ZF.Coupling.HighTemperature.Coupling
import CI2ZF.Potts.Theorems.PositiveGraphClassTransfer
import CI2ZF.Potts.Geometry.BoundedGraphClass
import CI2ZF.Potts.Transfer.PottsAnalytic

/-! The high-temperature appendix corollary, with no hard-colouring
feasibility assumption. Both coupling and analytic transfer are proved. -/
namespace CI2ZF.Appendix
open PottsCI PottsCI.FinDist CI2ZF.Potts Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) highTemperatureDecEq (A : Type*) : DecidableEq A := Classical.decEq _
universe u v
variable (C : Type v) [Fintype C] [Nonempty C]

/-- The graph-uniform CI input on the complete positive interval. -/
theorem high_temperature_graph_coupling (Δ : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hq : (11 / 6 : ℝ) * (1 - x₀) * Δ < Fintype.card C)
    (x : ℝ) (hx : x ∈ Icc x₀ 1) :
    GraphClassRootCouplingBound (GraphClass.boundedDegree.{u} Δ) C ⟨x, (hx₀.trans_le hx.1).le⟩
      (2 * (1 - x₀) * Δ / ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x₀) * Δ)) := by
  intro V _ G hd tau r a b ha hb
  exact root_high_temperature_uniform_ci tau G r a b hd hx₀ hx hq

/-- A single neighbourhood of `[x₀,1]` works for every graph size and
arbitrary pinning, whenever `q > 11(1-x₀)Δ/6`. -/
theorem high_temperature_zero_free (Δ : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hq : (11 / 6 : ℝ) * (1 - x₀) * Δ < Fintype.card C) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ tau : PartialColouring V C,
      ∀ z ∈ thickening eps (Complex.ofReal '' Icc x₀ 1),
        normalizedPartition tau G z ≠ 0 ∧ fullPartition tau G z ≠ 0 := by
  obtain ⟨r, hr, _, _, h⟩ := (GraphClass.boundedDegree.{u} Δ).positive_interval_zero_free_and_responses
    (C := C) Δ hx₀
    (2 * (1 - x₀) * Δ / ((Fintype.card C : ℝ) - (11 / 6 : ℝ) * (1 - x₀) * Δ))
    (fun x _ hx => high_temperature_graph_coupling C Δ hx₀ hq x hx)
  refine ⟨min r (x₀ / 2), lt_min hr (by linarith), ?_⟩
  intro V _ G hd tau z hz
  obtain ⟨w, ⟨x, hx, rfl⟩, hdist⟩ := mem_thickening_iff.mp hz
  have hn := (h G hd hd tau).1 x hx z
    (hdist.trans_le (min_le_left r (x₀ / 2)))
  have hzero : z ≠ 0 := by
    intro hz0
    subst z
    have hxpos : 0 < x := hx₀.trans_le hx.1
    have he : dist (0 : ℂ) (x : ℂ) = x := by
      simp only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    rw [he] at hdist
    have hh := hdist.trans_le (min_le_right r (x₀ / 2))
    linarith [hx.1]
  exact ⟨hn, fullPartition_ne_zero_of_normalized tau G hzero hn⟩

end
end CI2ZF.Appendix
