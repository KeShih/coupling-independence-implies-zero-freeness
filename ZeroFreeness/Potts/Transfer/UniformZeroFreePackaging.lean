import ZeroFreeness.Potts.Transfer.InductionState
import ZeroFreeness.Potts.Model.PinningPolynomial
import ZeroFreeness.Potts.Transfer.PottsAnalytic

/-! Endpoint patching with the radius chosen before the vertex type and
the actual pinning datum, followed by the original graph/pinning
semantics and the precise forced-zero statement. -/
namespace ZeroFreeness.Potts
open PottsCI Separator Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

/-- The type-uniform form of `patch_endpoint_and_positive`. Its proof
does not package vertex types as an index in the same universe. -/
theorem uniform_pinning_zero_free_of_endpoint_and_positive
    (C : Type v) [Fintype C] (Delta : ℕ)
    (hhard : ∃ rho > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      I.DegreeBound Delta → PartitionNonzeroOn I 0 rho)
    (hpositive : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
        I.DegreeBound Delta → ∀ x ∈ Icc delta 1, PartitionNonzeroOn I (x : ℂ) eps) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      I.DegreeBound Delta → ∀ z ∈ thickening eps pottsInterval,
        pinningProductPartition I z ≠ 0 := by
  obtain ⟨rho, hrho, hzero⟩ := hhard
  let delta : ℝ := min (1 / 2) (rho / 4)
  have hd : 0 < delta := lt_min (by norm_num) (by positivity)
  have hdhalf : delta ≤ 1 / 2 := min_le_left _ _
  have hdrho : delta ≤ rho / 4 := min_le_right _ _
  obtain ⟨ep, hep, hp⟩ := hpositive delta hd (by linarith)
  refine ⟨min ep delta, lt_min hep hd, ?_⟩
  intro V _ I hdegree z hz
  obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.mp hz
  obtain ⟨x, hx, rfl⟩ := hw
  by_cases hxd : x ≤ delta
  · apply hzero I hdegree z
    have hdist : dist z (x : ℂ) < delta :=
      lt_of_lt_of_le hzw (min_le_right _ _)
    have hnorm : ‖(x : ℂ)‖ = x := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    have htri : ‖z‖ ≤ dist z (x : ℂ) + ‖(x : ℂ)‖ := by
      simpa only [dist_zero_right] using dist_triangle z (x : ℂ) 0
    rw [hnorm] at htri
    rw [mem_ball, dist_zero_right]
    linarith
  · exact hp I hdegree x ⟨le_of_not_ge hxd, hx.2⟩ z
      (lt_of_lt_of_le hzw (min_le_left _ _))

/-- Convert a uniform actual pinning-data theorem to every original
bounded-degree graph and arbitrary, possibly improper, partial coloring. -/
theorem uniform_normalized_zero_free_of_pinning
    (C : Type v) [Fintype C] (Delta : ℕ) {eps : ℝ}
    (hnz : ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      I.DegreeBound Delta → ∀ z ∈ thickening eps pottsInterval,
        pinningProductPartition I z ≠ 0) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ w, G.degree w ≤ Delta) → ∀ tau : PartialColouring V C,
        ∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0 := by
  intro V _ G hd tau z hz
  have h := hnz (tau.toPinningData G) (tau.degreeBound_of_original G hd) z hz
  rwa [pinningProductPartition_toPinningData] at h

theorem uniform_normalizedPolynomial_zero_free_of_pinning
    (C : Type v) [Fintype C] (Delta : ℕ) {eps : ℝ}
    (hnz : ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      I.DegreeBound Delta → ∀ z ∈ thickening eps pottsInterval,
        pinningProductPartition I z ≠ 0) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ w, G.degree w ≤ Delta) → ∀ tau : PartialColouring V C,
        ∀ z ∈ thickening eps pottsInterval, (normalizedPolynomial tau G).eval z ≠ 0 := by
  intro V _ G hd tau z hz
  exact uniform_normalized_zero_free_of_pinning C Delta hnz G hd tau z hz

/-- Once normalization is nonzero, every zero of the full partition is
exactly the forced zero at activity zero. -/
theorem fullPartition_eq_zero_iff_of_normalized_ne_zero
    {V : Type u} {C : Type v} [Fintype V] [Fintype C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (z : ℂ)
    (hnz : normalizedPartition tau G z ≠ 0) :
    fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G := by
  simp only [fullPartition_eq, mul_eq_zero, hnz, or_false,
    pow_eq_zero_iff', Nat.pos_iff_ne_zero]

theorem fullPolynomial_rootMultiplicity_zero_of_normalized_ne_zero
    {V : Type u} {C : Type v} [Fintype V] [Fintype C]
    (tau : PartialColouring V C) (G : SimpleGraph V)
    (hnz : normalizedPartition tau G 0 ≠ 0) :
    (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G := by
  have hp : normalizedPolynomial tau G ≠ 0 := by
    intro heq
    simp [normalizedPartition, heq] at hnz
  have hnotRoot : ¬ (normalizedPolynomial tau G).IsRoot 0 := hnz
  have h := Polynomial.rootMultiplicity_mul_X_sub_C_pow
    (a := (0 : ℂ)) (n := tau.pinnedConflictCount G) hp
  rw [fullPolynomial_eq]
  simpa [Polynomial.rootMultiplicity_eq_zero hnotRoot, mul_comm] using h

/-- Final graph/pinning packaging of the two uniform disk conclusions.
The normalized polynomial is zero-free throughout the thickening; the
full polynomial has precisely the pinned-only forced zero and multiplicity. -/
theorem uniform_original_potts_zero_free_of_endpoint_and_positive
    (C : Type v) [Fintype C] (Delta : ℕ)
    (hhard : ∃ rho > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      I.DegreeBound Delta → PartitionNonzeroOn I 0 rho)
    (hpositive : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∃ eps > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
        I.DegreeBound Delta → ∀ x ∈ Icc delta 1, PartitionNonzeroOn I (x : ℂ) eps) :
    ∃ eps > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      (∀ w, G.degree w ≤ Delta) → ∀ tau : PartialColouring V C,
      (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
      (∀ z ∈ thickening eps pottsInterval,
        fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
      (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G := by
  obtain ⟨eps, heps, hnz⟩ :=
    uniform_pinning_zero_free_of_endpoint_and_positive C Delta hhard hpositive
  have hzero : (0 : ℂ) ∈ thickening eps pottsInterval := by
    apply mem_thickening_iff.mpr
    exact ⟨0, ⟨0, by simp, rfl⟩, by simpa using heps⟩
  refine ⟨eps, heps, ?_⟩
  intro V _ G hd tau
  have hnorm := uniform_normalized_zero_free_of_pinning C Delta hnz G hd tau
  refine ⟨hnorm, ?_, ?_⟩
  · intro z hz
    exact fullPartition_eq_zero_iff_of_normalized_ne_zero tau G z (hnorm z hz)
  · exact fullPolynomial_rootMultiplicity_zero_of_normalized_ne_zero tau G
      (hnorm 0 hzero)

end
end ZeroFreeness.Potts
