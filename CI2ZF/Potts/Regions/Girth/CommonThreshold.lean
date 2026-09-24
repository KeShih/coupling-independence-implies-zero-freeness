import CI2ZF.Potts.Regions.Girth.Transfer.ResidualOriginal

/-!
# One girth threshold for coupling independence and zero-freeness

Main-paper Table A.1 footnote: the thresholds `g_*(q,Δ)`, `g_BBR(q,Δ)` and
`Δ_5(δ)` of the zero-free rows are those of the coupling-independence
theorems (companion Theorems 6.1, 7.6 and 9.4). The library states the CI
theorem and the zero-free theorem separately, each with its own
existentially quantified girth. The statements below choose the girth once
and prove both conclusions for that same girth, by re-running the library
proofs from the common soft (resp. positive) coupling bound.
-/

namespace CI2ZF.Appendix.Girth

open scoped BigOperators
open PottsCI PottsCI.FinDist CI2ZF.Potts CI2ZF.Potts.Separator Set Metric
open CI2ZF.Appendix CI2ZF.Appendix.Girth

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

/-- Large girth, `q ≥ Δ+3`: one girth `g = g_*(q,Δ)` and one constant `K`
give the CI bound of companion Theorem 6.1 on all of `[0,1]`, and for the
same `g` the uniform zero-free neighbourhood of `[0,1]`, both for the
residual pinned polynomial and for the original pinned polynomial with the
girth condition only on the free residual graph. -/
theorem high_girth_common_threshold
    (Δ : ℕ) (hΔ : 3 ≤ Δ) (hq : Δ + 3 ≤ Fintype.card C) :
    ∃ (g : ℕ) (K : ℝ), 3 ≤ g ∧ 0 ≤ K ∧
      (∀ x : PinningData.NonnegativeParameter, (x : ℝ) ≤ 1 →
        (largeGirthFamily.{u,v} C g).RootCouplingBound Δ (by omega) x K) ∧
      ∃ eps > 0,
        (∀ {V : Type u} [Fintype V] (I : PinningData V C),
          (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
          ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0) ∧
        UniformResidualGirthPottsZeroFree.{u,v} C Δ g eps := by
  obtain ⟨g, K, hg, hK, hsoft⟩ := high_girth_soft_coupling.{u,v} (C := C) Δ hΔ hq
  obtain ⟨eps, heps, hzf⟩ := large_girth_zero_free_of_soft_ci (by omega) hK hsoft
  exact ⟨g, K, hg, hK, fun x hx => closed_root_coupling_of_soft (by omega) hK hsoft x hx,
    eps, heps, hzf, uniformResidualGirthPottsZeroFree_of_residual heps hzf⟩

/-- BBR interval: one girth `g = g_BBR(q,Δ)` and one constant `K` give the
CI bound of companion Theorem 7.6 on `[x₀,1]`, and for the same `g` the
uniform zero-free neighbourhood of `[x₀,1]`, for the residual pinned
polynomial and for both original pinned polynomials, with the girth
condition only on the free residual graph. -/
theorem bbr_common_threshold
    (Δ : ℕ) (hq : 3 ≤ Fintype.card C)
    (hr : (Real.exp 1 - 1 / 2) / (Real.exp 1 - 1) ≤ (Δ : ℝ) / Fintype.card C) :
    ∃ (g : ℕ) (K : ℝ), 3 ≤ g ∧ 0 ≤ K ∧
      (∀ (x : ℝ) (hx : 0 < x), x ∈ Icc (BBR.start (Fintype.card C) Δ) 1 →
        (largeGirthFamily.{u,v} C g).PositiveRootCouplingBound Δ x hx K) ∧
      ∃ eps > 0,
        (∀ {V : Type u} [Fintype V] (I : PinningData V C),
          (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
          ∀ z ∈ thickening eps (Complex.ofReal '' Icc (BBR.start (Fintype.card C) Δ) 1),
            pinningProductPartition I z ≠ 0) ∧
        (∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
          (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C,
          (g : ℕ∞) ≤ (tau.toPinningData G).graph.egirth →
          ∀ z ∈ thickening eps (Complex.ofReal '' Icc (BBR.start (Fintype.card C) Δ) 1),
            normalizedPartition tau G z ≠ 0 ∧ fullPartition tau G z ≠ 0) := by
  obtain ⟨g, K, hg, hK, hci⟩ := BBR.high_girth_coupling.{u,v} (C := C) Δ hq hr
  obtain ⟨r, hr0, hn⟩ := (largeGirthFamily.{u,v} C g).positive_interval_uniform_transfer_of_positive_ci
    Δ (BBR.start_mem hq hr).1 K hci
  let x₀ := BBR.start (Fintype.card C) Δ
  have hx₀ : 0 < x₀ := (BBR.start_mem hq hr).1
  have hres : ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      (g : ℕ∞) ≤ I.graph.egirth → I.DegreeBound Δ →
      ∀ z ∈ thickening (min r (x₀ / 2)) (Complex.ofReal '' Icc x₀ 1),
        pinningProductPartition I z ≠ 0 := by
    intro V _ I hgI hd z hz
    obtain ⟨w, ⟨x, hx, rfl⟩, hdw⟩ := mem_thickening_iff.mp hz
    exact hn I hgI hd x hx z (hdw.trans_le (min_le_left _ _))
  refine ⟨g, K, hg, hK, hci, min r (x₀ / 2), lt_min hr0 (by positivity), hres, ?_⟩
  intro V _ G hd tau hfree z hz
  obtain ⟨w, ⟨x, hx, rfl⟩, hdist⟩ := mem_thickening_iff.mp hz
  have hnorm : normalizedPartition tau G z ≠ 0 := by
    have h := hres (tau.toPinningData G) hfree (tau.degreeBound_of_original G hd) z hz
    rwa [pinningProductPartition_toPinningData] at h
  have hzero : z ≠ 0 := by
    intro hz0
    subst z
    have hxpos : 0 < x := hx₀.trans_le hx.1
    have he : dist (0 : ℂ) (x : ℂ) = x := by
      simp only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    rw [he] at hdist
    have hh := hdist.trans_le (min_le_right r (x₀ / 2))
    linarith [hx.1]
  exact ⟨hnorm, fullPartition_ne_zero_of_normalized tau G hzero hnorm⟩

/-- Girth five: the degree threshold `Δ_5(δ) = girthFiveCIThreshold δ` of
companion Theorem 9.4 serves both the CI bound and the zero-free
neighbourhood, with girth five of the free residual graph in both. -/
theorem girth_five_common_threshold
    {δ : ℝ} {Δ : ℕ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hThreshold : girthFiveCIThreshold δ ≤ Δ)
    (hq : (1 + δ) * Δ ≤ (Fintype.card C : ℝ)) :
    (∃ cost : ℝ, 0 ≤ cost ∧ ∀ (x : ℝ) (hx : 0 ≤ x), x ≤ 1 →
      ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
        I.DegreeBound Δ → 5 ≤ I.graph.egirth → ∀ (a b : C)
        (ha : 0 < (optionChildData I a).partition x)
        (hb : 0 < (optionChildData I b).partition x),
        W ham ((optionChildData I a).gibbs x hx ha)
          ((optionChildData I b).gibbs x hx hb) ≤ cost) ∧
    ∃ eps > 0,
      (∀ {V : Type u} [Fintype V] (I : PinningData V C),
        5 ≤ I.graph.egirth → I.DegreeBound Δ →
        ∀ z ∈ thickening eps pottsInterval, pinningProductPartition I z ≠ 0) ∧
      UniformResidualGirthPottsZeroFree.{u,v} C Δ 5 eps := by
  obtain ⟨eps, heps, hn⟩ := girth_five_zero_free.{u,v} (C := C) hδ hδ1 hThreshold hq
  exact ⟨girth_five_coupling.{u,v} (C := C) hδ hδ1 hThreshold hq, eps, heps,
    fun I hg hd z hz => hn I (by exact_mod_cast hg) hd z hz,
    uniformResidualGirthPottsZeroFree_of_residual heps
      (fun I hg hd z hz => hn I (by exact_mod_cast hg) hd z hz)⟩

end

end CI2ZF.Appendix.Girth
