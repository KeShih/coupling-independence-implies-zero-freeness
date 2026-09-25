import ZeroFreeness.Coupling.Girth.Covariance.Insertion.FullSource
import ZeroFreeness.Coupling.CLMM.Transfer

/-! Finite sign duality turns additive-source oscillation into weighted
total variation.  Distance weights are Lipschitz on the fixed ambient
graph and remain so after restricting to any residual instance. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C]

def singleSiteVariation (μ ν : FinDist (V → C)) (v : V) : ℝ :=
  (1/2 : ℝ) * ∑ c, |CLMM.singleSiteMass μ v c - CLMM.singleSiteMass ν v c|

def weightedInfluence (μ ν : FinDist (V → C)) (a : V → ℝ) : ℝ :=
  ∑ v, a v * singleSiteVariation μ ν v

theorem singleSiteVariation_nonneg (μ ν : FinDist (V → C)) (v : V) :
    0 ≤ singleSiteVariation μ ν v := by unfold singleSiteVariation; positivity

theorem singleSiteMass_eq_marginal (μ : FinDist (V → C)) (v : V) (c : C) :
    CLMM.singleSiteMass μ v c = (coordinateMarginal μ (fun σ => σ v)).w c := by
  simp [CLMM.singleSiteMass, coordinateMarginal, mapLaw, FinDist.bind, FinDist.pure, eq_comm]

theorem expect_additive_source (μ : FinDist (V → C)) (f : V → C → ℝ) :
    expectReal μ (fun σ => ∑ v, f v (σ v)) = ∑ v, ∑ c, CLMM.singleSiteMass μ v c * f v c := by
  rw [expectReal_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [← ZeroFreeness.expectReal_mapLaw μ (fun σ => σ v) (f v)]
  simp only [expectReal, singleSiteMass_eq_marginal, coordinateMarginal]

/-- Choosing the sign of each individual marginal difference attains
twice the weighted total variation exactly. -/
theorem exists_sign_source (μ ν : FinDist (V → C)) (a : V → ℝ) (ha : ∀ v, 0 ≤ a v) :
    ∃ f : V → C → ℝ, (∀ v c, |f v c| ≤ a v) ∧
      expectReal μ (fun σ => ∑ v, f v (σ v)) - expectReal ν (fun σ => ∑ v, f v (σ v)) =
        2 * weightedInfluence μ ν a := by
  let d := fun v c => CLMM.singleSiteMass μ v c - CLMM.singleSiteMass ν v c
  let f := fun v c => if 0 ≤ d v c then a v else -a v
  refine ⟨f, ?_, ?_⟩
  · intro v c
    dsimp [f]
    split <;> simp [abs_of_nonneg (ha v)]
  · rw [expect_additive_source, expect_additive_source, ← Finset.sum_sub_distrib]
    have ht (v : V) : (∑ c, CLMM.singleSiteMass μ v c * f v c) -
        (∑ c, CLMM.singleSiteMass ν v c * f v c) = a v * ∑ c, |d v c| := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      change _ - _ = a v * |CLMM.singleSiteMass μ v c - CLMM.singleSiteMass ν v c|
      dsimp [f, d]
      split_ifs with h
      · rw [abs_of_nonneg h]
        ring
      · rw [abs_of_neg (lt_of_not_ge h)]
        ring
    simp_rw [ht]
    unfold weightedInfluence singleSiteVariation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [d]
    ring

def SourceOscillation (μ ν : FinDist (V → C)) (a : V → ℝ) (K : ℝ) : Prop :=
  ∀ f : V → C → ℝ, (∀ v c, |f v c| ≤ a v) →
    |expectReal μ (fun σ => ∑ v, f v (σ v)) - expectReal ν (fun σ => ∑ v, f v (σ v))| ≤ K

theorem weightedInfluence_of_source (μ ν : FinDist (V → C)) (a : V → ℝ) {K : ℝ}
    (ha : ∀ v, 0 ≤ a v) (hf : SourceOscillation μ ν a K) : weightedInfluence μ ν a ≤ K/2 := by
  obtain ⟨f, hbound, heq⟩ := exists_sign_source μ ν a ha
  have h := (le_abs_self _).trans (hf f hbound)
  rw [heq] at h
  linarith

def WeightLipschitz (G : SimpleGraph V) (χ : ℝ) (a : V → ℝ) : Prop :=
  ∀ u v, G.Adj u v → a v ≤ χ * a u

def distanceWeight (G : SimpleGraph V) (r : V) (χ : ℝ) (v : V) : ℝ := χ ^ G.dist r v

theorem distanceWeight_pos (G : SimpleGraph V) (r : V) {χ : ℝ} (hχ : 0 < χ) (v : V) :
    0 < distanceWeight G r χ v := pow_pos hχ _

theorem distanceWeight_root (G : SimpleGraph V) (r : V) (χ : ℝ) : distanceWeight G r χ r = 1 := by
  simp [distanceWeight]

theorem distanceWeight_lipschitz (G : SimpleGraph V) (r : V) {χ : ℝ} (hχ : 1 ≤ χ) :
    WeightLipschitz G χ (distanceWeight G r χ) := by
  intro u v huv
  have hd : G.dist r v ≤ G.dist r u + 1 := by
    simpa only [SimpleGraph.dist_eq_one_iff_adj.mpr huv] using huv.reachable.dist_triangle_right r
  change χ ^ G.dist r v ≤ χ * χ ^ G.dist r u
  calc
    _ ≤ χ ^ (G.dist r u + 1) := pow_le_pow_right₀ hχ hd
    _ = _ := by rw [pow_succ, mul_comm]

/-- The weights are transported with the original instance, so pinning
cannot shorten the ambient distance used in the source induction. -/
theorem WeightLipschitz.comap {G : SimpleGraph V} {χ : ℝ} {a : V → ℝ}
    (h : WeightLipschitz G χ a) {W : Type*} (f : W → V) :
    WeightLipschitz (G.comap f) χ (fun w => a (f w)) := fun _ _ huv => h _ _ huv

theorem WeightLipschitz.of_le {G H : SimpleGraph V} {χ : ℝ} {a : V → ℝ}
    (h : WeightLipschitz G χ a) (hH : H ≤ G) : WeightLipschitz H χ a :=
  fun u v huv => h u v (hH huv)

theorem WeightLipschitz.two_steps {G : SimpleGraph V} {χ : ℝ} {a : V → ℝ}
    (h : WeightLipschitz G χ a) (hχ : 0 ≤ χ) {r u v : V}
    (hru : G.Adj r u) (huv : G.Adj u v) : a v ≤ χ ^ 2 * a r := by
  calc
    _ ≤ χ * a u := h u v huv
    _ ≤ χ * (χ * a r) := mul_le_mul_of_nonneg_left (h r u hru) hχ
    _ = _ := by ring

theorem distanceWeight_on_sphere (I : PinningData (Option V) C) (χ : ℝ) (R : ℕ)
    (v : V) (hv : I.graph.edist none (some v) = (R : ℕ∞)) :
    distanceWeight I.graph none χ (some v) = χ ^ R := by
  simp only [distanceWeight, SimpleGraph.dist, hv, ENat.toNat_natCast]

theorem sphereInfluence_le_weighted (I : PinningData (Option V) C) (μ ν : FinDist (V → C))
    {χ : ℝ} (hχ : 0 < χ) (R : ℕ) :
    χ ^ R * CLMM.sphereInfluence I R μ ν ≤
      weightedInfluence μ ν (fun v => distanceWeight I.graph none χ (some v)) := by
  unfold CLMM.sphereInfluence weightedInfluence
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  dsimp only
  by_cases hv : I.graph.edist none (some v) = (R : ℕ∞)
  · rw [if_pos hv, distanceWeight_on_sphere I χ R v hv]
    rfl
  · rw [if_neg hv, mul_zero]
    exact mul_nonneg (distanceWeight_pos I.graph none hχ _).le (singleSiteVariation_nonneg μ ν v)

theorem sphereInfluence_of_source (I : PinningData (Option V) C) (μ ν : FinDist (V → C))
    {χ M : ℝ} (hχ : 0 < χ) (R : ℕ)
    (hf : SourceOscillation μ ν (fun v => distanceWeight I.graph none χ (some v)) M) :
    CLMM.sphereInfluence I R μ ν ≤ (M/2) * (χ⁻¹) ^ R := by
  have hw := weightedInfluence_of_source μ ν (fun v => distanceWeight I.graph none χ (some v))
    (fun v => (distanceWeight_pos I.graph none hχ _).le) hf
  have h := (sphereInfluence_le_weighted I μ ν hχ R).trans hw
  calc
    _ ≤ (M/2) / χ ^ R := (le_div_iff₀ (pow_pos hχ R)).mpr (by simpa only [mul_comm] using h)
    _ = _ := by rw [div_eq_mul_inv, inv_pow]

/-- The same duality estimate for a fixed ambient graph.  Its metric is
kept unchanged when the current free vertices are restricted or pinned. -/
theorem ambient_sphere_of_source {A : Type*} [Fintype A] (G : SimpleGraph A) (e : Option V → A)
    (μ ν : FinDist (V → C)) {χ M : ℝ} (hχ : 0 < χ) (R : ℕ)
    (hf : SourceOscillation μ ν (fun v => distanceWeight G (e none) χ (e (some v))) M) :
    (∑ v, if G.edist (e none) (e (some v)) = (R : ℕ∞) then
      singleSiteVariation μ ν v else 0) ≤ (M/2) * (χ⁻¹)^R := by
  have hw := weightedInfluence_of_source μ ν (fun v => distanceWeight G (e none) χ (e (some v)))
    (fun _ => (distanceWeight_pos G (e none) hχ _).le) hf
  have hs : χ ^ R * (∑ v, if G.edist (e none) (e (some v)) = (R : ℕ∞) then
      singleSiteVariation μ ν v else 0) ≤
      weightedInfluence μ ν (fun v => distanceWeight G (e none) χ (e (some v))) := by
    unfold weightedInfluence
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    dsimp only
    by_cases hv : G.edist (e none) (e (some v)) = (R : ℕ∞)
    · have he : distanceWeight G (e none) χ (e (some v)) = χ ^ R := by
        simp only [distanceWeight, SimpleGraph.dist, hv, ENat.toNat_natCast]
      rw [if_pos hv, he]
    · rw [if_neg hv, mul_zero]
      exact mul_nonneg (distanceWeight_pos G (e none) hχ _).le (singleSiteVariation_nonneg μ ν v)
  calc
    _ ≤ (M/2) / χ ^ R := (le_div_iff₀ (pow_pos hχ R)).mpr
      (by simpa only [mul_comm] using hs.trans hw)
    _ = _ := by rw [div_eq_mul_inv, inv_pow]

end
end ZeroFreeness.Appendix.Girth
