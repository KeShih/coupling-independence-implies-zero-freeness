import ZeroFreeness.Coupling.Girth.Transfer.WeightedInfluence
import ZeroFreeness.Coupling.CLMM.AmbientDegree
import ZeroFreeness.Coupling.Vigoda.CouplingIndependence

/-! The final fixed-girth passage from proved source oscillation to
uniform coupling, through CLMM Lemma 5.13 as proved in
`ZeroFreeness.Coupling.CLMM.SphereCoupling`.  The influence radius and the
hard-endpoint limit are also proved here. -/
namespace ZeroFreeness.Appendix.Girth
open scoped BigOperators Topology
open PottsCI PottsCI.FinDist Filter ZeroFreeness.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
set_option maxHeartbeats 200000
universe u v
variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]

/-- The internally proved source theorem is used at arbitrary positive
ambient weights; those weights are kept fixed through all pinnings. -/
def UniformWeightedSource (C : Type v) [Fintype C] (Δ g : ℕ) (x χ M : ℝ) : Prop :=
  ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
    I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
    (hx : 0 < x) (ha : 0 < (optionChildData I a).partition x)
    (hb : 0 < (optionChildData I b).partition x) (w : Option O → ℝ),
    (∀ v, 0 < w v) → WeightLipschitz I.graph χ w →
    SourceOscillation ((optionChildData I a).gibbs x hx.le ha)
      ((optionChildData I b).gibbs x hx.le hb) (fun v => w (some v)) (M * w none)

theorem uniformWeightedSource_one (Δ g : ℕ) (χ : ℝ) {M : ℝ} (hM : 0 ≤ M) :
    UniformWeightedSource.{u,v} C Δ g 1 χ M := by
  intro O _ I _ _ a b hx ha hb w hw _ f _
  rw [ZeroFreeness.gibbs_one_eq (optionChildData I a) (optionChildData I b) ha hb]
  simp only [sub_self, abs_zero]
  exact mul_nonneg hM (hw none).le

theorem uniformWeightedSource_include_one {Δ g : ℕ} {χ M : ℝ} (hM : 0 ≤ M)
    (hsource : ∀ (x : ℝ), 0 < x → x < 1 → UniformWeightedSource.{u,v} C Δ g x χ M) :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → UniformWeightedSource.{u,v} C Δ g x χ M := by
  intro x hx hx1
  rcases eq_or_lt_of_le hx1 with rfl | hlt
  · exact uniformWeightedSource_one Δ g χ hM
  · exact hsource x hx hlt

theorem sphereDecay_of_weighted_source {Δ g : ℕ} {x χ M : ℝ}
    (hx : 0 < x) (hχ : 1 < χ) (hsource : UniformWeightedSource.{u,v} C Δ g x χ M)
    (R : ℕ) : CLMM.FixedAmbientSphereDecay.{u,v} C Δ g R x ((M/2) * (χ⁻¹)^R) := by
  intro A _ J hd hg O _ e pin hdom
  dsimp only
  intro a b hx0 ha hb
  let : DecidableEq C := fun _ _ => Classical.propDecidable _
  let I := restrictPinningData J e pin
  let w : Option O → ℝ := fun v => distanceWeight J.graph (e none) χ (e v)
  have hpos (v : Option O) : 0 < w v := distanceWeight_pos J.graph (e none) (by linarith) (e v)
  have hlip : WeightLipschitz I.graph χ w :=
    (distanceWeight_lipschitz J.graph (e none) hχ.le).comap e
  have hs := hsource I (CLMM.restrict_degreeBound J e pin hdom hd)
    (CLMM.restrict_girth J e pin hg) a b hx ha hb w hpos hlip
  change SourceOscillation ((optionChildData I a).gibbs x hx.le ha)
    ((optionChildData I b).gibbs x hx.le hb)
    (fun v => distanceWeight J.graph (e none) χ (e (some v)))
    (M * distanceWeight J.graph (e none) χ (e none)) at hs
  rw [distanceWeight_root, mul_one] at hs
  exact ambient_sphere_of_source (χ := χ) (M := M) J.graph e
    ((optionChildData I a).gibbs x hx.le ha) ((optionChildData I b).gibbs x hx.le hb)
    (by linarith) R hs

/-- A single radius works for the whole positive interval, and the girth
of the input family is unchanged by the radius selection. -/
theorem positive_coupling_from_weighted_source
    (Δ g : ℕ) (hΔ : 3 ≤ Δ) {χ M : ℝ} (hχ : 1 < χ) (_hM : 0 ≤ M)
    (hsource : ∀ (x : ℝ), 0 < x → x ≤ 1 → UniformWeightedSource.{u,v} C Δ g x χ M) :
    ∃ R : ℕ, 2 ≤ R ∧ ∀ (x : ℝ) (hx : 0 < x), x ≤ 1 →
      ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
        I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
        (ha : 0 < (optionChildData I a).partition x)
        (hb : 0 < (optionChildData I b).partition x),
        W ham ((optionChildData I a).gibbs x hx.le ha)
          ((optionChildData I b).gibbs x hx.le hb) ≤ 2 * (Δ : ℝ)^R := by
  have hχ0 : 0 < χ := by linarith
  have hρ0 : 0 ≤ χ⁻¹ := (inv_pos.mpr hχ0).le
  have hρ1 : χ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hχ
  have hd : (1 : ℝ) < Δ := by exact_mod_cast (show 1 < Δ by omega)
  obtain ⟨R, _, hR, he⟩ := CLMM.choose_influence_radius (A := M/2) hρ0 hρ1 hd 2
  refine ⟨R, hR, ?_⟩
  intro x hx hx1 O _ I hI hg a b ha hb
  have he' : 1 / (16 * R * Real.log Δ) ≤ 1 / (8 * R * Real.log Δ) := by
    apply one_div_le_one_div_of_le (by positivity [Real.log_pos hd])
    have hlog := (Real.log_pos hd).le
    nlinarith [show (0 : ℝ) ≤ R from Nat.cast_nonneg R]
  exact CLMM.Lemma513.sphere_to_coupling C Δ g R x (1 / (16 * R * Real.log Δ)) hΔ hR hx hx1
    (by positivity [Real.log_pos hd]) he'
    (CLMM.fixedAmbientSphereDecay_mono (sphereDecay_of_weighted_source hx hχ (hsource x hx hx1) R) he)
    I hI hg a b ha hb

/-- Finite Gibbs continuity extends a uniform positive-interval coupling
bound to the hard model whenever its two child laws are defined. -/
theorem coupling_closed_of_positive {O : Type u} [Fintype O]
    (J K : PinningData O C) (cost : ℝ)
    (hpos : ∀ (x : ℝ) (hx : 0 < x), x ≤ 1 →
      W ham (J.gibbs x hx.le (J.partition_pos_of_parameter_pos hx))
        (K.gibbs x hx.le (K.partition_pos_of_parameter_pos hx)) ≤ cost)
    (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hJ : 0 < J.partition x) (hK : 0 < K.partition x) :
    W ham (J.gibbs x hx hJ) (K.gibbs x hx hK) ≤ cost := by
  by_cases hz : x = 0
  · subst x
    have hl : Tendsto (fun n => (ZeroFreeness.hardApproach n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    let μ (D : PinningData O C) (n : ℕ) := D.gibbs (ZeroFreeness.hardApproach n)
      (ZeroFreeness.hardApproach n).property
      (D.partition_pos_of_parameter_pos (ZeroFreeness.hardApproach_pos n))
    have hlim (D : PinningData O C) (hD : 0 < D.partition 0) (σ : O → C) :
        Tendsto (fun n => (μ D n).w σ) atTop (𝓝 ((D.gibbs 0 le_rfl hD).w σ)) := by
      exact ((D.continuous_weight σ).continuousAt.tendsto.comp hl).div
        (D.continuous_partition.continuousAt.tendsto.comp hl) hD.ne'
    apply W_le_of_pointwise_limits ham_nonneg ham_self ham_triangle ham_le_card
      (μ J) (μ K) _ _ (hlim J hJ) (hlim K hK)
    exact Filter.Eventually.of_forall fun n => hpos (ZeroFreeness.hardApproach n)
      (ZeroFreeness.hardApproach_pos n) (ZeroFreeness.hardApproach_le_one n)
  · exact hpos x (lt_of_le_of_ne hx (Ne.symm hz)) hx1

theorem closed_coupling_from_weighted_source
    (Δ g : ℕ) (hΔ : 3 ≤ Δ) {χ M : ℝ} (hχ : 1 < χ) (hM : 0 ≤ M)
    (hsource : ∀ (x : ℝ), 0 < x → x ≤ 1 → UniformWeightedSource.{u,v} C Δ g x χ M) :
    ∃ cost : ℝ, 0 ≤ cost ∧ ∀ (x : ℝ) (hx : 0 ≤ x), x ≤ 1 →
      ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
        I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C)
        (ha : 0 < (optionChildData I a).partition x)
        (hb : 0 < (optionChildData I b).partition x),
        W ham ((optionChildData I a).gibbs x hx ha)
          ((optionChildData I b).gibbs x hx hb) ≤ cost := by
  obtain ⟨R, _, hR⟩ := positive_coupling_from_weighted_source Δ g hΔ hχ hM hsource
  refine ⟨2 * (Δ : ℝ)^R, by positivity, ?_⟩
  intro x hx hx1 O _ I hd hg a b ha hb
  apply coupling_closed_of_positive (optionChildData I a) (optionChildData I b) (2 * (Δ : ℝ)^R)
    (fun y hy hy1 => hR y hy hy1 I hd hg a b _ _) x hx hx1 ha hb

end
end ZeroFreeness.Appendix.Girth
