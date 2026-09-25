import ZeroFreeness.Potts.Transfer.InductionState
import ZeroFreeness.Potts.Geometry.OptionComponentFactorization

/-! Uniform local analytic inputs to the simultaneous induction. All
controls below concern the actual partition functions and the principal
response logarithms; the radius is chosen before any graph instance. -/
namespace ZeroFreeness.Potts
open PottsCI Separator
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

def PrincipalResponseControl (f : ℂ → ℂ) (x : ℂ) (r budget : ℝ) : Prop :=
  principalResponseLog f x x = 0 ∧
    DifferentiableOn ℂ (principalResponseLog f x) (Metric.ball x r) ∧
    (∀ z ∈ Metric.ball x r, Complex.exp (principalResponseLog f x z) = f z / f x) ∧
    ∀ z ∈ Metric.ball x r, ‖principalResponseLog f x z‖ ≤ budget

theorem PrincipalResponseControl.mono_radius {f : ℂ → ℂ} {x : ℂ} {r r' b : ℝ}
    (h : PrincipalResponseControl f x r b) (hr : r' ≤ r) :
    PrincipalResponseControl f x r' b :=
  ⟨h.1, h.2.1.mono (Metric.ball_subset_ball hr),
    fun z hz => h.2.2.1 z (Metric.ball_subset_ball hr hz),
    fun z hz => h.2.2.2 z (Metric.ball_subset_ball hr hz)⟩

structure PositiveLocalControls (C : Type v) [Fintype C] (Δ B : ℕ)
    (K : Set ℂ) (r alpha : ℝ) : Prop where
  inside : ∀ {U S O : Type u} [Fintype U] [Fintype S] [Fintype O]
    (I : PinningData (Vertex U S O) C), I.DegreeBound Δ →
    Fintype.card U + Fintype.card S ≤ B → ∀ ξ : S → C, ∀ x ∈ K,
    PrincipalResponseControl (fun z => insidePartition I z ξ) x r (alpha / 8)
  component : ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
    I.DegreeBound Δ → Fintype.card (Component.RootComponent I.graph none) ≤ B →
    ∀ x ∈ K, PartitionNonzeroOn (Component.optionCommonRemainderData I) x r →
    OptionRootResponses I x r (alpha / 4)
  boundary : ∀ m : ℕ, m ≤ Δ → ∀ x ∈ K,
    PrincipalResponseControl (fun z : ℂ => z ^ m) x r (alpha / 8)

/-- Positive compact intervals admit all three local controls with one
uniform radius, and with every subsequent smaller positive radius. -/
theorem exists_positive_local_controls (C : Type v) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0) {alpha : ℝ} (ha : 0 < alpha) :
    ∃ eps > 0, ∀ r : ℝ, 0 < r → r ≤ eps →
      PositiveLocalControls.{u, v} C Δ B K r alpha := by
  obtain ⟨ei, hei, hi⟩ := bounded_inside_positive_log_stability C Δ B K hK hreal ha
  obtain ⟨ec, hec, hc⟩ :=
    Component.bounded_option_component_positive_response_control C Δ B K hK hreal ha
  obtain ⟨eb, heb, hb⟩ := bounded_boundary_positive_log_stability Δ K hK hreal ha
  refine ⟨min ei (min ec eb), lt_min hei (lt_min hec heb), ?_⟩
  intro r hr hre
  have hri : r ≤ ei := hre.trans (min_le_left _ _)
  have hrc : r ≤ ec := hre.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrb : r ≤ eb := hre.trans ((min_le_right _ _).trans (min_le_right _ _))
  constructor
  · intro U S O _ _ _ I hd hB ξ x hx
    exact PrincipalResponseControl.mono_radius (hi I hd hB ξ x hx) hri
  · intro O _ I hd hB x hx hE
    exact (hc I hd hB x hx r hr hrc hE).2
  · intro m hm x hx
    exact PrincipalResponseControl.mono_radius (hb m hm x hx) hrb

structure HardLocalControls (C : Type v) [Fintype C] (Δ B : ℕ)
    (r alpha : ℝ) : Prop where
  component : ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
    I.DegreeBound Δ → Fintype.card (Component.RootComponent I.graph none) ≤ B →
    PartitionNonzeroOn (Component.optionCommonRemainderData I) 0 r →
    OptionRootResponses I 0 r (alpha / 4)

/-- The actual hard small-component controls are uniform over all
instances because the bounded polynomial family has a hard extension. -/
theorem exists_hard_local_controls (C : Type v) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (hq : Δ + 1 ≤ Fintype.card C) {alpha : ℝ} (ha : 0 < alpha) :
    ∃ eps > 0, ∀ r : ℝ, 0 < r → r ≤ eps →
      HardLocalControls.{u, v} C Δ B r alpha := by
  have hreal : ({0} : Set ℂ) ⊆ Complex.ofReal '' Set.Ici 0 := by
    intro x hx
    have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
    exact ⟨0, by simp, by simpa using hx0.symm⟩
  obtain ⟨eps, heps, hc⟩ :=
    Component.bounded_option_component_nonnegative_response_control C Δ B hq
      {0} isCompact_singleton hreal ha
  refine ⟨eps, heps, ?_⟩
  intro r hr hre
  constructor
  intro O _ I hd hB hE
  exact (hc I hd hB 0 (Set.mem_singleton 0) r hr hre hE).2

end
end ZeroFreeness.Potts
