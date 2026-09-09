import CI2ZF.Potts.Geometry.ComponentFactorization
import CI2ZF.Potts.Model.OptionPinning
import CI2ZF.Potts.Transfer.UniformLocalLogs

/-! The genuine root-component branch for arbitrary pinning data. The
common exterior is independent of the new root color. -/
namespace CI2ZF.Potts.Component
open PottsCI CI2ZF.Potts.Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {O C R : Type*} [Fintype O] [Fintype C]

def optionInRootComponent (I : PinningData (Option O) C) (o : O) : Prop :=
  I.graph.Reachable none (some o)

def optionComponentChildData (I : PinningData (Option O) C) (a : C) :
    PinningData {o : O // optionInRootComponent I o} C :=
  restrictData (optionChildData I a) (optionInRootComponent I)

def optionCommonRemainderData (I : PinningData (Option O) C) :
    PinningData {o : O // ¬ optionInRootComponent I o} C :=
  restrictData (optionMiddleData I) (fun o => ¬ optionInRootComponent I o)

lemma optionInRootComponent_closed (I : PinningData (Option O) C) (a : C)
    (u : O) (hu : optionInRootComponent I u) (w : O)
    (hadj : (optionChildData I a).graph.Adj u w) : optionInRootComponent I w :=
  hu.trans (show I.graph.Adj (some u) (some w) from hadj).reachable

lemma optionOutside_not_root_adj (I : PinningData (Option O) C) (o : O)
    (ho : ¬ optionInRootComponent I o) : ¬ I.graph.Adj none (some o) :=
  fun hadj => ho hadj.reachable

theorem optionChild_remainder_eq_common (I : PinningData (Option O) C) (a : C) :
    restrictData (optionChildData I a) (fun o => ¬ optionInRootComponent I o) =
      optionCommonRemainderData I := by
  unfold optionCommonRemainderData restrictData
  congr 1
  funext o c
  rw [optionChildData_count]
  simp [optionOutside_not_root_adj I o.val o.property, optionMiddleData]

theorem optionChild_component_factorization [CommSemiring R]
    (I : PinningData (Option O) C) (a : C) (z : R) :
    pinningProductPartition (optionChildData I a) z =
      pinningProductPartition (optionComponentChildData I a) z *
        pinningProductPartition (optionCommonRemainderData I) z := by
  rw [cut_partition_factorization _ _ (optionInRootComponent_closed I a),
    optionChild_remainder_eq_common]
  rfl

theorem optionComponentChildData_degreeBound (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (a : C) :
    (optionComponentChildData I a).DegreeBound Δ :=
  restrictData_degreeBound _ _ (optionInRootComponent_closed I a)
    (optionChildData_degreeBound I hd a)

theorem optionCommonRemainderData_degreeBound (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (optionCommonRemainderData I).DegreeBound Δ := by
  have hm : (optionMiddleData I).DegreeBound Δ := by
    intro o
    have h := hd (some o)
    have hg := optionMiddleData_degree I o
    change (optionMiddleData I).graph.degree o +
      (∑ c : C, I.boundaryCount (some o) c) ≤ Δ
    unfold PinningData.constraintDegree at h
    omega
  have hc (u : O) (hu : ¬ optionInRootComponent I u) (w : O)
      (hadj : (optionMiddleData I).graph.Adj u w) : ¬ optionInRootComponent I w := by
    intro hw
    exact hu (hw.trans (show I.graph.Adj (some w) (some u) from hadj.symm).reachable)
  convert restrictData_degreeBound _ (fun o => ¬ optionInRootComponent I o) hc hm using 1
  rfl

theorem optionComponentChild_card_le (I : PinningData (Option O) C) :
    Fintype.card {o : O // optionInRootComponent I o} ≤
      Fintype.card (RootComponent I.graph none) := by
  apply Fintype.card_le_of_injective
    (fun o : {o : O // optionInRootComponent I o} =>
      (⟨some o.val, o.property⟩ : RootComponent I.graph none))
  intro u w he
  exact Subtype.ext (Option.some.inj (congrArg Subtype.val he))

theorem optionComponentChild_card_lt_parent (I : PinningData (Option O) C) :
    Fintype.card {o : O // optionInRootComponent I o} < Fintype.card (Option O) := by
  have h := Fintype.card_le_of_injective
    (Subtype.val : {o : O // optionInRootComponent I o} → O) Subtype.coe_injective
  rw [Fintype.card_option]
  omega

theorem optionCommonRemainder_card_lt_parent (I : PinningData (Option O) C) :
    Fintype.card {o : O // ¬ optionInRootComponent I o} < Fintype.card (Option O) := by
  have h := Fintype.card_le_of_injective
    (Subtype.val : {o : O // ¬ optionInRootComponent I o} → O) Subtype.coe_injective
  rw [Fintype.card_option]
  omega

theorem optionRootComponent_card_le_of_shell_empty (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (r : ℕ)
    (hs : BFS.shell I.graph none (r + 1) = ∅) :
    Fintype.card (RootComponent I.graph none) ≤
      ∑ k ∈ Finset.range (r + 1), Δ ^ k := by
  have hg (w : Option O) : I.graph.degree w ≤ Δ := by
    have h := hd w
    unfold PinningData.constraintDegree at h
    omega
  simpa only [Fintype.card_subtype] using
    BFS.component_card_le_geom_of_shell_empty I.graph none r Δ hg hs

theorem optionComponentChild_card_le_of_shell_empty (I : PinningData (Option O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (r : ℕ)
    (hs : BFS.shell I.graph none (r + 1) = ∅) :
    Fintype.card {o : O // optionInRootComponent I o} ≤
      ∑ k ∈ Finset.range (r + 1), Δ ^ k :=
  (optionComponentChild_card_le I).trans
    (optionRootComponent_card_le_of_shell_empty I hd r hs)

theorem optionChildRatio_eq_component (I : PinningData (Option O) C)
    (a b : C) (z : ℂ)
    (hE : pinningProductPartition (optionCommonRemainderData I) z ≠ 0) :
    pinningProductPartition (optionChildData I a) z /
        pinningProductPartition (optionChildData I b) z =
      pinningProductPartition (optionComponentChildData I a) z /
        pinningProductPartition (optionComponentChildData I b) z := by
  rw [optionChild_component_factorization, optionChild_component_factorization]
  exact mul_div_mul_right _ _ hE

/-- This is the normalized response in the complex-average induction.
Only the common exterior must be nonzero for its exact cancellation. -/
theorem optionChildResponseRatio_eq_component (I : PinningData (Option O) C)
    (a b : C) (x z : ℂ)
    (hEx : pinningProductPartition (optionCommonRemainderData I) x ≠ 0)
    (hEz : pinningProductPartition (optionCommonRemainderData I) z ≠ 0) :
    (pinningProductPartition (optionChildData I a) z /
        pinningProductPartition (optionChildData I a) x) /
      (pinningProductPartition (optionChildData I b) z /
        pinningProductPartition (optionChildData I b) x) =
    (pinningProductPartition (optionComponentChildData I a) z /
        pinningProductPartition (optionComponentChildData I a) x) /
      (pinningProductPartition (optionComponentChildData I b) z /
        pinningProductPartition (optionComponentChildData I b) x) := by
  simp only [optionChild_component_factorization]
  rw [mul_div_mul_comm, mul_div_mul_comm]
  exact mul_div_mul_right _ _ (div_ne_zero hEz hEx)

/-- Local logarithms on the bounded component and nonvanishing of the
strictly smaller common exterior close the actual child-response branch. -/
theorem option_component_response_control (I : PinningData (Option O) C)
    {x : ℂ} {ε alpha : ℝ} (hε : 0 < ε) (L : C → ℂ → ℂ)
    (hzero : ∀ a, L a x = 0)
    (hdiff : ∀ a, DifferentiableOn ℂ (L a) (Metric.ball x ε))
    (hexp : ∀ a z, z ∈ Metric.ball x ε → Complex.exp (L a z) =
      pinningProductPartition (optionComponentChildData I a) z /
        pinningProductPartition (optionComponentChildData I a) x)
    (hbound : ∀ a z, z ∈ Metric.ball x ε → ‖L a z‖ ≤ alpha / 8)
    (hE : ∀ z ∈ Metric.ball x ε,
      pinningProductPartition (optionCommonRemainderData I) z ≠ 0) :
    (∀ a z, z ∈ Metric.ball x ε →
      pinningProductPartition (optionChildData I a) z ≠ 0) ∧
    ∀ a b, ∃ F : ℂ → ℂ, F x = 0 ∧
      DifferentiableOn ℂ F (Metric.ball x ε) ∧
      (∀ z ∈ Metric.ball x ε, Complex.exp (F z) =
        (pinningProductPartition (optionChildData I a) z /
          pinningProductPartition (optionChildData I a) x) /
        (pinningProductPartition (optionChildData I b) z /
          pinningProductPartition (optionChildData I b) x)) ∧
      ∀ z ∈ Metric.ball x ε, ‖F z‖ ≤ alpha / 4 := by
  refine ⟨?_, ?_⟩
  · intro a z hz
    rw [optionChild_component_factorization]
    apply mul_ne_zero _ (hE z hz)
    have hn := Complex.exp_ne_zero (L a z)
    rw [hexp a z hz] at hn
    exact (div_ne_zero_iff.mp hn).1
  · intro a b
    refine ⟨fun z => L a z - L b z, by simp only [hzero, sub_self],
      (hdiff a).sub (hdiff b), ?_, ?_⟩
    · intro z hz
      rw [Complex.exp_sub, hexp a z hz, hexp b z hz,
        optionChildResponseRatio_eq_component I a b x z
          (hE x (Metric.mem_ball_self hε)) (hE z hz)]
    · intro z hz
      calc
        ‖L a z - L b z‖ ≤ ‖L a z‖ + ‖L b z‖ := norm_sub_le _ _
        _ ≤ alpha / 4 := by linarith [hbound a z hz, hbound b z hz]

/-- A single local radius works for the small-component branch of every
parent instance. The exterior nonzero hypothesis is on a strictly smaller
actual datum; the working radius may be shrunk for the other branches. -/
theorem bounded_option_component_positive_response_control
    (C : Type*) [Fintype C] [Nonempty C] (Δ B : ℕ)
    (K : Set ℂ) (hK : IsCompact K) (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0)
    {alpha : ℝ} (ha : 0 < alpha) :
    ∃ ε > 0, ∀ {O : Type*} [Fintype O] (I : PinningData (Option O) C),
      I.DegreeBound Δ → Fintype.card (RootComponent I.graph none) ≤ B →
      ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ ε →
      (∀ z ∈ Metric.ball x r,
        pinningProductPartition (optionCommonRemainderData I) z ≠ 0) →
      (∀ a z, z ∈ Metric.ball x r →
        pinningProductPartition (optionChildData I a) z ≠ 0) ∧
      ∀ a b, ∃ F : ℂ → ℂ, F x = 0 ∧
        DifferentiableOn ℂ F (Metric.ball x r) ∧
        (∀ z ∈ Metric.ball x r, Complex.exp (F z) =
          (pinningProductPartition (optionChildData I a) z /
            pinningProductPartition (optionChildData I a) x) /
          (pinningProductPartition (optionChildData I b) z /
            pinningProductPartition (optionChildData I b) x)) ∧
        ∀ z ∈ Metric.ball x r, ‖F z‖ ≤ alpha / 4 := by
  obtain ⟨ε, hε, hb⟩ := bounded_pinning_positive_log_stability C Δ B K hK hreal ha
  refine ⟨ε, hε, ?_⟩
  intro O _ I hd hB x hx r hr hrε hE
  have hlocal (a : C) := hb (optionComponentChildData I a)
    (optionComponentChildData_degreeBound I hd a)
    ((optionComponentChild_card_le I).trans hB) x hx
  apply option_component_response_control I hr
    (fun a => principalResponseLog (pinningProductPartition (optionComponentChildData I a)) x)
  · exact fun a => (hlocal a).1
  · exact fun a => (hlocal a).2.1.mono (Metric.ball_subset_ball hrε)
  · exact fun a z hz => (hlocal a).2.2.1 z (Metric.ball_subset_ball hrε hz)
  · exact fun a z hz => (hlocal a).2.2.2 z (Metric.ball_subset_ball hrε hz)
  · exact hE

/-- The same actual small-component branch includes the hard base. The
color slack supplies nonzero local hard partitions uniformly. -/
theorem bounded_option_component_nonnegative_response_control
    (C : Type*) [Fintype C] [Nonempty C] (Δ B : ℕ)
    (hq : Δ + 1 ≤ Fintype.card C) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Set.Ici 0) {alpha : ℝ} (ha : 0 < alpha) :
    ∃ ε > 0, ∀ {O : Type*} [Fintype O] (I : PinningData (Option O) C),
      I.DegreeBound Δ → Fintype.card (RootComponent I.graph none) ≤ B →
      ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ ε →
      (∀ z ∈ Metric.ball x r,
        pinningProductPartition (optionCommonRemainderData I) z ≠ 0) →
      (∀ a z, z ∈ Metric.ball x r →
        pinningProductPartition (optionChildData I a) z ≠ 0) ∧
      ∀ a b, ∃ F : ℂ → ℂ, F x = 0 ∧
        DifferentiableOn ℂ F (Metric.ball x r) ∧
        (∀ z ∈ Metric.ball x r, Complex.exp (F z) =
          (pinningProductPartition (optionChildData I a) z /
            pinningProductPartition (optionChildData I a) x) /
          (pinningProductPartition (optionChildData I b) z /
            pinningProductPartition (optionChildData I b) x)) ∧
        ∀ z ∈ Metric.ball x r, ‖F z‖ ≤ alpha / 4 := by
  obtain ⟨ε, hε, hb⟩ :=
    bounded_pinning_nonnegative_log_stability C Δ B hq K hK hreal ha
  refine ⟨ε, hε, ?_⟩
  intro O _ I hd hB x hx r hr hrε hE
  have hlocal (a : C) := hb (optionComponentChildData I a)
    (optionComponentChildData_degreeBound I hd a)
    ((optionComponentChild_card_le I).trans hB) x hx
  apply option_component_response_control I hr
    (fun a => principalResponseLog (pinningProductPartition (optionComponentChildData I a)) x)
  · exact fun a => (hlocal a).1
  · exact fun a => (hlocal a).2.1.mono (Metric.ball_subset_ball hrε)
  · exact fun a z hz => (hlocal a).2.2.1 z (Metric.ball_subset_ball hrε hz)
  · exact fun a z hz => (hlocal a).2.2.2 z (Metric.ball_subset_ball hrε hz)
  · exact hE

end
end CI2ZF.Potts.Component
