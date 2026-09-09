import CI2ZF.Potts.Transfer.PositiveBFSResponseStep
import CI2ZF.Potts.Transfer.HardBFSResponseStep
import CI2ZF.Potts.Transfer.FamilyInduction

/-! The BFS response argument restricted to an operation-closed family
of actual pinning data. -/
namespace CI2ZF.Potts.Separator
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]

/-- Only the explicitly constructed one-vertex unpinnings are used in
the exterior Lipschitz proof; responses for unrelated data are unnecessary. -/
theorem exterior_logs_lipschitz_of_actual_repinning_responses
    (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    {x : ℂ} {ε α : ℝ} (hε : 0 < ε) (h : (S → C) → ℂ → ℂ)
    (hzero : ∀ ξ, h ξ x = 0)
    (hdiff : ∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball x ε))
    (hexp : ∀ ξ, ∀ z ∈ Metric.ball x ε,
      Complex.exp (h ξ z) = exteriorPartition I z ξ / exteriorPartition I x ξ)
    (hroot : ∀ (ξ : S → C) (s : S), OptionRootResponses (unpinnedExteriorData I ξ s) x ε α) :
    ∀ z ∈ Metric.ball x ε, ∀ ξ ξ' : S → C,
      ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ' := by
  have hstep (ξ : S → C) (s : S) (a : C) :
      ∀ z ∈ Metric.ball x ε, ‖h (Function.update ξ s a) z - h ξ z‖ ≤ α := by
    obtain ⟨L, hLzero, hLdiff, hLexp, hLbound⟩ := hroot ξ s a (ξ s)
    have hEq : Set.EqOn (fun z => h (Function.update ξ s a) z - h ξ z) L (Metric.ball x ε) := by
      apply logs_eq_on_ball_of_exp_eq hε _ L ((hdiff _).sub (hdiff ξ)) hLdiff
      · intro z hz
        change Complex.exp (h (Function.update ξ s a) z - h ξ z) = Complex.exp (L z)
        rw [Complex.exp_sub, hexp _ z hz, hexp _ z hz, hLexp z hz]
        simp only [unpinnedExterior_child_partition I hsep, Function.update_eq_self]
      · change h (Function.update ξ s a) x - h ξ x = L x
        rw [hzero, hzero, sub_self, hLzero]
    intro z hz
    rw [show h (Function.update ξ s a) z - h ξ z = L z from hEq hz]
    exact hLbound z hz
  intro z hz ξ ξ'
  exact norm_sub_le_ham_of_coordinates (fun η => h η z) (fun η s a => hstep η s a z hz) ξ ξ'

end
end CI2ZF.Potts.Separator


namespace CI2ZF.Potts.PinningFamily
open PottsCI PottsCI.FinDist Separator OptionBFS
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
attribute [local instance] optionBFSMarginalInsideEq optionBFSMarginalShellEq
  optionBFSMarginalOutsideEq optionBFSMarginalInsideFintype optionBFSMarginalOutsideFintype
universe u v
variable {O : Type u} {C : Type v} [Fintype O] [Fintype C] [Nonempty C]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _

omit [Nonempty C] in
/-- Each actual three-part child remains in the specified family. -/
theorem childSplit_mem (F : PinningFamily.{u, v} C)
    {I : PinningData (Option O) C} (hI : F.contains I) (a : C) (k : ℕ) :
    F.contains (childSplit I a k) :=
  F.relabel_mem (F.optionChild_mem hI a) (childEquiv I.graph k)

omit [Nonempty C] in
/-- The external analytic logs need induction only on family members:
actual exteriors and their single-vertex unpinnings. -/
theorem childSplit_exterior_response_logs (F : PinningFamily.{u, v} C)
    (I : PinningData (Option O) C) (hI : F.contains I) (a : C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (k : ℕ)
    (hs : Nonempty (BFS.Shell I.graph none k))
    {x : ℂ} {ε α : ℝ} (hε : 0 < ε)
    (hNZ : F.SmallerPartitionsNonzero Δ (Fintype.card (Option O)) x ε)
    (hRoot : F.SmallerRootResponses Δ (Fintype.card (Option O)) x ε α) :
    ∃ h : (BFS.Shell I.graph none k → C) → ℂ → ℂ,
      (∀ ξ, h ξ x = 0) ∧
      (∀ ξ, DifferentiableOn ℂ (h ξ) (Metric.ball x ε)) ∧
      (∀ ξ, ∀ z ∈ Metric.ball x ε, Complex.exp (h ξ z) =
        exteriorPartition (childSplit I a k) z ξ /
          exteriorPartition (childSplit I a k) x ξ) ∧
      ∀ z ∈ Metric.ball x ε, ∀ ξ ξ', ‖h ξ z - h ξ' z‖ ≤ α * ham ξ ξ' := by
  have hm := F.childSplit_mem hI a k
  have hsep := childSplit_separates I a k
  have hdegree := childSplit_degreeBound I a k hd
  have hnz (ξ : BFS.Shell I.graph none k → C) (z : ℂ) (hz : z ∈ Metric.ball x ε) :
      exteriorPartition (childSplit I a k) z ξ ≠ 0 := by
    rw [exteriorPartition_eq_pinningProductPartition _ hsep]
    exact hNZ (exteriorData (childSplit I a k) ξ) (F.exterior_mem hm ξ)
      (exteriorData_degreeBound _ hsep hdegree ξ) (outside_card_lt_parent I.graph k) z hz
  obtain ⟨h, hzero, hdiff, hexp⟩ := exists_exterior_response_logs _ hsep hε hnz
  refine ⟨h, hzero, hdiff, hexp, ?_⟩
  apply exterior_logs_lipschitz_of_actual_repinning_responses _ hsep hε h hzero hdiff hexp
  intro ξ s
  exact hRoot (unpinnedExteriorData (childSplit I a k) ξ s) (F.unpinnedExterior_mem hm ξ s)
    (unpinnedExterior_degreeBound _ hdegree ξ s) (unpinOutside_card_lt_parent I.graph k hs)

/-- A real coupling bound for the two actual children closes one full
large-component response step. All exterior hypotheses concern strictly
smaller actual instances, and the local input is the controlled principal
logarithm of the actual bounded inside polynomial. -/
theorem positive_bfs_response_step
    (F : PinningFamily.{u, v} C) (I : PinningData (Option O) C)
    (hI : F.contains I) (a b : C) {Δ L B : ℕ}
    (hd : I.DegreeBound Δ) (hL : 0 < L)
    (hB : (∑ j ∈ Finset.range (L + 2), Δ ^ j) ≤ B)
    (hlarge : B < Fintype.card (RootComponent I.graph))
    {x ε α cost : ℝ} (hx : 0 < x) (hε : 0 < ε)
    (ha : 0 ≤ α) (hα1 : α ≤ 1) (hαB : α * (B : ℝ) ≤ 1 / 8)
    (hcost : 64 * cost ≤ (L : ℝ))
    (hCI : W ham
      ((optionChildData I a).gibbs x hx.le
        ((optionChildData I a).partition_pos_of_parameter_pos hx))
      ((optionChildData I b).gibbs x hx.le
        ((optionChildData I b).partition_pos_of_parameter_pos hx)) ≤ cost)
    (hNZ : F.SmallerPartitionsNonzero Δ (Fintype.card (Option O)) (x : ℂ) ε)
    (hRoot : F.SmallerRootResponses Δ (Fintype.card (Option O)) (x : ℂ) ε α)
    (hLocal : ∀ {U S E : Type u} [Fintype U] [Fintype S] [Fintype E]
      (J : PinningData (Separator.Vertex U S E) C), J.DegreeBound Δ →
      Fintype.card U + Fintype.card S ≤ B → ∀ ξ : S → C,
      PrincipalResponseControl (fun z => insidePartition J z ξ) (x : ℂ) ε (α / 8)) :
    HasSmallResponseLog (pinningProductPartition (optionChildData I a))
      (pinningProductPartition (optionChildData I b)) (x : ℂ) ε α := by
  obtain ⟨k, hk, hkL, hW⟩ := exists_low_childGibbsShellLaw_of_ci I a b x hx.le
    ((optionChildData I a).partition_pos_of_parameter_pos hx)
    ((optionChildData I b).partition_pos_of_parameter_pos hx) hL hCI
  have hs := shell_nonempty_of_component_card_gt_bound I Δ (L + 1) B hd
    (by simpa only [Nat.add_assoc] using hB) hlarge k (by omega)
  have hcard := inside_shell_card_le_bound I hd hB k hkL
  have hda := childSplit_degreeBound I a k hd
  have hdb := childSplit_degreeBound I b k hd
  have hsa := childSplit_separates I a k
  have hsb := childSplit_separates I b k
  obtain ⟨h, hzero, hdiff, hexp, hlip⟩ :=
    F.childSplit_exterior_response_logs I hI a hd k hs hε hNZ hRoot
  let eta := fun ξ => principalResponseLog (fun z => insidePartition (childSplit I a k) z ξ) (x : ℂ)
  let theta := fun ξ => principalResponseLog (fun z => insidePartition (childSplit I b k) z ξ) (x : ℂ)
  have heta (ξ : BFS.Shell I.graph none k → C) := hLocal _ hda hcard ξ
  have htheta (ξ : BFS.Shell I.graph none k → C) := hLocal _ hdb hcard ξ
  have hosc (z : ℂ) (hz : z ∈ Metric.ball (x : ℂ) ε)
      (ξ ξ' : BFS.Shell I.graph none k → C) : ‖h ξ z - h ξ' z‖ ≤ (1 / 8 : ℝ) := by
    apply (hlip z hz ξ ξ').trans
    apply le_trans (mul_le_mul_of_nonneg_left (ham_le_card ξ ξ') ha)
    have hsB : Fintype.card (BFS.Shell I.graph none k) ≤ B := by omega
    have hsB' : (Fintype.card (BFS.Shell I.graph none k) : ℝ) ≤ B := by exact_mod_cast hsB
    apply le_trans (mul_le_mul_of_nonneg_left hsB' ha)
    exact hαB
  have hcommon (ξ : BFS.Shell I.graph none k → C) :
      exteriorData (childSplit I a k) ξ = exteriorData (childSplit I b k) ξ :=
    (childSplit_exterior_eq_parent I a k ξ).trans (childSplit_exterior_eq_parent I b k ξ).symm
  have hdelta : α / 8 ∈ Set.Icc 0 (1 / 8 : ℝ) := ⟨by positivity, by linarith⟩
  obtain ⟨_, ℓ, hℓzero, hℓdiff, hℓexp, hℓbound⟩ :=
    exists_positive_separator_quotient_log (childSplit I a k) (childSplit I b k)
      hsa hsb hcommon hx ha hdelta h eta theta hdiff
      (fun ξ => (heta ξ).2.1) (fun ξ => (htheta ξ).2.1)
      hzero (fun ξ => (heta ξ).1) (fun ξ => (htheta ξ).1)
      (fun z hz ξ => hexp ξ z hz)
      (fun z hz ξ => (heta ξ).2.2.1 z hz) (fun z hz ξ => (htheta ξ).2.2.1 z hz)
      hlip hosc (fun z hz ξ => (heta ξ).2.2.2 z hz) (fun z hz ξ => (htheta ξ).2.2.2 z hz)
  refine ⟨ℓ, hℓzero, hℓdiff, ?_, ?_⟩
  · intro z hz
    simpa only [childSplit_partition] using hℓexp z hz
  · intro z hz
    apply (hℓbound z hz).trans
    apply positive_shell_budget_closes hL hcost ha _ le_rfl
    simpa only [childGibbsShellLaw] using hW


private theorem ham_update_le_one {V D : Type*} [Fintype V] [DecidableEq V] [DecidableEq D]
    (σ : V → D) (u : V) (c : D) : ham (Function.update σ u c) σ ≤ 1 := by
  have hc : (Finset.univ.filter fun w => Function.update σ u c w ≠ σ w).card ≤ 1 := by
    calc
      _ ≤ ({u} : Finset V).card := Finset.card_le_card (by
        intro w hw
        by_contra hwu
        have hn : w ≠ u := by simpa only [Finset.mem_singleton] using hwu
        exact (Finset.mem_filter.mp hw).2 (Function.update_of_ne hn _ _))
      _ = 1 := Finset.card_singleton u
  unfold ham hamCard
  exact_mod_cast hc

/-- A genuine hard one-root response bound for the large-component
branch. The hypotheses contain only smaller-instance induction statements,
an actual Gibbs transportation bound, and graph-independent scalar budgets.
The colour assumption is exactly `Δ + 1 ≤ q`. -/
theorem hard_bfs_response_step
    (F : PinningFamily.{u, v} C) (I : PinningData (Option O) C)
    (hI : F.contains I) (a b : C) {Δ L B : ℕ}
    (hd : I.DegreeBound Δ) (hq : Δ + 1 ≤ Fintype.card C) (hL : 0 < L)
    (hB : (∑ j ∈ Finset.range (L + 2), Δ ^ j) ≤ B)
    (hlarge : B < Fintype.card (RootComponent I.graph))
    {r alpha cost : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ (1 / 16 : ℝ))
    (haB : alpha * B ≤ (1 / 16 : ℝ)) (hcost : 64 * cost ≤ (L : ℝ))
    (hCI : W ham
      ((optionChildData I a).gibbs 0 le_rfl
        (partition_zero_pos_of_succ_le _ (optionChildData_degreeBound I hd a) hq))
      ((optionChildData I b).gibbs 0 le_rfl
        (partition_zero_pos_of_succ_le _ (optionChildData_degreeBound I hd b) hq)) ≤ cost)
    (hNZ : F.SmallerPartitionsNonzero Δ (Fintype.card (Option O)) 0 r)
    (hRoot : F.SmallerRootResponses Δ (Fintype.card (Option O)) 0 r alpha)
    (hsmall : (3 / 2 : ℝ) * hardErrorCoefficient (Fintype.card C) Δ B B alpha * r ≤ alpha / 8) :
    HasSmallResponseLog (pinningProductPartition (optionChildData I a))
      (pinningProductPartition (optionChildData I b)) 0 r alpha := by
  obtain ⟨k, hk, hkL, hW⟩ := exists_low_childGibbsShellLaw_of_ci I a b 0 le_rfl _ _ hL hCI
  have hB' : (∑ j ∈ Finset.range (L + 1), Δ ^ j) ≤ B := by
    apply le_trans _ hB
    exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have hs := shell_nonempty_of_component_card_gt_bound I Δ L B hd hB' hlarge k hkL
  have hcard := inside_shell_card_le_bound I hd hB k hkL
  have hU : Fintype.card (Inside I.graph k) ≤ B := by omega
  have hS : Fintype.card (BFS.Shell I.graph none k) ≤ B := by omega
  obtain ⟨h, hh0, hhD, hhE, hhLip⟩ := F.childSplit_exterior_response_logs I hI a hd k hs hr hNZ hRoot
  have hcommon (ξ : BFS.Shell I.graph none k → C) :
      exteriorData (childSplit I a k) ξ = exteriorData (childSplit I b k) ξ := by
    rw [childSplit_exterior_eq_parent, childSplit_exterior_eq_parent]
  obtain ⟨_, H, hH0, hHD, hHE, hHB⟩ := exists_hard_separator_quotient_log
    (childSplit I a k) (childSplit I b k) (childSplit_separates I a k) (childSplit_separates I b k)
    hcommon (childSplit_degreeBound I a k hd) (childSplit_degreeBound I b k hd) hq hU hS
    hr hr1 ha (show alpha / 8 ∈ Set.Icc 0 (1 / 2 : ℝ) by constructor <;> linarith)
    (haB.trans (by norm_num)) hsmall h hhD hh0 (fun z hz ξ => hhE ξ z hz)
    (fun z hz ξ s c => (hhLip z hz (Function.update ξ s c) ξ).trans (by
      exact (mul_le_mul_of_nonneg_left (ham_update_le_one ξ s c) ha).trans_eq (mul_one alpha)))
  refine ⟨H, hH0, hHD, ?_, ?_⟩
  · intro z hz
    simpa only [childSplit_partition] using hHE z hz
  · intro z hz
    apply (hHB z hz).trans
    apply hard_shell_budget_closes hL hcost ha _ (le_refl _)
    exact hW


end
end CI2ZF.Potts.PinningFamily
