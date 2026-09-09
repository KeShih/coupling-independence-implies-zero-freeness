import CI2ZF.Coupling.Edge.Coupling
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.RealVectorSpace

/-! Finite transport attainment and the exposure table at the Wasserstein
level. Compactness supplies actual minimizing couplings, so finite slot
conditioning can use the table without an unproved optimality assumption. -/
namespace CI2ZF.Appendix.Edge
open PottsCI PottsCI.FinDist
open scoped BigOperators
noncomputable section
variable {S T J : Type*} [Fintype S] [Fintype T] [Fintype J]

private def couplingMatrices (μ : FinDist S) (ν : FinDist T) : Set (S → T → ℝ) :=
  {m | (∀ x y, 0 ≤ m x y) ∧ (∀ x, ∑ y, m x y = μ.w x) ∧ (∀ y, ∑ x, m x y = ν.w y)}

private lemma couplingMatrices_isClosed (μ : FinDist S) (ν : FinDist T) :
    IsClosed (couplingMatrices μ ν) := by
  have hnonneg : IsClosed {m : S → T → ℝ | ∀ x y, 0 ≤ m x y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_le continuous_const ((continuous_apply y).comp (continuous_apply x))
  have hrow : IsClosed {m : S → T → ℝ | ∀ x, ∑ y, m x y = μ.w x} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_eq
      (continuous_finsetSum _ fun y _ => (continuous_apply y).comp (continuous_apply x)) continuous_const
  have hcol : IsClosed {m : S → T → ℝ | ∀ y, ∑ x, m x y = ν.w y} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun y => isClosed_eq
      (continuous_finsetSum _ fun x _ => (continuous_apply y).comp (continuous_apply x)) continuous_const
  exact hnonneg.inter (hrow.inter hcol)

private lemma couplingMatrices_subset_box (μ : FinDist S) (ν : FinDist T) :
    couplingMatrices μ ν ⊆ Set.Icc (0 : S → T → ℝ) 1 := by
  intro m hm
  constructor
  · exact hm.1
  · intro x y
    have hs := Finset.single_le_sum (s := Finset.univ) (f := m x)
      (fun z _ => hm.1 x z) (Finset.mem_univ y)
    rw [hm.2.1 x] at hs
    exact hs.trans (μ.le_one x)

/-- Every finite real transport problem attains its infimum. -/
theorem exists_optimal_coupling (μ : FinDist S) (ν : FinDist T) (d : S → T → ℝ)
    (hd : ∀ x y, 0 ≤ d x y) : ∃ π : Coupling μ ν, π.cost d = W d μ ν := by
  have hc : IsCompact (couplingMatrices μ ν) :=
    isCompact_Icc.of_isClosed_subset (couplingMatrices_isClosed μ ν) (couplingMatrices_subset_box μ ν)
  have hne : (couplingMatrices μ ν).Nonempty :=
    ⟨(Coupling.prod μ ν).w, (Coupling.prod μ ν).nonneg,
      (Coupling.prod μ ν).sum_row, (Coupling.prod μ ν).sum_col⟩
  let cost : (S → T → ℝ) → ℝ := fun m => ∑ x, ∑ y, m x y * d x y
  have hcost : Continuous cost := by
    apply continuous_finsetSum
    intro x _
    apply continuous_finsetSum
    intro y _
    exact ((continuous_apply y).comp (continuous_apply x)).mul_const _
  obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hne hcost.continuousOn
  let π : Coupling μ ν := ⟨m, hm.1, hm.2.1, hm.2.2⟩
  refine ⟨π, le_antisymm ?_ (W_le_cost hd π)⟩
  apply le_W
  intro κ
  exact hmin ⟨κ.nonneg, κ.sum_row, κ.sum_col⟩

/-- The finite exposure table accepts Wasserstein bounds and constructs
an actual full coupling realizing the resulting bound. -/
theorem W_exposure_le (μ ν μ₀ : FinDist S) (μj νj : J → FinDist S)
    (ρ σ : J → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (hσ : ∀ j, 0 ≤ σ j)
    (hμ : ∀ x, μ₀.w x + ∑ j, ρ j * (μj j).w x = (1 + ∑ j, ρ j) * μ.w x)
    (hν : ∀ x, μ₀.w x + ∑ j, σ j * (νj j).w x = (1 + ∑ j, σ j) * ν.w x)
    (d : S → S → ℝ) (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    {t : ℝ} (ht : 0 ≤ t)
    (hm : ∀ j, W d (μj j) (νj j) ≤ 1 + t)
    (hl : ∀ j, W d (μj j) ν ≤ 1 + 2 * t)
    (hr : ∀ j, W d μ (νj j) ≤ 1 + 2 * t) :
    W d μ ν ≤ exposureBudget ρ σ / (1 + exposureBudget ρ σ) * (1 + 2 * t) := by
  classical
  choose πm hπm using fun j => exists_optimal_coupling (μj j) (νj j) d hd
  choose πl hπl using fun j => exists_optimal_coupling (μj j) ν d hd
  choose πr hπr using fun j => exists_optimal_coupling μ (νj j) d hd
  let π₀ := Coupling.diag μ₀
  have hc : π₀.cost d = 0 := by
    simp [π₀, Coupling.cost, Coupling.diag, hd0]
  apply (W_le_cost hd (exposureCoupling μ ν μ₀ μ₀ μj νj ρ σ hρ hσ hμ hν π₀ πm πl πr)).trans
  exact exposureCoupling_cost_le μ ν μ₀ μ₀ μj νj ρ σ hρ hσ hμ hν π₀ πm πl πr d ht hc
    (fun j => (hπm j).trans_le (hm j)) (fun j => (hπl j).trans_le (hl j))
    (fun j => (hπr j).trans_le (hr j))

private lemma weighted_bound_on_support {c a b : ℝ} (hc : 0 ≤ c)
    (h : 0 < c → a ≤ b) : c * a ≤ c * b := by
  rcases eq_or_lt_of_le hc with rfl | hp
  · simp
  · exact mul_le_mul_of_nonneg_left (h hp) hp.le

/-- Zero-mass exposure events need no conditional-cost hypothesis. -/
theorem W_exposure_le_supported (μ ν μ₀ : FinDist S) (μj νj : J → FinDist S)
    (ρ σ : J → ℝ) (hρ : ∀ j, 0 ≤ ρ j) (hσ : ∀ j, 0 ≤ σ j)
    (hμ : ∀ x, μ₀.w x + ∑ j, ρ j * (μj j).w x = (1 + ∑ j, ρ j) * μ.w x)
    (hν : ∀ x, μ₀.w x + ∑ j, σ j * (νj j).w x = (1 + ∑ j, σ j) * ν.w x)
    (d : S → S → ℝ) (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    {t : ℝ} (ht : 0 ≤ t)
    (hm : ∀ j, 0 < ρ j → 0 < σ j → W d (μj j) (νj j) ≤ 1 + t)
    (hl : ∀ j, 0 < ρ j → W d (μj j) ν ≤ 1 + 2 * t)
    (hr : ∀ j, 0 < σ j → W d μ (νj j) ≤ 1 + 2 * t) :
    W d μ ν ≤ exposureBudget ρ σ / (1 + exposureBudget ρ σ) * (1 + 2 * t) := by
  classical
  choose πm hπm using fun j => exists_optimal_coupling (μj j) (νj j) d hd
  choose πl hπl using fun j => exists_optimal_coupling (μj j) ν d hd
  choose πr hπr using fun j => exists_optimal_coupling μ (νj j) d hd
  let π₀ := Coupling.diag μ₀
  have hc : π₀.cost d = 0 := by simp [π₀, Coupling.cost, Coupling.diag, hd0]
  apply (W_le_cost hd (exposureCoupling μ ν μ₀ μ₀ μj νj ρ σ hρ hσ hμ hν π₀ πm πl πr)).trans
  rw [exposureCoupling_cost, hc, zero_add, div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by have := exposureBudget_nonneg ρ σ hρ; linarith)
  calc
    _ ≤ ∑ j, (min (ρ j) (σ j) * (1 + t) + |ρ j - σ j| * (1 + 2 * t)) := by
      apply Finset.sum_le_sum
      intro j _
      have hm' := weighted_bound_on_support (le_min (hρ j) (hσ j)) (fun hp =>
        (hπm j).trans_le (hm j (hp.trans_le (min_le_left _ _)) (hp.trans_le (min_le_right _ _))))
      have hl' := weighted_bound_on_support (le_max_right (ρ j - σ j) 0) (fun hp =>
        (hπl j).trans_le (hl j (by
          have hh : 0 < ρ j - σ j := (lt_max_iff.mp hp).resolve_right (lt_irrefl _)
          linarith [hσ j])))
      have hr' := weighted_bound_on_support (le_max_right (σ j - ρ j) 0) (fun hp =>
        (hπr j).trans_le (hr j (by
          have hh : 0 < σ j - ρ j := (lt_max_iff.mp hp).resolve_right (lt_irrefl _)
          linarith [hρ j])))
      have hp : max (ρ j - σ j) 0 + max (σ j - ρ j) 0 = |ρ j - σ j| := by
        rcases le_total (ρ j) (σ j) with hh | hh
        · rw [max_eq_right (sub_nonpos.mpr hh), max_eq_left (sub_nonneg.mpr hh),
            abs_of_nonpos (sub_nonpos.mpr hh)]; ring
        · rw [max_eq_left (sub_nonneg.mpr hh), max_eq_right (sub_nonpos.mpr hh),
            abs_of_nonneg (sub_nonneg.mpr hh), add_zero]
      nlinarith [hp]
    _ ≤ _ := exposure_cost_numerator_bound ρ σ hρ hσ ht

end
end CI2ZF.Appendix.Edge
