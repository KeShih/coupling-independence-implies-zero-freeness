import CI2ZF.Coupling.Girth.Covariance.Insertion.GraphStatistics
import CI2ZF.Coupling.Girth.Covariance.Constants
import CI2ZF.Coupling.Girth.Five.Poincare

/-! All scalar insertion and colour-covariance estimates for the actual
second-layer graph Gibbs model.  The final theorem uses only the graph,
degree, palette and explicit threshold assumptions. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI
open CI2ZF.Potts.Separator
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {U S O C : Type*} [Fintype U] [Fintype S] [Fintype O] [Fintype C]
  [DecidableEq U] [DecidableEq S] [DecidableEq O] [DecidableEq C] [Nonempty C]

namespace InsertionModel
variable {Ω : Type*} [Fintype Ω]

structure CovarianceEstimates (M : InsertionModel Ω U O C) (s : ℝ) (p : CovarianceScale) : Prop where
  atom : ∀ u c ξ, M.pi u c ξ ≤ p.B
  individual_variance : ∀ u c, variance M.shell (M.pi u c) ≤ p.Vπ
  total_variance : ∀ c, variance M.shell (M.centredCavitySum c) ≤ p.VM
  normalizer_pos : ∀ c, 0 < M.T s c
  log_quotient : ∀ c, |Real.log (M.T s c / M.Q s c)| ≤ p.E
  beta_second : ∀ u c, expectReal M.shell (fun ξ => M.beta s u c ξ ^ 2) ≤ p.b ^ 2
  colour_covariance : ColourCovarianceBound M.shell (M.G s) (p.g ^ 2)

end InsertionModel

namespace InsertionGraph
variable (I : PinningData (Vertex U S O) C) (x : ℝ) (hx : 0 < x)

theorem shell_card_le (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    {Δ : ℕ} (hd : I.DegreeBound Δ) (hU : Fintype.card U ≤ Δ) : Fintype.card S ≤ Δ ^ 2 := by
  have hc : Fintype.card S = ∑ u : U, Fintype.card {w : S // owner w = u} := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv owner)).symm
  rw [hc]
  calc
    _ ≤ ∑ _u : U, Δ := Finset.sum_le_sum fun u _ => owner_fibre_card_le I owner howner hd u
    _ = Fintype.card U * Δ := by simp
    _ ≤ Δ * Δ := Nat.mul_le_mul_right Δ hU
    _ = _ := (pow_two _).symm

theorem estimates_of_poincare (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hU : Fintype.card U ≤ Δ) (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ))
    (hP : ∀ f, covarianceGamma p.δ * variance (I.gibbs x hx.le hZ) f ≤
      ∑ v, expectReal (I.gibbs x hx.le hZ)
        (GraphHeatBath.localVariance I x hx (positive_sitePartition I x hx) v f)) :
    (model I x hx c₀ hZ).CovarianceEstimates (1-x) p := by
  let M := model I x hx c₀ hZ
  have hm : p.m = (Fintype.card C : ℝ) - Δ := by rw [CovarianceScale.m, hpq, hpΔ]
  have hL : p.L = (1 + Real.sqrt ((Fintype.card C : ℝ) / (p.m+1))) / p.m := by
    rw [CovarianceScale.L, hpq]
  have hVπ : p.Vπ = (Δ : ℝ) * (1/p.m) *
      ((1 + Real.sqrt ((Fintype.card C : ℝ) / (p.m+1))) / p.m) ^ 2 / covarianceGamma p.δ := by
    rw [CovarianceScale.Vπ, hpΔ, CovarianceScale.B, hL]
  have hVM : p.VM = (Δ : ℝ) ^ 2 * (1/p.m) *
      ((1 + Real.sqrt ((Fintype.card C : ℝ) / (p.m+1))) / p.m) ^ 2 / covarianceGamma p.δ := by
    rw [CovarianceScale.VM, hpΔ, hVπ]
    ring
  have hsize : (Fintype.card S : ℝ) ≤ (Δ : ℝ) ^ 2 := by
    exact_mod_cast shell_card_le I owner howner hd hU
  have hdeg : (Fintype.card U : ℝ) ≤ p.Δ := by rw [hpΔ]; exact_mod_cast hU
  have hcap (u : U) (c : C) (ξ : S → C) : M.pi u c ξ ≤ p.B := by
    change (GraphHeatBath.siteLaw I x hx.le (positive_sitePartition I x hx)
      (join (fun _ => c₀) ξ (fun _ => c₀)) (Sum.inl u)).w c ≤ 1/p.m
    exact GraphHeatBath.siteLaw_atom_le I x hx (positive_sitePartition I x hx) hx1 hd p.m_pos hm.le _ _ c
  have hπ (u : U) (c : C) : variance M.shell (M.pi u c) ≤ p.Vπ := by
    rw [hVπ]
    exact pi_variance I x hx hi hs c₀ hZ hx1 hd p.m_pos hm.le p.gamma_pos owner howner hP u c
  have hsum (c : C) : variance M.shell (M.centredCavitySum c) ≤ p.VM := by
    rw [hVM]
    exact centredCavitySum_variance I x hx hi hs c₀ hZ hx1 hd p.m_pos hm.le p.gamma_pos
      hsize owner howner hP c
  have hB1 : p.B < 1 := by linarith [p.B_le_half]
  have hD : p.D = p.Δ * p.B ^ 2 / (2 * (1-p.B)) := by
    unfold CovarianceScale.D CovarianceScale.a
    field_simp [(sub_pos.mpr hB1).ne']
  have hβ (u : U) (c : C) : expectReal M.shell (fun ξ => M.beta (1-x) u c ξ ^ 2) ≤ p.b ^ 2 := by
    have h := M.insertion_beta_mean_square c (s := 1-x) (by linarith) (by linarith) p.B_pos.le hB1 hdeg
      (fun u ξ => hcap u c ξ) (fun u => hπ u c) (hsum c) u
    simpa only [CovarianceScale.b, CovarianceScale.a, hD] using h
  refine ⟨hcap, hπ, hsum, ?_, ?_, hβ, ?_⟩
  · intro c
    exact M.insertion_T_pos c (s := 1-x) (by linarith) (by linarith) p.B_pos.le hB1 hdeg (fun u ξ => hcap u c ξ)
  · intro c
    have h := M.insertion_log_quotient c (s := 1-x) (by linarith) (by linarith) p.B_pos.le hB1 hdeg
      (fun u ξ => hcap u c ξ) (hsum c)
    simpa only [CovarianceScale.E, hD] using h
  · have h := residual_colour_covariance I x hx hi hs c₀ hZ hx1 hd p.m_pos hm.le p.gamma_pos
      hsize owner howner hP hβ
    have he : p.g ^ 2 = ((Δ : ℝ) ^ 2 * (1/p.m) *
        ((1 + Real.sqrt ((Fintype.card C : ℝ) / (p.m+1))) / p.m) ^ 2 / covarianceGamma p.δ) * p.b ^ 2 := by
      rw [CovarianceScale.g, mul_pow, Real.sq_sqrt p.VM_nonneg, hVM]
    rwa [he]

/-- The Poincaré premise in the preceding finite algebra is discharged
by the proved girth-five graph spectral theorem. -/
theorem actual_estimates (hi : Independent I) (hs : Separates I) (c₀ : C)
    (hZ : 0 < I.partition x) (hx1 : x ≤ 1) {Δ : ℕ} (hd : I.DegreeBound Δ)
    (hU : Fintype.card U ≤ Δ) (owner : S → U)
    (howner : ∀ w u, I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inl w)) ↔ u = owner w)
    (p : CovarianceScale) (hpΔ : p.Δ = (Δ : ℝ)) (hpq : p.q = (Fintype.card C : ℝ))
    (hδ1 : p.δ ≤ 1) (hthreshold : girthFiveThreshold p.δ ≤ Δ) (hg : 5 ≤ I.graph.egirth) :
    (model I x hx c₀ hZ).CovarianceEstimates (1-x) p := by
  apply estimates_of_poincare I x hx hi hs c₀ hZ hx1 hd hU owner howner p hpΔ hpq
  intro f
  have hcol : (1+p.δ) * (Δ : ℝ) ≤ Fintype.card C := by
    have hh := p.colour_budget
    rw [hpΔ, hpq] at hh
    nlinarith
  have h := girth_five_positive_poincare I hx hx1 p.delta_pos hδ1 hthreshold hd hg hcol hZ f
  have he := GraphHeatBath.dirichlet_eq_localVariances I x hx
    (positive_sitePartition I x hx) hZ f
  rw [← he]
  exact h

end InsertionGraph
end
end CI2ZF.Appendix.Girth
