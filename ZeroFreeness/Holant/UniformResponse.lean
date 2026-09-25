import ZeroFreeness.Holant.AmbientGraph
import ZeroFreeness.Holant.ShellCostSelection
import ZeroFreeness.Holant.CouplingTheorem
import ZeroFreeness.Holant.InductiveExterior
import ZeroFreeness.Holant.SeparatorEstimates
import ZeroFreeness.Holant.SeparatorResponse
import ZeroFreeness.Holant.ShellMarginals

/-! The actual, uniform response step. The real coupling selects an ambient
sphere, smaller residual instances give its exterior logarithms, and the
finite coefficient estimates close the complex response bound. -/
namespace ZeroFreeness.Holant
open Finset Set Metric PottsCI PottsCI.FinDist HolantCoupling
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem uniform_response_step (G : SimpleGraph V) (F : Finset Signature)
    (Δ : ℕ) (hΔ : ∀ v, G.degree v ≤ Δ) {R : ℝ} (hR : 0 ≤ R)
    (pars : TransferParameters (2 * (Δ - 1)) (residualGrowthBound F) R
      (2 * ((1 + (residualCouplingA F) ^ 2 * R) ^ Δ - 1)))
    (H : NormalizedInstance V (Sym2 V)) (hinc : H.incidence = graphIncidence)
    (hE : H.edges ⊆ G.edgeFinset) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (p : ActivityPath H.edges R pars.epsilon)
    (hsmallNZ : ∀ K : NormalizedInstance V (Sym2 V), K.incidence = H.incidence →
      K.edges ⊆ H.edges → K.edges.card < H.edges.card →
      (∀ v, K.signature v ∈ residualFamily F) →
      ∀ t ∈ ball (0 : ℂ) p.radius, K.toInstance.complexPartition (p.activity t) ≠ 0)
    (hsmallResponse : ∀ K : NormalizedInstance V (Sym2 V), K.incidence = H.incidence →
      ∀ hK : K.edges ⊆ H.edges, K.edges.card < H.edges.card →
      (∀ v, K.signature v ∈ residualFamily F) →
      ∀ a (ha : a ∈ K.edges) (hs : K.OneSurvives a),
      ResponseBound K a ha hs (p.restrict hK) pars.alpha)
    (e : Sym2 V) (he : e ∈ H.edges) (hs : H.OneSurvives e) :
    ResponseBound H e he hs p pars.alpha := by
  have hpair : TwoEndpoints H.incidence H.edges := by
    rw [hinc]
    exact (graph_twoEndpoints G).mono hE
  have hdegree : ∀ v, selectedDegree H.incidence H.edges v ≤ Δ := by
    intro v
    rw [hinc]
    exact (selectedDegree_mono graphIncidence hE v).trans
      (by simpa only [selectedDegree_graph] using hΔ v)
  let hx : ∀ a ∈ H.edges.erase e, 0 ≤ p.base a :=
    fun a ha => (p.realBox a (mem_of_mem_erase ha)).1
  let μ := signatureGibbs H.incidence (H.edges.erase e) (H.zeroChild e).signature p.base hx
  let ν := signatureGibbs H.incidence (H.edges.erase e) (H.oneChild e he hs).signature p.base hx
  have hCI : W subsetHam μ ν ≤ 2 * ((1 + (residualCouplingA F) ^ 2 * R) ^ Δ - 1) :=
    residual_family_sharp_child_W_le F H hF p.base R Δ hR p.realBox hpair hdegree e he hs
  obtain ⟨r, hr, hcost⟩ := exists_low_ambient_shell_cost H (ambientLineGraph G) e μ ν
    pars.layers_pos hCI
  let P := ambientSeparator H (ambientLineGraph G) e he
    (ambientLineGraph_compatible G H hinc hE) r
  have hlocal : (P.shell ∪ P.interior).card ≤ pars.localSize :=
    (ambient_local_card_le H (ambientLineGraph G) e r pars.layers (2 * (Δ - 1)) hr
      (ambientLineGraph_degree_le G Δ hΔ)).trans pars.ball_bound
  obtain ⟨h, hd, hzero, hexp, hlip, hosc⟩ := P.exists_inductive_exterior_logs he F hF
    pars.alpha_pos.le p hsmallNZ hsmallResponse
  obtain ⟨_, hD, hbudget, hshell⟩ := P.separator_estimates he hs F hF pars hR hlocal
    (fun a ha => hpair.card_eq_two a ha) p
  have hW : W (fun ξ η : P.State => subsetHam ξ.val η.val)
      (P.law he hs true p.base hx) (P.law he hs false p.base hx) ≤ 1 / 64 := by
    rw [HolantCoupling.W_comm _ _ (fun ξ η : P.State => subsetHam ξ.val η.val)
      (fun ξ η => subsetHam_nonneg ξ.val η.val) (fun ξ η => subsetHam_comm ξ.val η.val)]
    apply (P.W_law_le_intersection he hs p.base hx subsetHam subsetHam_nonneg).trans
    exact hcost.trans pars.coupling_small
  exact P.response_bound_of_exterior_logs he hs p pars.alpha_pos
    (pars.localErrorBound_nonneg (residualGrowthBound_nonneg F) hR)
    (pars.totalErrorBound_nonneg (residualGrowthBound_nonneg F) hR)
    pars.totalErrorBound_small pars.error_small hbudget h hd hzero
    (fun t ht ξ => hexp ξ t ht) hlip
    (fun t ht ξ η => (hosc t ht ξ η).trans hshell)
    (fun b t ht ξ => hD b ξ t ht)
    (fun b ξ => P.exterior_real_le_child he hs b ξ p.base hx) hW

end
end ZeroFreeness.Holant
