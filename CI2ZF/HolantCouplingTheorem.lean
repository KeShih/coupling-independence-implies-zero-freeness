import CI2ZF.HolantCouplingRecursion
import CI2ZF.HolantResidualModel

/-!
# Residual Holant coupling independence

This module supplies the actual normalized child Gibbs laws to the recursive
endpoint comparison.  Truncation outside the current degree is invisible to
the partition sum, and positive vertexwise normalization cancels from every
probability mass.  The final theorem has only the model hypotheses from the
residual-input lemma, with no assumed coupling bound.
-/

namespace CI2ZF.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist Holant

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Scaling signatures by positive vertex constants, with equality required
only at realizable degrees, leaves the normalized Gibbs law unchanged. -/
theorem signatureGibbs_eq_of_scaled_values (inc : E → V → Prop) (edges : Finset E)
    (f g : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (c : V → ℝ) (hc : ∀ v, 0 < c v)
    (hfg : ∀ v k, k ≤ selectedDegree inc edges v → (f v).value k = c v * (g v).value k) :
    signatureGibbs inc edges f x hx = signatureGibbs inc edges g x hx := by
  unfold signatureGibbs gibbs
  apply normalizeWeights_eq_of_scale _ _ _ _ _ _ (∏ v, c v)
    (Finset.prod_pos fun v _ => hc v)
  intro S
  unfold restrictedWeight
  split_ifs with hS
  · have hsig : signatureWeight inc (fun v => (f v).value) S =
        (∏ v, c v) * signatureWeight inc (fun v => (g v).value) S := by
      unfold signatureWeight
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun v _ =>
        hfg v _ (selectedDegree_mono inc hS v)
    simp only [weight, hsig]
    ring
  · ring

theorem signatureGibbs_eq_of_values (inc : E → V → Prop) (edges : Finset E)
    (f g : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (hfg : ∀ v k, k ≤ selectedDegree inc edges v → (f v).value k = (g v).value k) :
    signatureGibbs inc edges f x hx = signatureGibbs inc edges g x hx := by
  apply signatureGibbs_eq_of_scaled_values inc edges f g x hx (fun _ => 1)
    (fun _ => by norm_num)
  simpa only [one_mul] using hfg

/-- The zero-child signature truncation changes no probability mass. -/
theorem normalizedInstance_zero_child_law (H : NormalizedInstance V E) (e : E)
    (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    signatureGibbs H.incidence (H.edges.erase e) (H.zeroChild e).signature x hx =
      signatureGibbs H.incidence (H.edges.erase e) H.signature x hx := by
  apply signatureGibbs_eq_of_values
  intro v k hk
  simp [NormalizedInstance.zeroChild, Signature.normalizedResidual, hk, H.normalized]

/-- The positive scalar removed from the one-child cancels from the Gibbs
law even when the original conditioned edge has activity zero. -/
theorem normalizedInstance_one_child_law (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    signatureGibbs H.incidence (H.edges.erase e)
        (edgeShiftFamily H.incidence H.signature e hs) x hx =
      signatureGibbs H.incidence (H.edges.erase e) (H.oneChild e he hs).signature x hx := by
  apply signatureGibbs_eq_of_scaled_values _ _ _ _ x hx
    (fun v => if H.incidence e v then (H.signature v).value 1 else 1)
  · intro v
    split_ifs with hv
    · exact hs v hv
    · norm_num
  · intro v k hk
    by_cases hv : H.incidence e v
    · simp only [edgeShiftFamily, hv, ↓reduceDIte, shifted_value, ↓reduceIte,
        NormalizedInstance.oneChild, Signature.normalizedResidual, hk]
      simp only [Nat.add_comm 1 k]
      exact (mul_div_cancel₀ ((H.signature v).value (k + 1)) (hs v hv).ne').symm
    · simp [edgeShiftFamily, NormalizedInstance.oneChild, Signature.normalizedResidual,
        hv, hk, H.normalized]

/-- Full residual-input coupling independence for the actual normalized
zero- and one-children, with the exact stated two-endpoint constant. -/
theorem normalizedInstance_child_W_le (H : NormalizedInstance V E)
    (x : E → ℝ) (A R : ℝ) (Δ : ℕ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hx : ∀ e ∈ H.edges, x e ∈ Set.Icc 0 R)
    (hratio : ∀ v k, (H.signature v).value (k + 1) ≤ A * (H.signature v).value k)
    (hpair : TwoEndpoints H.incidence H.edges)
    (hdegree : ∀ v, selectedDegree H.incidence H.edges v ≤ Δ)
    (e : E) (he : e ∈ H.edges) (hs : H.OneSurvives e) :
    W subsetHam
      (signatureGibbs H.incidence (H.edges.erase e) (H.zeroChild e).signature x
        (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1))
      (signatureGibbs H.incidence (H.edges.erase e) (H.oneChild e he hs).signature x
        (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1)) ≤
      2 * ((1 + A ^ 2 * R) ^ Δ - 1) := by
  rw [normalizedInstance_zero_child_law, ← normalizedInstance_one_child_law]
  exact edge_child_W_le H.incidence H.edges H.signature x A R Δ
    hA hR hx hratio hpair hdegree e he hs

/-- A finite residual signature family supplies one graph-size-independent
coupling constant.  All required growth inequalities are derived from its
finite maximum and log-concavity. -/
theorem residual_family_child_W_le (F : Finset Signature) (H : NormalizedInstance V E)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (x : E → ℝ) (R : ℝ) (Δ : ℕ)
    (hR : 0 ≤ R) (hx : ∀ e ∈ H.edges, x e ∈ Set.Icc 0 R)
    (hpair : TwoEndpoints H.incidence H.edges)
    (hdegree : ∀ v, selectedDegree H.incidence H.edges v ≤ Δ)
    (e : E) (he : e ∈ H.edges) (hs : H.OneSurvives e) :
    W subsetHam
      (signatureGibbs H.incidence (H.edges.erase e) (H.zeroChild e).signature x
        (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1))
      (signatureGibbs H.incidence (H.edges.erase e) (H.oneChild e he hs).signature x
        (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1)) ≤
      2 * ((1 + (residualGrowthBound F) ^ 2 * R) ^ Δ - 1) := by
  apply normalizedInstance_child_W_le H x (residualGrowthBound F) R Δ
    (residualGrowthBound_nonneg F) hR hx
  · intro v k
    apply all_ratios_le_of_first
    simpa only [H.normalized, mul_one] using residual_first_le_growthBound F (hF v)
  · exact hpair
  · exact hdegree

/-- Actual simple-graph edges satisfy the incidence hypothesis used above. -/
theorem graph_twoEndpoints (G : SimpleGraph V) :
    TwoEndpoints (graphIncidence : Sym2 V → V → Prop) G.edgeFinset := by
  intro e
  refine Sym2.inductionOn e fun u v => ?_
  intro he
  refine ⟨u, v, ?_, fun w => Sym2.mem_iff⟩
  have h := G.not_isDiag_of_mem_edgeFinset he
  simpa only [Sym2.mk_isDiag_iff] using h

/-- The cardinality formulation used by the bounded-instance geometry gives
exactly the pair-of-distinct-endpoints hypothesis of recursive coupling. -/
theorem twoEndpoints_of_card_two (inc : E → V → Prop) (edges : Finset E)
    (htwo : ∀ e ∈ edges, (Finset.univ.filter (inc e)).card = 2) : TwoEndpoints inc edges := by
  intro e he
  obtain ⟨u, v, huv, hset⟩ := Finset.card_eq_two.mp (htwo e he)
  refine ⟨u, v, huv, fun w => ?_⟩
  have h : inc e w ↔ w ∈ Finset.univ.filter (inc e) := by simp
  rw [hset] at h
  simpa using h

/-- Encoding selected-edge subsets as Boolean configurations preserves the
transport bound with precisely the Hamming metric used in the manuscript. -/
theorem W_boolean_encoding_le (μ ν : FinDist (Finset E)) :
    W ham (mapLaw μ (fun S e => decide (e ∈ S)))
      (mapLaw ν (fun S e => decide (e ∈ S))) ≤ W subsetHam μ ν := by
  have h := W_mapLaw_le_add μ ν (fun S e => decide (e ∈ S))
    (fun S e => decide (e ∈ S)) subsetHam ham ham_nonneg 0
    (fun S T => by rw [← subsetHam_eq_ham]; simp)
  simpa using h

/-- The finite maximum used in the manuscript's explicit coupling constant.
Arity-zero signatures contribute zero because their value at one vanishes. -/
def residualCouplingA (F : Finset Signature) : ℝ :=
  (insert 0 ((residualFamily F).image fun g => g.value 1)).max'
    (Finset.insert_nonempty _ _)

theorem residualCouplingA_nonneg (F : Finset Signature) : 0 ≤ residualCouplingA F :=
  Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem residual_first_le_couplingA (F : Finset Signature) {g : Signature}
    (hg : g ∈ residualFamily F) : g.value 1 ≤ residualCouplingA F := by
  exact Finset.le_max' (insert 0 ((residualFamily F).image fun h => h.value 1))
    (g.value 1) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨g, hg, rfl⟩))

/-- Residual-family coupling independence with the exact finite maximum
`A = max ({0} ∪ {g(1) : g ∈ F_res})` from the body of the paper. -/
theorem residual_family_sharp_child_W_le (F : Finset Signature) (H : NormalizedInstance V E)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (x : E → ℝ) (R : ℝ) (Δ : ℕ)
    (hR : 0 ≤ R) (hx : ∀ e ∈ H.edges, x e ∈ Set.Icc 0 R)
    (hpair : TwoEndpoints H.incidence H.edges)
    (hdegree : ∀ v, selectedDegree H.incidence H.edges v ≤ Δ)
    (e : E) (he : e ∈ H.edges) (hs : H.OneSurvives e) :
    W subsetHam
      (signatureGibbs H.incidence (H.edges.erase e) (H.zeroChild e).signature x
        (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1))
      (signatureGibbs H.incidence (H.edges.erase e) (H.oneChild e he hs).signature x
        (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1)) ≤
      2 * ((1 + (residualCouplingA F) ^ 2 * R) ^ Δ - 1) := by
  apply normalizedInstance_child_W_le H x (residualCouplingA F) R Δ
    (residualCouplingA_nonneg F) hR hx
  · intro v k
    apply all_ratios_le_of_first
    simpa only [H.normalized, mul_one] using residual_first_le_couplingA F (hF v)
  · exact hpair
  · exact hdegree

end

end CI2ZF.HolantCoupling
