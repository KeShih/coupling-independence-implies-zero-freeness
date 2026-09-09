import CI2ZF.Holant.CouplingInstance
import CI2ZF.Holant.CouplingZero

/-!
# Degenerate branches of the Holant recursive coupling

An isolated disagreeing vertex changes only a scalar.  An edge whose
selected child is structurally zero can be deleted without changing either
law.  These exact identities handle hard signature zeros in the recursion.
-/

namespace CI2ZF.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist Holant

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem normalizeWeights_eq_of_scale {S : Type*} [Fintype S]
    (a b : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (hZa : 0 < ∑ s, a s) (hZb : 0 < ∑ s, b s) (c : ℝ) (hc : 0 < c)
    (hab : ∀ s, b s = c * a s) :
    normalizeWeights b hb hZb = normalizeWeights a ha hZa := by
  ext s
  simp only [normalizeWeights_apply, hab, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc.ne'

theorem selectedDegree_eq_zero_of_isolated (inc : E → V → Prop) (edges : Finset E)
    (v : V) (hiso : edges.filter (fun e => inc e v) = ∅)
    (S : Finset E) (hS : S ⊆ edges) : selectedDegree inc S v = 0 := by
  unfold selectedDegree
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  have h : e ∈ edges.filter (fun e => inc e v) := by
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
  rw [hiso] at h
  exact Finset.notMem_empty _ h

theorem signatureGibbs_shift_isolated (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (v : V) (hf1 : 0 < (f v).value 1)
    (hiso : edges.filter (fun e => inc e v) = ∅) :
    signatureGibbs inc edges (shiftFamily f v hf1) x hx =
      signatureGibbs inc edges f x hx := by
  rw [signatureGibbs_shift]
  unfold signatureGibbs gibbs
  apply normalizeWeights_eq_of_scale _ _ _ _ _ _ ((f v).value 1 / (f v).value 0)
    (div_pos hf1 (f v).zero_pos)
  intro S
  rw [restrictedWeight_shift_factor, restrictedWeight_factor inc edges _ x v S]
  by_cases hS : S ⊆ edges
  · rw [selectedDegree_eq_zero_of_isolated inc edges v hiso S hS]
    simp only [zero_add]
    field_simp [(f v).zero_pos.ne']
  · simp [exteriorWeight, hS]

theorem restrictedWeight_dead_shift (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E)
    (hdead : ∃ v, inc e v ∧ ∀ k, f v (k + 1) = 0) (S : Finset E) :
    restrictedWeight inc edges (shiftedSignature inc f e) x S = 0 := by
  obtain ⟨v, hv, hf⟩ := hdead
  have hprod : signatureWeight inc (shiftedSignature inc f e) S = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [shiftedSignature, hv, hf]
  simp [restrictedWeight, weight, hprod]

/-- A structurally impossible selected child can be deleted exactly. -/
theorem gibbs_delete_dead (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges)
    (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, 0 < f v 0)
    (hx : ∀ a ∈ edges, 0 ≤ x a)
    (hdead : ∃ v, inc e v ∧ ∀ k, f v (k + 1) = 0) :
    gibbs inc edges f x hf hf0 hx =
      gibbs inc (edges.erase e) f x hf hf0
        (fun a ha => hx a (Finset.mem_of_mem_erase ha)) := by
  have hZ : partition inc edges f x = partition inc (edges.erase e) f x := by
    rw [partition_deletion inc edges f x e he,
      shifted_partition_zero inc (edges.erase e) f x e hdead, mul_zero, add_zero]
  ext S
  simp only [gibbs_apply, hZ]
  congr 1
  have h := restrictedWeight_deletion inc edges f x e he S
  simpa only [restrictedWeight_dead_shift inc (edges.erase e) f x e hdead,
    ite_self, mul_zero, add_zero] using h

theorem signatureGibbs_delete_dead (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ a ∈ edges, 0 ≤ x a)
    (e : E) (he : e ∈ edges) (u : V) (hu : inc e u) (hdead : (f u).value 1 = 0) :
    signatureGibbs inc edges f x hx =
      signatureGibbs inc (edges.erase e) f x
        (fun a ha => hx a (Finset.mem_of_mem_erase ha)) :=
  gibbs_delete_dead inc edges _ x e he (fun v => (f v).nonneg)
    (fun v => (f v).zero_pos) hx
    ⟨u, hu, fun k => (f u).zero_of_zero_le hdead (by omega)⟩

@[simp] theorem zeroOn_empty (μ : FinDist (Finset E)) : zeroOn μ ∅ = 1 := by
  simp [zeroOn, μ.sum_one]

theorem incident_erase (inc : E → V → Prop) (edges : Finset E) (e : E) (v : V) :
    (edges.erase e).filter (fun a => inc a v) = (edges.filter (fun a => inc a v)).erase e := by
  ext a
  simp [and_assoc]

theorem signatureGibbs_zeroOn_erase (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ a ∈ edges, 0 ≤ x a)
    (e : E) (v : V) (he : e ∈ edges.filter (fun a => inc a v)) :
    zeroOn (signatureGibbs inc (edges.erase e) f x
      (fun a ha => hx a (Finset.mem_of_mem_erase ha))) (edges.filter (fun a => inc a v)) =
      zeroOn (signatureGibbs inc (edges.erase e) f x
        (fun a ha => hx a (Finset.mem_of_mem_erase ha)))
        ((edges.erase e).filter (fun a => inc a v)) := by
  rw [incident_erase]
  exact zeroOn_erase_of_absent _ _ e he
    (gibbs_no_edge inc (edges.erase e) _ x _ _ _ e (Finset.notMem_erase e edges))

/-- The exact all-zero probability retained by the `00` recursion branch. -/
theorem signatureGibbs_zeroOn_edge_mix (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ a ∈ edges, 0 ≤ x a)
    (e : E) (v : V) (he : e ∈ edges.filter (fun a => inc a v))
    (hfirst : ∀ w, inc e w → 0 < (f w).value 1) :
    zeroOn (signatureGibbs inc edges f x hx) (edges.filter (fun a => inc a v)) =
      (1 - occupiedProbability inc edges (fun w => (f w).value) x e) *
        zeroOn (signatureGibbs inc (edges.erase e) f x
          (fun a ha => hx a (Finset.mem_of_mem_erase ha)))
          ((edges.erase e).filter (fun a => inc a v)) := by
  rw [signatureGibbs_edge_mix inc edges f x hx e (Finset.mem_filter.mp he).1 hfirst]
  simp only [signatureGibbs]
  rw [zeroOn_bernoulli_delete _ _ _ e he
    (gibbs_no_edge inc (edges.erase e) _ x _ _ _ e (Finset.notMem_erase e edges)),
    incident_erase]

end

end CI2ZF.HolantCoupling
