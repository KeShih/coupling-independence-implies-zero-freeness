import ZeroFreeness.Holant.CouplingBoundary
import ZeroFreeness.Holant.CouplingSharpZero

/-!
# Recursive endpoint comparison for actual Holant Gibbs distributions
-/

namespace ZeroFreeness.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist Holant

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Every current edge has two distinct endpoints. -/
def TwoEndpoints (inc : E → V → Prop) (edges : Finset E) : Prop :=
  ∀ e ∈ edges, ∃ u v, u ≠ v ∧ ∀ w, inc e w ↔ w = u ∨ w = v

theorem TwoEndpoints.mono {inc : E → V → Prop} {edges edges' : Finset E}
    (h : TwoEndpoints inc edges) (hsub : edges' ⊆ edges) : TwoEndpoints inc edges' :=
  fun e he => h e (hsub he)

theorem TwoEndpoints.card_eq_two {inc : E → V → Prop} {edges : Finset E}
    (h : TwoEndpoints inc edges) (e : E) (he : e ∈ edges) :
    (Finset.univ.filter (inc e)).card = 2 := by
  obtain ⟨u, v, huv, hinc⟩ := h e he
  have heq : Finset.univ.filter (inc e) = {u, v} := by
    ext w
    simp [hinc]
  simp [heq, huv]

theorem TwoEndpoints.card_le_two {inc : E → V → Prop} {edges : Finset E}
    (h : TwoEndpoints inc edges) (e : E) (he : e ∈ edges) :
    (Finset.univ.filter (inc e)).card ≤ 2 := (h.card_eq_two e he).le

theorem TwoEndpoints.other {inc : E → V → Prop} {edges : Finset E}
    (h : TwoEndpoints inc edges) (e : E) (he : e ∈ edges) (v : V) (hv : inc e v) :
    ∃ u, u ≠ v ∧ ∀ w, inc e w ↔ w = u ∨ w = v := by
  obtain ⟨a, b, hab, hinc⟩ := h e he
  rcases (hinc v).mp hv with hva | hvb
  · subst v
    exact ⟨b, hab.symm, fun w => by rw [hinc]; tauto⟩
  · subst v
    exact ⟨a, hab, hinc⟩

def comparisonP (A R : ℝ) (Δ : ℕ) : ℝ := (1 + A ^ 2 * R) ^ Δ

theorem comparisonP_pos {A R : ℝ} (hR : 0 ≤ R) (Δ : ℕ) :
    0 < comparisonP A R Δ := by unfold comparisonP; positivity

theorem signatureGibbs_root_zero_lower (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) {A R : ℝ} (Δ : ℕ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hx : ∀ e ∈ edges, x e ∈ Set.Icc 0 R)
    (hratio : ∀ v k, (f v).value (k + 1) ≤ A * (f v).value k)
    (hpair : TwoEndpoints inc edges) (hdegree : ∀ v, selectedDegree inc edges v ≤ Δ)
    (v : V) :
    1 / comparisonP A R Δ ≤
      zeroOn (signatureGibbs inc edges f x (fun e he => (hx e he).1))
        (edges.filter fun e => inc e v) := by
  have hlocal := Sharp.gibbs_zeroOn_lower inc edges (edges.filter fun e => inc e v)
    (fun v => (f v).value) x hA hR (fun v => (f v).nonneg)
    (fun v => (f v).zero_pos) hx hratio hpair.card_eq_two (Finset.filter_subset _ _)
  have hbase : 1 ≤ 1 + A ^ 2 * R := by nlinarith [mul_nonneg (sq_nonneg A) hR]
  have hp : 0 < (1 + A ^ 2 * R) ^ (edges.filter fun e => inc e v).card := by positivity
  have hpow : (1 + A ^ 2 * R) ^ (edges.filter fun e => inc e v).card ≤
      comparisonP A R Δ := pow_le_pow_right₀ hbase (hdegree v)
  exact (one_div_le_one_div_of_le hp hpow).trans (by simpa [one_div, signatureGibbs] using hlocal)

/-- The strengthened endpoint bound carries the probability of terminating
without a disagreement.  Strong induction is on the actual current edge set. -/
theorem endpoint_strong (inc : E → V → Prop) (A R : ℝ) (Δ : ℕ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∀ (edges : Finset E) (f : V → Signature) (x : E → ℝ)
      (hx : ∀ e ∈ edges, x e ∈ Set.Icc 0 R)
      (_hratio : ∀ v k, (f v).value (k + 1) ≤ A * (f v).value k)
      (_hpair : TwoEndpoints inc edges)
      (_hdegree : ∀ v, selectedDegree inc edges v ≤ Δ)
      (v : V) (hv : 0 < (f v).value 1),
      W subsetHam
          (signatureGibbs inc edges f x (fun e he => (hx e he).1))
          (signatureGibbs inc edges (shiftFamily f v hv) x (fun e he => (hx e he).1)) ≤
        comparisonP A R Δ *
          (1 - zeroOn (signatureGibbs inc edges f x (fun e he => (hx e he).1))
            (edges.filter fun e => inc e v)) := by
  intro edges
  refine Finset.strongInductionOn edges ?_
  intro edges ih f x hx hratio hpair hdegree v hv
  let hx0 : ∀ e ∈ edges, 0 ≤ x e := fun e he => (hx e he).1
  let P := comparisonP A R Δ
  have hP : 0 < P := comparisonP_pos hR Δ
  by_cases hiso : edges.filter (fun e => inc e v) = ∅
  · rw [signatureGibbs_shift_isolated inc edges f x _ v hv hiso]
    simp [W_self subsetHam_nonneg subsetHam_self, hiso]
  obtain ⟨e, heI, horder⟩ := signatureGibbs_exists_ordered_edge inc edges f x hx0 v hv
    (Finset.nonempty_iff_ne_empty.mpr hiso)
  have he : e ∈ edges := (Finset.mem_filter.mp heI).1
  have hev : inc e v := (Finset.mem_filter.mp heI).2
  obtain ⟨u, huv, hinc⟩ := hpair.other e he v hev
  have heu : inc e u := (hinc u).mpr (Or.inl rfl)
  let edges' := edges.erase e
  let hx' : ∀ a ∈ edges', x a ∈ Set.Icc 0 R :=
    fun a ha => hx a (Finset.mem_of_mem_erase ha)
  let hx0' : ∀ a ∈ edges', 0 ≤ x a := fun a ha => (hx' a ha).1
  have hproper : edges' ⊂ edges := Finset.erase_ssubset he
  have hpair' : TwoEndpoints inc edges' := hpair.mono (Finset.erase_subset _ _)
  have hdegree' : ∀ w, selectedDegree inc edges' w ≤ Δ :=
    fun w => (selectedDegree_mono inc (Finset.erase_subset _ _) w).trans (hdegree w)
  have ihStrong (g : V → Signature)
      (hg : ∀ w k, (g w).value (k + 1) ≤ A * (g w).value k)
      (w : V) (hw : 0 < (g w).value 1) :
      W subsetHam (signatureGibbs inc edges' g x hx0')
        (signatureGibbs inc edges' (shiftFamily g w hw) x hx0') ≤
        P * (1 - zeroOn (signatureGibbs inc edges' g x hx0')
          (edges'.filter fun e => inc e w)) :=
    ih edges' hproper g x hx' hg hpair' hdegree' w hw
  have ihBound (g : V → Signature)
      (hg : ∀ w k, (g w).value (k + 1) ≤ A * (g w).value k)
      (w : V) (hw : 0 < (g w).value 1) :
      W subsetHam (signatureGibbs inc edges' g x hx0')
        (signatureGibbs inc edges' (shiftFamily g w hw) x hx0') ≤ P - 1 :=
    root_zero_closes_bound hP
      (signatureGibbs_root_zero_lower inc edges' g x Δ hA hR hx' hg hpair' hdegree' w)
      (ihStrong g hg w hw)
  let fV := shiftFamily f v hv
  have hfV : ∀ w k, (fV w).value (k + 1) ≤ A * (fV w).value k :=
    shiftFamily_ratio_bound f v hv A hratio
  by_cases hu : 0 < (f u).value 1
  · have hfirst : ∀ w, inc e w → 0 < (f w).value 1 := by
      intro w hw
      rcases (hinc w).mp hw with rfl | rfl
      · exact hu
      · exact hv
    let fE := edgeShiftFamily inc f e hfirst
    have hfE : ∀ w k, (fE w).value (k + 1) ≤ A * (fE w).value k :=
      edgeShiftFamily_ratio_bound inc f e hfirst A hratio
    have huV : 0 < (fV u).value 1 := by
      simpa only [fV, shiftFamily_away f v u hv huv] using hu
    have hEeq : fE = shiftFamily fV u huV :=
      edgeShiftFamily_as_other_shift inc f e u v huv hinc hfirst hv huV
    let μ0 := signatureGibbs inc edges' f x hx0'
    let ν0 := signatureGibbs inc edges' fV x hx0'
    let μ1 := signatureGibbs inc edges' fE x hx0'
    let p := occupiedProbability inc edges (fun w => (f w).value) x e
    have hp0 : 0 ≤ p := occupiedProbability_nonneg inc edges _ x e he
      (fun w => (f w).nonneg) (fun w => (f w).zero_pos) hfirst hx0
    have hp1 : p ≤ 1 := occupiedProbability_le_one inc edges _ x e he
      (fun w => (f w).nonneg) (fun w => (f w).zero_pos) hx0
    let K : Bool → FinDist (Finset E) := fun b => if b then mapLaw μ1 (insert e) else μ0
    have hμmix : signatureGibbs inc edges f x hx0 = (bernoulli p hp0 hp1).bind K :=
      signatureGibbs_edge_mix inc edges f x hx0 e he hfirst
    have hz : zeroOn (signatureGibbs inc edges f x hx0) (edges.filter fun e => inc e v) =
        (1 - p) * zeroOn μ0 (edges'.filter fun e => inc e v) :=
      signatureGibbs_zeroOn_edge_mix inc edges f x hx0 e v heI hfirst
    have h00 : W subsetHam μ0 ν0 ≤ P * (1 - zeroOn μ0 (edges'.filter fun e => inc e v)) :=
      ihStrong f hratio v hv
    have h10base : W subsetHam μ1 ν0 ≤ P - 1 := by
      dsimp only [μ1, ν0]
      rw [hEeq, W_comm _ _ subsetHam subsetHam_nonneg subsetHam_comm]
      exact ihBound fV hfV u huV
    have h10 : W subsetHam (mapLaw μ1 (insert e)) ν0 ≤ 1 + (P - 1) :=
      (W_insert_left_le μ1 ν0 e).trans (by linarith)
    by_cases hv2 : 0 < (f v).value 2
    · have hfirst' : ∀ w, inc e w → 0 < (fV w).value 1 := by
        intro w hw
        rcases (hinc w).mp hw with rfl | rfl
        · exact huV
        · simpa only [fV, shiftFamily_at] using hv2
      let fVE := edgeShiftFamily inc fV e hfirst'
      let ν1 := signatureGibbs inc edges' fVE x hx0'
      let q := occupiedProbability inc edges (fun w => (fV w).value) x e
      have hq0 : 0 ≤ q := occupiedProbability_nonneg inc edges _ x e he
        (fun w => (fV w).nonneg) (fun w => (fV w).zero_pos) hfirst' hx0
      have hq1 : q ≤ 1 := occupiedProbability_le_one inc edges _ x e he
        (fun w => (fV w).nonneg) (fun w => (fV w).zero_pos) hx0
      have hqp : q ≤ p := by
        rw [signatureGibbs_marginal_eq_occupiedProbability inc edges fV x hx0 e he hfirst',
          signatureGibbs_marginal_eq_occupiedProbability inc edges f x hx0 e he hfirst] at horder
        exact horder
      let L : Bool → FinDist (Finset E) := fun b => if b then mapLaw ν1 (insert e) else ν0
      have hνmix : signatureGibbs inc edges fV x hx0 = (bernoulli q hq0 hq1).bind L :=
        signatureGibbs_edge_mix inc edges fV x hx0 e he hfirst'
      have hvE : 0 < (fE v).value 1 := by
        simpa [fE, edgeShiftFamily, hev] using hv2
      have hVEeq : fVE = shiftFamily fE v hvE :=
        edgeShiftFamily_comm_shift inc f e v hv hfirst hfirst' hvE
      have h11base : W subsetHam μ1 ν1 ≤ P - 1 := by
        dsimp only [μ1, ν1]
        rw [hVEeq]
        exact ihBound fE hfE v hvE
      have h11 : W subsetHam (mapLaw μ1 (insert e)) (mapLaw ν1 (insert e)) ≤ P - 1 :=
        (W_insert_both_le μ1 ν1 e).trans h11base
      have hW : W subsetHam (signatureGibbs inc edges f x hx0)
          (signatureGibbs inc edges fV x hx0) ≤
          (1 - p) * W subsetHam μ0 ν0 +
            q * W subsetHam (mapLaw μ1 (insert e)) (mapLaw ν1 (insert e)) +
            (p - q) * W subsetHam (mapLaw μ1 (insert e)) ν0 := by
        rw [hμmix, hνmix]
        exact three_branch_W_le hq0 hqp hp1 subsetHam_nonneg K L
      exact hW.trans (recursive_cost_step hq0 hqp hp1 hz h00 h11 h10)
    · have hv2zero : (f v).value 2 = 0 := le_antisymm (le_of_not_gt hv2) ((f v).nonneg 2)
      have hfVdead : (fV v).value 1 = 0 := by simpa only [fV, shiftFamily_at] using hv2zero
      have hνdel : signatureGibbs inc edges fV x hx0 = ν0 :=
        signatureGibbs_delete_dead inc edges fV x hx0 e he v hev hfVdead
      let L : Bool → FinDist (Finset E) := fun _ => ν0
      have hνmix : ν0 = (bernoulli 0 (by norm_num) (by norm_num)).bind L := by
        ext S
        simp [bind_w, bernoulli, L]
      have hW : W subsetHam (signatureGibbs inc edges f x hx0) ν0 ≤
          (1 - p) * W subsetHam μ0 ν0 + p * W subsetHam (mapLaw μ1 (insert e)) ν0 := by
        conv_lhs => rw [hμmix, hνmix]
        simpa [K, L] using three_branch_W_le (q := 0) (by norm_num) hp0 hp1 subsetHam_nonneg K L
      have hstep : (1 - p) * W subsetHam μ0 ν0 +
          p * W subsetHam (mapLaw μ1 (insert e)) ν0 ≤
            P * (1 - zeroOn (signatureGibbs inc edges f x hx0) (edges.filter fun e => inc e v)) := by
        simpa using recursive_cost_step (q := 0) (c₁ := P - 1)
          (by norm_num) hp0 hp1 hz h00 le_rfl h10
      change W subsetHam (signatureGibbs inc edges f x hx0)
        (signatureGibbs inc edges fV x hx0) ≤ _
      rw [hνdel]
      exact hW.trans hstep
  · have hzero : (f u).value 1 = 0 := le_antisymm (le_of_not_gt hu) ((f u).nonneg 1)
    have hzeroV : (fV u).value 1 = 0 := by
      simpa only [fV, shiftFamily_away f v u hv huv] using hzero
    have hμdel := signatureGibbs_delete_dead inc edges f x hx0 e he u heu hzero
    have hνdel := signatureGibbs_delete_dead inc edges fV x hx0 e he u heu hzeroV
    change W subsetHam (signatureGibbs inc edges f x hx0)
      (signatureGibbs inc edges fV x hx0) ≤ _
    rw [hμdel, hνdel, signatureGibbs_zeroOn_erase inc edges f x hx0 e v heI]
    exact ihStrong f hratio v hv

/-- Uniform single-endpoint coupling independence, for actual finite Gibbs
laws and arbitrary nonnegative activities in the prescribed box. -/
theorem endpoint_W_le (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (A R : ℝ) (Δ : ℕ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hx : ∀ e ∈ edges, x e ∈ Set.Icc 0 R)
    (hratio : ∀ v k, (f v).value (k + 1) ≤ A * (f v).value k)
    (hpair : TwoEndpoints inc edges) (hdegree : ∀ v, selectedDegree inc edges v ≤ Δ)
    (v : V) (hv : 0 < (f v).value 1) :
    W subsetHam (signatureGibbs inc edges f x (fun e he => (hx e he).1))
      (signatureGibbs inc edges (shiftFamily f v hv) x (fun e he => (hx e he).1)) ≤
      comparisonP A R Δ - 1 :=
  root_zero_closes_bound (comparisonP_pos hR Δ)
    (signatureGibbs_root_zero_lower inc edges f x Δ hA hR hx hratio hpair hdegree v)
    (endpoint_strong inc A R Δ hA hR edges f x hx hratio hpair hdegree v hv)

/-- Applying the two endpoint comparisons successively gives exactly the
paper's constant, without any positive lower activity bound. -/
theorem two_endpoint_W_le (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (A R : ℝ) (Δ : ℕ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hx : ∀ e ∈ edges, x e ∈ Set.Icc 0 R)
    (hratio : ∀ v k, (f v).value (k + 1) ≤ A * (f v).value k)
    (hpair : TwoEndpoints inc edges) (hdegree : ∀ v, selectedDegree inc edges v ≤ Δ)
    (u v : V) (hv : 0 < (f v).value 1)
    (hu : 0 < (shiftFamily f v hv u).value 1) :
    W subsetHam (signatureGibbs inc edges f x (fun e he => (hx e he).1))
      (signatureGibbs inc edges (shiftFamily (shiftFamily f v hv) u hu) x
        (fun e he => (hx e he).1)) ≤ 2 * (comparisonP A R Δ - 1) := by
  have hleft := endpoint_W_le inc edges f x A R Δ hA hR hx hratio hpair hdegree v hv
  have hright := endpoint_W_le inc edges (shiftFamily f v hv) x A R Δ hA hR hx
    (shiftFamily_ratio_bound f v hv A hratio) hpair hdegree u hu
  have htri := W_triangle subsetHam_nonneg subsetHam_nonneg subsetHam_nonneg
    subsetHam_triangle
    (signatureGibbs inc edges f x (fun e he => (hx e he).1))
    (signatureGibbs inc edges (shiftFamily f v hv) x (fun e he => (hx e he).1))
    (signatureGibbs inc edges (shiftFamily (shiftFamily f v hv) u hu) x
      (fun e he => (hx e he).1))
  linarith

/-- The two actual deleted-edge Gibbs children satisfy the residual Holant
coupling bound.  Their state space contains only the remaining selected
edges; insertion of the conditioned edge is not charged. -/
theorem edge_child_W_le (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (A R : ℝ) (Δ : ℕ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hx : ∀ e ∈ edges, x e ∈ Set.Icc 0 R)
    (hratio : ∀ v k, (f v).value (k + 1) ≤ A * (f v).value k)
    (hpair : TwoEndpoints inc edges) (hdegree : ∀ v, selectedDegree inc edges v ≤ Δ)
    (e : E) (he : e ∈ edges) (hfirst : ∀ v, inc e v → 0 < (f v).value 1) :
    W subsetHam
      (signatureGibbs inc (edges.erase e) f x (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1))
      (signatureGibbs inc (edges.erase e) (edgeShiftFamily inc f e hfirst) x
        (fun a ha => (hx a (Finset.mem_of_mem_erase ha)).1)) ≤
      2 * (comparisonP A R Δ - 1) := by
  obtain ⟨u, v, huv, hinc⟩ := hpair e he
  have hv : 0 < (f v).value 1 := hfirst v ((hinc v).mpr (Or.inr rfl))
  have hu : 0 < (shiftFamily f v hv u).value 1 := by
    rw [shiftFamily_away f v u hv huv]
    exact hfirst u ((hinc u).mpr (Or.inl rfl))
  rw [edgeShiftFamily_as_other_shift inc f e u v huv hinc hfirst hv hu]
  exact two_endpoint_W_le inc (edges.erase e) f x A R Δ hA hR
    (fun a ha => hx a (Finset.mem_of_mem_erase ha)) hratio
    (hpair.mono (Finset.erase_subset _ _))
    (fun w => (selectedDegree_mono inc (Finset.erase_subset _ _) w).trans (hdegree w)) u v hv hu

end

end ZeroFreeness.HolantCoupling
