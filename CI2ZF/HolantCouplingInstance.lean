import CI2ZF.HolantCouplingDeletion
import CI2ZF.HolantCouplingTransport

/-!
# Signature shifts and edge marginals for recursive Holant comparison
-/

namespace CI2ZF.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist Holant

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- A shift of a log-concave signature is again a log-concave signature.
Keeping the old arity as a harmless upper bound avoids truncation before
the shift; the value function is the exact original tail. -/
def shifted (f : Signature) (hf : 0 < f.value 1) : Signature where
  arity := f.arity
  value k := f.value (k + 1)
  nonneg k := f.nonneg _
  outside k hk := f.outside _ (by omega)
  zero_pos := hf
  support_interval hij hjk hi hk :=
    f.support_interval (by omega) (by omega) hi hk
  log_concave k _ := by
    have h := f.ratio_cross_le (k := k + 1) (l := k + 2) (by omega)
    simpa only [Nat.add_assoc, Nat.reduceAdd, pow_two] using h

@[simp] theorem shifted_value (f : Signature) (hf : 0 < f.value 1) (k : ℕ) :
    (shifted f hf).value k = f.value (k + 1) := rfl

/-- Shift just one vertex of a signature family. -/
def shiftFamily (f : V → Signature) (v : V) (hf1 : 0 < (f v).value 1) :
    V → Signature :=
  fun w => if h : w = v then shifted (f w) (by simpa only [h] using hf1) else f w

@[simp] theorem shiftFamily_arity (f : V → Signature) (v : V)
    (hf1 : 0 < (f v).value 1) (w : V) :
    (shiftFamily f v hf1 w).arity = (f w).arity := by
  by_cases h : w = v <;> simp [shiftFamily, shifted, h]

theorem shiftFamily_value (f : V → Signature) (v : V) (hf1 : 0 < (f v).value 1) :
    (fun w => (shiftFamily f v hf1 w).value) = shiftVertex (fun w => (f w).value) v := by
  funext w k
  by_cases h : w = v <;> simp [shiftFamily, shiftVertex, h]

@[simp] theorem shiftFamily_at (f : V → Signature) (v : V) (hf1 : 0 < (f v).value 1)
    (k : ℕ) : (shiftFamily f v hf1 v).value k = (f v).value (k + 1) := by
  simp [shiftFamily]

theorem shiftFamily_away (f : V → Signature) (v w : V)
    (hf1 : 0 < (f v).value 1) (hw : w ≠ v) : shiftFamily f v hf1 w = f w := by
  simp [shiftFamily, hw]

theorem shiftFamily_ratio_bound (f : V → Signature) (v : V)
    (hf1 : 0 < (f v).value 1) (A : ℝ)
    (hA : ∀ w k, (f w).value (k + 1) ≤ A * (f w).value k) :
    ∀ w k, (shiftFamily f v hf1 w).value (k + 1) ≤
      A * (shiftFamily f v hf1 w).value k := by
  intro w k
  by_cases h : w = v
  · subst w
    simpa only [shiftFamily_at] using hA v (k + 1)
  · simpa only [shiftFamily_away f v w hf1 h] using hA w k

/-- A first-ratio bound controls all successive ratios, including zero tails. -/
theorem all_ratios_le_of_first (f : Signature) (A : ℝ)
    (hA : f.value 1 ≤ A * f.value 0) (k : ℕ) :
    f.value (k + 1) ≤ A * f.value k := by
  have hcross := f.ratio_cross_le (k := 0) (l := k) (Nat.zero_le _)
  have hmul := mul_le_mul_of_nonneg_right hA (f.nonneg k)
  apply (mul_le_mul_iff_left₀ f.zero_pos).mp
  nlinarith

/-- Gibbs law specialized to the signature structure. -/
def signatureGibbs (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e) : FinDist (Finset E) :=
  gibbs inc edges (fun v => (f v).value) x
    (fun v => (f v).nonneg) (fun v => (f v).zero_pos) hx

theorem signatureGibbs_shift (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (v : V) (hf1 : 0 < (f v).value 1) :
    signatureGibbs inc edges (shiftFamily f v hf1) x hx =
      gibbs inc edges (shiftVertex (fun w => (f w).value) v) x
        (shiftVertex_nonneg _ v (fun w => (f w).nonneg))
        (shiftVertex_zero_pos _ v (fun w => (f w).zero_pos) hf1) hx := by
  unfold signatureGibbs
  congr 1
  exact shiftFamily_value f v hf1

/-- Selected-edge marginal on the ambient finite powerset. -/
def subsetMarginal (μ : FinDist (Finset E)) (e : E) : ℝ :=
  expectReal μ (fun S => if e ∈ S then 1 else 0)

theorem subsetMarginal_nonneg (μ : FinDist (Finset E)) (e : E) :
    0 ≤ subsetMarginal μ e := by
  apply Finset.sum_nonneg
  intro S _
  exact mul_nonneg (μ.nonneg S) (by dsimp; split_ifs <;> norm_num)

theorem subsetMarginal_le_one (μ : FinDist (Finset E)) (e : E) :
    subsetMarginal μ e ≤ 1 := by
  calc
    subsetMarginal μ e ≤ expectReal μ (fun _ => 1) := by
      apply expectReal_mono
      intro S
      split_ifs <;> norm_num
    _ = 1 := expectReal_const _ _

theorem expected_selectedDegree_eq_marginals (inc : E → V → Prop) (edges : Finset E)
    (μ : FinDist (Finset E)) (hsupport : ∀ S, ¬S ⊆ edges → μ.w S = 0) (v : V) :
    expectReal μ (fun S => (selectedDegree inc S v : ℝ)) =
      ∑ e ∈ edges.filter (fun e => inc e v), subsetMarginal μ e := by
  have hpoint (S : Finset E) : μ.w S * (selectedDegree inc S v : ℝ) =
      μ.w S * ∑ e ∈ edges.filter (fun e => inc e v), (if e ∈ S then 1 else 0 : ℝ) := by
    by_cases hS : S ⊆ edges
    · congr 1
      rw [Finset.sum_boole]
      unfold selectedDegree
      congr 1
      congr 1
      ext e
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨⟨hS h.1, h.2⟩, h.1⟩
      · intro h
        exact ⟨h.2, h.1.2⟩
    · simp [hsupport S hS]
  unfold expectReal subsetMarginal
  simp_rw [hpoint, Finset.mul_sum]
  exact Finset.sum_comm

/-- Actual Holant Gibbs laws have an incident edge with the ordered marginal
needed by the recursive coupling. -/
theorem signatureGibbs_exists_ordered_edge (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (v : V) (hf1 : 0 < (f v).value 1)
    (hne : (edges.filter fun e => inc e v).Nonempty) :
    ∃ e ∈ edges.filter (fun e => inc e v),
      subsetMarginal (signatureGibbs inc edges (shiftFamily f v hf1) x hx) e ≤
        subsetMarginal (signatureGibbs inc edges f x hx) e := by
  have h := gibbs_shift_degree_le inc edges f x v hx hf1
  rw [← signatureGibbs_shift inc edges f x hx v hf1] at h
  change expectReal (signatureGibbs inc edges (shiftFamily f v hf1) x hx) _ ≤
    expectReal (signatureGibbs inc edges f x hx) _ at h
  have hs (g : V → Signature) (S : Finset E) (hS : ¬S ⊆ edges) :
      (signatureGibbs inc edges g x hx).w S = 0 := by
    simp [signatureGibbs, restrictedWeight, hS]
  rw [expected_selectedDegree_eq_marginals inc edges _ (hs (shiftFamily f v hf1)) v,
    expected_selectedDegree_eq_marginals inc edges _ (hs f) v] at h
  exact Finset.exists_le_of_sum_le hne h

/-- A two-endpoint edge shift equals the two successive vertex shifts. -/
theorem edgeShift_eq_two_shifts (inc : E → V → Prop) (f : V → ℕ → ℝ)
    (e : E) (u v : V) (huv : u ≠ v) (hinc : ∀ w, inc e w ↔ w = u ∨ w = v) :
    shiftedSignature inc f e = shiftVertex (shiftVertex f v) u := by
  funext w k
  by_cases hwu : w = u
  · subst w
    simp [shiftedSignature, shiftVertex, hinc, huv]
  · by_cases hwv : w = v
    · subst w
      simp [shiftedSignature, shiftVertex, hinc, Ne.symm huv]
    · simp [shiftedSignature, shiftVertex, hinc, hwu, hwv]

theorem shiftVertex_comm (f : V → ℕ → ℝ) (u v : V) :
    shiftVertex (shiftVertex f u) v = shiftVertex (shiftVertex f v) u := by
  funext w k
  by_cases hwu : w = u <;> by_cases hwv : w = v <;> simp [shiftVertex, hwu, hwv]

/-- Shift all signatures incident to an edge; feasibility supplies precisely
the positive initial values needed at those endpoints. -/
def edgeShiftFamily (inc : E → V → Prop) (f : V → Signature) (e : E)
    (hfirst : ∀ v, inc e v → 0 < (f v).value 1) : V → Signature :=
  fun v => if h : inc e v then shifted (f v) (hfirst v h) else f v

@[simp] theorem edgeShiftFamily_arity (inc : E → V → Prop) (f : V → Signature) (e : E)
    (hfirst : ∀ v, inc e v → 0 < (f v).value 1) (v : V) :
    (edgeShiftFamily inc f e hfirst v).arity = (f v).arity := by
  by_cases h : inc e v <;> simp [edgeShiftFamily, shifted, h]

theorem edgeShiftFamily_value (inc : E → V → Prop) (f : V → Signature) (e : E)
    (hfirst : ∀ v, inc e v → 0 < (f v).value 1) :
    (fun v => (edgeShiftFamily inc f e hfirst v).value) =
      shiftedSignature inc (fun v => (f v).value) e := by
  funext v k
  by_cases h : inc e v <;> simp [edgeShiftFamily, shiftedSignature, h]

theorem edgeShiftFamily_ratio_bound (inc : E → V → Prop) (f : V → Signature) (e : E)
    (hfirst : ∀ v, inc e v → 0 < (f v).value 1) (A : ℝ)
    (hA : ∀ v k, (f v).value (k + 1) ≤ A * (f v).value k) :
    ∀ v k, (edgeShiftFamily inc f e hfirst v).value (k + 1) ≤
      A * (edgeShiftFamily inc f e hfirst v).value k := by
  intro v k
  by_cases h : inc e v
  · simpa [edgeShiftFamily, h] using hA v (k + 1)
  · simpa [edgeShiftFamily, h] using hA v k

theorem signatureGibbs_edgeShift (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (e : E) (hfirst : ∀ v, inc e v → 0 < (f v).value 1) :
    signatureGibbs inc edges (edgeShiftFamily inc f e hfirst) x hx =
      gibbs inc edges (shiftedSignature inc (fun v => (f v).value) e) x
        (edgeShift_nonneg inc _ e (fun v => (f v).nonneg))
        (edgeShift_zero_pos inc _ e (fun v => (f v).zero_pos) hfirst) hx := by
  unfold signatureGibbs
  congr 1
  exact edgeShiftFamily_value inc f e hfirst

theorem signatureGibbs_edge_mix (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (e : E) (he : e ∈ edges) (hfirst : ∀ v, inc e v → 0 < (f v).value 1) :
    signatureGibbs inc edges f x hx =
      (bernoulli (occupiedProbability inc edges (fun v => (f v).value) x e)
        (occupiedProbability_nonneg inc edges _ x e he
          (fun v => (f v).nonneg) (fun v => (f v).zero_pos) hfirst hx)
        (occupiedProbability_le_one inc edges _ x e he
          (fun v => (f v).nonneg) (fun v => (f v).zero_pos) hx)).bind
        (fun b => if b then
          mapLaw (signatureGibbs inc (edges.erase e) (edgeShiftFamily inc f e hfirst) x
            (fun a ha => hx a (Finset.mem_of_mem_erase ha))) (fun S : Finset E => insert e S)
          else signatureGibbs inc (edges.erase e) f x
            (fun a ha => hx a (Finset.mem_of_mem_erase ha))) := by
  rw [signatureGibbs_edgeShift]
  exact gibbs_deletion_mix inc edges _ x e he
    (fun v => (f v).nonneg) (fun v => (f v).zero_pos) hfirst hx

theorem expectReal_bind {A B : Type*} [Fintype A] [Fintype B]
    (μ : FinDist A) (K : A → FinDist B) (h : B → ℝ) :
    expectReal (μ.bind K) h = ∑ a, μ.w a * expectReal (K a) h := by
  unfold expectReal
  simp only [bind_w, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_assoc]

@[simp] theorem subsetMarginal_insert (μ : FinDist (Finset E)) (e : E) :
    subsetMarginal (mapLaw μ (fun S : Finset E => insert e S)) e = 1 := by
  unfold subsetMarginal
  rw [expectReal_mapLaw]
  simp only [Finset.mem_insert_self, ↓reduceIte]
  exact expectReal_const _ _

theorem subsetMarginal_eq_zero_of_no_edge (μ : FinDist (Finset E)) (e : E)
    (hμ : ∀ S, e ∈ S → μ.w S = 0) : subsetMarginal μ e = 0 := by
  apply Finset.sum_eq_zero
  intro S _
  by_cases h : e ∈ S <;> simp [h, hμ S]

theorem signatureGibbs_marginal_eq_occupiedProbability (inc : E → V → Prop)
    (edges : Finset E) (f : V → Signature) (x : E → ℝ)
    (hx : ∀ e ∈ edges, 0 ≤ x e) (e : E) (he : e ∈ edges)
    (hfirst : ∀ v, inc e v → 0 < (f v).value 1) :
    subsetMarginal (signatureGibbs inc edges f x hx) e =
      occupiedProbability inc edges (fun v => (f v).value) x e := by
  rw [signatureGibbs_edge_mix inc edges f x hx e he hfirst]
  unfold subsetMarginal
  rw [expectReal_bind]
  simp only [bernoulli, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
  rw [add_comm]
  change (1 - occupiedProbability inc edges (fun v => (f v).value) x e) *
      subsetMarginal (signatureGibbs inc (edges.erase e) f x _) e +
      occupiedProbability inc edges (fun v => (f v).value) x e *
      subsetMarginal (mapLaw (signatureGibbs inc (edges.erase e)
        (edgeShiftFamily inc f e hfirst) x _) (fun S : Finset E => insert e S)) e = _
  rw [subsetMarginal_insert]
  simp only [signatureGibbs]
  rw [subsetMarginal_eq_zero_of_no_edge _ e
    (gibbs_no_edge inc (edges.erase e) _ x _ _ _ e (Finset.notMem_erase e edges))]
  ring

theorem edgeShiftFamily_as_other_shift (inc : E → V → Prop) (f : V → Signature)
    (e : E) (u v : V) (huv : u ≠ v)
    (hinc : ∀ w, inc e w ↔ w = u ∨ w = v)
    (hs : ∀ w, inc e w → 0 < (f w).value 1)
    (hv : 0 < (f v).value 1)
    (hu : 0 < (shiftFamily f v hv u).value 1) :
    edgeShiftFamily inc f e hs = shiftFamily (shiftFamily f v hv) u hu := by
  funext w
  apply Signature.ext
  · simp only [edgeShiftFamily_arity, shiftFamily_arity]
  · funext k
    by_cases hwu : w = u
    · subst w
      simp [edgeShiftFamily, shiftFamily, shifted, hinc, huv]
    · by_cases hwv : w = v
      · subst w
        simp [edgeShiftFamily, shiftFamily, shifted, hinc, Ne.symm huv]
      · simp [edgeShiftFamily, shiftFamily, hinc, hwu, hwv]

theorem edgeShiftFamily_comm_shift (inc : E → V → Prop) (f : V → Signature)
    (e : E) (v : V) (hv : 0 < (f v).value 1)
    (hs : ∀ w, inc e w → 0 < (f w).value 1)
    (hs' : ∀ w, inc e w → 0 < (shiftFamily f v hv w).value 1)
    (hv' : 0 < (edgeShiftFamily inc f e hs v).value 1) :
    edgeShiftFamily inc (shiftFamily f v hv) e hs' =
      shiftFamily (edgeShiftFamily inc f e hs) v hv' := by
  funext w
  apply Signature.ext
  · simp only [edgeShiftFamily_arity, shiftFamily_arity]
  · funext k
    by_cases hwv : w = v
    · subst w
      by_cases hw : inc e v <;> simp [edgeShiftFamily, shiftFamily, hw]
    · by_cases hw : inc e w <;> simp [edgeShiftFamily, shiftFamily, hwv, hw]

end

end CI2ZF.HolantCoupling
