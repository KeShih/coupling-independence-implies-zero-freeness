import CI2ZF.HolantCoupling
import CI2ZF.HolantModel

/-!
# Gibbs laws for finite Holant instances

The state space is the fixed ambient finite powerset.  Deleting an edge
changes the support and the weights, not the state type.  All Gibbs laws
are normalized actual Holant weights, including at zero activities.
-/

namespace CI2ZF.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist Holant

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Extend the actual Holant weights by zero outside the current edge set. -/
def restrictedWeight (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (S : Finset E) : ℝ :=
  if S ⊆ edges then weight inc f x S else 0

theorem sum_restrictedWeight (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) :
    (∑ S, restrictedWeight inc edges f x S) = partition inc edges f x := by
  unfold restrictedWeight partition
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp

theorem restrictedWeight_nonneg (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ e ∈ edges, 0 ≤ x e) (S : Finset E) :
    0 ≤ restrictedWeight inc edges f x S := by
  unfold restrictedWeight
  split_ifs with h
  · exact weight_nonneg inc edges f x hf hx h
  · exact le_rfl

theorem sum_restrictedWeight_pos (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ e ∈ edges, 0 ≤ x e) :
    0 < ∑ S, restrictedWeight inc edges f x S := by
  rw [sum_restrictedWeight]
  exact partition_pos inc edges f x hf hf0 hx

/-- The actual finite Holant Gibbs distribution.  Its definition needs
nonnegative activities, with no positive lower bound. -/
def gibbs (inc : E → V → Prop) (edges : Finset E) (f : V → ℕ → ℝ)
    (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, 0 < f v 0)
    (hx : ∀ e ∈ edges, 0 ≤ x e) : FinDist (Finset E) :=
  normalizeWeights (restrictedWeight inc edges f x)
    (restrictedWeight_nonneg inc edges f x hf hx)
    (sum_restrictedWeight_pos inc edges f x hf hf0 hx)

@[simp] theorem gibbs_apply (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ e ∈ edges, 0 ≤ x e) (S : Finset E) :
    (gibbs inc edges f x hf hf0 hx).w S =
      restrictedWeight inc edges f x S / partition inc edges f x := by
  simp only [gibbs, normalizeWeights_apply, sum_restrictedWeight]

/-- One downward signature shift, performed before restricting the arity. -/
def shiftVertex (f : V → ℕ → ℝ) (v : V) : V → ℕ → ℝ :=
  fun w k => if w = v then f w (k + 1) else f w k

theorem shiftVertex_nonneg (f : V → ℕ → ℝ) (v : V)
    (hf : ∀ w k, 0 ≤ f w k) : ∀ w k, 0 ≤ shiftVertex f v w k := by
  intro w k
  unfold shiftVertex
  split_ifs <;> exact hf _ _

theorem shiftVertex_zero_pos (f : V → ℕ → ℝ) (v : V)
    (hf0 : ∀ w, 0 < f w 0) (hf1 : 0 < f v 1) :
    ∀ w, 0 < shiftVertex f v w 0 := by
  intro w
  by_cases h : w = v
  · simpa [shiftVertex, h] using hf1
  · simpa [shiftVertex, h] using hf0 w

/-- All factors except the designated signature, retaining the actual
global activity weight and allowed-edge condition. -/
def exteriorWeight (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (v : V) (S : Finset E) : ℝ :=
  if S ⊆ edges then
    (∏ w ∈ Finset.univ.erase v, f w (selectedDegree inc S w)) * ∏ e ∈ S, x e
  else 0

theorem exteriorWeight_nonneg (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (v : V) (hf : ∀ w k, 0 ≤ f w k)
    (hx : ∀ e ∈ edges, 0 ≤ x e) (S : Finset E) :
    0 ≤ exteriorWeight inc edges f x v S := by
  unfold exteriorWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun w _ => hf w _)
      (Finset.prod_nonneg fun e he => hx e (h he))
  · exact le_rfl

theorem restrictedWeight_factor (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (v : V) (S : Finset E) :
    restrictedWeight inc edges f x S =
      exteriorWeight inc edges f x v S * f v (selectedDegree inc S v) := by
  unfold restrictedWeight exteriorWeight weight signatureWeight
  split_ifs with h
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v)]
    ring
  · ring

theorem restrictedWeight_shift_factor (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (v : V) (S : Finset E) :
    restrictedWeight inc edges (shiftVertex f v) x S =
      exteriorWeight inc edges f x v S * f v (selectedDegree inc S v + 1) := by
  rw [restrictedWeight_factor inc edges (shiftVertex f v) x v S]
  have hext : exteriorWeight inc edges (shiftVertex f v) x v S =
      exteriorWeight inc edges f x v S := by
    unfold exteriorWeight
    congr 1
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    simp [shiftVertex, (Finset.mem_erase.mp hw).1]
  simp [hext, shiftVertex]

/-- Chen--Gu Lemma 18 for the actual finite-subset Gibbs laws.  The only
input beyond Gibbs well-definedness is the root signature's log-concavity. -/
theorem gibbs_shift_degree_le (inc : E → V → Prop) (edges : Finset E)
    (f : V → Signature) (x : E → ℝ) (v : V)
    (hx : ∀ e ∈ edges, 0 ≤ x e) (hf1 : 0 < (f v).value 1) :
    expectReal
      (gibbs inc edges (shiftVertex (fun w => (f w).value) v) x
        (shiftVertex_nonneg _ v (fun w => (f w).nonneg))
        (shiftVertex_zero_pos _ v (fun w => (f w).zero_pos) hf1) hx)
      (fun S => (selectedDegree inc S v : ℝ)) ≤
    expectReal
      (gibbs inc edges (fun w => (f w).value) x
        (fun w => (f w).nonneg) (fun w => (f w).zero_pos) hx)
      (fun S => (selectedDegree inc S v : ℝ)) := by
  let base := exteriorWeight inc edges (fun w => (f w).value) x v
  have ha : (fun S => base S * (f v).value (selectedDegree inc S v)) =
      restrictedWeight inc edges (fun w => (f w).value) x := by
    funext S
    exact (restrictedWeight_factor inc edges _ x v S).symm
  have hb : (fun S => base S * (f v).value (selectedDegree inc S v + 1)) =
      restrictedWeight inc edges (shiftVertex (fun w => (f w).value) v) x := by
    funext S
    exact (restrictedWeight_shift_factor inc edges _ x v S).symm
  have hZa : 0 < ∑ S, base S * (f v).value (selectedDegree inc S v) := by
    rw [ha]
    exact sum_restrictedWeight_pos inc edges _ x
      (fun w => (f w).nonneg) (fun w => (f w).zero_pos) hx
  have hZb : 0 < ∑ S, base S * (f v).value (selectedDegree inc S v + 1) := by
    rw [hb]
    exact sum_restrictedWeight_pos inc edges _ x
      (shiftVertex_nonneg _ v (fun w => (f w).nonneg))
      (shiftVertex_zero_pos _ v (fun w => (f w).zero_pos) hf1) hx
  have h := shifted_degree_expectation_le (f v) base (fun S => selectedDegree inc S v)
    (exteriorWeight_nonneg inc edges _ x v (fun w => (f w).nonneg) hx) hZa hZb
  simpa only [ha, hb, gibbs] using h

end

end CI2ZF.HolantCoupling
