import CI2ZF.Holant.Signatures
import CI2ZF.Holant.Model

/-!
# Capacity signatures, b-matchings, and complementary b-edge covers

The matching signatures are constructed and proved log-concave, and all
bounded-arity capacities belong to one explicit finite family.  Complementing
selected edges proves the exact reciprocal-activity cover identity.
-/
namespace CI2ZF.Holant
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

/-- The signature imposing the upper degree capacity `b` at a vertex of
arity `d`. Its positive support is precisely `0..b`. -/
def capacitySignature (d b : ℕ) (hb : b ≤ d) : Signature where
  arity := d
  value k := if k ≤ b then 1 else 0
  nonneg k := by split <;> norm_num
  outside k hk := by simp [show ¬ k ≤ b by omega]
  zero_pos := by simp
  support_interval := by
    intro i j k _ hjk _ hk
    have hkb : k ≤ b := by by_contra h; simp [h] at hk
    simp [show j ≤ b by omega]
  log_concave k _ := by
    by_cases hk2 : k + 2 ≤ b
    · simp [hk2, show k ≤ b by omega, show k + 1 ≤ b by omega]
    · simp only [if_neg hk2, mul_zero]
      exact sq_nonneg _

@[simp] theorem capacitySignature_arity (d b : ℕ) (hb : b ≤ d) :
    (capacitySignature d b hb).arity = d := rfl

@[simp] theorem capacitySignature_value (d b : ℕ) (hb : b ≤ d) (k : ℕ) :
    (capacitySignature d b hb).value k = if k ≤ b then 1 else 0 := rfl

@[simp] theorem capacitySignature_zero (d b : ℕ) (hb : b ≤ d) :
    (capacitySignature d b hb).value 0 = 1 := by simp

/-- One finite input family contains every capacity at every arity at most Δ. -/
def capacityFamily (Δ : ℕ) : Finset Signature :=
  (range (Δ + 1)).biUnion fun d =>
    (range (d + 1)).attach.image fun b => capacitySignature d b.val
      (by have := mem_range.mp b.property; omega)

theorem capacitySignature_mem_family (Δ d b : ℕ) (hb : b ≤ d) (hd : d ≤ Δ) :
    capacitySignature d b hb ∈ capacityFamily Δ := by
  apply mem_biUnion.mpr
  refine ⟨d, mem_range.mpr (by omega), ?_⟩
  apply mem_image.mpr
  exact ⟨⟨b, mem_range.mpr (by omega)⟩, mem_attach _ _, rfl⟩

variable {V E R : Type*} [Fintype V] [DecidableEq E]

/-- Weighted subsets satisfying all upper degree capacities. -/
def matchingPartition [CommSemiring R] (inc : E → V → Prop) (edges : Finset E)
    (b : V → ℕ) (z : E → R) : R :=
  ∑ S ∈ edges.powerset,
    if ∀ v, selectedDegree inc S v ≤ b v then ∏ e ∈ S, z e else 0

/-- Weighted subsets satisfying all lower degree demands. -/
def coverPartition [CommSemiring R] (inc : E → V → Prop) (edges : Finset E)
    (b : V → ℕ) (z : E → R) : R :=
  ∑ S ∈ edges.powerset,
    if ∀ v, b v ≤ selectedDegree inc S v then ∏ e ∈ S, z e else 0

/-- The matching polynomial is exactly the Holant polynomial of capacity
indicators, over any coefficient semiring. -/
theorem matchingPartition_eq_holant [CommSemiring R]
    (inc : E → V → Prop) (edges : Finset E) (b : V → ℕ) (z : E → R) :
    matchingPartition inc edges b z =
      partition inc edges (fun v k => if k ≤ b v then 1 else 0) z := by
  unfold matchingPartition partition weight signatureWeight
  apply sum_congr rfl
  intro S _
  by_cases hs : ∀ v, selectedDegree inc S v ≤ b v
  · simp [hs]
  · have hp : (∏ v, if selectedDegree inc S v ≤ b v then (1 : R) else 0) = 0 := by
      obtain ⟨v, hv⟩ := not_forall.mp hs
      apply prod_eq_zero (mem_univ v)
      simp [hv]
    simp [hs, hp]

/-- The complex capacity-signature specialization has precisely the
b-matching partition sum, with no extra normalization factors. -/
theorem matchingPartition_eq_capacity_holant (inc : E → V → Prop) (edges : Finset E)
    (d b : V → ℕ) (hb : ∀ v, b v ≤ d v) (z : E → ℂ) :
    matchingPartition inc edges b z =
      partition inc edges (fun v k => ((capacitySignature (d v) (b v) (hb v)).value k : ℂ)) z := by
  rw [matchingPartition_eq_holant]
  congr 1
  funext v k
  simp only [capacitySignature_value]
  split <;> simp

/-- Complementation subtracts selected incidence counts, exactly. -/
theorem selectedDegree_complement (inc : E → V → Prop) (edges S : Finset E)
    (hS : S ⊆ edges) (v : V) :
    selectedDegree inc (edges \ S) v = selectedDegree inc edges v - selectedDegree inc S v := by
  unfold selectedDegree
  have hf : (edges \ S).filter (fun e => inc e v) =
      (edges.filter fun e => inc e v) \ (S.filter fun e => inc e v) := by
    ext e
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [hf]
  exact card_sdiff_of_subset (filter_subset_filter _ hS)

/-- Lower degree demands for a complement become upper degree capacities. -/
theorem cover_complement_iff (inc : E → V → Prop) (edges S : Finset E)
    (hS : S ⊆ edges) (b : V → ℕ) (hb : ∀ v, b v ≤ selectedDegree inc edges v) :
    (∀ v, b v ≤ selectedDegree inc (edges \ S) v) ↔
      ∀ v, selectedDegree inc S v ≤ selectedDegree inc edges v - b v := by
  simp only [selectedDegree_complement inc edges S hS]
  constructor <;> intro h v
  · have htotal := selectedDegree_mono inc hS v
    have hbound := hb v
    have := h v
    omega
  · have htotal := selectedDegree_mono inc hS v
    have hbound := hb v
    have := h v
    omega

/-- Complementation is a bijection on the finite powerset. -/
theorem sum_powerset_complement [AddCommMonoid R] (edges : Finset E)
    (w : Finset E → R) :
    (∑ S ∈ edges.powerset, w (edges \ S)) = ∑ S ∈ edges.powerset, w S := by
  apply sum_bij (fun S _ => edges \ S)
  · intro S _
    exact mem_powerset.mpr sdiff_subset
  · intro S hS T hT hst
    have h := congrArg (fun U => edges \ U) hst
    simpa [Finset.sdiff_sdiff_eq_self (mem_powerset.mp hS),
      Finset.sdiff_sdiff_eq_self (mem_powerset.mp hT)] using h
  · intro S hS
    exact ⟨edges \ S, mem_powerset.mpr sdiff_subset,
      Finset.sdiff_sdiff_eq_self (mem_powerset.mp hS)⟩
  · intro S _
    rfl

/-- A complement monomial is the full monomial times reciprocal activities
on the removed subset. -/
theorem prod_complement_eq [Field R] (edges S : Finset E) (hS : S ⊆ edges)
    (z : E → R) (hz : ∀ e ∈ edges, z e ≠ 0) :
    (∏ e ∈ edges \ S, z e) = (∏ e ∈ edges, z e) * ∏ e ∈ S, (z e)⁻¹ := by
  have hp : (∏ e ∈ S, z e) ≠ 0 := prod_ne_zero_iff.mpr (fun e he => hz e (hS he))
  rw [Finset.prod_inv_distrib, ← Finset.prod_sdiff hS, mul_assoc,
    mul_inv_cancel₀ hp, mul_one]

/-- The exact b-edge-cover/b-matching reciprocal polynomial identity. -/
theorem coverPartition_eq_complement_matching [Field R]
    (inc : E → V → Prop) (edges : Finset E) (b : V → ℕ)
    (hb : ∀ v, b v ≤ selectedDegree inc edges v) (z : E → R)
    (hz : ∀ e ∈ edges, z e ≠ 0) :
    coverPartition inc edges b z = (∏ e ∈ edges, z e) *
      matchingPartition inc edges (fun v => selectedDegree inc edges v - b v)
        (fun e => (z e)⁻¹) := by
  unfold coverPartition
  rw [← sum_powerset_complement edges]
  unfold matchingPartition
  rw [mul_sum]
  apply sum_congr rfl
  intro S hS
  have hsub := mem_powerset.mp hS
  simp only [cover_complement_iff inc edges S hsub b hb]
  split
  · exact prod_complement_eq edges S hsub z hz
  · simp

/-- Nonvanishing transfers through complementation whenever the activities
and the reciprocal matching partition are nonzero. -/
theorem coverPartition_ne_zero_of_matching [Field R]
    (inc : E → V → Prop) (edges : Finset E) (b : V → ℕ)
    (hb : ∀ v, b v ≤ selectedDegree inc edges v) (z : E → R)
    (hz : ∀ e ∈ edges, z e ≠ 0)
    (hmatch : matchingPartition inc edges
      (fun v => selectedDegree inc edges v - b v) (fun e => (z e)⁻¹) ≠ 0) :
    coverPartition inc edges b z ≠ 0 := by
  rw [coverPartition_eq_complement_matching inc edges b hb z hz]
  exact mul_ne_zero (prod_ne_zero_iff.mpr hz) hmatch

section Graph
variable [DecidableEq V]

theorem graph_cover_eq_complement_matching [Field R] (G : SimpleGraph V)
    (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v) (z : Sym2 V → R)
    (hz : ∀ e ∈ G.edgeFinset, z e ≠ 0) :
    coverPartition graphIncidence G.edgeFinset b z =
      (∏ e ∈ G.edgeFinset, z e) * matchingPartition graphIncidence G.edgeFinset
        (fun v => G.degree v - b v) (fun e => (z e)⁻¹) := by
  simpa using coverPartition_eq_complement_matching graphIncidence G.edgeFinset b
    (by simpa using hb) z hz

end Graph
end
end CI2ZF.Holant
