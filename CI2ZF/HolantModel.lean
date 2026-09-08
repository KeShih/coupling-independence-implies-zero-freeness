import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic

/-!
# Finite-subset semantics for Boolean Holant partition functions

The ambient edge type stays fixed when edges are deleted.  This permits exact
child identities without identifying different subtype state spaces.  A simple
graph is instantiated below by its actual unordered edge finset and incidence.
No recursion is assumed: the deletion identity is proved by splitting a powerset.
-/

namespace CI2ZF.Holant

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E R : Type*} [Fintype V] [DecidableEq E]

/-- The number of selected edges incident to a vertex. -/
def selectedDegree (inc : E → V → Prop) (S : Finset E) (v : V) : ℕ :=
  (S.filter fun e => inc e v).card

@[simp] theorem selectedDegree_empty (inc : E → V → Prop) (v : V) :
    selectedDegree inc ∅ v = 0 := by simp [selectedDegree]

theorem selectedDegree_mono (inc : E → V → Prop) {S T : Finset E}
    (hST : S ⊆ T) (v : V) : selectedDegree inc S v ≤ selectedDegree inc T v :=
  Finset.card_le_card (Finset.filter_subset_filter _ hST)

theorem selectedDegree_insert (inc : E → V → Prop) (e : E) (S : Finset E)
    (he : e ∉ S) (v : V) :
    selectedDegree inc (insert e S) v =
      selectedDegree inc S v + if inc e v then 1 else 0 := by
  by_cases h : inc e v
  · simp [selectedDegree, Finset.filter_insert, h, he]
  · simp [selectedDegree, Finset.filter_insert, h]

section Semiring
variable [CommSemiring R]

/-- The signature coefficient of a selected edge set. -/
def signatureWeight (inc : E → V → Prop) (f : V → ℕ → R) (S : Finset E) : R :=
  ∏ v, f v (selectedDegree inc S v)

/-- A single multivariate Holant monomial. -/
def weight (inc : E → V → Prop) (f : V → ℕ → R) (z : E → R) (S : Finset E) : R :=
  signatureWeight inc f S * ∏ e ∈ S, z e

/-- The actual finite subset partition sum. -/
def partition (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → R) (z : E → R) : R :=
  ∑ S ∈ edges.powerset, weight inc f z S

@[simp] theorem weight_empty (inc : E → V → Prop) (f : V → ℕ → R) (z : E → R) :
    weight inc f z ∅ = ∏ v, f v 0 := by simp [weight, signatureWeight]

@[simp] theorem partition_empty (inc : E → V → Prop) (f : V → ℕ → R) (z : E → R) :
    partition inc ∅ f z = ∏ v, f v 0 := by simp [partition]

/-- Fixing an edge to one shifts precisely the signatures incident to it. -/
def shiftedSignature (inc : E → V → Prop) (f : V → ℕ → R) (e : E) : V → ℕ → R :=
  fun v k => f v (k + if inc e v then 1 else 0)

theorem weight_insert (inc : E → V → Prop) (f : V → ℕ → R)
    (z : E → R) (e : E) (S : Finset E) (he : e ∉ S) :
    weight inc f z (insert e S) = z e * weight inc (shiftedSignature inc f e) z S := by
  simp only [weight, signatureWeight, selectedDegree_insert inc e S he,
    shiftedSignature, Finset.prod_insert he]
  ring

/-- Exact deletion recursion for the unnormalized children, valid also when
an activity or the entire one-child vanishes. -/
theorem partition_deletion (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → R) (z : E → R) (e : E) (he : e ∈ edges) :
    partition inc edges f z = partition inc (edges.erase e) f z +
      z e * partition inc (edges.erase e) (shiftedSignature inc f e) z := by
  conv_lhs => rw [← Finset.insert_erase he]
  rw [partition, Finset.sum_powerset_insert (Finset.notMem_erase e edges)]
  unfold partition
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  exact weight_insert inc f z e S (fun h =>
    (Finset.notMem_erase e edges) ((Finset.mem_powerset.mp hS) h))

/-- Vertexwise multiplication by constants multiplies the partition function
by their product, independently of all activities. -/
theorem partition_scale (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → R) (c : V → R) (z : E → R) :
    partition inc edges (fun v k => c v * f v k) z =
      (∏ v, c v) * partition inc edges f z := by
  unfold partition weight signatureWeight
  simp only [Finset.prod_mul_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Values outside the actual vertex degree never affect the polynomial. -/
theorem partition_congr_signatures (inc : E → V → Prop) (edges : Finset E)
    (f g : V → ℕ → R) (z : E → R)
    (hfg : ∀ v k, k ≤ selectedDegree inc edges v → f v k = g v k) :
    partition inc edges f z = partition inc edges g z := by
  apply Finset.sum_congr rfl
  intro S hS
  unfold weight signatureWeight
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  exact hfg v _ (selectedDegree_mono inc (Finset.mem_powerset.mp hS) v)

/-- If a shifted signature is identically zero, so is the one-child. -/
theorem shifted_partition_zero (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → R) (z : E → R) (e : E)
    (hdead : ∃ v, inc e v ∧ ∀ k, f v (k + 1) = 0) :
    partition inc edges (shiftedSignature inc f e) z = 0 := by
  obtain ⟨v, hv, hf⟩ := hdead
  apply Finset.sum_eq_zero
  intro S _
  unfold weight signatureWeight
  have hp : (∏ w, shiftedSignature inc f e w (selectedDegree inc S w)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simpa [shiftedSignature, hv] using hf (selectedDegree inc S v)
  rw [hp, zero_mul]

end Semiring

section Field
variable [Field R]

/-- Normalizing a signature at zero is multiplication by an activity-independent
scalar, including when some activities vanish. -/
def normalizedSignature (f : V → ℕ → R) : V → ℕ → R := fun v k => f v k / f v 0

theorem partition_normalization (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → R) (z : E → R) (h0 : ∀ v, f v 0 ≠ 0) :
    partition inc edges f z = (∏ v, f v 0) *
      partition inc edges (normalizedSignature f) z := by
  rw [← partition_scale]
  congr 1
  funext v k
  exact (mul_div_cancel₀ (f v k) (h0 v)).symm

/-- Each shifted endpoint is divided by its first signature value. -/
def normalizedChildSignature (inc : E → V → Prop) (f : V → ℕ → R)
    (e : E) : V → ℕ → R :=
  fun v k => if inc e v then f v (k + 1) / f v 1 else f v k

def childCoefficient (inc : E → V → Prop) (f : V → ℕ → R) (e : E) : R :=
  ∏ v, if inc e v then f v 1 else 1

theorem partition_shift_normalization (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → R) (z : E → R) (e : E)
    (h1 : ∀ v, inc e v → f v 1 ≠ 0) :
    partition inc edges (shiftedSignature inc f e) z =
      childCoefficient inc f e * partition inc edges (normalizedChildSignature inc f e) z := by
  rw [childCoefficient, ← partition_scale]
  congr 1
  funext v k
  by_cases h : inc e v
  · simp only [shiftedSignature, normalizedChildSignature, if_pos h]
    exact (mul_div_cancel₀ (f v (k + 1)) (h1 v h)).symm
  · simp [shiftedSignature, normalizedChildSignature, h]

/-- The normalized zero-child and one-child have exactly the paper's recursion.
In particular the normalized one-child is defined even when `z e = 0`. -/
theorem partition_normalized_deletion (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → R) (z : E → R) (e : E) (he : e ∈ edges)
    (h1 : ∀ v, inc e v → f v 1 ≠ 0) :
    partition inc edges f z = partition inc (edges.erase e) f z +
      z e * childCoefficient inc f e *
        partition inc (edges.erase e) (normalizedChildSignature inc f e) z := by
  rw [partition_deletion inc edges f z e he,
    partition_shift_normalization inc (edges.erase e) f z e h1, mul_assoc]

end Field

section Real

variable (inc : E → V → Prop) (edges : Finset E) (f : V → ℕ → ℝ) (x : E → ℝ)

lemma weight_nonneg (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ e ∈ edges, 0 ≤ x e) {S : Finset E} (hS : S ⊆ edges) :
    0 ≤ weight inc f x S :=
  mul_nonneg (Finset.prod_nonneg fun v _ => hf v _)
    (Finset.prod_nonneg fun e he => hx e (hS he))

/-- The empty configuration alone gives a strictly positive lower bound on
the entire nonnegative orthant. -/
theorem partition_ge_empty (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ e ∈ edges, 0 ≤ x e) : (∏ v, f v 0) ≤ partition inc edges f x := by
  simpa only [weight_empty, partition] using Finset.single_le_sum
    (s := edges.powerset) (f := weight inc f x)
    (fun S hS => weight_nonneg inc edges f x hf hx (Finset.mem_powerset.mp hS))
    (Finset.empty_mem_powerset edges)

theorem partition_pos (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, 0 < f v 0)
    (hx : ∀ e ∈ edges, 0 ≤ x e) : 0 < partition inc edges f x :=
  lt_of_lt_of_le (Finset.prod_pos fun v _ => hf0 v) (partition_ge_empty inc edges f x hf hx)

theorem normalized_partition_ge_one (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, f v 0 = 1) (hx : ∀ e ∈ edges, 0 ≤ x e) :
    1 ≤ partition inc edges f x := by
  simpa only [hf0, Finset.prod_const_one] using partition_ge_empty inc edges f x hf hx

/-- Termwise monotonicity uses only the degrees that can actually occur. -/
theorem partition_mono_signatures (g : V → ℕ → ℝ)
    (hf : ∀ v k, 0 ≤ f v k) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (hfg : ∀ v k, k ≤ selectedDegree inc edges v → f v k ≤ g v k) :
    partition inc edges f x ≤ partition inc edges g x := by
  apply Finset.sum_le_sum
  intro S hS
  have hs := Finset.mem_powerset.mp hS
  apply mul_le_mul_of_nonneg_right
  · exact Finset.prod_le_prod (fun v _ => hf v _) fun v _ =>
      hfg v _ (selectedDegree_mono inc hs v)
  · exact Finset.prod_nonneg fun e he => hx e (hs he)

/-- The log-concave shift inequality implies normalized child monotonicity by
comparing the actual finite subset summands. -/
theorem child_partition_le (e : E) (hf : ∀ v k, 0 ≤ f v k)
    (hx : ∀ a ∈ edges.erase e, 0 ≤ x a)
    (hshift : ∀ v k, inc e v → k ≤ selectedDegree inc (edges.erase e) v →
      f v (k + 1) / f v 1 ≤ f v k) :
    partition inc (edges.erase e) (normalizedChildSignature inc f e) x ≤
      partition inc (edges.erase e) f x := by
  apply partition_mono_signatures inc (edges.erase e) _ x f
  · intro v k
    unfold normalizedChildSignature
    split_ifs
    · exact div_nonneg (hf v _) (hf v _)
    · exact hf v k
  · exact hx
  · intro v k hk
    unfold normalizedChildSignature
    split_ifs with h
    · exact hshift v k h hk
    · exact le_rfl

end Real

/-- Structural feasibility ignores activities, as required at zero base
coordinates in the separator expansion. -/
def Feasible (inc : E → V → Prop) (f : V → ℕ → ℝ) (S : Finset E) : Prop :=
  ∀ v, 0 < f v (selectedDegree inc S v)

/-- Initial-interval signature support gives downward closure of structural
feasibility, independently of zero activities. -/
theorem feasible_downward (inc : E → V → Prop) (f : V → ℕ → ℝ)
    (hsupport : ∀ v i j, i ≤ j → 0 < f v j → 0 < f v i)
    {S T : Finset E} (hST : S ⊆ T) (hT : Feasible inc f T) : Feasible inc f S := by
  intro v
  exact hsupport v _ _ (selectedDegree_mono inc hST v) (hT v)

@[simp] theorem feasible_empty (inc : E → V → Prop) (f : V → ℕ → ℝ)
    (hf0 : ∀ v, 0 < f v 0) : Feasible inc f ∅ := by
  intro v
  simpa using hf0 v

/-- Casting the real subset sum gives precisely its complex evaluation. -/
theorem partition_ofReal (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) :
    partition inc edges (fun v k => (f v k : ℂ)) (fun e => (x e : ℂ)) =
      ((partition inc edges f x : ℝ) : ℂ) := by
  simp [partition, weight, signatureWeight, Complex.ofReal_sum, Complex.ofReal_prod]

theorem partition_complex_ne_zero (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ e ∈ edges, 0 ≤ x e) :
    partition inc edges (fun v k => (f v k : ℂ)) (fun e => (x e : ℂ)) ≠ 0 := by
  rw [partition_ofReal]
  exact_mod_cast (partition_pos inc edges f x hf hf0 hx).ne'

section Graph
variable [DecidableEq V]

/-- Incidence for actual unordered simple-graph edges. -/
def graphIncidence (e : Sym2 V) (v : V) : Prop := v ∈ e

/-- The multivariate finite-simple-graph polynomial in equation
`eq:holant-short-Z`, with one independent activity per unordered edge. -/
def graphPartition [CommSemiring R] (G : SimpleGraph V)
    (f : V → ℕ → R) (z : Sym2 V → R) : R :=
  partition graphIncidence G.edgeFinset f z

theorem graphPartition_pos (G : SimpleGraph V) (f : V → ℕ → ℝ)
    (x : Sym2 V → ℝ) (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, 0 < f v 0)
    (hx : ∀ e ∈ G.edgeFinset, 0 ≤ x e) : 0 < graphPartition G f x :=
  partition_pos graphIncidence G.edgeFinset f x hf hf0 hx

@[simp] theorem selectedDegree_graph (G : SimpleGraph V) (v : V) :
    selectedDegree graphIncidence G.edgeFinset v = G.degree v := by
  unfold selectedDegree
  convert G.card_incidenceFinset_eq_degree v using 2
  rw [G.incidenceFinset_eq_filter]
  congr 1

/-- The ambient-edge deletion representation is exactly actual graph deletion. -/
@[simp] theorem graphPartition_delete [CommSemiring R] (G : SimpleGraph V)
    (f : V → ℕ → R) (z : Sym2 V → R) (e : Sym2 V) :
    graphPartition (G.deleteEdges {e}) f z =
      partition graphIncidence (G.edgeFinset.erase e) f z := by
  unfold graphPartition
  congr 1
  ext a
  simp [and_comm]

/-- In a simple graph the removed normalization is precisely the product of
the two endpoint first entries. -/
theorem graph_childCoefficient [Field R] (f : V → ℕ → R) (u v : V) (huv : u ≠ v) :
    childCoefficient graphIncidence f s(u, v) = f u 1 * f v 1 := by
  unfold childCoefficient graphIncidence
  have hmem (w : V) : w ∈ s(u, v) ↔ w ∈ ({u, v} : Finset V) := by
    simp [Sym2.mem_iff]
  simp_rw [hmem]
  rw [Finset.prod_ite_mem_eq, Finset.prod_pair huv]

theorem graphPartition_normalized_deletion [Field R] (G : SimpleGraph V)
    (f : V → ℕ → R) (z : Sym2 V → R) (u v : V) (huv : G.Adj u v)
    (hu : f u 1 ≠ 0) (hv : f v 1 ≠ 0) :
    graphPartition G f z = graphPartition (G.deleteEdges {s(u, v)}) f z +
      z s(u, v) * (f u 1 * f v 1) *
        graphPartition (G.deleteEdges {s(u, v)})
          (normalizedChildSignature graphIncidence f s(u, v)) z := by
  rw [graphPartition_delete, graphPartition_delete, graphPartition,
    partition_normalized_deletion graphIncidence G.edgeFinset f z s(u, v)
      (by simpa using huv) (by
        intro w hw
        rcases Sym2.mem_iff.mp hw with rfl | rfl
        · exact hu
        · exact hv), graph_childCoefficient f u v huv.ne]

end Graph
end
end CI2ZF.Holant
