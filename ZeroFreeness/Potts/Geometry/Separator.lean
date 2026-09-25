import ZeroFreeness.Coupling.Foundations.FiniteCoupling
import ZeroFreeness.Potts.Model.Real.Model
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
# Exact Potts factorization across a separator

The free vertex set is explicitly `U ⊕ (S ⊕ O)`. Only the absence of
`U`--`O` edges is assumed. Boundary-count factors and all actual graph-edge
factors are split into inside and exterior factors, then the original finite
partition sum is factored. The exterior factors are independent of the
inside coloring. All algebra works over any commutative semiring, hence
both for real activities and for complex activities, including zero.
-/

namespace ZeroFreeness.Potts.Separator

open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section

local instance (priority := 2000) (A B : Type*) : DecidableEq (A → B) := Classical.decEq _

variable {U S O C R : Type*}

abbrev Vertex (U S O : Type*) := U ⊕ (S ⊕ O)

/-- Assemble the three pieces of a coloring. -/
def join (α : U → C) (ξ : S → C) (ζ : O → C) : Vertex U S O → C :=
  Sum.elim α (Sum.elim ξ ζ)

/-- The separator restriction of a full free coloring. -/
def shell (σ : Vertex U S O → C) : S → C := fun s => σ (Sum.inr (Sum.inl s))

/-- Colorings split bijectively into separator, inside, and outside colorings. -/
def coloringEquiv : (Vertex U S O → C) ≃ (S → C) × ((U → C) × (O → C)) where
  toFun σ := (shell σ, (fun u => σ (Sum.inl u)), fun o => σ (Sum.inr (Sum.inr o)))
  invFun p := join p.2.1 p.1 p.2.2
  left_inv σ := by funext v; rcases v with u | s | o <;> rfl
  right_inv p := by cases p with | mk ξ p => cases p; rfl

/-- A true graph separator: no free edge joins inside directly to outside. -/
def Separates (I : PinningData (Vertex U S O) C) : Prop :=
  ∀ u o, ¬ I.graph.Adj (Sum.inl u) (Sum.inr (Sum.inr o))

section Weight

variable [CommSemiring R]

/-- The actual Potts edge factor, over an arbitrary commutative semiring. -/
def edgeWeight {V : Type*} (z : R) (σ : V → C) (e : Sym2 V) : R :=
  Sym2.lift ⟨fun u v => if σ u = σ v then z else 1, fun u v => by simp [eq_comm]⟩ e

@[simp] theorem edgeWeight_mk {V : Type*} (z : R) (σ : V → C) (u v : V) :
    edgeWeight z σ s(u, v) = if σ u = σ v then z else 1 := rfl

/-- A partial coloring supplies factors only when both ends have a color. -/
def partialEdgeWeight (z : R) (σ : Vertex U S O → Option C) (e : Sym2 (Vertex U S O)) : R :=
  Sym2.lift ⟨fun u v => if ∃ c, σ u = some c ∧ σ v = some c then z else 1,
    fun u v => by simp [and_comm]⟩ e

@[simp] theorem partialEdgeWeight_mk (z : R) (σ : Vertex U S O → Option C)
    (u v : Vertex U S O) :
    partialEdgeWeight z σ s(u, v) =
      if ∃ c, σ u = some c ∧ σ v = some c then z else 1 := rfl

end Weight

def insideColor (α : U → C) (ξ : S → C) : Vertex U S O → Option C :=
  Sum.elim (fun u => some (α u)) (Sum.elim (fun s => some (ξ s)) (fun _ => none))

def exteriorColor (ξ : S → C) (ζ : O → C) : Vertex U S O → Option C :=
  Sum.elim (fun _ => none) (Sum.elim (fun s => some (ξ s)) (fun o => some (ζ o)))

def isOutside : Vertex U S O → Prop := Sum.elim (fun _ => False) (Sum.elim (fun _ => False) (fun _ => True))

def touchesOutside (e : Sym2 (Vertex U S O)) : Prop :=
  Sym2.lift ⟨fun u v => isOutside u ∨ isOutside v, fun u v => by simp [or_comm]⟩ e

@[simp] theorem touchesOutside_mk (u v : Vertex U S O) :
    touchesOutside s(u, v) ↔ isOutside u ∨ isOutside v := Iff.rfl

section Finite

variable [Fintype U] [Fintype S] [Fintype O] [Fintype C] [CommSemiring R]

/-- Original free-vertex Potts weight, with every boundary and edge factor. -/
def weight (I : PinningData (Vertex U S O) C) (z : R) (σ : Vertex U S O → C) : R :=
  (∏ v, z ^ I.boundaryCount v (σ v)) * ∏ e ∈ I.graph.edgeFinset, edgeWeight z σ e

/-- Original free-vertex finite partition sum. -/
def partition (I : PinningData (Vertex U S O) C) (z : R) : R :=
  ∑ σ : Vertex U S O → C, weight I z σ

/-- Exactly those factors involving no outside vertex. -/
def insideWeight (I : PinningData (Vertex U S O) C) (z : R) (α : U → C) (ξ : S → C) : R :=
  ((∏ u, z ^ I.boundaryCount (Sum.inl u) (α u)) *
    (∏ s, z ^ I.boundaryCount (Sum.inr (Sum.inl s)) (ξ s))) *
    ∏ e ∈ I.graph.edgeFinset.filter (fun e => ¬ touchesOutside e),
      partialEdgeWeight z (insideColor α ξ) e

/-- Exactly those factors involving an outside free vertex; this expression
has no inside-color argument. -/
def exteriorWeight (I : PinningData (Vertex U S O) C) (z : R) (ξ : S → C) (ζ : O → C) : R :=
  (∏ o, z ^ I.boundaryCount (Sum.inr (Sum.inr o)) (ζ o)) *
    ∏ e ∈ I.graph.edgeFinset.filter touchesOutside,
      partialEdgeWeight z (exteriorColor ξ ζ) e

/-- The bounded inside polynomial `D` from the paper. -/
def insidePartition (I : PinningData (Vertex U S O) C) (z : R) (ξ : S → C) : R :=
  ∑ α : U → C, insideWeight I z α ξ

/-- The exterior partition sum after fixing the separator coloring. -/
def exteriorPartition (I : PinningData (Vertex U S O) C) (z : R) (ξ : S → C) : R :=
  ∑ ζ : O → C, exteriorWeight I z ξ ζ

omit [Fintype U] [Fintype S] [Fintype O] [Fintype C] in
lemma edgeWeight_eq_inside (z : R) (α : U → C) (ξ : S → C) (ζ : O → C)
    (e : Sym2 (Vertex U S O)) (he : ¬ touchesOutside e) :
    edgeWeight z (join α ξ ζ) e = partialEdgeWeight z (insideColor α ξ) e := by
  induction e using Sym2.ind with
  | _ v w =>
    rcases v with u | s | o <;> rcases w with u' | s' | o'
    all_goals simp_all [touchesOutside_mk, isOutside, insideColor, join, eq_comm]
    all_goals split_ifs <;> simp_all

omit [Fintype C] in
lemma edgeWeight_eq_exterior (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (z : R) (α : U → C) (ξ : S → C) (ζ : O → C)
    (e : Sym2 (Vertex U S O)) (he : e ∈ I.graph.edgeFinset) (hout : touchesOutside e) :
    edgeWeight z (join α ξ ζ) e = partialEdgeWeight z (exteriorColor ξ ζ) e := by
  induction e using Sym2.ind with
  | _ v w =>
    have hadj : I.graph.Adj v w := (SimpleGraph.mem_edgeFinset.mp he)
    rcases v with u | s | o <;> rcases w with u' | s' | o'
    all_goals simp_all [touchesOutside_mk, isOutside, exteriorColor, join, eq_comm]
    all_goals first
      | exact (hsep _ _ hadj).elim
      | exact (hsep _ _ hadj.symm).elim
      | split_ifs <;> simp_all

omit [Fintype C] in
/-- The weight factorization is proved from the original graph edges and
the absence of inside--outside edges, with no partition identity assumed. -/
theorem weight_join (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (z : R) (α : U → C) (ξ : S → C) (ζ : O → C) :
    weight I z (join α ξ ζ) = insideWeight I z α ξ * exteriorWeight I z ξ ζ := by
  have hin : (∏ e ∈ I.graph.edgeFinset.filter (fun e => ¬ touchesOutside e),
      edgeWeight z (join α ξ ζ) e) =
      ∏ e ∈ I.graph.edgeFinset.filter (fun e => ¬ touchesOutside e),
        partialEdgeWeight z (insideColor α ξ) e := by
    apply Finset.prod_congr rfl
    intro e he
    exact edgeWeight_eq_inside z α ξ ζ e (Finset.mem_filter.mp he).2
  have hout : (∏ e ∈ I.graph.edgeFinset.filter touchesOutside,
      edgeWeight z (join α ξ ζ) e) =
      ∏ e ∈ I.graph.edgeFinset.filter touchesOutside,
        partialEdgeWeight z (exteriorColor ξ ζ) e := by
    apply Finset.prod_congr rfl
    intro e he
    exact edgeWeight_eq_exterior I hsep z α ξ ζ e
      (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
  unfold weight insideWeight exteriorWeight
  rw [← Finset.prod_filter_mul_prod_filter_not I.graph.edgeFinset touchesOutside]
  rw [hin, hout]
  simp only [Fintype.prod_sum_type, join, Sum.elim_inl, Sum.elim_inr]
  ring

omit [CommSemiring R] in
/-- Finite colorings split into independent sums over the three pieces. -/
theorem sum_colorings {M : Type*} [AddCommMonoid M] (f : (Vertex U S O → C) → M) :
    (∑ σ : Vertex U S O → C, f σ) =
      ∑ ξ : S → C, ∑ α : U → C, ∑ ζ : O → C, f (join α ξ ζ) := by
  rw [Fintype.sum_equiv coloringEquiv _
    (fun p : (S → C) × ((U → C) × (O → C)) => f (join p.2.1 p.1 p.2.2))
      (fun σ => by congr 1; exact (coloringEquiv.left_inv σ).symm)]
  simp only [Fintype.sum_prod_type]

/-- Reindex the original finite sum by the three actual coloring pieces. -/
theorem partition_eq_triple_sum (I : PinningData (Vertex U S O) C) (z : R) :
    partition I z = ∑ ξ : S → C, ∑ α : U → C, ∑ ζ : O → C, weight I z (join α ξ ζ) := by
  unfold partition
  rw [Fintype.sum_equiv coloringEquiv _
    (fun p : (S → C) × ((U → C) × (O → C)) => weight I z (join p.2.1 p.1 p.2.2))
      (fun σ => by congr 1; exact (coloringEquiv.left_inv σ).symm)]
  simp only [Fintype.sum_prod_type]

/-- Exact separator partition factorization, at every activity including zero. -/
theorem partition_factorization (I : PinningData (Vertex U S O) C) (hsep : Separates I) (z : R) :
    partition I z = ∑ ξ : S → C, insidePartition I z ξ * exteriorPartition I z ξ := by
  rw [partition_eq_triple_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  simp_rw [weight_join I hsep]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

end Finite

section Real

variable [Fintype U] [Fintype S] [Fintype O] [Fintype C]

omit [Fintype C] in
/-- The real specialization is exactly the pre-existing Potts weight. -/
theorem weight_real (I : PinningData (Vertex U S O) C) (x : ℝ) (σ : Vertex U S O → C) :
    weight I x σ = I.weight x σ := rfl

/-- The partition factorized above is the actual original real Potts partition. -/
theorem partition_real (I : PinningData (Vertex U S O) C) (x : ℝ) :
    partition I x = I.partition x := rfl

/-- The paper's finite-sum separator formula for the actual real model. -/
theorem real_partition_factorization (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) (x : ℝ) :
    I.partition x = ∑ ξ : S → C, insidePartition I x ξ * exteriorPartition I x ξ :=
  partition_factorization I hsep x

/-- The shell marginal is the actual pushforward of the normalized Gibbs law. -/
def shellMarginal (I : PinningData (Vertex U S O) C) (x : ℝ) (hx : 0 ≤ x)
    (hZ : 0 < I.partition x) : FinDist (S → C) :=
  mapLaw (I.gibbs x hx hZ) shell

/-- The paper's shell-marginal formula, proved from the actual Gibbs
pushforward and the separator's original finite sum. -/
theorem shellMarginal_apply (I : PinningData (Vertex U S O) C) (hsep : Separates I)
    (x : ℝ) (hx : 0 ≤ x) (hZ : 0 < I.partition x) (ξ : S → C) :
    (shellMarginal I x hx hZ).w ξ =
      insidePartition I x ξ * exteriorPartition I x ξ / I.partition x := by
  simp only [shellMarginal, mapLaw, FinDist.bind, FinDist.pure, PinningData.gibbs]
  change (∑ σ : Vertex U S O → C,
    (weight I x σ / I.partition x) * (if ξ = shell σ then 1 else 0)) = _
  rw [sum_colorings]
  simp_rw [weight_join I hsep]
  change (∑ η : S → C, ∑ α : U → C, ∑ ζ : O → C,
    (insideWeight I x α η * exteriorWeight I x η ζ / I.partition x) *
      (if ξ = η then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [← Finset.sum_div, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rfl

end Real

end

end ZeroFreeness.Potts.Separator
