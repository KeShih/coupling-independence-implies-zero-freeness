import CI2ZF.Coupling.Edge.Approximation
import Mathlib.Data.Fintype.Perm

/-!
# Finite distinct-slot moments

The coefficient of the product of linear slot factors is the elementary
symmetric sum. Multiplying by `k!` gives the literal sum over injective
ordered slot assignments. This is the finite version of the slot identity.
-/

namespace CI2ZF.Appendix.Edge

open Polynomial
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {R : Type*} [Fintype R] [DecidableEq R]

def slotGeneratingPolynomial (κ : R → ℝ) : Polynomial ℝ :=
  ∏ r, (1 + C (κ r) * X)

lemma slotGeneratingPolynomial_constant (κ : R → ℝ) :
    (slotGeneratingPolynomial κ).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero]
  simp [slotGeneratingPolynomial, eval_prod]

lemma prod_slot_monomials (κ : R → ℝ) (A : Finset R) :
    (∏ r ∈ A, C (κ r) * X) = C (∏ r ∈ A, κ r) * X ^ A.card := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, map_prod]

lemma slotGeneratingPolynomial_coeff (κ : R → ℝ) (k : ℕ) :
    (slotGeneratingPolynomial κ).coeff k =
      ∑ A ∈ (Finset.univ : Finset R).powersetCard k, ∏ r ∈ A, κ r := by
  unfold slotGeneratingPolynomial
  rw [Finset.prod_one_add]
  simp only [finsetSum_coeff, prod_slot_monomials, coeff_C_mul_X_pow,
    Finset.powersetCard_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  simp [eq_comm]

lemma slotGeneratingPolynomial_linear (κ : R → ℝ) :
    (slotGeneratingPolynomial κ).coeff 1 = ∑ r, κ r := by
  rw [slotGeneratingPolynomial_coeff, Finset.powersetCard_one, Finset.sum_map]
  simp

/-- The finite set of values attained by an injective ordered tuple. -/
def slotEmbeddingRange {k : ℕ} (e : Fin k ↪ R) : Finset R := Finset.univ.map e

@[simp] lemma slotEmbeddingRange_card {k : ℕ} (e : Fin k ↪ R) :
    (slotEmbeddingRange e).card = k := by simp [slotEmbeddingRange]

def slotRangeFibreEquiv (k : ℕ) (A : Finset R) :
    {e : Fin k ↪ R // slotEmbeddingRange e = A} ≃ (Fin k ≃ A) where
  toFun z := Equiv.ofBijective
    (fun i => ⟨z.val i, by
      have hm : z.val i ∈ slotEmbeddingRange z.val :=
        Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
      exact (congrArg (fun B : Finset R => z.val i ∈ B) z.property).mp hm⟩)
    ⟨fun _ _ h => z.val.injective (Subtype.mk.inj h), by
      intro a
      have ha : a.val ∈ slotEmbeddingRange z.val := z.property.symm ▸ a.property
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ha
      exact ⟨i, Subtype.ext hi⟩⟩
  invFun e := ⟨Equiv.asEmbedding e, by
    ext r
    constructor
    · intro h
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
      exact hi ▸ (e i).property
    · intro hr
      obtain ⟨i, hi⟩ := e.surjective ⟨r, hr⟩
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, congrArg Subtype.val hi⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

lemma slotRangeFibre_card (k : ℕ) (A : Finset R) (hA : A.card = k) :
    Fintype.card {e : Fin k ↪ R // slotEmbeddingRange e = A} = k.factorial := by
  rw [Fintype.card_congr (slotRangeFibreEquiv k A)]
  have e : Fin k ≃ A := Fintype.equivOfCardEq (by simp [hA])
  simpa using Fintype.card_equiv e

lemma slotRangeFibre_weight (κ : R → ℝ) (k : ℕ) (A : Finset R)
    (e : {e : Fin k ↪ R // slotEmbeddingRange e = A}) :
    (∏ i, κ (e.val i)) = ∏ r ∈ A, κ r := by
  calc
    _ = ∏ r ∈ slotEmbeddingRange e.val, κ r := (Finset.prod_map Finset.univ e.val κ).symm
    _ = _ := congrArg (fun B : Finset R => ∏ r ∈ B, κ r) e.property

lemma slotRangeFibre_sum (κ : R → ℝ) (k : ℕ) (A : Finset R) (hA : A.card = k) :
    (∑ e : Fin k ↪ R with slotEmbeddingRange e = A, ∏ i, κ (e i)) =
      k.factorial * ∏ r ∈ A, κ r := by
  classical
  have hsub : (∑ e : Fin k ↪ R with slotEmbeddingRange e = A, ∏ i, κ (e i)) =
      ∑ e : {e : Fin k ↪ R // slotEmbeddingRange e = A}, ∏ i, κ (e.val i) :=
    Finset.sum_subtype _ (by simp) _
  rw [hsub]
  simp only [slotRangeFibre_weight, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    slotRangeFibre_card k A hA]

lemma sum_slot_embedding_eq_factorial_coeff (κ : R → ℝ) (k : ℕ) :
    (∑ e : Fin k ↪ R, ∏ i, κ (e i)) = k.factorial * (slotGeneratingPolynomial κ).coeff k := by
  have hm : ∀ e ∈ (Finset.univ : Finset (Fin k ↪ R)),
      slotEmbeddingRange e ∈ (Finset.univ : Finset R).powersetCard k := by
    intro e _
    simp [Finset.mem_powersetCard]
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun e => ∏ i, κ (e i)),
    slotGeneratingPolynomial_coeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact slotRangeFibre_sum κ k A (Finset.mem_powersetCard.mp hA).2

/-- The actual probability numerator for `k` independently sampled slots to
be all distinct, written as a finite sum over ordinary functions. -/
def distinctSlotMass (κ : R → ℝ) (k : ℕ) : ℝ :=
  ∑ f : Fin k → R, if Function.Injective f then ∏ i, κ (f i) else 0

lemma distinctSlotMass_eq_embedding_sum (κ : R → ℝ) (k : ℕ) :
    distinctSlotMass κ k = ∑ e : Fin k ↪ R, ∏ i, κ (e i) := by
  classical
  unfold distinctSlotMass
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (p := Function.Injective) (by simp)]
  apply Fintype.sum_equiv (Equiv.subtypeInjectiveEquivEmbedding (Fin k) R)
  intro f
  rfl

/-- Ordered injective tuples contribute exactly `k!` times the degree-`k`
coefficient of the slot generating polynomial. -/
lemma distinctSlotMass_eq_factorial_coeff (κ : R → ℝ) (k : ℕ) :
    distinctSlotMass κ k = k.factorial * (slotGeneratingPolynomial κ).coeff k := by
  rw [distinctSlotMass_eq_embedding_sum, sum_slot_embedding_eq_factorial_coeff]

end
end CI2ZF.Appendix.Edge
