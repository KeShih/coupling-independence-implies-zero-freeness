import ZeroFreeness.Potts.Model.Real.Model
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Active constraints for the soft Potts model

This file formalizes the elementary soft-to-hard expansion used by the
near-Vigoda and Carlson--Vigoda coupling arguments.  Every free edge is one
physical constraint, while a boundary colour of multiplicity `m` contributes
`m` separately labelled constraint occurrences.  Expanding

`x * 1[equality] + 1 * 1[inequality] = x + (1-x) * 1[inequality]`

over those occurrences gives an exact sum over active sets.  This module also
identifies the normalized conditional spin law with the uniform law on its
hard fibre.  Component-flip arguments remain in the model-specific coupling
modules.
-/

namespace PottsCI

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} {C : Type*}
variable [Fintype V] [Fintype C]

namespace PinningData

variable (I : PinningData V C)

/-- A free edge, carrying a proof that it belongs to the free graph. -/
abbrev FreeEdge (I : PinningData V C) := ↥I.graph.edgeFinset

/-- A separately labelled boundary occurrence.  The last coordinate records
which one of the `boundaryCount u c` pinned neighbours is meant. -/
abbrev BoundaryOccurrence (I : PinningData V C) :=
  Σ u : V, Σ c : C, Fin (I.boundaryCount u c)

/-- The finite type of all physical constraint occurrences. -/
abbrev Constraint (I : PinningData V C) := FreeEdge I ⊕ BoundaryOccurrence I

/-- A free edge is satisfied when it is bichromatic; a boundary occurrence of
colour `c` at `u` is satisfied when the free spin at `u` is not `c`. -/
def constraintSatisfied (σ : V → C) : Constraint I → Prop
  | Sum.inl e =>
      Sym2.lift
        ⟨fun u v => σ u ≠ σ v, fun u v => by simp only [ne_eq, ne_comm]⟩ e.1
  | Sum.inr ⟨u, c, _⟩ => σ u ≠ c

/-- The ordinary Potts factor belonging to one physical constraint. -/
noncomputable def constraintFactor (x : ℝ) (σ : V → C) (k : Constraint I) : ℝ :=
  if I.constraintSatisfied σ k then 1 else x

/-- The active contribution of one constraint: it is `1-x` if this constraint
may be activated at `σ`, and zero otherwise. -/
noncomputable def activationFactor (x : ℝ) (σ : V → C) (k : Constraint I) : ℝ :=
  if I.constraintSatisfied σ k then 1 - x else 0

/-- The contribution of a fixed active set.  Each member contributes its
activation weight; each inactive physical constraint contributes `x`. -/
noncomputable def activeSetWeight (x : ℝ) (σ : V → C)
    (A : Finset (Constraint I)) : ℝ := by
  classical
  exact (∏ k ∈ A, I.activationFactor x σ k) * ∏ _k ∈ Finset.univ \ A, x

/-- A colouring satisfies all hard inequalities selected by `A`. -/
def ActiveCompatible (σ : V → C) (A : Finset (Constraint I)) : Prop :=
  ∀ k ∈ A, I.constraintSatisfied σ k

/-- The set of constraints eligible for activation at `σ`. -/
noncomputable def eligibleSet (σ : V → C) : Finset (Constraint I) :=
  Finset.univ.filter fun k => I.constraintSatisfied σ k

/-- The scalar attached to an active set.  It does not depend on the spin
configuration; compatibility with the selected hard inequalities is recorded
separately. -/
noncomputable def activeScalar (x : ℝ) (A : Finset (Constraint I)) : ℝ := by
  exact (1 - x) ^ A.card * x ^ (Fintype.card (Constraint I) - A.card)

/-- The unnormalized joint spin--active-set weight. -/
noncomputable def jointActiveWeight (x : ℝ) (A : Finset (Constraint I))
    (σ : V → C) : ℝ :=
  if I.ActiveCompatible σ A then I.activeScalar x A else 0

/-- The hard fibre selected by an active set. -/
noncomputable def compatibleColorings (A : Finset (Constraint I)) : Finset (V → C) :=
  Finset.univ.filter fun σ => I.ActiveCompatible σ A

omit [Fintype C] in
@[simp]
lemma constraintFactor_freeEdge (x : ℝ) (σ : V → C) (e : FreeEdge I) :
    I.constraintFactor x σ (Sum.inl e) = edgeFactor x σ e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
    simp only [constraintFactor, constraintSatisfied, Sym2.lift_mk, edgeFactor_mk]
    by_cases huv : σ u = σ v <;> simp [huv]

omit [Fintype C] in
@[simp]
lemma constraintFactor_boundary (x : ℝ) (σ : V → C) (u : V) (c : C)
    (i : Fin (I.boundaryCount u c)) :
    I.constraintFactor x σ (Sum.inr ⟨u, c, i⟩) =
      if σ u = c then x else 1 := by
  by_cases huc : σ u = c <;> simp [constraintFactor, constraintSatisfied, huc]

/-- Multiplying the factors of all separately labelled boundary occurrences
recovers the boundary part of the Potts weight. -/
lemma boundaryConstraintProduct (x : ℝ) (σ : V → C) :
    (∏ b : BoundaryOccurrence I, I.constraintFactor x σ (Sum.inr b)) =
      ∏ u, x ^ I.boundaryCount u (σ u) := by
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [Fintype.prod_sigma]
  classical
  rw [Finset.prod_eq_single (σ u)]
  · simp
  · intro c _ hcu
    have huc : σ u ≠ c := fun h => hcu h.symm
    simp [huc]
  · simp

omit [Fintype C] in
/-- Multiplying the constraint factors over the free-edge occurrences recovers
the free-edge part of the Potts weight. -/
lemma freeEdgeConstraintProduct (x : ℝ) (σ : V → C) :
    (∏ e : FreeEdge I, I.constraintFactor x σ (Sum.inl e)) =
      ∏ e ∈ I.graph.edgeFinset, edgeFactor x σ e := by
  calc
    (∏ e : FreeEdge I, I.constraintFactor x σ (Sum.inl e)) =
        ∏ e : FreeEdge I, edgeFactor x σ e.1 := by
          refine Finset.prod_congr rfl fun e _ => ?_
          exact I.constraintFactor_freeEdge x σ e
    _ = ∏ e ∈ I.graph.edgeFinset, edgeFactor x σ e :=
      Finset.prod_coe_sort I.graph.edgeFinset (edgeFactor x σ)

/-- The original Potts weight is the product of its separately labelled
physical constraint factors. -/
lemma weight_eq_constraintProduct (x : ℝ) (σ : V → C) :
    I.weight x σ = ∏ k : Constraint I, I.constraintFactor x σ k := by
  rw [Fintype.prod_sum_type, I.freeEdgeConstraintProduct, I.boundaryConstraintProduct]
  simp only [weight, mul_comm]

omit [Fintype C] in
/-- The one-constraint soft-to-hard identity. -/
lemma constraintFactor_eq_activation_add (x : ℝ) (σ : V → C) (k : Constraint I) :
    I.constraintFactor x σ k = I.activationFactor x σ k + x := by
  by_cases hk : I.constraintSatisfied σ k
  · simp [constraintFactor, activationFactor, hk]
  · simp [constraintFactor, activationFactor, hk]

/-- Exact expansion of one spin weight as a sum over active sets. -/
lemma weight_eq_sum_activeSetWeight (x : ℝ) (σ : V → C) :
    I.weight x σ = ∑ A : Finset (Constraint I), I.activeSetWeight x σ A := by
  rw [I.weight_eq_constraintProduct]
  calc
    (∏ k : Constraint I, I.constraintFactor x σ k) =
        ∏ k : Constraint I, (I.activationFactor x σ k + x) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          exact I.constraintFactor_eq_activation_add x σ k
    _ = ∑ A : Finset (Constraint I), I.activeSetWeight x σ A := by
      simpa [activeSetWeight, Finset.compl_eq_univ_sdiff] using
        (Fintype.prod_add (fun k : Constraint I => I.activationFactor x σ k)
          (fun _k : Constraint I => x))

@[simp]
lemma mem_eligibleSet (σ : V → C) (k : Constraint I) :
    k ∈ I.eligibleSet σ ↔ I.constraintSatisfied σ k := by
  simp [eligibleSet]

lemma activeCompatible_iff_subset_eligible (σ : V → C) (A : Finset (Constraint I)) :
    I.ActiveCompatible σ A ↔ A ⊆ I.eligibleSet σ := by
  simp only [ActiveCompatible, Finset.subset_iff, mem_eligibleSet]

/-- Closed form of the active-set scalar. -/
lemma activeScalar_eq (x : ℝ) (A : Finset (Constraint I)) :
    I.activeScalar x A =
      (1 - x) ^ A.card * x ^ (Fintype.card (Constraint I) - A.card) := by
  rfl

/-- On a compatible colouring, a fixed active set contributes its common
scalar and hence is independent of that colouring. -/
lemma activeSetWeight_eq_activeScalar {x : ℝ} {σ : V → C}
    {A : Finset (Constraint I)}
    (hA : I.ActiveCompatible σ A) :
    I.activeSetWeight x σ A = I.activeScalar x A := by
  classical
  have hactive : (∏ k ∈ A, I.activationFactor x σ k) = (1 - x) ^ A.card := by
    calc
      (∏ k ∈ A, I.activationFactor x σ k) = ∏ _k ∈ A, (1 - x : ℝ) := by
        refine Finset.prod_congr rfl fun k hk => ?_
        simp [activationFactor, hA k hk]
      _ = (1 - x) ^ A.card := Finset.prod_const _
  have hinactive : (∏ _k ∈ Finset.univ \ A, (x : ℝ)) =
      x ^ (Fintype.card (Constraint I) - A.card) := by
    rw [Finset.prod_const]
    congr 1
    simp [Finset.card_sdiff]
  unfold activeSetWeight activeScalar
  rw [hactive, hinactive]

/-- An active set containing an unsatisfied constraint has zero contribution.
-/
lemma activeSetWeight_eq_zero {x : ℝ} {σ : V → C}
    {A : Finset (Constraint I)}
    (hA : ¬I.ActiveCompatible σ A) :
    I.activeSetWeight x σ A = 0 := by
  unfold ActiveCompatible at hA
  push Not at hA
  obtain ⟨k, hkA, hksat⟩ := hA
  unfold activeSetWeight
  rw [Finset.prod_eq_zero hkA]
  · exact zero_mul _
  · rw [activationFactor, if_neg hksat]

/-- A fixed-active-set contribution is exactly its joint spin--active-set
weight. -/
lemma activeSetWeight_eq_jointActiveWeight (x : ℝ) (σ : V → C)
    (A : Finset (Constraint I)) :
    I.activeSetWeight x σ A = I.jointActiveWeight x A σ := by
  by_cases hA : I.ActiveCompatible σ A
  · rw [I.activeSetWeight_eq_activeScalar hA, jointActiveWeight, if_pos hA]
  · rw [I.activeSetWeight_eq_zero hA, jointActiveWeight, if_neg hA]

/-- For a fixed active set, all colourings in its hard fibre have exactly the
same joint weight.  This is the algebraic content of conditional uniformity. -/
lemma jointActiveWeight_eq_of_compatible {x : ℝ} {A : Finset (Constraint I)}
    {σ τ : V → C} (hσ : I.ActiveCompatible σ A) (hτ : I.ActiveCompatible τ A) :
    I.jointActiveWeight x A σ = I.jointActiveWeight x A τ := by
  simp [jointActiveWeight, hσ, hτ]

/-- Summing out the active set recovers the original Potts spin weight. -/
lemma sum_jointActiveWeight_eq_weight (x : ℝ) (σ : V → C) :
    (∑ A : Finset (Constraint I), I.jointActiveWeight x A σ) = I.weight x σ := by
  rw [I.weight_eq_sum_activeSetWeight]
  symm
  refine Finset.sum_congr rfl fun A _ => ?_
  exact I.activeSetWeight_eq_jointActiveWeight x σ A

/-- The total joint mass above a fixed active set is its common scalar times
the cardinality of the corresponding hard fibre. -/
lemma sum_jointActiveWeight_fixedActive (x : ℝ) (A : Finset (Constraint I)) :
    (∑ σ : V → C, I.jointActiveWeight x A σ) =
      (I.compatibleColorings A).card * I.activeScalar x A := by
  classical
  calc
    (∑ σ : V → C, I.jointActiveWeight x A σ) =
        (∑ σ : V → C, if I.ActiveCompatible σ A then (1 : ℝ) else 0) *
          I.activeScalar x A := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun σ _ => ?_
            by_cases hσ : I.ActiveCompatible σ A <;>
              simp [jointActiveWeight, hσ]
    _ = (I.compatibleColorings A).card * I.activeScalar x A := by
      congr 1
      simp [compatibleColorings]

/-- Exact spin marginal identity for the unnormalized joint
spin--active-set model. -/
lemma partition_eq_sum_jointActiveWeight (x : ℝ) :
    I.partition x =
      ∑ σ : V → C, ∑ A : Finset (Constraint I), I.jointActiveWeight x A σ := by
  unfold partition
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact (I.sum_jointActiveWeight_eq_weight x σ).symm

/-- Equivalent active-set marginal form of the partition function. -/
lemma partition_eq_sum_activeFibres (x : ℝ) :
    I.partition x = ∑ A : Finset (Constraint I),
      (I.compatibleColorings A).card * I.activeScalar x A := by
  rw [I.partition_eq_sum_jointActiveWeight, Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  exact I.sum_jointActiveWeight_fixedActive x A

/-- The joint weight is nonnegative throughout the probabilistic interval. -/
lemma jointActiveWeight_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (A : Finset (Constraint I)) (σ : V → C) :
    0 ≤ I.jointActiveWeight x A σ := by
  by_cases hA : I.ActiveCompatible σ A
  · rw [jointActiveWeight, if_pos hA, I.activeScalar_eq]
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hx1) _) (pow_nonneg hx0 _)
  · rw [jointActiveWeight, if_neg hA]

/-! ## The normalized conditional law -/

/-- The unnormalized marginal weight of an active set. -/
noncomputable def activeMass (x : ℝ) (A : Finset (Constraint I)) : ℝ :=
  ∑ σ : V → C, I.jointActiveWeight x A σ

lemma activeMass_eq (x : ℝ) (A : Finset (Constraint I)) :
    I.activeMass x A =
      (I.compatibleColorings A).card * I.activeScalar x A := by
  exact I.sum_jointActiveWeight_fixedActive x A

/-- Positive active-set mass forces the selected hard fibre to be nonempty.
This is the point that must not be omitted at `x = 0` or `x = 1`. -/
lemma compatibleColorings_nonempty_of_activeMass_pos {x : ℝ}
    {A : Finset (Constraint I)} (hmass : 0 < I.activeMass x A) :
    (I.compatibleColorings A).Nonempty := by
  by_contra hnone
  have hempty : I.compatibleColorings A = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hnone
  rw [I.activeMass_eq, hempty] at hmass
  simp at hmass

/-- Positive active-set mass also forces its common scalar to be positive. -/
lemma activeScalar_pos_of_activeMass_pos {x : ℝ} {A : Finset (Constraint I)}
    (hmass : 0 < I.activeMass x A) : 0 < I.activeScalar x A := by
  have hproduct :
      0 < (I.compatibleColorings A).card * I.activeScalar x A := by
    rw [← I.activeMass_eq]
    exact hmass
  exact pos_of_mul_pos_right hproduct (Nat.cast_nonneg _)

/-- The normalized spin law obtained by conditioning the joint model on an
active set of strictly positive mass. -/
noncomputable def spinLawGivenActive (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (A : Finset (Constraint I)) (hmass : 0 < I.activeMass x A) : FinDist (V → C) where
  w := fun σ => I.jointActiveWeight x A σ / I.activeMass x A
  nonneg := fun σ => div_nonneg (I.jointActiveWeight_nonneg hx0 hx1 A σ) hmass.le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self hmass.ne'

@[simp]
lemma spinLawGivenActive_w (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (A : Finset (Constraint I)) (hmass : 0 < I.activeMass x A) (σ : V → C) :
    (I.spinLawGivenActive x hx0 hx1 A hmass).w σ =
      I.jointActiveWeight x A σ / I.activeMass x A := rfl

/-- The uniform probability law on the compatible hard fibre, represented on
the full colouring space and extended by zero outside the fibre. -/
noncomputable def uniformHardFibre (A : Finset (Constraint I))
    (hne : (I.compatibleColorings A).Nonempty) : FinDist (V → C) where
  w := fun σ =>
    if I.ActiveCompatible σ A then ((I.compatibleColorings A).card : ℝ)⁻¹ else 0
  nonneg := fun σ => by
    split
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  sum_one := by
    classical
    have hcard : ((I.compatibleColorings A).card : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
    calc
      (∑ σ : V → C,
          if I.ActiveCompatible σ A then ((I.compatibleColorings A).card : ℝ)⁻¹ else 0) =
          (∑ σ : V → C, if I.ActiveCompatible σ A then (1 : ℝ) else 0) *
            ((I.compatibleColorings A).card : ℝ)⁻¹ := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun σ _ => ?_
              by_cases hσ : I.ActiveCompatible σ A <;> simp [hσ]
      _ = ((I.compatibleColorings A).card : ℝ) *
            ((I.compatibleColorings A).card : ℝ)⁻¹ := by
              congr 1
              simp [compatibleColorings]
      _ = 1 := mul_inv_cancel₀ hcard

@[simp]
lemma uniformHardFibre_w (A : Finset (Constraint I))
    (hne : (I.compatibleColorings A).Nonempty) (σ : V → C) :
    (I.uniformHardFibre A hne).w σ =
      if I.ActiveCompatible σ A then ((I.compatibleColorings A).card : ℝ)⁻¹ else 0 := rfl

/-- The genuine conditional-law statement: whenever the active set has
positive joint mass, conditioning on it makes the spin law uniform on the
proper list-colourings selected by its active hard inequalities. -/
theorem spinLawGivenActive_eq_uniformHardFibre {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (A : Finset (Constraint I)) (hmass : 0 < I.activeMass x A) :
    I.spinLawGivenActive x hx0 hx1 A hmass =
      I.uniformHardFibre A (I.compatibleColorings_nonempty_of_activeMass_pos hmass) := by
  apply PottsCI.FinDist.ext
  funext σ
  have hscalar : I.activeScalar x A ≠ 0 :=
    (I.activeScalar_pos_of_activeMass_pos hmass).ne'
  have hcard : ((I.compatibleColorings A).card : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr
      (I.compatibleColorings_nonempty_of_activeMass_pos hmass))
  by_cases hσ : I.ActiveCompatible σ A
  · rw [I.spinLawGivenActive_w, I.uniformHardFibre_w, if_pos hσ,
      jointActiveWeight, if_pos hσ, I.activeMass_eq]
    field_simp
  · rw [I.spinLawGivenActive_w, I.uniformHardFibre_w, if_neg hσ,
      jointActiveWeight, if_neg hσ, zero_div]

end PinningData

end PottsCI
