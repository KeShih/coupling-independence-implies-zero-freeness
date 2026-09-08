import CI2ZF.SeparatorRelabel
import CI2ZF.BoundedLocalFamily

/-! Polynomial semantics and a uniform finite-family bound for arbitrary
actual `PinningData`, including the smaller exterior after separator pinning. -/

namespace CI2ZF.Potts

open PottsCI Separator
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false

variable {V C R : Type*} [Fintype V] [Fintype C]

def pinningSameColour (σ : V → C) (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => σ u = σ v, fun _ _ => propext eq_comm⟩ e

@[simp] lemma pinningSameColour_mk (σ : V → C) (u v : V) :
    pinningSameColour σ s(u, v) ↔ σ u = σ v := Iff.rfl

def pinningExponent (I : PinningData V C) (σ : V → C) : ℕ :=
  (∑ v : V, I.boundaryCount v (σ v)) + (I.graph.edgeFinset.filter (pinningSameColour σ)).card

lemma edgeWeight_eq_ite [CommSemiring R] (z : R) (σ : V → C) (e : Sym2 V) :
    edgeWeight z σ e = if pinningSameColour σ e then z else 1 := by
  induction e using Sym2.ind with
  | _ u v => rfl

theorem pinningProductWeight_eq_pow [CommSemiring R]
    (I : PinningData V C) (z : R) (σ : V → C) :
    pinningProductWeight I z σ = z ^ pinningExponent I σ := by
  unfold pinningProductWeight pinningExponent
  rw [pow_add, Finset.prod_pow_eq_pow_sum]
  congr 1
  simp only [edgeWeight_eq_ite, Finset.prod_ite, Finset.prod_const_one,
    mul_one, Finset.prod_const, Finset.card_eq_sum_ones]

def pinningPolynomial (I : PinningData V C) : Polynomial ℂ :=
  ∑ σ : V → C, Polynomial.X ^ pinningExponent I σ

/-- The polynomial is exactly the original finite product partition. -/
theorem pinningPolynomial_eval (I : PinningData V C) (z : ℂ) :
    (pinningPolynomial I).eval z = pinningProductPartition I z := by
  simp only [pinningPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_pow,
    Polynomial.eval_X, pinningProductPartition, pinningProductWeight_eq_pow]

theorem pinningProductPartition_real (I : PinningData V C) (x : ℝ) :
    pinningProductPartition I x = I.partition x := rfl

theorem pinningPolynomial_ofReal (I : PinningData V C) (x : ℝ) :
    (pinningPolynomial I).eval (x : ℂ) = ((I.partition x : ℝ) : ℂ) := by
  rw [pinningPolynomial_eval, ← pinningProductPartition_real]
  simp only [pinningProductPartition, pinningProductWeight_eq_pow,
    Complex.ofReal_sum, Complex.ofReal_pow]

theorem pinningExponent_le (I : PinningData V C) (σ : V → C) (Δ B : ℕ)
    (hdegree : I.DegreeBound Δ) (hB : Fintype.card V ≤ B) :
    pinningExponent I σ ≤ 2 * B * Δ := by
  have hboundary (u : V) : I.boundaryCount u (σ u) ≤ Δ := by
    have hb := Finset.single_le_sum (s := Finset.univ)
      (f := fun c => I.boundaryCount u c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (σ u))
    have hd := hdegree u
    unfold PinningData.constraintDegree at hd
    omega
  have hb : (∑ u : V, I.boundaryCount u (σ u)) ≤ Fintype.card V * Δ :=
    (Finset.sum_le_sum (s := Finset.univ) (fun u _ => hboundary u)).trans_eq (by simp)
  have hfree (u : V) : I.graph.degree u ≤ Δ := by
    have hd := hdegree u
    unfold PinningData.constraintDegree at hd
    omega
  have hdeg : (∑ u : V, I.graph.degree u) ≤ Fintype.card V * Δ :=
    (Finset.sum_le_sum (fun u _ => hfree u)).trans_eq (by simp)
  have hedge := I.graph.sum_degrees_eq_twice_card_edges
  have hf : (I.graph.edgeFinset.filter (pinningSameColour σ)).card ≤ I.graph.edgeFinset.card :=
    Finset.card_filter_le _ _
  have hmul := Nat.mul_le_mul_right Δ hB
  unfold pinningExponent
  nlinarith

theorem pinningPolynomial_has_bounded_code [Nonempty C]
    (I : PinningData V C) (Δ B : ℕ) (hdegree : I.DegreeBound Δ)
    (hB : Fintype.card V ≤ B) :
    ∃ i : MonomialCode ((Fintype.card C) ^ B) (2 * B * Δ),
      i.polynomial = pinningPolynomial I := by
  apply encode_sum_monomials (pinningExponent I)
  · rw [Fintype.card_fun]
    exact Nat.pow_le_pow_right (Fintype.card_pos (α := C)) hB
  · exact fun σ => pinningExponent_le I σ Δ B hdegree hB

/-- The generic polynomial agrees exactly with the original normalized
polynomial semantics for an arbitrary partial colouring. -/
theorem pinningPolynomial_toPinningData (tau : PartialColouring V C) (G : SimpleGraph V) :
    pinningPolynomial (tau.toPinningData G) = normalizedPolynomial tau G := by
  unfold pinningPolynomial normalizedPolynomial
  have he (σ : tau.FreeVertex → C) : pinningExponent (tau.toPinningData G) σ =
      tau.boundaryConflictCount G σ + tau.freeConflictCount G σ := by
    unfold pinningExponent PartialColouring.boundaryConflictCount PartialColouring.freeConflictCount
    congr 1
  simp_rw [he]
  congr 2
  exact Subsingleton.elim _ _

theorem pinningProductPartition_toPinningData (tau : PartialColouring V C)
    (G : SimpleGraph V) (z : ℂ) :
    pinningProductPartition (tau.toPinningData G) z = normalizedPartition tau G z := by
  rw [← pinningPolynomial_eval, pinningPolynomial_toPinningData]
  rfl

/-- One radius works for every bounded free-volume, bounded-constraint-degree
pinning datum, with no dependence on its vertex names or boundary multiplicities. -/
theorem bounded_pinning_relative_stability (C : Type*) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (hcolours : Δ + 1 ≤ Fintype.card C)
    (K : Set ℂ) (hK : IsCompact K) (hreal : K ⊆ Complex.ofReal '' Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ {V : Type*} [Fintype V] (I : PinningData V C),
      I.DegreeBound Δ → Fintype.card V ≤ B →
      ∀ x ∈ K, ∀ z : ℂ, dist z x < ε →
        ‖pinningProductPartition I z / pinningProductPartition I x - 1‖ < η := by
  obtain ⟨ε, hε, hb⟩ := bounded_monomials_relative_stability ((Fintype.card C) ^ B)
    (2 * B * Δ) K hK hη
  refine ⟨ε, hε, ?_⟩
  intro W _ I hd hB x hx z hz
  obtain ⟨i, hi⟩ := pinningPolynomial_has_bounded_code I Δ B hd hB
  have hn : ∀ y ∈ K, i.polynomial.eval y ≠ 0 := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hreal hy
    rw [hi, pinningPolynomial_ofReal]
    exact_mod_cast (partition_pos_of_succ_le I ht hd hcolours).ne'
  simpa only [hi, pinningPolynomial_eval] using hb i hn x hx z hz

/-- At positive real bases no colour-slack assumption is needed for the
same finite-family reduction. -/
theorem bounded_pinning_positive_relative_stability (C : Type*) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ {V : Type*} [Fintype V] (I : PinningData V C),
      I.DegreeBound Δ → Fintype.card V ≤ B →
      ∀ x ∈ K, ∀ z : ℂ, dist z x < ε →
        ‖pinningProductPartition I z / pinningProductPartition I x - 1‖ < η := by
  obtain ⟨ε, hε, hb⟩ := bounded_monomials_relative_stability ((Fintype.card C) ^ B)
    (2 * B * Δ) K hK hη
  refine ⟨ε, hε, ?_⟩
  intro W _ I hd hB x hx z hz
  obtain ⟨i, hi⟩ := pinningPolynomial_has_bounded_code I Δ B hd hB
  have hn : ∀ y ∈ K, i.polynomial.eval y ≠ 0 := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hreal hy
    rw [hi, pinningPolynomial_ofReal]
    exact_mod_cast (I.partition_pos_of_parameter_pos ht).ne'
  simpa only [hi, pinningPolynomial_eval] using hb i hn x hx z hz

end
end CI2ZF.Potts
