import CI2ZF.PottsModel
import CI2ZF.LocalStability
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! A finite encoding of bounded local Potts polynomials, independent of
the ambient vertex type and of the number of pinned vertices. -/
namespace CI2ZF
open PottsCI
attribute [local instance] Classical.propDecidable
noncomputable section

/-- At most `N` monomials, each of degree at most `D`. -/
abbrev MonomialCode (N D : ℕ) := (n : Fin (N + 1)) × (Fin n.val → Fin (D + 1))

def MonomialCode.polynomial {N D : ℕ} (i : MonomialCode N D) : Polynomial ℂ :=
  ∑ k : Fin i.1.val, Polynomial.X ^ (i.2 k).val

theorem encode_sum_monomials {S : Type*} [Fintype S] (f : S → ℕ) (N D : ℕ)
    (hN : Fintype.card S ≤ N) (hD : ∀ s, f s ≤ D) :
    ∃ i : MonomialCode N D, i.polynomial = ∑ s : S, Polynomial.X ^ f s := by
  let e := Fintype.equivFin S
  let i : MonomialCode N D := ⟨⟨Fintype.card S, by omega⟩,
    fun k => ⟨f (e.symm k), by have := hD (e.symm k); omega⟩⟩
  refine ⟨i, ?_⟩
  change (∑ k : Fin (Fintype.card S), Polynomial.X ^ f (e.symm k)) = _
  exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)

/-- The nonvanishing members of the explicitly finite family have one
common relative-stability radius. -/
theorem bounded_monomials_relative_stability (N D : ℕ) (K : Set ℂ) (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ i : MonomialCode N D,
      (∀ x ∈ K, i.polynomial.eval x ≠ 0) →
      ∀ x ∈ K, ∀ z : ℂ, dist z x < ε →
        ‖i.polynomial.eval z / i.polynomial.eval x - 1‖ < η := by
  let T := {i : MonomialCode N D // ∀ x ∈ K, i.polynomial.eval x ≠ 0}
  obtain ⟨ε, hε, hb⟩ := finite_polynomial_relative_stability
    (fun i : T => i.val.polynomial) K hK (fun i => i.property) hη
  exact ⟨ε, hε, fun i hi => hb ⟨i, hi⟩⟩

namespace Potts
variable {V C : Type*} [Fintype V] [Fintype C]

/-- Bounded free volume and degree give an explicit bound on every
monomial exponent, including arbitrary pinned boundary data. -/
theorem local_exponent_le (tau : PartialColouring V C) (G : SimpleGraph V)
    (σ : tau.FreeVertex → C) (Δ B : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ)
    (hB : Fintype.card tau.FreeVertex ≤ B) :
    tau.boundaryConflictCount G σ + tau.freeConflictCount G σ ≤ 2 * B * Δ := by
  let I := tau.toPinningData G
  have hI : I.DegreeBound Δ := tau.degreeBound_of_original G hdegree
  have hboundary (u : tau.FreeVertex) : tau.boundaryCount G u (σ u) ≤ Δ := by
    have hb := Finset.single_le_sum (s := Finset.univ)
      (f := fun c => I.boundaryCount u c) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (σ u))
    have hd := hI u
    unfold PinningData.constraintDegree at hd
    exact hb.trans (Nat.le_trans (Nat.le_add_left _ _) hd)
  have hb : tau.boundaryConflictCount G σ ≤ Fintype.card tau.FreeVertex * Δ := by
    exact (Finset.sum_le_sum (s := Finset.univ) (fun u _ => hboundary u)).trans_eq (by simp)
  have hfree (u : tau.FreeVertex) : (tau.freeGraph G).degree u ≤ Δ := by
    have hd := hI u
    unfold PinningData.constraintDegree at hd
    exact (Nat.le_add_right _ _).trans hd
  have hdeg : (∑ u : tau.FreeVertex, (tau.freeGraph G).degree u) ≤
      Fintype.card tau.FreeVertex * Δ :=
    (Finset.sum_le_sum (fun u _ => hfree u)).trans_eq (by simp)
  have hedge := (tau.freeGraph G).sum_degrees_eq_twice_card_edges
  have hf : tau.freeConflictCount G σ ≤ (tau.freeGraph G).edgeFinset.card :=
    Finset.card_filter_le _ _
  have hmul := Nat.mul_le_mul_right Δ hB
  nlinarith

theorem normalizedPolynomial_has_bounded_code [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (Δ B : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Δ) (hB : Fintype.card tau.FreeVertex ≤ B) :
    ∃ i : MonomialCode ((Fintype.card C) ^ B) (2 * B * Δ),
      i.polynomial = normalizedPolynomial tau G := by
  apply encode_sum_monomials
    (fun σ => tau.boundaryConflictCount G σ + tau.freeConflictCount G σ)
  · rw [Fintype.card_fun]
    exact Nat.pow_le_pow_right (Fintype.card_pos (α := C)) hB
  · exact fun σ => local_exponent_le tau G σ Δ B hdegree hB

/-- A relative-stability radius depending only on the colour count,
degree bound, free-volume bound, compact real base set, and tolerance.
The finite-family reduction is proved for all vertex types and pinnings. -/
theorem bounded_local_potts_relative_stability (C : Type*) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (hcolours : Δ + 1 ≤ Fintype.card C)
    (K : Set ℂ) (hK : IsCompact K) (hreal : K ⊆ Complex.ofReal '' Set.Ici 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ {V : Type*} [Fintype V] (tau : PartialColouring V C) (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → Fintype.card tau.FreeVertex ≤ B →
      ∀ x ∈ K, ∀ z : ℂ, dist z x < ε →
        ‖normalizedPartition tau G z / normalizedPartition tau G x - 1‖ < η := by
  obtain ⟨ε, hε, hb⟩ := bounded_monomials_relative_stability ((Fintype.card C) ^ B)
    (2 * B * Δ) K hK hη
  refine ⟨ε, hε, ?_⟩
  intro W _ tau G hd hB x hx z hz
  obtain ⟨i, hi⟩ := normalizedPolynomial_has_bounded_code tau G Δ B hd hB
  have hn : ∀ y ∈ K, i.polynomial.eval y ≠ 0 := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hreal hy
    rw [hi]
    exact normalizedPartition_nonnegative_ne_zero tau G hd hcolours ht
  simpa only [hi, normalizedPartition] using hb i hn x hx z hz

end Potts
end
end CI2ZF
