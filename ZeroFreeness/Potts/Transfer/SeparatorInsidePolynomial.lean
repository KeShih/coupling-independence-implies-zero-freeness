import ZeroFreeness.Potts.Model.PinningPolynomial
import ZeroFreeness.Potts.Transfer.HardEndpointLocalError

/-! Actual separator inside polynomials: monomial semantics, bounded finite
coding, uniform positive-base stability and additive hard-endpoint errors. -/
namespace ZeroFreeness.Potts.Separator
open PottsCI Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {U S O C R : Type*}

def insideEmbedding : U ⊕ S ↪ Vertex U S O where
  toFun := Sum.elim Sum.inl (fun s => Sum.inr (Sum.inl s))
  inj' := by intro a b h; cases a <;> cases b <;> simp_all

@[simp] lemma insideEmbedding_inl (u : U) :
    (insideEmbedding (Sum.inl u) : Vertex U S O) = Sum.inl u := rfl

@[simp] lemma insideEmbedding_inr (s : S) :
    (insideEmbedding (Sum.inr s) : Vertex U S O) = Sum.inr (Sum.inl s) := rfl

def insideData (I : PinningData (Vertex U S O) C) : PinningData (U ⊕ S) C where
  graph := I.graph.comap insideEmbedding
  boundaryCount u := I.boundaryCount (insideEmbedding u)

variable [Fintype U] [Fintype S] [Fintype O] [Fintype C]

omit [Fintype C] in
lemma insideEdges_eq_filter (I : PinningData (Vertex U S O) C) :
    (insideData I).graph.edgeFinset.map insideEmbedding.sym2Map =
      I.graph.edgeFinset.filter (fun e => ¬ touchesOutside e) := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_map.mp he
    induction f using Sym2.ind with
    | _ a b =>
      have ha : (insideData I).graph.Adj a b := SimpleGraph.mem_edgeFinset.mp hf
      refine mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr ha, ?_⟩
      cases a <;> cases b <;> simp [touchesOutside_mk, isOutside]
  · intro he
    obtain ⟨he, hn⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      have ha : I.graph.Adj a b := SimpleGraph.mem_edgeFinset.mp he
      rcases a with u | s | o <;> rcases b with v | t | p
      all_goals simp_all only [touchesOutside_mk, isOutside, Sum.elim_inl,
        Sum.elim_inr, false_or, or_false, true_or, not_true_eq_false]
      · exact mem_map.mpr ⟨s(Sum.inl u, Sum.inl v), SimpleGraph.mem_edgeFinset.mpr ha, rfl⟩
      · exact mem_map.mpr ⟨s(Sum.inl u, Sum.inr t), SimpleGraph.mem_edgeFinset.mpr ha, rfl⟩
      · exact mem_map.mpr ⟨s(Sum.inr s, Sum.inl v), SimpleGraph.mem_edgeFinset.mpr ha, rfl⟩
      · exact mem_map.mpr ⟨s(Sum.inr s, Sum.inr t), SimpleGraph.mem_edgeFinset.mpr ha, rfl⟩

omit [Fintype C] in
theorem insideWeight_eq_pinningProductWeight [CommSemiring R]
    (I : PinningData (Vertex U S O) C) (z : R) (α : U → C) (ξ : S → C) :
    insideWeight I z α ξ = pinningProductWeight (insideData I) z (Sum.elim α ξ) := by
  have he (e : Sym2 (U ⊕ S)) :
      partialEdgeWeight z (insideColor (O := O) α ξ) (insideEmbedding.sym2Map e) =
        edgeWeight z (Sum.elim α ξ) e := by
    induction e using Sym2.ind with
    | _ a b =>
      cases a <;> cases b <;>
        simp [partialEdgeWeight_mk, insideColor, edgeWeight_mk, eq_comm]
      all_goals split_ifs <;> simp_all
  unfold insideWeight pinningProductWeight
  rw [← insideEdges_eq_filter, prod_map]
  simp only [he, Fintype.prod_sum_type, insideData, insideEmbedding_inl, insideEmbedding_inr,
    Sum.elim_inl, Sum.elim_inr]

theorem insideData_degreeBound (I : PinningData (Vertex U S O) C)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (insideData I).DegreeBound Δ := by
  intro u
  have hg : (insideData I).graph.degree u ≤ I.graph.degree (insideEmbedding u) := by
    let f : (insideData I).graph.neighborSet u → I.graph.neighborSet (insideEmbedding u) :=
      fun w => ⟨insideEmbedding w.val, w.property⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact insideEmbedding.injective (congrArg Subtype.val h)
    simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_le_of_injective f hf
  change (insideData I).graph.degree u + (∑ c : C, I.boundaryCount (insideEmbedding u) c) ≤ Δ
  exact (Nat.add_le_add_right hg _).trans (hd (insideEmbedding u))

/-- Actual total monochromatic exponent among inside and fixed-shell
boundary and graph factors. -/
def insideExponent (I : PinningData (Vertex U S O) C) (α : U → C) (ξ : S → C) : ℕ :=
  pinningExponent (insideData I) (Sum.elim α ξ)

theorem insideWeight_eq_pow [CommSemiring R] (I : PinningData (Vertex U S O) C)
    (z : R) (α : U → C) (ξ : S → C) : insideWeight I z α ξ = z ^ insideExponent I α ξ := by
  rw [insideWeight_eq_pinningProductWeight, pinningProductWeight_eq_pow]
  rfl

theorem insidePartition_eq_sum_pow [CommSemiring R] (I : PinningData (Vertex U S O) C)
    (z : R) (ξ : S → C) :
    insidePartition I z ξ = ∑ α : U → C, z ^ insideExponent I α ξ := by
  unfold insidePartition
  simp_rw [insideWeight_eq_pow]

theorem insideWeight_zero_eq [CommSemiring R] (I : PinningData (Vertex U S O) C)
    (α : U → C) (ξ : S → C) :
    insideWeight I (0 : R) α ξ = if insideExponent I α ξ = 0 then 1 else 0 := by
  rw [insideWeight_eq_pow]
  cases insideExponent I α ξ <;> simp

theorem insidePartition_zero_eq_card [CommSemiring R]
    (I : PinningData (Vertex U S O) C) (ξ : S → C) :
    insidePartition I (0 : R) ξ =
      ((univ.filter fun α : U → C => insideExponent I α ξ = 0).card : R) := by
  unfold insidePartition
  simp_rw [insideWeight_zero_eq]
  rw [natCast_card_filter]

def insidePolynomial (I : PinningData (Vertex U S O) C) (ξ : S → C) : Polynomial ℂ :=
  ∑ α : U → C, Polynomial.X ^ insideExponent I α ξ

@[simp] theorem insidePolynomial_eval (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (z : ℂ) : (insidePolynomial I ξ).eval z = insidePartition I z ξ := by
  simp [insidePolynomial, Polynomial.eval_finsetSum, insidePartition_eq_sum_pow]

theorem insideExponent_le (I : PinningData (Vertex U S O) C) (α : U → C) (ξ : S → C)
    (Δ B : ℕ) (hd : I.DegreeBound Δ) (hB : Fintype.card U + Fintype.card S ≤ B) :
    insideExponent I α ξ ≤ 2 * B * Δ :=
  pinningExponent_le (insideData I) (Sum.elim α ξ) Δ B (insideData_degreeBound I hd)
    (by simpa only [Fintype.card_sum] using hB)

theorem insidePolynomial_has_bounded_code [Nonempty C]
    (I : PinningData (Vertex U S O) C) (ξ : S → C) (Δ B : ℕ)
    (hd : I.DegreeBound Δ) (hB : Fintype.card U + Fintype.card S ≤ B) :
    ∃ i : MonomialCode ((Fintype.card C) ^ B) (2 * B * Δ),
      i.polynomial = insidePolynomial I ξ := by
  apply encode_sum_monomials (fun α => insideExponent I α ξ)
  · rw [Fintype.card_fun]
    exact Nat.pow_le_pow_right (Fintype.card_pos (α := C)) (by omega)
  · exact fun α => insideExponent_le I α ξ Δ B hd hB

theorem insidePartition_error_zero (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖insidePartition I z ξ - insidePartition I 0 ξ‖ ≤
      ((Fintype.card C) ^ Fintype.card U : ℕ) * ‖z‖ := by
  rw [insidePartition_eq_sum_pow, insidePartition_eq_sum_pow]
  simpa only [Fintype.card_fun] using sum_monomials_error_zero
    (fun α => insideExponent I α ξ) z hz

/-- Defective shell colorings are included: the hard-base value may be zero. -/
theorem bounded_inside_error_zero [Nonempty C] (I : PinningData (Vertex U S O) C)
    (ξ : S → C) (B : ℕ) (hB : Fintype.card U + Fintype.card S ≤ B)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖insidePartition I z ξ - insidePartition I 0 ξ‖ ≤
      ((Fintype.card C) ^ B : ℕ) * ‖z‖ := by
  apply (insidePartition_error_zero I ξ z hz).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  exact_mod_cast Nat.pow_le_pow_right (Fintype.card_pos (α := C)) (show Fintype.card U ≤ B by omega)

/-- A uniform positive-base radius for every actual bounded inside system.
No hard-endpoint feasibility assumption is made for the fixed shell. -/
theorem bounded_inside_positive_relative_stability (C : Type*) [Fintype C] [Nonempty C]
    (Δ B : ℕ) (K : Set ℂ) (hK : IsCompact K)
    (hreal : K ⊆ Complex.ofReal '' Set.Ioi 0) {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ {U S O : Type*} [Fintype U] [Fintype S] [Fintype O]
      (I : PinningData (Vertex U S O) C), I.DegreeBound Δ →
      Fintype.card U + Fintype.card S ≤ B → ∀ ξ : S → C,
      ∀ x ∈ K, ∀ z : ℂ, dist z x < ε →
        ‖insidePartition I z ξ / insidePartition I x ξ - 1‖ < η := by
  obtain ⟨ε, hε, hb⟩ := bounded_monomials_relative_stability ((Fintype.card C) ^ B)
    (2 * B * Δ) K hK hη
  refine ⟨ε, hε, ?_⟩
  intro U S O _ _ _ I hd hB ξ x hx z hz
  obtain ⟨i, hi⟩ := insidePolynomial_has_bounded_code I ξ Δ B hd hB
  have hn : ∀ y ∈ K, i.polynomial.eval y ≠ 0 := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hreal hy
    rw [hi, insidePolynomial_eval]
    have he := map_insidePartition Complex.ofRealHom I t ξ
    have hp := (insidePartition_pos I t ht ξ).ne'
    have hmap : insidePartition I (t : ℂ) ξ = ((insidePartition I t ξ : ℝ) : ℂ) := by
      simpa only [Complex.ofRealHom_eq_coe] using he.symm
    rw [hmap]
    exact_mod_cast hp
  simpa only [hi, insidePolynomial_eval] using hb i hn x hx z hz

end
end ZeroFreeness.Potts.Separator
