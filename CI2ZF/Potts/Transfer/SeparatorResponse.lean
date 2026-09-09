import CI2ZF.Potts.Geometry.Separator

/-!
# The separator response as an actual shell average

Polynomial factors commute with semiring homomorphisms. At a positive real
base all inside and exterior factors are positive, so the exact separator
identity gives the complex normalized response as a finite average under
the actual shell marginal.
-/

namespace CI2ZF.Potts.Separator

open PottsCI PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable section

local instance (priority := 2000) (A B : Type*) : DecidableEq (A → B) := Classical.decEq _

variable {U S O C R R' : Type*}

section Map

variable [CommSemiring R] [CommSemiring R']

lemma map_edgeWeight {V : Type*} (f : R →+* R') (z : R) (σ : V → C) (e : Sym2 V) :
    f (edgeWeight z σ e) = edgeWeight (f z) σ e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [edgeWeight_mk, apply_ite, map_one]
    split_ifs <;> simp_all

lemma map_partialEdgeWeight (f : R →+* R') (z : R)
    (σ : Vertex U S O → Option C) (e : Sym2 (Vertex U S O)) :
    f (partialEdgeWeight z σ e) = partialEdgeWeight (f z) σ e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [partialEdgeWeight_mk, apply_ite, map_one]
    split_ifs <;> simp_all

variable [Fintype U] [Fintype S] [Fintype O] [Fintype C]

omit [Fintype C] in
lemma map_weight (f : R →+* R') (I : PinningData (Vertex U S O) C)
    (z : R) (σ : Vertex U S O → C) : f (weight I z σ) = weight I (f z) σ := by
  simp [weight, map_edgeWeight]

omit [Fintype C] in
lemma map_insideWeight (f : R →+* R') (I : PinningData (Vertex U S O) C)
    (z : R) (α : U → C) (ξ : S → C) :
    f (insideWeight I z α ξ) = insideWeight I (f z) α ξ := by
  simp [insideWeight, map_partialEdgeWeight]

omit [Fintype C] in
lemma map_exteriorWeight (f : R →+* R') (I : PinningData (Vertex U S O) C)
    (z : R) (ξ : S → C) (ζ : O → C) :
    f (exteriorWeight I z ξ ζ) = exteriorWeight I (f z) ξ ζ := by
  simp [exteriorWeight, map_partialEdgeWeight]

lemma map_partition (f : R →+* R') (I : PinningData (Vertex U S O) C) (z : R) :
    f (partition I z) = partition I (f z) := by simp [partition, map_weight]

lemma map_insidePartition (f : R →+* R') (I : PinningData (Vertex U S O) C)
    (z : R) (ξ : S → C) :
    f (insidePartition I z ξ) = insidePartition I (f z) ξ := by
  simp [insidePartition, map_insideWeight]

lemma map_exteriorPartition (f : R →+* R') (I : PinningData (Vertex U S O) C)
    (z : R) (ξ : S → C) :
    f (exteriorPartition I z ξ) = exteriorPartition I (f z) ξ := by
  simp [exteriorPartition, map_exteriorWeight]

end Map

section Positive

variable [Fintype U] [Fintype S] [Fintype O] [Fintype C]

omit [Fintype U] [Fintype S] [Fintype O] [Fintype C] in
lemma partialEdgeWeight_pos (x : ℝ) (hx : 0 < x) (σ : Vertex U S O → Option C)
    (e : Sym2 (Vertex U S O)) : 0 < partialEdgeWeight x σ e := by
  induction e using Sym2.ind with
  | _ u v => simp only [partialEdgeWeight_mk]; split_ifs <;> positivity

omit [Fintype C] in
lemma insideWeight_pos (I : PinningData (Vertex U S O) C) (x : ℝ) (hx : 0 < x)
    (α : U → C) (ξ : S → C) : 0 < insideWeight I x α ξ := by
  unfold insideWeight
  refine mul_pos (mul_pos ?_ ?_) ?_
  · exact Finset.prod_pos (fun _ _ => pow_pos hx _)
  · exact Finset.prod_pos (fun _ _ => pow_pos hx _)
  · exact Finset.prod_pos (fun e _ => partialEdgeWeight_pos x hx _ e)

omit [Fintype C] in
lemma exteriorWeight_pos (I : PinningData (Vertex U S O) C) (x : ℝ) (hx : 0 < x)
    (ξ : S → C) (ζ : O → C) : 0 < exteriorWeight I x ξ ζ := by
  unfold exteriorWeight
  exact mul_pos (Finset.prod_pos (fun _ _ => pow_pos hx _))
    (Finset.prod_pos (fun e _ => partialEdgeWeight_pos x hx _ e))

lemma insidePartition_pos [Nonempty C] (I : PinningData (Vertex U S O) C)
    (x : ℝ) (hx : 0 < x) (ξ : S → C) : 0 < insidePartition I x ξ :=
  Finset.sum_pos (fun α _ => insideWeight_pos I x hx α ξ) Finset.univ_nonempty

lemma exteriorPartition_pos [Nonempty C] (I : PinningData (Vertex U S O) C)
    (x : ℝ) (hx : 0 < x) (ξ : S → C) : 0 < exteriorPartition I x ξ :=
  Finset.sum_pos (fun ζ _ => exteriorWeight_pos I x hx ξ ζ) Finset.univ_nonempty

/-- Exact complex response formula using the actual positive-base shell law.
No nonvanishing at the complex argument is assumed. -/
theorem response_eq_shell_average [Nonempty C] (I : PinningData (Vertex U S O) C)
    (hsep : Separates I) (x : ℝ) (hx : 0 < x) (z : ℂ) :
    partition I z / partition I (x : ℂ) =
      ∑ ξ : S → C,
        ((shellMarginal I x hx.le (I.partition_pos_of_parameter_pos hx)).w ξ : ℂ) *
          (insidePartition I z ξ / insidePartition I (x : ℂ) ξ) *
          (exteriorPartition I z ξ / exteriorPartition I (x : ℂ) ξ) := by
  have hmapZ : partition I (x : ℂ) = (I.partition x : ℂ) := by
    simpa only [Complex.ofRealHom_eq_coe, partition_real] using
      (map_partition Complex.ofRealHom I x).symm
  have hmapD (ξ : S → C) : insidePartition I (x : ℂ) ξ = ((insidePartition I x ξ : ℝ) : ℂ) := by
    simpa only [Complex.ofRealHom_eq_coe] using
      (map_insidePartition Complex.ofRealHom I x ξ).symm
  have hmapE (ξ : S → C) : exteriorPartition I (x : ℂ) ξ = ((exteriorPartition I x ξ : ℝ) : ℂ) := by
    simpa only [Complex.ofRealHom_eq_coe] using
      (map_exteriorPartition Complex.ofRealHom I x ξ).symm
  rw [partition_factorization I hsep z, hmapZ]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ξ _
  rw [shellMarginal_apply I hsep]
  rw [hmapD, hmapE]
  have hD : ((insidePartition I x ξ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (insidePartition_pos I x hx ξ).ne'
  have hE : ((exteriorPartition I x ξ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (exteriorPartition_pos I x hx ξ).ne'
  have hZ : (I.partition x : ℂ) ≠ 0 := by
    exact_mod_cast (I.partition_pos_of_parameter_pos hx).ne'
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  field_simp [hD, hE, hZ]

end Positive

end

end CI2ZF.Potts.Separator
