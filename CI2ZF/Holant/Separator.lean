import CI2ZF.Holant.Model

/-!
# Exact finite-subset separator expansion for Holant

Interior, shell, and exterior are arbitrary disjoint edge finsets.  The only
geometric hypothesis is that no vertex is incident to both an interior and an
exterior edge.  All identities are derived from the actual partition sum.
-/

namespace CI2ZF.Holant
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E R : Type*} [Fintype V] [DecidableEq E]

/-- Splitting selected subsets along a disjoint union is a genuine bijection. -/
theorem sum_powerset_union [AddCommMonoid R] (A B : Finset E) (hAB : Disjoint A B)
    (F : Finset E → R) :
    (∑ T ∈ (A ∪ B).powerset, F T) =
      ∑ a ∈ A.powerset, ∑ b ∈ B.powerset, F (a ∪ b) := by
  rw [← Finset.sum_product A.powerset B.powerset (fun p : Finset E × Finset E => F (p.1 ∪ p.2))]
  apply Finset.sum_bij' (fun T _ => (T ∩ A, T ∩ B)) (fun p _ => p.1 ∪ p.2)
  · intro T _
    simp only [Finset.mem_product, Finset.mem_powerset]
    exact ⟨Finset.inter_subset_right, Finset.inter_subset_right⟩
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp ha) (Finset.mem_powerset.mp hb))
  · intro T hT
    exact (Finset.inter_union_distrib_left T A B).symm.trans
      (Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hT))
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    have ha' := Finset.mem_powerset.mp ha
    have hb' := Finset.mem_powerset.mp hb
    apply Prod.ext
    · ext e
      have hd := Finset.disjoint_left.mp hAB
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hA⟩
        · exact h
        · exact (hd hA (hb' h)).elim
      · intro h
        exact ⟨Or.inl h, ha' h⟩
    · ext e
      have hd := Finset.disjoint_left.mp hAB
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨h | h, hB⟩
        · exact (hd (ha' h) hB).elim
        · exact h
      · intro h
        exact ⟨Or.inr h, hb' h⟩
  · intro T hT
    congr 1
    exact ((Finset.inter_union_distrib_left T A B).symm.trans
      (Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hT))).symm

theorem selectedDegree_union (inc : E → V → Prop) (A B : Finset E)
    (hAB : Disjoint A B) (v : V) :
    selectedDegree inc (A ∪ B) v = selectedDegree inc A v + selectedDegree inc B v := by
  unfold selectedDegree
  rw [Finset.filter_union, Finset.card_union_of_disjoint
    (hAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

/-- Geometric separator condition: an interior and exterior edge cannot meet. -/
def EdgeSeparated (inc : E → V → Prop) (I O : Finset E) : Prop :=
  ∀ v, ∀ a ∈ I, ∀ b ∈ O, inc a v → inc b v → False

/-- A vertex belongs to the exterior precisely when it touches an exterior edge. -/
def ExteriorVertex (inc : E → V → Prop) (O : Finset E) (v : V) : Prop :=
  ∃ b ∈ O, inc b v

theorem selectedDegree_eq_zero_of_no_incidence (inc : E → V → Prop)
    (S : Finset E) (v : V) (h : ∀ e ∈ S, ¬ inc e v) : selectedDegree inc S v = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  exact h e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2

theorem inside_degree_zero (inc : E → V → Prop) (I O A : Finset E)
    (hsep : EdgeSeparated inc I O) (hA : A ⊆ I) (v : V)
    (hv : ExteriorVertex inc O v) : selectedDegree inc A v = 0 := by
  obtain ⟨b, hb, hbi⟩ := hv
  exact selectedDegree_eq_zero_of_no_incidence inc A v
    (fun a ha hai => hsep v a (hA ha) b hb hai hbi)

theorem outside_degree_zero (inc : E → V → Prop) (O B : Finset E)
    (hB : B ⊆ O) (v : V) (hv : ¬ ExteriorVertex inc O v) :
    selectedDegree inc B v = 0 :=
  selectedDegree_eq_zero_of_no_incidence inc B v (fun b hb hbi => hv ⟨b, hB hb, hbi⟩)

section Field
variable [Field R]

/-- The scalar-normalized exterior residual signature.  Vertices not touching
an exterior edge have the neutral signature and contribute no factor. -/
def exteriorSignature (inc : E → V → Prop) (O ξ : Finset E) (f : V → ℕ → R) :
    V → ℕ → R := fun v k =>
  if ExteriorVertex inc O v then
    f v (selectedDegree inc ξ v + k) / f v (selectedDegree inc ξ v)
  else 1

/-- The removed normalization constants belong to the inside coefficient. -/
def interiorSignature (inc : E → V → Prop) (O ξ : Finset E) (f : V → ℕ → R) :
    V → ℕ → R := fun v k =>
  if ExteriorVertex inc O v then f v (selectedDegree inc ξ v)
  else f v (selectedDegree inc ξ v + k)

/-- The paper's `D_ξ`: shell monomial times the remaining interior sum. -/
def separatorCoefficient (inc : E → V → Prop) (I O ξ : Finset E)
    (f : V → ℕ → R) (z : E → R) : R :=
  (∏ e ∈ ξ, z e) * partition inc I (interiorSignature inc O ξ f) z

/-- Exact factorization of a single selected-subset monomial.  The zero-tail
hypothesis handles impossible shell assignments without dividing by zero. -/
theorem separator_weight_factorization (inc : E → V → Prop) (I O ξ A B : Finset E)
    (f : V → ℕ → R) (z : E → R) (hsep : EdgeSeparated inc I O)
    (hA : A ⊆ I) (hB : B ⊆ O) (hξA : Disjoint ξ A)
    (hξB : Disjoint ξ B) (hAB : Disjoint A B)
    (htail : ∀ v j k, f v j = 0 → f v (j + k) = 0) :
    weight inc f z (ξ ∪ (A ∪ B)) =
      (∏ e ∈ ξ, z e) * weight inc (interiorSignature inc O ξ f) z A *
        weight inc (exteriorSignature inc O ξ f) z B := by
  have hsig : signatureWeight inc f (ξ ∪ (A ∪ B)) =
      signatureWeight inc (interiorSignature inc O ξ f) A *
        signatureWeight inc (exteriorSignature inc O ξ f) B := by
    rw [signatureWeight, signatureWeight, signatureWeight, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [selectedDegree_union inc ξ (A ∪ B) (Finset.disjoint_union_right.mpr ⟨hξA, hξB⟩),
      selectedDegree_union inc A B hAB]
    by_cases hv : ExteriorVertex inc O v
    · rw [inside_degree_zero inc I O A hsep hA v hv]
      simp only [zero_add, interiorSignature, exteriorSignature, if_pos hv]
      by_cases hf : f v (selectedDegree inc ξ v) = 0
      · rw [hf, zero_mul, htail v _ _ hf]
      · exact (mul_div_cancel₀ _ hf).symm
    · rw [outside_degree_zero inc O B hB v hv]
      simp [interiorSignature, exteriorSignature, hv]
  unfold weight
  rw [hsig, Finset.prod_union (Finset.disjoint_union_right.mpr ⟨hξA, hξB⟩),
    Finset.prod_union hAB]
  ring

/-- The actual partition function splits into the shell coefficients and
normalized exterior partitions, with all edge activities independent. -/
theorem partition_separator (inc : E → V → Prop) (I S O : Finset E)
    (f : V → ℕ → R) (z : E → R) (hSI : Disjoint S I) (hSO : Disjoint S O)
    (hIO : Disjoint I O) (hsep : EdgeSeparated inc I O)
    (htail : ∀ v j k, f v j = 0 → f v (j + k) = 0) :
    partition inc (S ∪ (I ∪ O)) f z =
      ∑ ξ ∈ S.powerset, separatorCoefficient inc I O ξ f z *
        partition inc O (exteriorSignature inc O ξ f) z := by
  unfold partition
  rw [sum_powerset_union S (I ∪ O) (Finset.disjoint_union_right.mpr ⟨hSI, hSO⟩)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [sum_powerset_union I O hIO]
  simp_rw [separatorCoefficient, partition, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := O.powerset)]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  have hξ' := Finset.mem_powerset.mp hξ
  have hA' := Finset.mem_powerset.mp hA
  have hB' := Finset.mem_powerset.mp hB
  exact separator_weight_factorization inc I O ξ A B f z hsep hA' hB'
    (hSI.mono hξ' hA') (hSO.mono hξ' hB') (hIO.mono hA' hB') htail

/-- Conditioning the root does not change any exterior signature when its
endpoints are separated from exterior edges.  Thus the exterior is common to
both root children as an exact function, not merely at the base point. -/
theorem exteriorSignature_child_eq (inc : E → V → Prop) (O ξ : Finset E)
    (f : V → ℕ → R) (e : E)
    (hroot : ∀ v, ExteriorVertex inc O v → ¬ inc e v) :
    exteriorSignature inc O ξ (normalizedChildSignature inc f e) =
      exteriorSignature inc O ξ f := by
  funext v k
  unfold exteriorSignature
  split_ifs with hv
  · simp only [normalizedChildSignature, if_neg (hroot v hv)]
  · rfl

/-- Disconnected edge components factor exactly for normalized signatures. -/
theorem partition_disjoint_factorization (inc : E → V → Prop) (I O : Finset E)
    (f : V → ℕ → R) (z : E → R) (hIO : Disjoint I O)
    (hsep : EdgeSeparated inc I O) (hf0 : ∀ v, f v 0 = 1) :
    partition inc (I ∪ O) f z = partition inc I f z * partition inc O f z := by
  unfold partition
  rw [sum_powerset_union I O hIO, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hA' := Finset.mem_powerset.mp hA
  have hB' := Finset.mem_powerset.mp hB
  have hd := hIO.mono hA' hB'
  have hsig : signatureWeight inc f (A ∪ B) = signatureWeight inc f A * signatureWeight inc f B := by
    simp only [signatureWeight, selectedDegree_union inc A B hd, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro v _
    by_cases hv : ExteriorVertex inc O v
    · rw [inside_degree_zero inc I O A hsep hA' v hv, zero_add, hf0, one_mul]
    · rw [outside_degree_zero inc O B hB' v hv, add_zero, hf0, mul_one]
  simp only [weight, hsig, Finset.prod_union hd]
  ring

/-- Structural survival of a shell assignment; no activity occurs in this test. -/
def ShellSurvives (inc : E → V → Prop) (f : V → ℕ → R) (ξ : Finset E) : Prop :=
  ∀ v, f v (selectedDegree inc ξ v) ≠ 0

theorem exteriorSignature_zero (inc : E → V → Prop) (O ξ : Finset E)
    (f : V → ℕ → R) (hξ : ShellSurvives inc f ξ) (v : V) :
    exteriorSignature inc O ξ f v 0 = 1 := by
  unfold exteriorSignature
  split_ifs
  · simp only [add_zero, div_self (hξ v)]
  · rfl

/-- A structurally impossible shell has coefficient zero as an identity in
all activities, even though no activity has been divided out. -/
theorem separatorCoefficient_zero_of_not_survives (inc : E → V → Prop)
    (I O ξ : Finset E) (f : V → ℕ → R) (z : E → R)
    (htail : ∀ v j k, f v j = 0 → f v (j + k) = 0)
    (hξ : ¬ ShellSurvives inc f ξ) : separatorCoefficient inc I O ξ f z = 0 := by
  have hex : ∃ v, f v (selectedDegree inc ξ v) = 0 := by
    simpa [ShellSurvives] using hξ
  obtain ⟨v, hv⟩ := hex
  unfold separatorCoefficient
  suffices partition inc I (interiorSignature inc O ξ f) z = 0 by rw [this, mul_zero]
  apply Finset.sum_eq_zero
  intro A _
  unfold weight signatureWeight
  have hp : (∏ w, interiorSignature inc O ξ f w (selectedDegree inc A w)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    unfold interiorSignature
    split_ifs
    · exact hv
    · exact htail v _ _ hv
  rw [hp, zero_mul]

/-- Removing the structurally impossible assignments yields exactly the common
shell domain used in the paper; assignments with zero real activity remain. -/
theorem partition_separator_surviving (inc : E → V → Prop) (I S O : Finset E)
    (f : V → ℕ → R) (z : E → R) (hSI : Disjoint S I) (hSO : Disjoint S O)
    (hIO : Disjoint I O) (hsep : EdgeSeparated inc I O)
    (htail : ∀ v j k, f v j = 0 → f v (j + k) = 0) :
    partition inc (S ∪ (I ∪ O)) f z =
      ∑ ξ ∈ S.powerset.filter (ShellSurvives inc f),
        separatorCoefficient inc I O ξ f z *
          partition inc O (exteriorSignature inc O ξ f) z := by
  rw [partition_separator inc I S O f z hSI hSO hIO hsep htail]
  symm
  apply Finset.sum_filter_of_ne
  intro ξ _ hne
  by_contra hξ
  exact hne (by rw [separatorCoefficient_zero_of_not_survives inc I O ξ f z htail hξ,
    zero_mul])

end Field
section Real

/-- All shell coefficients are nonnegative on the nonnegative orthant. -/
theorem separatorCoefficient_nonneg (inc : E → V → Prop) (I O ξ : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hxI : ∀ e ∈ I, 0 ≤ x e) (hxξ : ∀ e ∈ ξ, 0 ≤ x e) :
    0 ≤ separatorCoefficient inc I O ξ f x := by
  unfold separatorCoefficient
  apply mul_nonneg (Finset.prod_nonneg hxξ)
  apply Finset.sum_nonneg
  intro A hA
  apply weight_nonneg inc I _ x _ hxI (Finset.mem_powerset.mp hA)
  intro v k
  unfold interiorSignature
  split_ifs <;> apply hf

/-- The all-zero shell coefficient contains the all-zero interior summand,
which is exactly one.  This is the additive-response denominator bound. -/
theorem separatorCoefficient_empty_ge_one (inc : E → V → Prop) (I O : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, f v 0 = 1) (hxI : ∀ e ∈ I, 0 ≤ x e) :
    1 ≤ separatorCoefficient inc I O ∅ f x := by
  simp only [separatorCoefficient, Finset.prod_empty, one_mul]
  apply normalized_partition_ge_one inc I _ x _ _ hxI
  · intro v k
    unfold interiorSignature
    split_ifs <;> apply hf
  · intro v
    simp [interiorSignature, hf0]

/-- A residual shift cannot increase the exterior partition at a nonnegative
base point.  The common exterior at the empty shell supplies the denominator. -/
theorem exterior_partition_le_empty (inc : E → V → Prop) (O ξ : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, f v 0 = 1) (hxO : ∀ e ∈ O, 0 ≤ x e)
    (hshift : ∀ v t k, f v (t + k) / f v t ≤ f v k) :
    partition inc O (exteriorSignature inc O ξ f) x ≤
      partition inc O (exteriorSignature inc O ∅ f) x := by
  refine partition_mono_signatures inc O _ x _ ?_ hxO ?_
  · intro v k
    unfold exteriorSignature
    split_ifs
    · exact div_nonneg (hf v _) (hf v _)
    · exact zero_le_one
  · intro v k _
    unfold exteriorSignature
    split_ifs
    · simpa only [selectedDegree_empty, zero_add, hf0, div_one] using
        hshift v (selectedDegree inc ξ v) k
    · exact le_rfl

theorem exterior_partition_nonneg (inc : E → V → Prop) (O ξ : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hxO : ∀ e ∈ O, 0 ≤ x e) :
    0 ≤ partition inc O (exteriorSignature inc O ξ f) x := by
  apply Finset.sum_nonneg
  intro B hB
  apply weight_nonneg inc O _ x _ hxO (Finset.mem_powerset.mp hB)
  intro v k
  unfold exteriorSignature
  split_ifs
  · exact div_nonneg (hf v _) (hf v _)
  · exact zero_le_one

/-- The real parent partition dominates every normalized exterior.  Therefore
an absolute error in a separator coefficient is not magnified by dividing by
the real parent partition. -/
theorem exterior_partition_le_parent (inc : E → V → Prop) (I S O ξ : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hSI : Disjoint S I) (hSO : Disjoint S O)
    (hIO : Disjoint I O) (hsep : EdgeSeparated inc I O)
    (htail : ∀ v j k, f v j = 0 → f v (j + k) = 0)
    (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, f v 0 = 1)
    (hxI : ∀ e ∈ I, 0 ≤ x e) (hxS : ∀ e ∈ S, 0 ≤ x e)
    (hxO : ∀ e ∈ O, 0 ≤ x e)
    (hshift : ∀ v t k, f v (t + k) / f v t ≤ f v k) :
    partition inc O (exteriorSignature inc O ξ f) x ≤ partition inc (S ∪ (I ∪ O)) f x := by
  have hext0 := exterior_partition_nonneg inc O ∅ f x hf hxO
  calc
    partition inc O (exteriorSignature inc O ξ f) x ≤
        partition inc O (exteriorSignature inc O ∅ f) x :=
      exterior_partition_le_empty inc O ξ f x hf hf0 hxO hshift
    _ ≤ separatorCoefficient inc I O ∅ f x *
        partition inc O (exteriorSignature inc O ∅ f) x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (separatorCoefficient_empty_ge_one inc I O f x hf hf0 hxI) hext0
    _ ≤ partition inc (S ∪ (I ∪ O)) f x := by
      rw [partition_separator inc I S O f x hSI hSO hIO hsep htail]
      apply Finset.single_le_sum (f := fun η => separatorCoefficient inc I O η f x *
        partition inc O (exteriorSignature inc O η f) x) _ (Finset.empty_mem_powerset S)
      intro η hη
      apply mul_nonneg
      · exact separatorCoefficient_nonneg inc I O η f x hf hxI
          (fun e he => hxS e (Finset.mem_powerset.mp hη he))
      · exact exterior_partition_nonneg inc O η f x hf hxO

end Real
end
end CI2ZF.Holant
