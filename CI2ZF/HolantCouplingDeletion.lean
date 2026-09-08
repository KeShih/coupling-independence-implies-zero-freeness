import CI2ZF.HolantCouplingGibbs

/-!
# Edge deletion and reconstruction of Holant Gibbs laws

Deleting an edge leaves both child laws on the same ambient powerset.
The one-child is lifted by inserting the fixed edge.  The formulas below
are identities of actual finite distributions, not conditional-law axioms.
-/

namespace CI2ZF.HolantCoupling

open scoped BigOperators
open PottsCI PottsCI.FinDist Holant

noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem mapLaw_insert_apply (μ : FinDist (Finset E)) (e : E)
    (hsupport : ∀ S, e ∈ S → μ.w S = 0) (S : Finset E) :
    (mapLaw μ (fun S : Finset E => insert e S)).w S =
      if e ∈ S then μ.w (S.erase e) else 0 := by
  simp only [mapLaw, bind_w, FinDist.pure]
  by_cases hS : e ∈ S
  · rw [if_pos hS, Finset.sum_eq_single (S.erase e)]
    · simp [Finset.insert_erase hS]
    · intro T _ hT
      by_cases heT : e ∈ T
      · simp [hsupport T heT]
      · have hne : S ≠ insert e T := by
          intro heq
          have ht : S.erase e = T := by rw [heq, Finset.erase_insert heT]
          exact hT ht.symm
        simp [hne]
    · simp
  · rw [if_neg hS]
    apply Finset.sum_eq_zero
    intro T _
    have hne : S ≠ insert e T := by
      intro h
      exact hS (h ▸ Finset.mem_insert_self e T)
    simp [hne]

theorem gibbs_no_edge (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (hf : ∀ v k, 0 ≤ f v k)
    (hf0 : ∀ v, 0 < f v 0) (hx : ∀ e ∈ edges, 0 ≤ x e)
    (e : E) (he : e ∉ edges) (S : Finset E) (hS : e ∈ S) :
    (gibbs inc edges f x hf hf0 hx).w S = 0 := by
  rw [gibbs_apply]
  have hsub : ¬S ⊆ edges := fun h => he (h hS)
  simp [restrictedWeight, hsub]

theorem edgeShift_nonneg (inc : E → V → Prop) (f : V → ℕ → ℝ) (e : E)
    (hf : ∀ v k, 0 ≤ f v k) : ∀ v k, 0 ≤ shiftedSignature inc f e v k := by
  intro v k
  exact hf _ _

theorem edgeShift_zero_pos (inc : E → V → Prop) (f : V → ℕ → ℝ) (e : E)
    (hf0 : ∀ v, 0 < f v 0) (hf1 : ∀ v, inc e v → 0 < f v 1) :
    ∀ v, 0 < shiftedSignature inc f e v 0 := by
  intro v
  by_cases h : inc e v
  · simpa [shiftedSignature, h] using hf1 v h
  · simpa [shiftedSignature, h] using hf0 v

/-- Splitting the actual weight by whether the distinguished edge is
selected.  The selected branch is exactly the shifted residual weight. -/
theorem restrictedWeight_deletion (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges) (S : Finset E) :
    restrictedWeight inc edges f x S = restrictedWeight inc (edges.erase e) f x S +
      x e * (if e ∈ S then
        restrictedWeight inc (edges.erase e) (shiftedSignature inc f e) x (S.erase e)
        else 0) := by
  by_cases hS : e ∈ S
  · have hnot : ¬S ⊆ edges.erase e := fun h => Finset.notMem_erase e edges (h hS)
    have hsub : S ⊆ edges ↔ S.erase e ⊆ edges.erase e := by
      constructor
      · exact Finset.erase_subset_erase e
      · intro h a ha
        by_cases hae : a = e
        · simpa [hae] using he
        · exact Finset.mem_of_mem_erase (h (Finset.mem_erase.mpr ⟨hae, ha⟩))
    simp only [if_pos hS, restrictedWeight, if_neg hnot, zero_add]
    by_cases h : S ⊆ edges
    · rw [if_pos h, if_pos (hsub.mp h)]
      conv_lhs => rw [← Finset.insert_erase hS]
      exact weight_insert inc f x e (S.erase e) (Finset.notMem_erase e S)
    · rw [if_neg h, if_neg (mt hsub.mpr h), mul_zero]
  · have hsub : S ⊆ edges.erase e ↔ S ⊆ edges := by
      constructor
      · exact fun h => h.trans (Finset.erase_subset _ _)
      · intro h a ha
        exact Finset.mem_erase.mpr ⟨fun hae => hS (hae ▸ ha), h ha⟩
    simp [hS, restrictedWeight, hsub]

/-- The exact probability of selecting the deleted edge. -/
def occupiedProbability (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) : ℝ :=
  x e * partition inc (edges.erase e) (shiftedSignature inc f e) x /
    partition inc edges f x

theorem occupiedProbability_nonneg (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges)
    (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, 0 < f v 0)
    (hf1 : ∀ v, inc e v → 0 < f v 1) (hx : ∀ a ∈ edges, 0 ≤ x a) :
    0 ≤ occupiedProbability inc edges f x e := by
  apply div_nonneg
  · exact mul_nonneg (hx e he)
      (partition_pos inc (edges.erase e) _ x (edgeShift_nonneg inc f e hf)
        (edgeShift_zero_pos inc f e hf0 hf1) (fun a ha => hx a (Finset.mem_of_mem_erase ha))).le
  · exact (partition_pos inc edges f x hf hf0 hx).le

theorem occupiedProbability_complement (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges)
    (hZ : partition inc edges f x ≠ 0) :
    1 - occupiedProbability inc edges f x e =
      partition inc (edges.erase e) f x / partition inc edges f x := by
  unfold occupiedProbability
  apply (eq_div_iff hZ).2
  field_simp
  linarith [partition_deletion inc edges f x e he]

theorem occupiedProbability_le_one (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges)
    (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, 0 < f v 0)
    (hx : ∀ a ∈ edges, 0 ≤ x a) :
    occupiedProbability inc edges f x e ≤ 1 := by
  have hZ := partition_pos inc edges f x hf hf0 hx
  have hZ₀ := partition_pos inc (edges.erase e) f x hf hf0
    (fun a ha => hx a (Finset.mem_of_mem_erase ha))
  have h := occupiedProbability_complement inc edges f x e he hZ.ne'
  have hnonneg : 0 ≤ 1 - occupiedProbability inc edges f x e := by
    rw [h]
    exact div_nonneg hZ₀.le hZ.le
  linarith

/-- Exact Bernoulli reconstruction of a surviving pair of children.  Zero
activity is allowed: the coefficient of the one-child is then zero. -/
theorem gibbs_deletion_mix (inc : E → V → Prop) (edges : Finset E)
    (f : V → ℕ → ℝ) (x : E → ℝ) (e : E) (he : e ∈ edges)
    (hf : ∀ v k, 0 ≤ f v k) (hf0 : ∀ v, 0 < f v 0)
    (hf1 : ∀ v, inc e v → 0 < f v 1) (hx : ∀ a ∈ edges, 0 ≤ x a) :
    gibbs inc edges f x hf hf0 hx =
      (bernoulli (occupiedProbability inc edges f x e)
        (occupiedProbability_nonneg inc edges f x e he hf hf0 hf1 hx)
        (occupiedProbability_le_one inc edges f x e he hf hf0 hx)).bind
        (fun b => if b then
          mapLaw (gibbs inc (edges.erase e) (shiftedSignature inc f e) x
            (edgeShift_nonneg inc f e hf) (edgeShift_zero_pos inc f e hf0 hf1)
            (fun a ha => hx a (Finset.mem_of_mem_erase ha))) (fun S : Finset E => insert e S)
          else gibbs inc (edges.erase e) f x hf hf0
            (fun a ha => hx a (Finset.mem_of_mem_erase ha))) := by
  have hZ := partition_pos inc edges f x hf hf0 hx
  have hZ₀ := partition_pos inc (edges.erase e) f x hf hf0
    (fun a ha => hx a (Finset.mem_of_mem_erase ha))
  have hZ₁ := partition_pos inc (edges.erase e) (shiftedSignature inc f e) x
    (edgeShift_nonneg inc f e hf) (edgeShift_zero_pos inc f e hf0 hf1)
    (fun a ha => hx a (Finset.mem_of_mem_erase ha))
  ext S
  simp only [bind_w, bernoulli, Fintype.sum_bool, Bool.false_eq_true,
    ↓reduceIte]
  rw [mapLaw_insert_apply _ e
    (gibbs_no_edge inc (edges.erase e) _ x _ _ _ e (Finset.notMem_erase e edges))]
  simp only [gibbs_apply]
  rw [occupiedProbability_complement inc edges f x e he hZ.ne']
  unfold occupiedProbability
  have hw := restrictedWeight_deletion inc edges f x e he S
  by_cases hS : e ∈ S
  · simp only [if_pos hS] at hw ⊢
    field_simp
    nlinarith [hw]
  · simp only [if_neg hS] at hw ⊢
    field_simp
    nlinarith [hw]

end

end CI2ZF.HolantCoupling
