import CI2ZF.Coupling.Edge.Finite.ConditionalCosts

/-! The smaller-instance comparisons required by the exposure recursion.
Single-vertex replacement is the induction predicate; the two-endpoint
comparison is proved by an admissible mixed boundary and a triangle. -/
namespace CI2ZF.Appendix.Edge.FiniteSystem
open PottsCI PottsCI.FinDist Finset FiniteLaw
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E A L : Type*} [Fintype V] [Fintype E] [Fintype A] [Fintype L]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq A := Classical.decEq A
local instance (priority := 2000) : DecidableEq L := Classical.decEq L

def SingleReplacementCI (I : FiniteSystem V E A L) (Δ : ℕ) (t : ℝ) : Prop :=
  ∀ (B : Boundary V L) (v : V) (a b : L), a ∉ B v → b ∉ B v →
    ∀ (ha : I.Bounds (addBoundary B v a) Δ) (hb : I.Bounds (addBoundary B v b) Δ),
      W ham (I.validLaw (addBoundary B v a) ha) (I.validLaw (addBoundary B v b) hb) ≤ t

lemma addBoundary_comm_vertices (B : Boundary V L) {v w : V} (hvw : v ≠ w) (a b : L) :
    addBoundary (addBoundary B v a) w b = addBoundary (addBoundary B w b) v a := by
  ext z
  by_cases hzv : z = v
  · subst z
    simp [addBoundary, hvw, Ne.symm hvw]
  · by_cases hzw : z = w
    · subst z
      simp [addBoundary, hvw, Ne.symm hvw]
    · simp [addBoundary, hzv, hzw]

/-- On a graph with the exposed edge removed, replacing one label at each
of its endpoints costs at most twice the single-replacement bound. -/
theorem W_two_endpoint_replacements (I : FiniteSystem V E A L) (e : E)
    {v w : V} (hv : v ∈ I.endpoints e) (hw : w ∈ I.endpoints e) (hvw : v ≠ w)
    {Δ : ℕ} {t : ℝ} (hCI : (I.remove e).SingleReplacementCI Δ t)
    (B : Boundary V L) (a b c d : L) (ha : a ∉ B v) (hb : b ∉ B v) (hc : c ∉ B w) (hd : d ∉ B w)
    (hS : (I.remove e).Bounds (addBoundary (addBoundary B v a) w c) Δ)
    (hT : (I.remove e).Bounds (addBoundary (addBoundary B v b) w d) Δ) :
    W ham ((I.remove e).validLaw (addBoundary (addBoundary B v a) w c) hS)
      ((I.remove e).validLaw (addBoundary (addBoundary B v b) w d) hT) ≤ 2 * t := by
  let S := addBoundary (addBoundary B v a) w c
  let T := addBoundary (addBoundary B v b) w d
  let M := addBoundary (addBoundary B v a) w d
  have hagree : ∀ z, z ≠ v → z ≠ w → S z = T z := by
    intro z hzv hzw
    simp only [S, T, addBoundary_other _ w z c hzw, addBoundary_other _ w z d hzw,
      addBoundary_other B v z a hzv, addBoundary_other B v z b hzv]
  have hMeq : M = Function.update T v (S v) := by
    ext z
    by_cases hzv : z = v
    · subst z
      simp [M, S, T, addBoundary, hvw]
    · by_cases hzw : z = w
      · subst z
        simp [M, S, T, addBoundary, Ne.symm hvw]
      · simp [M, S, T, addBoundary, hzv, hzw]
  have hM : (I.remove e).Bounds M Δ := by
    rw [hMeq]
    exact hS.mixed_endpoints I e hv hw hvw S T hagree hT
  have hc' : c ∉ addBoundary B v a w := by simpa only [addBoundary_other B v w a (Ne.symm hvw)] using hc
  have hd' : d ∉ addBoundary B v a w := by simpa only [addBoundary_other B v w a (Ne.symm hvw)] using hd
  have hSM := hCI (addBoundary B v a) w c d hc' hd' hS hM
  have hMa : M = addBoundary (addBoundary B w d) v a := addBoundary_comm_vertices B hvw a d
  have hTb : T = addBoundary (addBoundary B w d) v b := addBoundary_comm_vertices B hvw b d
  have ha' : a ∉ addBoundary B w d v := by simpa only [addBoundary_other B w v d hvw] using ha
  have hb' : b ∉ addBoundary B w d v := by simpa only [addBoundary_other B w v d hvw] using hb
  have hMT : W ham ((I.remove e).validLaw M hM) ((I.remove e).validLaw T hT) ≤ t := by
    have hMaB : (I.remove e).Bounds (addBoundary (addBoundary B w d) v a) Δ := hMa ▸ hM
    have hTbB : (I.remove e).Bounds (addBoundary (addBoundary B w d) v b) Δ := hTb ▸ hT
    have hh := hCI (addBoundary B w d) v a b ha' hb' hMaB hTbB
    simpa only [← hMa, ← hTb] using hh
  have htri := W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle
    ((I.remove e).validLaw S hS) ((I.remove e).validLaw M hM) ((I.remove e).validLaw T hT)
  linarith

/-- When opposite exposure labels are both present at the deleted edge,
the residual boundaries agree at the exposed vertex. -/
theorem matched_residual_le (I : FiniteSystem V E A L) (B : Boundary V L)
    (v : V) (α β : L) {Δ : ℕ} (hα : I.Bounds (addBoundary B v α) Δ)
    (hβ : I.Bounds (addBoundary B v β) Δ) (j : ↑(I.incident v)) {t : ℝ}
    (hCI : (I.remove j.val).SingleReplacementCI Δ t) (a b : A)
    (hac : I.Compatible (addBoundary B v α) j.val a)
    (hbc : I.Compatible (addBoundary B v β) j.val b)
    (hav : I.label j.val v a = β) (hbv : I.label j.val v b = α) :
    W ham (I.pinnedLaw (addBoundary B v α) hα j.val a)
      (I.pinnedLaw (addBoundary B v β) hβ j.val b) ≤ t := by
  obtain ⟨w, hvw, he⟩ := I.endpoints_pair j.val v (I.incident_mem v j)
  have hw : w ∈ I.endpoints j.val := by rw [he]; simp
  let C := addBoundary (addBoundary B v α) v β
  have hPa : I.pinBoundary (addBoundary B v α) j.val a = addBoundary C w (I.label j.val w a) := by
    rw [I.pinBoundary_pair _ _ _ hvw he, hav]
  have hPb : I.pinBoundary (addBoundary B v β) j.val b = addBoundary C w (I.label j.val w b) := by
    rw [I.pinBoundary_pair _ _ _ hvw he, hbv, addBoundary_comm B v β α]
  have hca : I.label j.val w a ∉ C w := by
    have hh := hac w hw
    simpa only [C, addBoundary_other _ v w β (Ne.symm hvw)] using hh
  have hcb : I.label j.val w b ∉ C w := by
    have hh := hbc w hw
    simpa only [C, addBoundary_other _ v w β (Ne.symm hvw),
      addBoundary_other B v w α (Ne.symm hvw), addBoundary_other B v w β (Ne.symm hvw)] using hh
  have hBa := hα.pin I (addBoundary B v α) j.val a
  have hBb := hβ.pin I (addBoundary B v β) j.val b
  have hBa' : (I.remove j.val).Bounds (addBoundary C w (I.label j.val w a)) Δ := hPa ▸ hBa
  have hBb' : (I.remove j.val).Bounds (addBoundary C w (I.label j.val w b)) Δ := hPb ▸ hBb
  have hh := hCI C w (I.label j.val w a) (I.label j.val w b) hca hcb hBa' hBb'
  simpa only [pinnedLaw, ← hPa, ← hPb] using hh

/-- The unmatched residuals differ by one replacement at each endpoint.
The mixed system is admissible by simplicity, not by an extra hypothesis. -/
theorem unmatched_residual_le (I : FiniteSystem V E A L) (B : Boundary V L)
    (v : V) (α β : L) (hα0 : α ∉ B v) (hαβ : α ≠ β) {Δ : ℕ}
    (hα : I.Bounds (addBoundary B v α) Δ) (hβ : I.Bounds (addBoundary B v β) Δ)
    (j : ↑(I.incident v)) {t : ℝ} (hCI : (I.remove j.val).SingleReplacementCI Δ t) (a b : A)
    (hac : I.Compatible (addBoundary B v α) j.val a)
    (hbc : I.Compatible (addBoundary B v β) j.val b) (hav : I.label j.val v a = β) :
    W ham (I.pinnedLaw (addBoundary B v α) hα j.val a)
      (I.pinnedLaw (addBoundary B v β) hβ j.val b) ≤ 2 * t := by
  obtain ⟨w, hvw, he⟩ := I.endpoints_pair j.val v (I.incident_mem v j)
  have hv := I.incident_mem v j
  have hw : w ∈ I.endpoints j.val := by rw [he]; simp
  let C := addBoundary B v β
  have hPa : I.pinBoundary (addBoundary B v α) j.val a =
      addBoundary (addBoundary C v α) w (I.label j.val w a) := by
    rw [I.pinBoundary_pair _ _ _ hvw he, hav, addBoundary_comm B v α β]
  have hPb : I.pinBoundary (addBoundary B v β) j.val b =
      addBoundary (addBoundary C v (I.label j.val v b)) w (I.label j.val w b) :=
    I.pinBoundary_pair _ _ _ hvw he
  have hca : α ∉ C v := by simp only [C, addBoundary_self, Finset.mem_insert, not_or]; exact ⟨hαβ, hα0⟩
  have hcb : I.label j.val v b ∉ C v := hbc v hv
  have hcc : I.label j.val w a ∉ C w := by
    simpa only [C, addBoundary_other B v w β (Ne.symm hvw),
      addBoundary_other B v w α (Ne.symm hvw)] using hac w hw
  have hcd : I.label j.val w b ∉ C w := hbc w hw
  have hBa := hα.pin I (addBoundary B v α) j.val a
  have hBb := hβ.pin I (addBoundary B v β) j.val b
  have hBa' : (I.remove j.val).Bounds (addBoundary (addBoundary C v α) w (I.label j.val w a)) Δ := hPa ▸ hBa
  have hBb' : (I.remove j.val).Bounds
      (addBoundary (addBoundary C v (I.label j.val v b)) w (I.label j.val w b)) Δ := hPb ▸ hBb
  have hh := I.W_two_endpoint_replacements j.val hv hw hvw hCI C α (I.label j.val v b)
    (I.label j.val w a) (I.label j.val w b) hca hcb hcc hcd hBa' hBb'
  simpa only [pinnedLaw, ← hPa, ← hPb] using hh

end
end CI2ZF.Appendix.Edge.FiniteSystem
