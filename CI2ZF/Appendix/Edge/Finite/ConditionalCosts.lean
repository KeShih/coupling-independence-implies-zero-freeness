import CI2ZF.Appendix.Edge.Finite.Restore

/-! Exact conditional mixtures for the matched and unmatched rows of the
exposure table. The only transport inputs are the smaller residual laws. -/
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

def validLaw (I : FiniteSystem V E A L) (B : Boundary V L) {Δ : ℕ} (hB : I.Bounds B Δ) :
    FinDist (E → A) := I.gibbs B (hB.partition_pos I B)

def pinnedLaw (I : FiniteSystem V E A L) (B : Boundary V L) {Δ : ℕ}
    (hB : I.Bounds B Δ) (e : E) (a : A) : FinDist ({f : E // f ≠ e} → A) :=
  (I.remove e).validLaw (I.pinBoundary B e a) (hB.pin I B e a)

lemma conditional_validLaw_coordinate (I : FiniteSystem V E A L) (B : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (e : E) (a : A)
    (ha : 0 < eventMass (I.validLaw B hB) (fun σ => σ e = a)) :
    conditional (I.validLaw B hB) (fun σ => σ e = a) = CI2ZF.mapLaw (I.pinnedLaw B hB e a) (joinConfig e a) :=
  I.conditional_gibbs_coordinate B _ e a
    ((hB.pin I B e a).partition_pos (I.remove e) (I.pinBoundary B e a)) ha

lemma occurrence_coordinate_data (I : FiniteSystem V E A L) (B : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (v : V) (l : L) (j : ↑(I.incident v))
    (ho : 0 < eventMass (I.validLaw B hB) (I.Occurs v l j)) (a : A)
    (ha : 0 < eventMass (conditional (I.validLaw B hB) (I.Occurs v l j)) (fun σ => σ j.val = a)) :
    I.label j.val v a = l ∧ I.Compatible B j.val a ∧
      conditional (conditional (I.validLaw B hB) (I.Occurs v l j)) (fun σ => σ j.val = a) =
        CI2ZF.mapLaw (I.pinnedLaw B hB j.val a) (joinConfig j.val a) := by
  obtain ⟨σ, he, hs⟩ := eventMass_pos_exists _ _ ha
  have hp := (conditional_pos_support _ _ ho hs).1
  have hl : I.label j.val v a = l := by simpa only [Occurs, he] using hp
  have himp (τ : E → A) (hτ : τ j.val = a) : I.Occurs v l j τ := by
    change I.label j.val v (τ j.val) = l
    rw [hτ, hl]
  have hm := eventMass_conditional_of_imp (I.validLaw B hB) (I.Occurs v l j)
    (fun σ => σ j.val = a) ho himp
  have hd : 0 < eventMass (I.validLaw B hB) (fun σ => σ j.val = a) := by
    rw [hm] at ha
    exact (div_pos_iff_of_pos_right ho).mp ha
  refine ⟨hl, I.gibbs_coordinate_pos_compatible B _ j.val a hd, ?_⟩
  rw [conditional_conditional_of_imp _ _ _ ho ha himp]
  exact I.conditional_validLaw_coordinate B hB j.val a hd

/-- Full occurrence blocks are coupled by mixing the true residual pinned
laws; each restored edge adds at most one unit to Hamming cost. -/
theorem W_occurrences_le (I : FiniteSystem V E A L) (B D : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (hD : I.Bounds D Δ) (v : V) (l r : L) (j : ↑(I.incident v))
    (hl : 0 < eventMass (I.validLaw B hB) (I.Occurs v l j))
    (hr : 0 < eventMass (I.validLaw D hD) (I.Occurs v r j)) {t : ℝ}
    (hres : ∀ a b, I.Compatible B j.val a → I.Compatible D j.val b →
      I.label j.val v a = l → I.label j.val v b = r →
      W ham (I.pinnedLaw B hB j.val a) (I.pinnedLaw D hD j.val b) ≤ t) :
    W ham (conditional (I.validLaw B hB) (I.Occurs v l j))
      (conditional (I.validLaw D hD) (I.Occurs v r j)) ≤ 1 + t := by
  apply W_le_of_conditionals _ _ (fun σ => σ j.val) (fun σ => σ j.val) ham ham_nonneg
  intro a b ha hb
  obtain ⟨hal, hac, hae⟩ := I.occurrence_coordinate_data B hB v l j hl a ha
  obtain ⟨hbl, hbc, hbe⟩ := I.occurrence_coordinate_data D hD v r j hr b hb
  rw [hae, hbe]
  exact (W_restore_le j.val a b _ _).trans (add_le_add le_rfl (hres a b hac hbc hal hbl))

/-- The unmatched occurrence/full-law row uses the same exact disintegration. -/
theorem W_occurrence_full_le (I : FiniteSystem V E A L) (B D : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (hD : I.Bounds D Δ) (v : V) (l : L) (j : ↑(I.incident v))
    (hl : 0 < eventMass (I.validLaw B hB) (I.Occurs v l j)) {t : ℝ}
    (hres : ∀ a b, I.Compatible B j.val a → I.Compatible D j.val b →
      I.label j.val v a = l →
      W ham (I.pinnedLaw B hB j.val a) (I.pinnedLaw D hD j.val b) ≤ t) :
    W ham (conditional (I.validLaw B hB) (I.Occurs v l j)) (I.validLaw D hD) ≤ 1 + t := by
  apply W_le_of_conditionals _ _ (fun σ => σ j.val) (fun σ => σ j.val) ham ham_nonneg
  intro a b ha hb
  obtain ⟨hal, hac, hae⟩ := I.occurrence_coordinate_data B hB v l j hl a ha
  have hbc := I.gibbs_coordinate_pos_compatible D _ j.val b hb
  rw [hae, I.conditional_validLaw_coordinate D hD j.val b hb]
  exact (W_restore_le j.val a b _ _).trans (add_le_add le_rfl (hres a b hac hbc hal))

lemma W_ham_comm (μ ν : FinDist (E → A)) : W ham μ ν = W ham ν μ := by
  have hs (μ ν : FinDist (E → A)) : W ham μ ν ≤ W ham ν μ := by
    obtain ⟨π, hπ⟩ := exists_optimal_coupling ν μ ham ham_nonneg
    let π' : Coupling μ ν := ⟨fun x y => π.w y x, fun x y => π.nonneg y x, π.sum_col, π.sum_row⟩
    apply (W_le_cost ham_nonneg π').trans_eq
    rw [← hπ]
    change (∑ x, ∑ y, π.w y x * ham x y) = ∑ y, ∑ x, π.w y x * ham y x
    rw [Finset.sum_comm]
    simp only [ham_comm]
  exact le_antisymm (hs μ ν) (hs ν μ)

theorem W_full_occurrence_le (I : FiniteSystem V E A L) (B D : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (hD : I.Bounds D Δ) (v : V) (r : L) (j : ↑(I.incident v))
    (hr : 0 < eventMass (I.validLaw D hD) (I.Occurs v r j)) {t : ℝ}
    (hres : ∀ a b, I.Compatible B j.val a → I.Compatible D j.val b →
      I.label j.val v b = r →
      W ham (I.pinnedLaw B hB j.val a) (I.pinnedLaw D hD j.val b) ≤ t) :
    W ham (I.validLaw B hB) (conditional (I.validLaw D hD) (I.Occurs v r j)) ≤ 1 + t := by
  rw [W_ham_comm]
  apply I.W_occurrence_full_le D B hD hB v r j hr
  intro b a hbc hac hbl
  rw [W_ham_comm]
  exact hres a b hac hbc hbl

end
end CI2ZF.Appendix.Edge.FiniteSystem
