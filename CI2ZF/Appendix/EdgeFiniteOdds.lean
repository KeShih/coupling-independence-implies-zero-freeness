import CI2ZF.Appendix.EdgeFiniteExposure

/-! The occurrence/avoidance ratio is derived from actual conditional
partition sums. At each fixed off-edge configuration an occurrence has
at most one unit of activity, while avoidance has at least Δ+1. -/
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

lemma sum_all_coordinates (e : E) (w : (E → A) → ℝ) :
    (∑ σ, w σ) = ∑ τ, ∑ a, w (joinConfig e a τ) := by
  rw [← Fintype.sum_equiv (Equiv.funSplitAt e A).symm
    (fun p => w (joinConfig e p.1 p.2)) w (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma occurrence_admissible_residual (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (v : V) (hv : v ∈ I.endpoints e) (l : L) (a : A)
    (τ : {f : E // f ≠ e} → A) (ha : I.Admissible B (joinConfig e a τ))
    (hl : I.label e v a = l) : (I.remove e).Admissible (addBoundary B v l) τ := by
  have hr := (I.admissible_join_unpinned_iff B e a a τ).mp ha
  rw [(I.remove e).admissible_add_iff]
  refine ⟨hr.1, ?_⟩
  intro f hvf
  have hp := I.goodAt_pair hr.2 f.val (Ne.symm f.property) v hv hvf
  rw [joinConfig_other, hl] at hp
  exact Ne.symm hp

lemma configurationWeight_join_le_product (I : FiniteSystem V E A L) (B : Boundary V L)
    (e : E) (a : A) (τ : {f : E // f ≠ e} → A) :
    I.configurationWeight B (joinConfig e a τ) ≤ I.activity e a * ∏ f, I.activity f.val (τ f) := by
  unfold configurationWeight
  split_ifs with ha
  · rw [product_split e]
    simp
  · exact mul_nonneg (I.activity_nonneg e a) (Finset.prod_nonneg fun f _ => I.activity_nonneg f.val (τ f))

/-- Fixing all edges except the exposed edge already gives the ratio bound. -/
lemma occurrence_avoidance_fibre (I : FiniteSystem V E A L) (B : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (e : E) (v : V) (hv : v ∈ I.endpoints e)
    (l : L) (b : A) (τ : {f : E // f ≠ e} → A) :
    ((Δ : ℝ) + 1) * (∑ a, if I.label e v a = l then I.configurationWeight B (joinConfig e a τ) else 0) ≤
      ∑ a, I.configurationWeight (addBoundary B v l) (joinConfig e a τ) := by
  let P : ℝ := ∏ f, I.activity f.val (τ f)
  have hP : 0 ≤ P := Finset.prod_nonneg fun f _ => I.activity_nonneg f.val (τ f)
  by_cases hr : (I.remove e).Admissible (addBoundary B v l) τ
  · have hN : (∑ a, if I.label e v a = l then I.configurationWeight B (joinConfig e a τ) else 0) ≤ P := by
      calc
        _ ≤ ∑ a, (if I.label e v a = l then I.activity e a else 0) * P := by
          apply Finset.sum_le_sum
          intro a _
          by_cases hl : I.label e v a = l
          · simp only [if_pos hl]
            exact I.configurationWeight_join_le_product B e a τ
          · simp only [if_neg hl, zero_mul, le_refl]
        _ = (∑ a, if I.label e v a = l then I.activity e a else 0) * P := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * P := mul_le_mul_of_nonneg_right (hB.2.1 e v hv l) hP
        _ = P := one_mul _
    have hD : (∑ a, I.configurationWeight (addBoundary B v l) (joinConfig e a τ)) =
        I.availableMass (addBoundary B v l) e (joinConfig e b τ) * P := by
      simp_rw [I.configurationWeight_join_available (addBoundary B v l) e _ b τ]
      change (∑ a, (if I.GoodAt (addBoundary B v l) e (joinConfig e b τ) a then I.activity e a else 0) *
        (if (I.remove e).Admissible (addBoundary B v l) τ then P else 0)) = _
      rw [if_pos hr, ← Finset.sum_mul]
      rfl
    have hav : (Δ : ℝ) + 1 ≤ I.availableMass (addBoundary B v l) e (joinConfig e b τ) := by
      have ha := I.availableMass_lower (addBoundary B v l) e (joinConfig e b τ) hB.2.1
      have hm := I.compatibleMass_add_lower B v l e hB.2.1
      have hs := hB.2.2 e
      linarith
    rw [hD]
    exact (mul_le_mul_of_nonneg_left hN (by positivity)).trans (mul_le_mul_of_nonneg_right hav hP)
  · have hz (a : A) : (if I.label e v a = l then I.configurationWeight B (joinConfig e a τ) else 0) = 0 := by
      by_cases hl : I.label e v a = l
      · rw [if_pos hl]
        have hna : ¬I.Admissible B (joinConfig e a τ) :=
          fun ha => hr (I.occurrence_admissible_residual B e v hv l a τ ha hl)
        exact if_neg hna
      · exact if_neg hl
    simp_rw [hz, Finset.sum_const_zero, mul_zero]
    exact Finset.sum_nonneg fun a _ => I.configurationWeight_nonneg _ _

def occurrencePartition (I : FiniteSystem V E A L) (B : Boundary V L) (v : V) (l : L)
    (j : ↑(I.incident v)) : ℝ := ∑ σ, if I.Occurs v l j σ then I.configurationWeight B σ else 0

lemma occurrence_partition_bound [Nonempty A] (I : FiniteSystem V E A L) (B : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (v : V) (l : L) (j : ↑(I.incident v)) :
    ((Δ : ℝ) + 1) * I.occurrencePartition B v l j ≤ I.partition (addBoundary B v l) := by
  let b : A := Classical.choice inferInstance
  rw [occurrencePartition, sum_all_coordinates j.val, partition, sum_all_coordinates j.val,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  simp only [Occurs, joinConfig_self]
  exact I.occurrence_avoidance_fibre B hB j.val v (I.incident_mem v j) l b τ

lemma gibbs_occurrence_mass (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) (v : V) (l : L) (j : ↑(I.incident v)) :
    eventMass (I.gibbs B hZ) (I.Occurs v l j) = I.occurrencePartition B v l j / I.partition B := by
  unfold occurrencePartition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hs : I.Occurs v l j σ <;> simp [gibbs, hs]

/-- The odds in the actual exposure decomposition are at most 1/(Δ+1). -/
theorem occurrence_odds_le [Nonempty A] (I : FiniteSystem V E A L) (B : Boundary V L)
    {Δ : ℕ} (hB : I.Bounds B Δ) (v : V) (l : L) (j : ↑(I.incident v)) :
    eventMass (I.gibbs B (hB.partition_pos I B)) (I.Occurs v l j) /
      eventMass (I.gibbs B (hB.partition_pos I B)) (I.Avoids v l) ≤ 1 / ((Δ : ℝ) + 1) := by
  rw [I.gibbs_occurrence_mass, I.gibbs_avoidance_mass,
    div_div_div_cancel_right₀ (hB.partition_pos I B).ne']
  have hZa := hB.add_partition_pos I B v l
  have hd : 0 < (Δ : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hZa).mpr
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hd).mpr
  simpa only [mul_comm] using I.occurrence_partition_bound B hB v l j

end
end CI2ZF.Appendix.Edge.FiniteSystem
