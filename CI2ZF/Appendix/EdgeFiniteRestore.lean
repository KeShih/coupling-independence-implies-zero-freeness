import CI2ZF.Appendix.EdgeFiniteOdds

/-! Restoring an exposed edge costs at most one Hamming disagreement.
These transport bounds use actual minimizing finite couplings. -/
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

lemma ham_eq_sum (σ τ : E → A) :
    ham σ τ = ∑ e, if σ e = τ e then (0 : ℝ) else 1 := by
  simp only [ham, hamCard, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_not]

lemma sum_split (e : E) (f : E → ℝ) :
    (∑ j, f j) = f e + ∑ j : {j : E // j ≠ e}, f j.val := by
  rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ e)]
  congr 1
  exact Finset.sum_subtype (Finset.univ.erase e) (by simp) f

lemma ham_join (e : E) (a b : A) (σ τ : {f : E // f ≠ e} → A) :
    ham (joinConfig e a σ) (joinConfig e b τ) = (if a = b then (0 : ℝ) else 1) + ham σ τ := by
  rw [ham_eq_sum, sum_split e, ham_eq_sum]
  simp only [joinConfig_self, joinConfig_other]

lemma ham_join_le (e : E) (a b : A) (σ τ : {f : E // f ≠ e} → A) :
    ham (joinConfig e a σ) (joinConfig e b τ) ≤ 1 + ham σ τ := by
  rw [ham_join]
  gcongr
  split_ifs <;> norm_num

/-- Restoring possibly different states of one edge changes the transport
bound by at most one, with no assumption about an optimal plan. -/
theorem W_restore_le (e : E) (a b : A)
    (μ ν : FinDist ({f : E // f ≠ e} → A)) :
    W ham (CI2ZF.mapLaw μ (joinConfig e a)) (CI2ZF.mapLaw ν (joinConfig e b)) ≤ 1 + W ham μ ν := by
  obtain ⟨π, hπ⟩ := exists_optimal_coupling μ ν ham ham_nonneg
  apply (W_le_cost ham_nonneg (CI2ZF.mapCoupling π (joinConfig e a) (joinConfig e b))).trans
  rw [CI2ZF.cost_mapCoupling]
  calc
    _ ≤ π.cost (fun σ τ => 1 + ham σ τ) := CI2ZF.cost_le_cost π (ham_join_le e a b)
    _ = 1 + π.cost ham := by
      simp only [Coupling.cost, mul_add, mul_one, Finset.sum_add_distrib]
      rw [π.total_mass]
    _ = _ := by rw [hπ]

lemma gibbs_coordinate_pos_compatible (I : FiniteSystem V E A L) (B : Boundary V L)
    (hZ : 0 < I.partition B) (e : E) (a : A)
    (ha : 0 < eventMass (I.gibbs B hZ) (fun σ => σ e = a)) : I.Compatible B e a := by
  by_contra hh
  rw [I.gibbs_coordinate_mass, if_neg hh, zero_mul, zero_div] at ha
  exact lt_irrefl _ ha

lemma pinBoundary_pair (I : FiniteSystem V E A L) (B : Boundary V L) (e : E) (a : A)
    {v w : V} (hvw : v ≠ w) (he : I.endpoints e = {v, w}) :
    I.pinBoundary B e a = addBoundary (addBoundary B v (I.label e v a)) w (I.label e w a) := by
  ext z
  by_cases hzv : z = v
  · subst z
    simp [pinBoundary, he, addBoundary, Function.update_of_ne hvw]
  · by_cases hzw : z = w
    · subst z
      simp [pinBoundary, he, addBoundary, Function.update_of_ne (Ne.symm hvw)]
    · simp [pinBoundary, he, addBoundary, hzv, hzw]

lemma endpoints_pair (I : FiniteSystem V E A L) (e : E) (v : V) (hv : v ∈ I.endpoints e) :
    ∃ w, v ≠ w ∧ I.endpoints e = {v, w} := by
  obtain ⟨u, w, huw, he⟩ := Finset.card_eq_two.mp (I.endpoints_card e)
  rw [he] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨w, huw, he⟩
  · exact ⟨u, Ne.symm huw, he.trans (Finset.pair_comm _ _)⟩

end
end CI2ZF.Appendix.Edge.FiniteSystem
