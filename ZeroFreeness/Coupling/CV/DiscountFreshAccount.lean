import ZeroFreeness.Coupling.CV.DiscountAverage

/-! Pointwise and expected fresh-colour gains, accounted once per actual
singleton output and once per physical metric incidence. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]
local instance cvFreshAccountConfigDecEq : DecidableEq (V → C) := Classical.decEq _

def eligibleFreshVertices (X Y : V → C) (v : V) : Finset V :=
  Finset.univ.filter fun s => s ≠ v ∧ (X s = X v ∨ X s = Y v)

def freshGainCost (I : PinningData V C) (x : ℝ) (X Y : V → C) (v : V) (U Z : V → C) : ℝ :=
  ∑ s ∈ eligibleFreshVertices X Y v, ∑ c ∈ freshColours I X s (X v) (Y v),
    if U = Function.update X s c ∧ Z = Function.update Y s c then freshScoreGain I x X Y v s else 0

lemma fresh_colour_ne_old (I : PinningData V C) (X Y : V → C) (v s : V) (c : C)
    (hs : s ∈ eligibleFreshVertices X Y v) (hc : c ∈ freshColours I X s (X v) (Y v)) : c ≠ X s := by
  have hs := (Finset.mem_filter.mp hs).2.2
  have hc := (mem_freshColours I X s (X v) (Y v) c).mp hc
  rcases hs with hs | hs
  · simpa only [hs] using hc.1
  · simpa only [hs] using hc.2.1

lemma update_change_unique (X : V → C) {s t : V} {c d : C}
    (hc : c ≠ X s) (_hd : d ≠ X t) (he : Function.update X s c = Function.update X t d) :
    s = t ∧ c = d := by
  classical
  have hst : s = t := by
    by_contra hst
    have hh := congrFun he s
    rw [Function.update_self, Function.update_of_ne hst] at hh
    exact hc hh
  subst t
  exact ⟨rfl, by simpa only [Function.update_self] using congrFun he s⟩

lemma freshGainCost_at_fresh (I : PinningData V C) (x : ℝ) (X Y : V → C) (v s : V) (c : C)
    (hs : s ∈ eligibleFreshVertices X Y v) (hc : c ∈ freshColours I X s (X v) (Y v)) :
    freshGainCost I x X Y v (Function.update X s c) (Function.update Y s c) =
      freshScoreGain I x X Y v s := by
  classical
  have hcs := fresh_colour_ne_old I X Y v s c hs hc
  unfold freshGainCost
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro d hd hdc
      rw [if_neg]
      intro hm
      exact hdc (update_change_unique X (fresh_colour_ne_old I X Y v s d hs hd) hcs hm.1.symm).2
    · exact fun hh => (hh hc).elim
  · intro t ht hts
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro hm
    exact hts (update_change_unique X (fresh_colour_ne_old I X Y v t d ht hd) hcs hm.1.symm).1
  · exact fun hh => (hh hs).elim

lemma newTargetCount_fresh_eq_zero (I : PinningData V C) (X Y : V → C) (v s u : V) (c : C)
    (hst : X s = X v ∨ X s = Y v) :
    newTargetCount I X Y (Function.update X s c) (Function.update Y s c) v u = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hwreg, hbad⟩ := Finset.mem_filter.mp hw
  obtain ⟨_, _, hreg⟩ := Finset.mem_filter.mp hwreg
  have hws : w ≠ s := by intro hh; subst w; exact hst.elim hreg.2.1 hreg.2.2
  apply hbad
  simpa only [Function.update_of_ne hws] using hreg

lemma discountLoss_fresh_eq_zero (I : PinningData V C) (x : ℝ) (X Y : V → C)
    (v s u : V) (c : C) (hsv : s ≠ v) (hst : X s = X v ∨ X s = Y v) :
    discountLoss I x X Y (Function.update X s c) (Function.update Y s c) v u = 0 := by
  have hf : rootFixed X Y (Function.update X s c) (Function.update Y s c) v := by
    exact ⟨Function.update_of_ne hsv.symm _ _, Function.update_of_ne hsv.symm _ _⟩
  rw [discountLoss, if_pos hf, newTargetCount_fresh_eq_zero I X Y v s u c hst]
  simp only [Nat.cast_zero, mul_zero, ite_self, add_zero, zero_add]
  by_cases hreg : regularAt X Y v u
  · have hus : u ≠ s := by intro hh; subst u; exact hst.elim hreg.2.1 hreg.2.2
    have hnb : ¬ badAt X Y (Function.update X s c) (Function.update Y s c) v u := by
      intro hh
      apply hh
      simpa only [regularAt, Function.update_of_ne hus] using hreg
    exact if_neg (fun hh => hnb hh.2)
  · have hz : incidenceDiscount I x X Y v u = 0 := if_neg hreg
    simp only [hz, ite_self]

/-- Fresh gains can be added to the pointwise loss bound without reusing
a root score: every nonzero fresh term identifies one unique output. -/
theorem root_loss_add_freshGain_le (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X Y U Z : V → C) (v : V)
    (hagree : ∀ w, w ≠ v → X w = Y w) :
    vertexScore I x X Y v - (∑ u ∈ I.graph.neighborFinset v, discountLoss I x X Y U Z v u) +
      freshGainCost I x X Y v U Z ≤
      if rootFixed X Y U Z v then vertexScore I x U Z v else 0 := by
  by_cases he : ∃ s ∈ eligibleFreshVertices X Y v,
      ∃ c ∈ freshColours I X s (X v) (Y v),
        U = Function.update X s c ∧ Z = Function.update Y s c
  · obtain ⟨s, hs, c, hc, rfl, rfl⟩ := he
    obtain ⟨hsv, hst⟩ := (Finset.mem_filter.mp hs).2
    have hcdata := (mem_freshColours I X s (X v) (Y v) c).mp hc
    rw [freshGainCost_at_fresh I x X Y v s c hs hc]
    have hf : rootFixed X Y (Function.update X s c) (Function.update Y s c) v := by
      exact ⟨Function.update_of_ne hsv.symm _ _, Function.update_of_ne hsv.symm _ _⟩
    rw [if_pos hf]
    simp only [discountLoss_fresh_eq_zero I x X Y v s _ c hsv hst, Finset.sum_const_zero, sub_zero]
    exact vertexScore_update_fresh_ge I hx X Y v s c hsv hcdata.1 hcdata.2.1 hst
  · have hz : freshGainCost I x X Y v U Z = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      apply Finset.sum_eq_zero
      intro c hc
      exact if_neg (fun hh => he ⟨s, hs, c, hc, hh⟩)
    rw [hz, add_zero]
    exact root_score_loss_le I hx X Y U Z v hagree

lemma coupling_cost_finset_sum {S T J : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (A : Finset J)
    (f : J → S → T → ℝ) : γ.cost (fun s t => ∑ j ∈ A, f j s t) = ∑ j ∈ A, γ.cost (f j) := by
  unfold Coupling.cost
  simp only [Finset.mul_sum]
  calc
    _ = ∑ s, ∑ j ∈ A, ∑ t, γ.w s t * f j s t :=
      Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma coupling_cost_point {S T : Type*} [Fintype S] [Fintype T]
    {μ : FinDist S} {ν : FinDist T} (γ : Coupling μ ν) (s₀ : S) (t₀ : T) (c : ℝ) :
    γ.cost (fun s t => if s = s₀ ∧ t = t₀ then c else 0) = γ.w s₀ t₀ * c := by
  classical
  simp only [Coupling.cost, mul_ite, mul_zero]
  rw [Finset.sum_eq_single s₀]
  · simp
  · intro s _ hs; simp [hs]
  · simp

/-- Exact gain expectation under the actual hard coupling for each fixed
activation, including all repeated physical gain incidences. -/
theorem adjacentHard_freshGain_cost [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (ω : I.Constraint → Bool) (x : ℝ) :
    (adjacentHardCoupling I X Y v hroot hagree choice ω).cost (freshGainCost I x X Y v) =
      (∑ s ∈ eligibleFreshVertices X Y v,
        (freshColours I X s (X v) (Y v)).card * freshScoreGain I x X Y v s) /
          ((Fintype.card V : ℝ) * Fintype.card C) := by
  unfold freshGainCost
  rw [coupling_cost_finset_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  rw [coupling_cost_finset_sum]
  obtain ⟨hsv, hst⟩ := (Finset.mem_filter.mp hs).2
  have hentry (c : C) (hc : c ∈ freshColours I X s (X v) (Y v)) :
      (adjacentHardCoupling I X Y v hroot hagree choice ω).w
        (Function.update X s c) (Function.update Y s c) =
      1 / ((Fintype.card V : ℝ) * Fintype.card C) :=
    fullHardCoupling_fresh_entry I X Y ω v (X v) (Y v) rfl rfl hroot hagree (choice ω) s hsv hst c hc
  calc
    _ = ∑ _c ∈ freshColours I X s (X v) (Y v),
        (1 / ((Fintype.card V : ℝ) * Fintype.card C)) * freshScoreGain I x X Y v s := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [coupling_cost_point, hentry c hc]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Sum of unique-blocker probabilities, with the zero-blocker case
vanishing automatically through the factor `freeBlockers.card`. -/
def singleBlockerTotal (I : PinningData V C) (x : ℝ) (X Y : V → C) (v : V) : ℝ :=
  ∑ u ∈ I.graph.neighborFinset v, if regularAt X Y v u then
    (freeBlockers I X Y v u).card * (1 - x)^2 * x^(blockerCount I X Y v u - 1) else 0

lemma sum_freshScoreGain_eq_singleBlockerTotal (I : PinningData V C) (x : ℝ)
    (X Y : V → C) (v : V) (hagree : ∀ w, w ≠ v → X w = Y w) :
    (∑ s ∈ eligibleFreshVertices X Y v, freshScoreGain I x X Y v s) =
      singleBlockerTotal I x X Y v := by
  classical
  unfold freshScoreGain singleBlockerTotal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : regularAt X Y v u
  · rw [if_pos hu]
    have hif (s : V) : ((X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v) ∧ I.graph.Adj u s) ↔ I.graph.Adj u s :=
      ⟨And.right, fun hh => ⟨hu, hh⟩⟩
    simp_rw [hif]
    rw [← Finset.sum_filter]
    have hset : (eligibleFreshVertices X Y v).filter (I.graph.Adj u) = freeBlockers I X Y v u := by
      ext s
      simp only [eligibleFreshVertices, freeBlockers, Finset.mem_filter, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨⟨hsv, hst⟩, hadj⟩
        exact ⟨hadj, hsv, hst.elim Or.inl (fun hh => Or.inr (Or.inl hh))⟩
      · rintro ⟨hadj, hsv, hst⟩
        rw [← hagree s hsv] at hst
        exact ⟨⟨hsv, by tauto⟩, hadj⟩
    rw [hset]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  · have hif (s : V) : ¬ ((X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v) ∧ I.graph.Adj u s) := fun hh => hu hh.1
    simp only [if_neg hu, if_neg (hif _), Finset.sum_const_zero]

/-- The fresh-colour contribution has the exact coefficient `q-Δ-2`
against the physical unique-blocker total. -/
theorem adjacentHard_freshGain_lower [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (ω : I.Constraint → Bool) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (Δ : ℕ) (hdegree : ∀ s, I.graph.degree s + ∑ c, I.boundaryCount s c ≤ Δ) :
    (((Fintype.card C : ℝ) - Δ - 2) * singleBlockerTotal I x X Y v) /
      ((Fintype.card V : ℝ) * Fintype.card C) ≤
      (adjacentHardCoupling I X Y v hroot hagree choice ω).cost (freshGainCost I x X Y v) := by
  rw [adjacentHard_freshGain_cost, ← sum_freshScoreGain_eq_singleBlockerTotal I x X Y v hagree,
    Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro s _
  have hc := freshColours_card I X s (X v) (Y v) (hdegree s)
  have hcR : (Fintype.card C : ℝ) ≤ (freshColours I X s (X v) (Y v)).card + Δ + 2 := by exact_mod_cast hc
  apply mul_le_mul_of_nonneg_right (by linarith) (freshScoreGain_nonneg I hx.1 X Y v s)

end
end ZeroFreeness.Appendix.CV
