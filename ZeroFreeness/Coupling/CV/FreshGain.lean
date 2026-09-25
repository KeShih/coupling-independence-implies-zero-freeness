import ZeroFreeness.Coupling.CV.SingleBlockerActivation

/-!
# Lemma `lem:cv-fresh` (companion appendix CV, Lemma 5.12), per neighbour

For a regular root neighbour `u` (`regularAt X Y v u`), with
`R = r_u = (freeBlockers I X Y v u).card` free target blockers and
`e = e_u = bcount_u(a) + bcount_u(b)` target pinned-neighbour constraints:

* `singleBlockerEvent` is the activation event `SB_u`: the root edge `vu` is
  active, exactly one of the `R` blocker edges is active, and every other
  target constraint at `u` is inactive.
* `singleBlocker_probability`: `Pr(SB_u) = R θ² x^(R+e-1)` if `R ≥ 1`, and
  `0` if `R = 0` (`θ = 1 - x`).
* `freshIncrementAt u` is the increase of the output `u`-discount
  (the `(v,u)` summand `incidenceDiscount`) over its input value `s_u`, on the
  singleton fresh-colour recolourings of the blockers of `u`.
* `cv_fresh`: under the actual coupled update, for every activation outcome and
  hence on average, its expectation is at least `α_fr / (nq) · Pr(SB_u)` with
  `α_fr = q - Δ - 2`.
* `sum_freshGainAt_eq_freshGainCost`: the per-neighbour gains sum to the
  library's global fresh-gain cost `freshGainCost`, so the per-`u` bound is the
  summand of the global one used in `expected_discount_decrease_le`.
-/

namespace ZeroFreeness.Appendix.CV

open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section
set_option linter.unusedSectionVars false

variable {V C : Type*} [Fintype V] [Fintype C]
local instance (priority := 2000) freshGainConfigDecEq : DecidableEq (V → C) :=
  Classical.decEq _

/-! ## The single-blocker event and its probability -/

/-- The event `SB_u`. -/
def singleBlockerEvent (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool) : Prop :=
  ∃ w : freeBlockers I X Y v u.val, singleBlockerActivation I X Y v u w ω

/-- `e_u`: the pinned-neighbour constraints at `u` forbidding a target colour. -/
def targetBoundaryCount (I : PinningData V C) (X Y : V → C) (v u : V) : ℕ :=
  I.boundaryCount u (X v) + I.boundaryCount u (Y v)

lemma blockerCount_eq (I : PinningData V C) (X Y : V → C) (v u : V) (hroot : X v ≠ Y v) :
    blockerCount I X Y v u =
      (freeBlockers I X Y v u).card + targetBoundaryCount I X Y v u := by
  unfold blockerCount targetBoundaryCount freeBlockers
  congr 1
  have hs : (Finset.univ.filter fun c => c = X v ∨ c = Y v) = {X v, Y v} := by
    ext c
    simp
  rw [hs, Finset.sum_pair hroot]

lemma blockerFreeConstraint_injective (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) :
    Function.Injective (blockerFreeConstraint I X Y v u) := by
  intro w w' he
  have h := rootFreeConstraint_injective I u.val he
  exact Subtype.ext (Subtype.mk.inj h)

/-- At most one blocker realizes the single-blocker pattern. -/
lemma singleBlockerActivation_unique (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    {w w' : freeBlockers I X Y v u.val}
    (hw : singleBlockerActivation I X Y v u w ω)
    (hw' : singleBlockerActivation I X Y v u w' ω) : w = w' := by
  by_contra hne
  have htrue : ω (blockerFreeConstraint I X Y v u w') = true :=
    hw'.1 _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hfalse : ω (blockerFreeConstraint I X Y v u w') = false := by
    apply hw.2
    apply Finset.mem_sdiff.mpr
    refine ⟨blockerFreeConstraint_mem_targets I X Y v u w', ?_⟩
    intro hmem
    rcases Finset.mem_insert.mp hmem with hr | hb
    · exact blockerFreeConstraint_ne_root I X Y v u w' hr
    · exact hne (blockerFreeConstraint_injective I X Y v u (Finset.mem_singleton.mp hb)).symm
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

lemma singleBlockerEvent_indicator (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool) :
    (if singleBlockerEvent I X Y v u ω then (1 : ℝ) else 0) =
      ∑ w : freeBlockers I X Y v u.val,
        if singleBlockerActivation I X Y v u w ω then (1 : ℝ) else 0 := by
  by_cases hE : singleBlockerEvent I X Y v u ω
  · obtain ⟨w₀, hw₀⟩ := hE
    rw [if_pos ⟨w₀, hw₀⟩, Finset.sum_eq_single w₀]
    · rw [if_pos hw₀]
    · intro w _ hw
      rw [if_neg]
      intro hh
      exact hw (singleBlockerActivation_unique I X Y v u ω hh hw₀)
    · intro hh
      exact (hh (Finset.mem_univ _)).elim
  · rw [if_neg hE]
    symm
    apply Finset.sum_eq_zero
    intro w _
    exact if_neg (fun hh => hE ⟨w, hh⟩)

/-- `b_u^SB = Pr(SB_u) = R θ² x^(R+e-1)` (natural-number exponent; the factor
`R` makes it vanish when `R = 0`). -/
theorem singleBlocker_probability (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (hroot : X v ≠ Y v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx)
        (fun ω => if singleBlockerEvent I X Y v u ω then (1 : ℝ) else 0) =
      (freeBlockers I X Y v u.val).card * (1 - x) ^ 2 *
        x ^ ((freeBlockers I X Y v u.val).card + targetBoundaryCount I X Y v u.val - 1) := by
  simp_rw [singleBlockerEvent_indicator I X Y v u]
  rw [expectReal_sum]
  simp only [singleBlockerActivation_probability I X Y v u _ x hx, Finset.sum_const,
    Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, blockerCount_eq I X Y v u.val hroot]
  ring

/-- The case form printed in the paper. -/
theorem singleBlocker_probability_cases (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (hroot : X v ≠ Y v) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    expectReal (activityCoins I x hx)
        (fun ω => if singleBlockerEvent I X Y v u ω then (1 : ℝ) else 0) =
      if 1 ≤ (freeBlockers I X Y v u.val).card then
        (freeBlockers I X Y v u.val).card * (1 - x) ^ 2 *
          x ^ ((freeBlockers I X Y v u.val).card + targetBoundaryCount I X Y v u.val - 1)
      else 0 := by
  rw [singleBlocker_probability I X Y v u hroot x hx]
  split_ifs with hR
  · rfl
  · have h0 : (freeBlockers I X Y v u.val).card = 0 := by omega
    simp [h0]

/-! ## The per-neighbour fresh-colour gain -/

/-- Increase of the output `u`-discount over its input value `s_u`, on the
singleton fresh-colour recolourings of the blockers of `u`. -/
def freshIncrementAt (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V)
    (U Z : V → C) : ℝ :=
  ∑ s ∈ freeBlockers I X Y v u, ∑ c ∈ freshColours I X s (X v) (Y v),
    if U = Function.update X s c ∧ Z = Function.update Y s c then
      incidenceDiscount I x U Z v u - incidenceDiscount I x X Y v u else 0

lemma freeBlockers_data {I : PinningData V C} {X Y : V → C} {v u s : V}
    (hagree : ∀ w, w ≠ v → X w = Y w) (hs : s ∈ freeBlockers I X Y v u) :
    I.graph.Adj u s ∧ s ≠ v ∧ (X s = X v ∨ X s = Y v) := by
  simp only [freeBlockers, Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hs
  obtain ⟨hadj, hsv, hst⟩ := hs
  refine ⟨hadj, hsv, ?_⟩
  rw [← hagree s hsv] at hst
  tauto

/-- On each fresh singleton output the `u`-discount rises by exactly
`θ² x^(R+e-1)`. -/
lemma freshIncrementAt_eq (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V)
    (hagree : ∀ w, w ≠ v → X w = Y w) (hu : regularAt X Y v u) (U Z : V → C) :
    freshIncrementAt I x X Y v u U Z =
      ∑ s ∈ freeBlockers I X Y v u, ∑ c ∈ freshColours I X s (X v) (Y v),
        if U = Function.update X s c ∧ Z = Function.update Y s c then
          (1 - x) ^ 2 * x ^ (blockerCount I X Y v u - 1) else 0 := by
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro c hc
  obtain ⟨hadj, hsv, hst⟩ := freeBlockers_data hagree hs
  obtain ⟨hca, hcb, -, -⟩ := (mem_freshColours I X s (X v) (Y v) c).mp hc
  by_cases hE : U = Function.update X s c ∧ Z = Function.update Y s c
  · rw [if_pos hE, if_pos hE]
    obtain ⟨rfl, rfl⟩ := hE
    rw [incidenceDiscount_update_fresh I x X Y v u s c hsv hca hcb hst hu, if_pos hadj]
    ring
  · rw [if_neg hE, if_neg hE]

/-- Exact coupled expectation of the per-neighbour fresh gain, for every
activation outcome. -/
theorem adjacentHard_freshIncrementAt_cost [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (ω : I.Constraint → Bool) (x : ℝ) (u : V) (hu : regularAt X Y v u) :
    (adjacentHardCoupling I X Y v hroot hagree choice ω).cost (freshIncrementAt I x X Y v u) =
      (∑ s ∈ freeBlockers I X Y v u, ((freshColours I X s (X v) (Y v)).card : ℝ) *
        ((1 - x) ^ 2 * x ^ (blockerCount I X Y v u - 1))) /
          ((Fintype.card V : ℝ) * Fintype.card C) := by
  have hf : freshIncrementAt I x X Y v u = fun U Z =>
      ∑ s ∈ freeBlockers I X Y v u, ∑ c ∈ freshColours I X s (X v) (Y v),
        if U = Function.update X s c ∧ Z = Function.update Y s c then
          (1 - x) ^ 2 * x ^ (blockerCount I X Y v u - 1) else 0 := by
    funext U Z
    exact freshIncrementAt_eq I x X Y v u hagree hu U Z
  rw [hf, coupling_cost_finset_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  obtain ⟨-, hsv, hst⟩ := freeBlockers_data hagree hs
  rw [coupling_cost_finset_sum]
  have hentry (c : C) (hc : c ∈ freshColours I X s (X v) (Y v)) :
      (adjacentHardCoupling I X Y v hroot hagree choice ω).w
        (Function.update X s c) (Function.update Y s c) =
      1 / ((Fintype.card V : ℝ) * Fintype.card C) :=
    fullHardCoupling_fresh_entry I X Y ω v (X v) (Y v) rfl rfl hroot hagree (choice ω)
      s hsv hst c hc
  calc
    _ = ∑ _c ∈ freshColours I X s (X v) (Y v),
        (1 / ((Fintype.card V : ℝ) * Fintype.card C)) *
          ((1 - x) ^ 2 * x ^ (blockerCount I X Y v u - 1)) := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [coupling_cost_point, hentry c hc]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- `lem:cv-fresh`, per regular neighbour `u`: the expected increase of the
output `u`-discount caused by fresh singleton recolourings of its blockers is
at least `α_fr/(nq) · b_u^SB`, where `b_u^SB = Pr(SB_u)`.  The bound holds for
every activation outcome (`pointwise`) and after averaging (`averaged`). -/
theorem cv_fresh [Nonempty V] [Nonempty C]
    (I : PinningData V C) (X Y : V → C) (v : V) (hroot : X v ≠ Y v)
    (hagree : ∀ w, w ≠ v → X w = Y w) (choice : AdjacentChoices I X Y v hroot hagree)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (Δ : ℕ)
    (hdegree : ∀ s, I.graph.degree s + ∑ c, I.boundaryCount s c ≤ Δ)
    (u : I.graph.neighborSet v) (hu : regularAt X Y v u.val) :
    (∀ ω, ((Fintype.card C : ℝ) - Δ - 2) / ((Fintype.card V : ℝ) * Fintype.card C) *
        expectReal (activityCoins I x hx)
          (fun ω => if singleBlockerEvent I X Y v u ω then (1 : ℝ) else 0) ≤
      (adjacentHardCoupling I X Y v hroot hagree choice ω).cost
        (freshIncrementAt I x X Y v u.val)) ∧
    ((Fintype.card C : ℝ) - Δ - 2) / ((Fintype.card V : ℝ) * Fintype.card C) *
        expectReal (activityCoins I x hx)
          (fun ω => if singleBlockerEvent I X Y v u ω then (1 : ℝ) else 0) ≤
      averagedCost I X Y v hroot hagree choice x hx (freshIncrementAt I x X Y v u.val) ∧
    expectReal (activityCoins I x hx)
        (fun ω => if singleBlockerEvent I X Y v u ω then (1 : ℝ) else 0) =
      if 1 ≤ (freeBlockers I X Y v u.val).card then
        (freeBlockers I X Y v u.val).card * (1 - x) ^ 2 *
          x ^ ((freeBlockers I X Y v u.val).card + targetBoundaryCount I X Y v u.val - 1)
      else 0 := by
  have hpw : ∀ ω, ((Fintype.card C : ℝ) - Δ - 2) / ((Fintype.card V : ℝ) * Fintype.card C) *
        expectReal (activityCoins I x hx)
          (fun ω => if singleBlockerEvent I X Y v u ω then (1 : ℝ) else 0) ≤
      (adjacentHardCoupling I X Y v hroot hagree choice ω).cost
        (freshIncrementAt I x X Y v u.val) := by
    intro ω
    rw [adjacentHard_freshIncrementAt_cost I X Y v hroot hagree choice ω x u.val hu,
      singleBlocker_probability I X Y v u hroot x hx, ← blockerCount_eq I X Y v u.val hroot]
    have hn : (0 : ℝ) < (Fintype.card V : ℝ) * Fintype.card C := by positivity
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hn.le
    have hg : 0 ≤ (1 - x) ^ 2 * x ^ (blockerCount I X Y v u.val - 1) :=
      mul_nonneg (sq_nonneg _) (pow_nonneg hx.1 _)
    calc
      ((Fintype.card C : ℝ) - Δ - 2) *
          ((freeBlockers I X Y v u.val).card * (1 - x) ^ 2 *
            x ^ (blockerCount I X Y v u.val - 1)) =
        ∑ _s ∈ freeBlockers I X Y v u.val, ((Fintype.card C : ℝ) - Δ - 2) *
          ((1 - x) ^ 2 * x ^ (blockerCount I X Y v u.val - 1)) := by
        simp only [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s _
        have hc := freshColours_card I X s (X v) (Y v) (hdegree s)
        have hcR : (Fintype.card C : ℝ) ≤
            (freshColours I X s (X v) (Y v)).card + Δ + 2 := by exact_mod_cast hc
        exact mul_le_mul_of_nonneg_right (by linarith) hg
  refine ⟨hpw, ?_, singleBlocker_probability_cases I X Y v u hroot x hx⟩
  have hm := expectReal_mono (activityCoins I x hx) hpw
  rw [expectReal_const] at hm
  exact hm

/-! ## Consistency with the library's global fresh-gain account -/

/-- The per-neighbour fresh gain in the form summed by the library. -/
def freshGainAt (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V) (U Z : V → C) : ℝ :=
  ∑ s ∈ eligibleFreshVertices X Y v, ∑ c ∈ freshColours I X s (X v) (Y v),
    if U = Function.update X s c ∧ Z = Function.update Y s c then
      (if (X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v) ∧ I.graph.Adj u s then
        (1 - x) ^ 2 * x ^ (blockerCount I X Y v u - 1) else 0) else 0

theorem sum_freshGainAt_eq_freshGainCost (I : PinningData V C) (x : ℝ) (X Y : V → C) (v : V)
    (U Z : V → C) :
    (∑ u ∈ I.graph.neighborFinset v, freshGainAt I x X Y v u U Z) =
      freshGainCost I x X Y v U Z := by
  unfold freshGainAt freshGainCost freshScoreGain
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

/-- For a regular neighbour, the library-form gain `freshGainAt` is the
`u`-discount increment `freshIncrementAt`. -/
theorem freshGainAt_eq_freshIncrementAt (I : PinningData V C) (x : ℝ) (X Y : V → C) (v u : V)
    (hagree : ∀ w, w ≠ v → X w = Y w) (hu : regularAt X Y v u) (U Z : V → C) :
    freshGainAt I x X Y v u U Z = freshIncrementAt I x X Y v u U Z := by
  rw [freshIncrementAt_eq I x X Y v u hagree hu U Z]
  unfold freshGainAt
  have hsub : freeBlockers I X Y v u ⊆ eligibleFreshVertices X Y v := by
    intro s hs
    obtain ⟨-, hsv, hst⟩ := freeBlockers_data hagree hs
    simp only [eligibleFreshVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hsv, hst⟩
  rw [← Finset.sum_subset hsub ?_]
  · apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro c _
    have hadj := (freeBlockers_data hagree hs).1
    have hu' : X u = Y u ∧ X u ≠ X v ∧ X u ≠ Y v := hu
    by_cases hE : U = Function.update X s c ∧ Z = Function.update Y s c
    · rw [if_pos hE, if_pos hE, if_pos ⟨hu', hadj⟩]
    · rw [if_neg hE, if_neg hE]
  · intro s hs hnot
    apply Finset.sum_eq_zero
    intro c _
    have hadj : ¬ I.graph.Adj u s := by
      intro hadj
      apply hnot
      obtain ⟨hsv, hst⟩ := (Finset.mem_filter.mp hs).2
      simp only [freeBlockers, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      exact ⟨hadj, hsv, by tauto⟩
    by_cases hE : U = Function.update X s c ∧ Z = Function.update Y s c
    · rw [if_pos hE, if_neg (fun hh => hadj hh.2)]
    · rw [if_neg hE]

end

end ZeroFreeness.Appendix.CV
