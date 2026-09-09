import CI2ZF.Appendix.CV.GlobalEnvelope
import CI2ZF.Appendix.CV.DiscountFreshAccount

/-! The actual N₁₁/N₁₂ counts are tied to physical activation events.
This file converts the deterministic metric resources into the corrected
colour charges used in the global envelope. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda PottsCI.FinDist RootComponentGeometry
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
variable {V C : Type*} [Fintype V] [Fintype C]

lemma activeRootIncidence_sum (I : PinningData V C) (X : V → C) (v : V)
    (c : C) (hc : c ≠ X v) (ω : I.Constraint → Bool) (f : V → ℝ) :
    (∑ i : RootIncidence (activeHardListInstance I (activatedSet I X ω)) X v c, f i.val) =
      ∑ u : I.graph.neighborSet v,
        if X u.val = c ∧ ω (rootFreeConstraint I v u) = true then f u.val else 0 := by
  let F := activeHardListInstance I (activatedSet I X ω)
  let e : RootIncidence F X v c ≃
      {u : I.graph.neighborSet v // X u.val = c ∧ ω (rootFreeConstraint I v u) = true} :=
    { toFun := fun u => ⟨⟨u.val, activeGraph_le_original I _ (mem_rootNeighbours.mp u.property).1⟩,
        (activeRootIncidence_iff_coin I X v c hc ω _).mp u.property⟩
      invFun := fun u => ⟨u.val.val, (activeRootIncidence_iff_coin I X v c hc ω u.val).mpr u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  calc
    _ = ∑ u : {u : I.graph.neighborSet v // X u.val = c ∧ ω (rootFreeConstraint I v u) = true},
        f u.val.val := Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [← Finset.sum_subtype (Finset.univ.filter (fun u : I.graph.neighborSet v =>
        X u.val = c ∧ ω (rootFreeConstraint I v u) = true)) (by simp) (fun u => f u.val)]
      rw [Finset.sum_filter]

lemma active_regular_incidence_partition (I : PinningData V C) (X Y : V → C) (v : V)
    (hagree : ∀ u, u ≠ v → X u = Y u) (ω : I.Constraint → Bool) (f : C → V → ℝ) :
    (∑ c, if c ≠ X v ∧ c ≠ Y v then
      ∑ i : RootIncidence (activeHardListInstance I (activatedSet I X ω)) X v c, f c i.val else 0) =
      ∑ u : I.graph.neighborSet v,
        if regularAt X Y v u.val ∧ ω (rootFreeConstraint I v u) = true then f (X u.val) u.val else 0 := by
  have he (c : C) :
      (if c ≠ X v ∧ c ≠ Y v then
        ∑ i : RootIncidence (activeHardListInstance I (activatedSet I X ω)) X v c, f c i.val else 0) =
        ∑ u : I.graph.neighborSet v,
          if c ≠ X v ∧ c ≠ Y v ∧ X u.val = c ∧ ω (rootFreeConstraint I v u) = true then f c u.val else 0 := by
    by_cases hc : c ≠ X v ∧ c ≠ Y v
    · rw [if_pos hc, activeRootIncidence_sum I X v c hc.1 ω]
      apply Finset.sum_congr rfl
      intro u _
      have hh : (c ≠ X v ∧ c ≠ Y v ∧ X u.val = c ∧ ω (rootFreeConstraint I v u) = true) ↔
          (X u.val = c ∧ ω (rootFreeConstraint I v u) = true) := by tauto
      exact (if_congr hh rfl rfl).symm
    · rw [if_neg hc]
      symm
      apply Finset.sum_eq_zero
      intro u _
      exact if_neg (fun hh => hc ⟨hh.1, hh.2.1⟩)
  rw [Finset.sum_congr rfl (fun c _ => he c), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single (X u.val)]
  · simp only [regularAt, hagree u.val u.property.ne.symm, true_and]
    simp only [and_assoc]
  · intro c _ hc
    exact if_neg (fun hh => hc hh.2.2.1.symm)
  · simp

def activatedLossAt (I : PinningData V C) (X Y : V → C) (v : V)
    (ω : I.Constraint → Bool) (u : I.graph.neighborSet v) : ℝ :=
  if regularAt X Y v u.val ∧ ω (rootFreeConstraint I v u) = true then
    if X u.val ∈ (activeHardListInstance I (activatedSet I X ω)).list v then
      (componentSafe11 (activeHardListInstance I (activatedSet I X ω))
        (activeHardListInstance I (activatedSet I Y ω)) X Y v u.val (X u.val) : ℝ) else 1
  else 0

def activatedGainAt (I : PinningData V C) (X Y : V → C) (v : V)
    (ω : I.Constraint → Bool) (u : I.graph.neighborSet v) : ℝ :=
  if regularAt X Y v u.val ∧ ω (rootFreeConstraint I v u) = true then
    if X u.val ∈ (activeHardListInstance I (activatedSet I X ω)).list v then
      (componentSafe12 (activeHardListInstance I (activatedSet I X ω))
        (activeHardListInstance I (activatedSet I Y ω)) X Y v u.val (X u.val) : ℝ) else 0
  else 0

lemma sum_colourLossCount_eq (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u) (ω : I.Constraint → Bool) :
    (∑ c, colourLossCount (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) c) =
      ∑ u : I.graph.neighborSet v, activatedLossAt I X Y v ω u := by
  let FX := activeHardListInstance I (activatedSet I X ω)
  let FY := activeHardListInstance I (activatedSet I Y ω)
  have he (c : C) :
      colourLossCount (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) c =
        if c ≠ X v ∧ c ≠ Y v then ∑ i : RootIncidence FX X v c,
          (if c ∈ FX.list v then (componentSafe11 FX FY X Y v i.val c : ℝ) else 1) else 0 := by
    change (if c ≠ X v ∧ c ≠ Y v then if c ∈ FX.list v then
      (safety11Count FX FY X Y v c : ℝ) else ((rootNeighbours FX X v c).card : ℝ) else 0) = _
    by_cases hc : c ≠ X v ∧ c ≠ Y v
    · simp only [if_pos hc]
      by_cases hav : c ∈ FX.list v
      · simp only [hav, if_true, safety11Count, Nat.cast_sum]
      · simp only [hav, if_false, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one, Fintype.card_coe]
    · simp only [if_neg hc]
  rw [Finset.sum_congr rfl (fun c _ => he c)]
  simpa only [activatedLossAt, FX, FY] using active_regular_incidence_partition I X Y v hagree ω
    (fun c u => if c ∈ FX.list v then (componentSafe11 FX FY X Y v u c : ℝ) else 1)

lemma sum_colourGainCount_eq (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u) (ω : I.Constraint → Bool) :
    (∑ c, colourGainCount (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) c) =
      ∑ u : I.graph.neighborSet v, activatedGainAt I X Y v ω u := by
  let FX := activeHardListInstance I (activatedSet I X ω)
  let FY := activeHardListInstance I (activatedSet I Y ω)
  have he (c : C) :
      colourGainCount (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) c =
        if c ≠ X v ∧ c ≠ Y v then ∑ i : RootIncidence FX X v c,
          (if c ∈ FX.list v then (componentSafe12 FX FY X Y v i.val c : ℝ) else 0) else 0 := by
    change (if c ≠ X v ∧ c ≠ Y v ∧ c ∈ FX.list v then
      (safety12Count FX FY X Y v c : ℝ) else 0) = _
    by_cases hc : c ≠ X v ∧ c ≠ Y v
    · rw [if_pos hc]
      by_cases hav : c ∈ FX.list v
      · rw [if_pos ⟨hc.1, hc.2, hav⟩]
        simp only [hav, if_true, safety12Count, Nat.cast_sum]
      · rw [if_neg (fun hh => hav hh.2.2)]
        simp only [hav, if_false, Finset.sum_const_zero]
    · have hn : ¬ (c ≠ X v ∧ c ≠ Y v ∧ c ∈ FX.list v) := by tauto
      simp only [if_neg hc, if_neg hn]
  rw [Finset.sum_congr rfl (fun c _ => he c)]
  simpa only [activatedGainAt, FX, FY] using active_regular_incidence_partition I X Y v hagree ω
    (fun c u => if c ∈ FX.list v then (componentSafe12 FX FY X Y v u c : ℝ) else 0)

lemma safeActivation_componentSafe11 (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hroot : X v ≠ Y v) (hu : regularAt X Y v u.val)
    (hagree : ∀ w, w ≠ v → X w = Y w) (hsafe : safeActivation I X Y v u ω) :
    componentSafe11 (activeHardListInstance I (activatedSet I X ω))
      (activeHardListInstance I (activatedSet I Y ω)) X Y v u.val (X u.val) = 1 := by
  let h := activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree
  obtain ⟨hmem, hx, hy, _, _⟩ := safeActivation_singletons I X Y v u ω hroot hu hagree hsafe
  have hmemY := h.rootNeighbours_eq hu.2.1 hu.2.2 ▸ hmem
  have hsX := h.offRootComponent_eq_opposite_flipSet hu.2.2 hmem
  have hsY := h.symm.offRootComponent_eq_opposite_flipSet hu.2.1 hmemY
  rw [hy] at hsX
  rw [hx] at hsY
  unfold componentSafe11
  rw [if_pos]
  exact ⟨by rw [hsX]; rfl, by rw [hsY]; rfl,
    safeActivation_target_list I X Y v u ω hsafe (X v) (Or.inl rfl) X,
    safeActivation_target_list I X Y v u ω hsafe (Y v) (Or.inr rfl) Y⟩

theorem safeActivation_indicator_le_loss (I : PinningData V C) (X Y : V → C) (v : V)
    (u : I.graph.neighborSet v) (ω : I.Constraint → Bool)
    (hroot : X v ≠ Y v) (hu : regularAt X Y v u.val)
    (hagree : ∀ w, w ≠ v → X w = Y w) :
    (if safeActivation I X Y v u ω then (1 : ℝ) else 0) ≤ activatedLossAt I X Y v ω u := by
  by_cases hs : safeActivation I X Y v u ω
  · rw [if_pos hs, activatedLossAt, if_pos ⟨hu, hs.1⟩]
    rw [safeActivation_componentSafe11 I X Y v u ω hroot hu hagree hs]
    split_ifs <;> norm_num
  · rw [if_neg hs]
    unfold activatedLossAt
    split_ifs <;> positivity

theorem inputScore_le_expected_colourLoss (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ w, w ≠ v → X w = Y w)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    vertexScore I x X Y v ≤ expectReal (activityCoins I x hx)
      (fun ω => ∑ c, colourLossCount
        (activatedSet_rootLocal I X Y ω v (X v) (Y v) rfl rfl hroot hagree) c) := by
  have he (ω : I.Constraint → Bool) := sum_colourLossCount_eq I X Y v hroot hagree ω
  simp_rw [he]
  rw [expectReal_sum]
  have hs : vertexScore I x X Y v =
      ∑ u : I.graph.neighborSet v, if regularAt X Y v u.val then
        (1 - x) * x^(blockerCount I X Y v u.val) else 0 := by
    change (∑ u ∈ I.graph.neighborFinset v, incidenceDiscount I x X Y v u) = _
    rw [Finset.sum_subtype (I.graph.neighborFinset v) (p := fun u => I.graph.Adj v u)
      (by simp) (fun u => incidenceDiscount I x X Y v u)]
    apply Finset.sum_congr rfl
    intro u _
    unfold incidenceDiscount regularAt
    split_ifs <;> rfl
  rw [hs]
  apply Finset.sum_le_sum
  intro u _
  by_cases hu : regularAt X Y v u.val
  · rw [if_pos hu]
    have hp := expectReal_mono (activityCoins I x hx)
      (fun ω => safeActivation_indicator_le_loss I X Y v u ω hroot hu hagree)
    have he := safeActivation_probability I X Y v u x hx
    change expectReal (activityCoins I x hx) _ = _ at he
    rw [he] at hp
    exact hp
  · rw [if_neg hu]
    have hz (ω : I.Constraint → Bool) : activatedLossAt I X Y v ω u = 0 := by
      exact if_neg (fun hh => hu hh.1)
    simp_rw [hz]
    rw [expectReal_const]

end
end CI2ZF.Appendix.CV
