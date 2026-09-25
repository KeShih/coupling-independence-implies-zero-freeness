import ZeroFreeness.Coupling.CV.Metric
import ZeroFreeness.Coupling.Vigoda.HardCouplingInput

/-! The actual geometric CV score and its metric comparison. The blocker count
uses each free edge once and retains every labelled boundary occurrence. -/
namespace ZeroFreeness.Appendix.CV
open PottsCI
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
local instance (priority := 2000) cVGeometryDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
variable {V C : Type*} [Fintype V] [Fintype C]

/-- Union blockers of the two endpoint configurations, excluding the incidence edge. -/
def blockerCount (I : PinningData V C) (X Y : V → C) (v w : V) : ℕ :=
  ((I.graph.neighborFinset w).filter fun s => s ≠ v ∧
    (X s = X v ∨ X s = Y v ∨ Y s = X v ∨ Y s = Y v)).card +
    ∑ c ∈ (Finset.univ.filter fun c => c = X v ∨ c = Y v), I.boundaryCount w c

/-- The summand belonging to one output disagreement. -/
def vertexScore (I : PinningData V C) (x : ℝ) (X Y : V → C) (v : V) : ℝ :=
  ∑ w ∈ I.graph.neighborFinset v,
    if X w = Y w ∧ X w ≠ X v ∧ X w ≠ Y v then
      (1 - x) * x ^ blockerCount I X Y v w else 0

/-- The appendix's output-score double sum. -/
def outputScore (I : PinningData V C) (x : ℝ) (X Y : V → C) : ℝ :=
  ∑ v, if X v ≠ Y v then vertexScore I x X Y v else 0

/-- The direct one-coordinate edge length. Values at nonadjacent pairs are
irrelevant to the shortest-path construction. -/
def edgeLength (I : PinningData V C) (x : ℝ) (X Y : V → C) : ℝ :=
  1 - (17 / (200 * Fintype.card C)) * outputScore I x X Y

def geometricMetric (I : PinningData V C) (x : ℝ) : (V → C) → (V → C) → ℝ :=
  pathMetric (edgeLength I x)

lemma blockerCount_comm (I : PinningData V C) (X Y : V → C) (v w : V) :
    blockerCount I X Y v w = blockerCount I Y X v w := by
  unfold blockerCount
  congr 2
  · ext s; simp only [Finset.mem_filter]; tauto
  · ext c; simp only [Finset.mem_filter]; tauto

lemma vertexScore_comm (I : PinningData V C) (x : ℝ) (X Y : V → C) (v : V) :
    vertexScore I x X Y v = vertexScore I x Y X v := by
  unfold vertexScore
  apply Finset.sum_congr rfl
  intro w _
  rw [blockerCount_comm I X Y]
  by_cases h : X w = Y w
  · simp [h, and_comm]
  · simp [h, Ne.symm h]

lemma outputScore_comm (I : PinningData V C) (x : ℝ) (X Y : V → C) :
    outputScore I x X Y = outputScore I x Y X := by
  unfold outputScore
  apply Finset.sum_congr rfl
  intro v _
  rw [vertexScore_comm I x X Y]
  simp [ne_comm]

lemma edgeLength_comm (I : PinningData V C) (x : ℝ) (X Y : V → C) :
    edgeLength I x X Y = edgeLength I x Y X := by
  unfold edgeLength
  rw [outputScore_comm]

lemma vertexScore_nonneg (I : PinningData V C) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (X Y : V → C) (v : V) : 0 ≤ vertexScore I x X Y v := by
  apply Finset.sum_nonneg
  intro w _
  split
  · exact mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg hx.1 _)
  · rfl

lemma outputScore_nonneg (I : PinningData V C) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (X Y : V → C) : 0 ≤ outputScore I x X Y := by
  apply Finset.sum_nonneg
  intro v _
  split
  · exact vertexScore_nonneg I hx X Y v
  · rfl

lemma vertexScore_le_degree (I : PinningData V C) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (X Y : V → C) (v : V) : vertexScore I x X Y v ≤ I.graph.degree v := by
  calc
    vertexScore I x X Y v ≤ ∑ _w ∈ I.graph.neighborFinset v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro w _
      split
      · have hp : x ^ blockerCount I X Y v w ≤ 1 := pow_le_one₀ hx.1 hx.2
        calc
          (1 - x) * x ^ blockerCount I X Y v w ≤ (1 - x) * 1 :=
            mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr hx.2)
          _ ≤ 1 := by linarith [hx.1]
      · norm_num
    _ = I.graph.degree v := by simp

lemma outputScore_adjacent (I : PinningData V C) (x : ℝ) {X Y : V → C}
    {v : V} (hv : X v ≠ Y v) (hother : ∀ w, w ≠ v → X w = Y w) :
    outputScore I x X Y = vertexScore I x X Y v := by
  unfold outputScore
  rw [Finset.sum_eq_single v]
  · simp [hv]
  · intro w _ hw; simp [hother w hw]
  · simp

lemma edgeLength_bounds (I : PinningData V C) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {Δ : ℕ} (hΔ : 0 < Δ) (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (X Y : V → C) (hxy : hamCard X Y = 1) :
    metricLower ≤ edgeLength I x X Y ∧ edgeLength I x X Y ≤ 1 := by
  obtain ⟨v, hv, hother⟩ := ZeroFreeness.exists_unique_disagreement hxy
  have hq0 : (0 : ℝ) < Fintype.card C := by
    have : (0 : ℝ) < Δ := by exact_mod_cast hΔ
    linarith
  have hS0 := outputScore_nonneg I hx X Y
  have hS1 : outputScore I x X Y ≤ Δ := by
    rw [outputScore_adjacent I x hv hother]
    exact (vertexScore_le_degree I hx X Y v).trans (by exact_mod_cast hdegree v)
  have hw0 : (0 : ℝ) ≤ 17 / (200 * Fintype.card C) := by positivity
  have hsmall : (17 / (200 * (Fintype.card C : ℝ))) * Δ ≤ 85 / 1809 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 200 * (Fintype.card C : ℝ))).mpr
    linarith
  have hS := mul_le_mul_of_nonneg_left hS1 hw0
  have hN := mul_nonneg hw0 hS0
  unfold edgeLength metricLower
  constructor <;> linarith

/-- Lemma cv-metric for the actual graph, lists, and activity-dependent scores. -/
theorem geometricMetric_comparison (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X Y : V → C) :
    metricLower * ham X Y ≤ geometricMetric I x X Y ∧ geometricMetric I x X Y ≤ ham X Y := by
  exact pathMetric_comparison _ (by norm_num [metricLower])
    (fun X Y h => (edgeLength_bounds I hx hΔ hdegree hq X Y h).1)
    (fun X Y h => (edgeLength_bounds I hx hΔ hdegree hq X Y h).2) X Y

theorem geometricMetric_adjacent (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) {X Y : V → C}
    (hxy : hamCard X Y = 1) : geometricMetric I x X Y = edgeLength I x X Y := by
  exact pathMetric_adjacent _ (by norm_num [metricLower]) (by norm_num [metricLower])
    (fun X Y h => (edgeLength_bounds I hx hΔ hdegree hq X Y h).1)
    (fun X Y h => (edgeLength_bounds I hx hΔ hdegree hq X Y h).2) hxy

/-- Every coordinate of an intermediate state is taken from an endpoint. -/
def Between (Z X Y : V → C) : Prop := ∀ s, Z s = X s ∨ Z s = Y s

lemma blockerCount_mono (I : PinningData V C) {X Y A B : V → C} {v w : V}
    (ha : A v = X v) (hb : B v = Y v) (hA : Between A X Y) (hB : Between B X Y) :
    blockerCount I A B v w ≤ blockerCount I X Y v w := by
  unfold blockerCount
  rw [ha, hb]
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsn, hsv, hst⟩ := Finset.mem_filter.mp hs
  apply Finset.mem_filter.mpr
  refine ⟨hsn, hsv, ?_⟩
  rcases hA s with hA | hA <;> rcases hB s with hB | hB <;> simp only [hA, hB] at hst <;> tauto

lemma vertexScore_mono (I : PinningData V C) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {X Y A B : V → C} {v : V}
    (ha : A v = X v) (hb : B v = Y v) (hA : Between A X Y) (hB : Between B X Y) :
    vertexScore I x X Y v ≤ vertexScore I x A B v := by
  unfold vertexScore
  apply Finset.sum_le_sum
  intro w _
  by_cases hcommon : X w = Y w ∧ X w ≠ X v ∧ X w ≠ Y v
  · have haw : A w = X w := (hA w).elim id (fun h => h.trans hcommon.1.symm)
    have hbw : B w = X w := (hB w).elim id (fun h => h.trans hcommon.1.symm)
    rw [if_pos hcommon, if_pos (by simpa [haw, hbw, ha, hb] using hcommon.2)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one hx.1 hx.2 (blockerCount_mono I ha hb hA hB))
      (sub_nonneg.mpr hx.2)
  · rw [if_neg hcommon]
    split
    · exact mul_nonneg (sub_nonneg.mpr hx.2) (pow_nonneg hx.1 _)
    · rfl

/-- The union-blocker score can only increase when an endpoint path is split
at a configuration whose coordinates come from the two endpoints. -/
theorem outputScore_split (I : PinningData V C) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {X Y Z : V → C} (hZ : Between Z X Y) :
    outputScore I x X Y ≤ outputScore I x X Z + outputScore I x Z Y := by
  unfold outputScore
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have hX : Between X X Y := fun _ => Or.inl rfl
  have hY : Between Y X Y := fun _ => Or.inr rfl
  by_cases hxy : X v = Y v
  · have hzv : Z v = X v := (hZ v).elim id (fun h => h.trans hxy.symm)
    simp [hxy, hzv]
  · rcases hZ v with hzv | hzv
    · simp only [if_pos hxy, hzv, ne_eq, not_true_eq_false, if_false, zero_add]
      exact vertexScore_mono I hx hzv rfl hZ hY
    · simp only [if_pos hxy, hzv, ne_eq, not_true_eq_false, if_false, add_zero]
      exact vertexScore_mono I hx rfl hzv hX hZ

lemma exists_intermediate_between {X Y : V → C} {k : ℕ} (h : hamCard X Y = k + 1) :
    ∃ Z : V → C, hamCard X Z = 1 ∧ hamCard Z Y = k ∧ Between Z X Y := by
  have hne : (Finset.univ.filter fun u => X u ≠ Y u).Nonempty := by
    rw [← Finset.card_pos, ← hamCard, h]
    exact Nat.succ_pos k
  obtain ⟨u, hu⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  refine ⟨Function.update X u (Y u), ?_, ?_, ?_⟩
  · have hs : (Finset.univ.filter fun v => X v ≠ Function.update X u (Y u) v) = {u} := by
      ext v
      rcases eq_or_ne v u with rfl | hv
      · simp [hu]
      · simp [hv]
    rw [hamCard, hs, Finset.card_singleton]
  · have hs : (Finset.univ.filter fun v => Function.update X u (Y u) v ≠ Y v) =
        (Finset.univ.filter fun v => X v ≠ Y v).erase u := by
      ext v
      rcases eq_or_ne v u with rfl | hv
      · simp
      · simp [hv]
    rw [hamCard, hs, Finset.card_erase_of_mem (by simpa using hu), ← hamCard, h]
    simp
  · intro v
    by_cases hv : v = u
    · subst v; exact Or.inr (by simp)
    · exact Or.inl (Function.update_of_ne hv _ _)

lemma outputScore_self (I : PinningData V C) (x : ℝ) (X : V → C) : outputScore I x X X = 0 := by
  simp [outputScore]

/-- The coordinate-changing path retains every endpoint-common union-blocker
credit. This is the actual path bound of Lemma cv-path. -/
theorem geometricMetric_path_upper (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hΔ : 0 < Δ)
    (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (X Y : V → C) :
    geometricMetric I x X Y ≤ ham X Y -
      (17 / (200 * Fintype.card C)) * outputScore I x X Y := by
  have hw : (0 : ℝ) ≤ 17 / (200 * Fintype.card C) := by positivity
  have hlow := fun X Y h => (edgeLength_bounds I hx hΔ hdegree hq X Y h).1
  have hex : ∀ k : ℕ, ∀ X Y : V → C, hamCard X Y = k →
      ∃ p : Route X Y, p.cost (edgeLength I x) ≤ (k : ℝ) -
        (17 / (200 * Fintype.card C)) * outputScore I x X Y := by
    intro k
    induction k with
    | zero =>
      intro X Y h
      have he := hamCard_eq_zero h
      subst Y
      exact ⟨.nil X, by simp [Route.cost, outputScore_self]⟩
    | succ k ih =>
      intro X Y h
      obtain ⟨Z, hxz, hzy, hz⟩ := exists_intermediate_between h
      obtain ⟨p, hp⟩ := ih Z Y hzy
      refine ⟨.cons hxz p, ?_⟩
      have hscore := mul_le_mul_of_nonneg_left (outputScore_split I hx hz) hw
      simp only [Route.cost, edgeLength, Nat.cast_add, Nat.cast_one]
      linarith
  obtain ⟨p, hp⟩ := hex _ X Y rfl
  exact (pathMetric_le_cost _ (by norm_num [metricLower]) hlow p).trans hp


end
end ZeroFreeness.Appendix.CV
