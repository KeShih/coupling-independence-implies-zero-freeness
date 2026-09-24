import CI2ZF.Coupling.CV.SoftEndgame
import CI2ZF.Coupling.CV.GeometricDrift

/-!
# The closed-interval CV kernel (companion appendix `cv-1809.tex`)

Formalizes `def:cv-metric` (Definition 5.3, the side remark on the hard
metric), `thm:cv-contraction` (Theorem 5.25) and `lem:cv-child-middle`
(Lemma 5.26).

1. `def:cv-metric`: the hard CV edge length and hard CV metric, the identity
   `edgeLength I 0 = hardEdgeLength I` (0^0 = 1), the survival-probability limits,
   and the limit `d_x → d_hard` as `x ↓ 0`.
2. `thm:cv-contraction`: the closed-interval CV kernel `cvKernel` on `x ∈ (0,1]`
   (the paper's coin mixture, equal to `softCVKernel` on `(0,1)`), an explicit
   coupling of its rows with additive drift `≤ -δ_CV Δ / (nq)`, and the W form.
3. `lem:cv-child-middle`: the Hamming and child-metric row bounds on `x ∈ (0,1]`.
-/

namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.FinDist CI2ZF.Appendix.CV CI2ZF.Potts Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

/-! ## Item 1: the hard CV metric and the limit `x ↓ 0` -/

section MetricLimit
local instance (priority := 2000) closedKernelDecEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- The CV coefficient `(P₂ - P₃)/2` equals `17/200`. -/
theorem cv_coefficient : (mass 2 - mass 3) / 2 = 17 / 200 := by
  norm_num [mass]

/-- The survival probability `θ x^k` with `θ = 1 - x` tends to `1` when
there is no blocker or target deletion (`k = 0`) and to `0` otherwise. -/
theorem survival_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => (1 - x) * x ^ k) (𝓝[>] 0) (𝓝 (if k = 0 then 1 else 0)) := by
  have hc : Continuous (fun x : ℝ => (1 - x) * x ^ k) := by fun_prop
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using h
  · simpa [hk.ne', zero_pow hk.ne'] using h

/-- `blockerCount = 0` means: no free neighbour of `w` other than `v` carries
a target colour in either endpoint, and no pinned neighbour of `w` carries a
target colour (no target deletion). -/
theorem blockerCount_eq_zero_iff (I : PinningData V C) (X Y : V → C) (v w : V) :
    blockerCount I X Y v w = 0 ↔
      (∀ s ∈ I.graph.neighborFinset w, s ≠ v →
          ¬ (X s = X v ∨ X s = Y v ∨ Y s = X v ∨ Y s = Y v)) ∧
        ∀ c, (c = X v ∨ c = Y v) → I.boundaryCount w c = 0 := by
  unfold blockerCount
  rw [Nat.add_eq_zero_iff, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.sum_eq_zero_iff]
  apply and_congr
  · constructor
    · intro h s hs hsv hb
      exact h hs ⟨hsv, hb⟩
    · intro h s hs hb
      exact h s hs hb.1 hb.2
  · constructor
    · intro h c hc
      exact h c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    · intro h c hc
      exact h c (Finset.mem_filter.mp hc).2

/-- Hard survival count at an output disagreement `v`: the regular neighbours
`w` (common colour outside `{X v, Y v}`) with no blocker and no target deletion. -/
def hardVertexScore (I : PinningData V C) (X Y : V → C) (v : V) : ℕ :=
  ((I.graph.neighborFinset v).filter fun w =>
    (X w = Y w ∧ X w ≠ X v ∧ X w ≠ Y v) ∧ blockerCount I X Y v w = 0).card

/-- Hard output score. -/
def hardOutputScore (I : PinningData V C) (X Y : V → C) : ℝ :=
  ∑ v, if X v ≠ Y v then (hardVertexScore I X Y v : ℝ) else 0

/-- The hard Carlson–Vigoda edge length: `1 - (P₂-P₃)/(2q)` times the number of
unblocked regular neighbours. -/
def hardEdgeLength (I : PinningData V C) (X Y : V → C) : ℝ :=
  1 - (17 / (200 * Fintype.card C)) * hardOutputScore I X Y

/-- The hard Carlson–Vigoda metric: the shortest-path metric of the hard lengths. -/
def hardMetric (I : PinningData V C) : (V → C) → (V → C) → ℝ :=
  pathMetric (hardEdgeLength I)

theorem vertexScore_zero (I : PinningData V C) (X Y : V → C) (v : V) :
    vertexScore I 0 X Y v = hardVertexScore I X Y v := by
  unfold vertexScore hardVertexScore
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hr : X w = Y w ∧ X w ≠ X v ∧ X w ≠ Y v
  · rcases Nat.eq_zero_or_pos (blockerCount I X Y v w) with hb | hb
    · simp [hr, hb]
    · simp [hr, hb.ne', zero_pow hb.ne']
  · simp [hr]

/-- By `0^0 = 1`, the geometric edge length at `x = 0` is exactly the hard
CV edge length. -/
theorem edgeLength_zero (I : PinningData V C) (X Y : V → C) :
    edgeLength I 0 X Y = hardEdgeLength I X Y := by
  unfold edgeLength hardEdgeLength outputScore hardOutputScore
  congr 2
  apply Finset.sum_congr rfl
  intro v _
  rw [vertexScore_zero]

theorem geometricMetric_zero (I : PinningData V C) : geometricMetric I 0 = hardMetric I := by
  unfold geometricMetric hardMetric
  congr 1
  funext X Y
  exact edgeLength_zero I X Y

theorem edgeLength_continuous (I : PinningData V C) (X Y : V → C) :
    Continuous fun x => edgeLength I x X Y := by
  unfold edgeLength outputScore vertexScore
  apply continuous_const.sub
  apply continuous_const.mul
  apply continuous_finsetSum
  intro v _
  apply continuous_if_const
  · intro _
    apply continuous_finsetSum
    intro w _
    apply continuous_if_const
    · intro _; fun_prop
    · intro _; exact continuous_const
  · intro _; exact continuous_const

/-- Each geometric edge length tends to the hard CV edge length as `x ↓ 0`. -/
theorem edgeLength_tendsto (I : PinningData V C) (X Y : V → C) :
    Tendsto (fun x => edgeLength I x X Y) (𝓝[>] 0) (𝓝 (hardEdgeLength I X Y)) := by
  rw [← edgeLength_zero]
  exact ((edgeLength_continuous I X Y).tendsto 0).mono_left nhdsWithin_le_nhds

/-- Edge-length bounds only from the degree bound and `17Δ ≤ 200q`. -/
theorem edgeLength_bounds_general (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq0 : (0 : ℝ) < Fintype.card C) (X Y : V → C) (hxy : hamCard X Y = 1) :
    1 - 17 * Δ / (200 * Fintype.card C) ≤ edgeLength I x X Y ∧ edgeLength I x X Y ≤ 1 := by
  obtain ⟨v, hv, hother⟩ := CI2ZF.exists_unique_disagreement hxy
  have hS0 := outputScore_nonneg I hx X Y
  have hS1 : outputScore I x X Y ≤ Δ := by
    rw [outputScore_adjacent I x hv hother]
    exact (vertexScore_le_degree I hx X Y v).trans (by exact_mod_cast hdegree v)
  have hw0 : (0 : ℝ) ≤ 17 / (200 * Fintype.card C) := by positivity
  have hS := mul_le_mul_of_nonneg_left hS1 hw0
  have hN := mul_nonneg hw0 hS0
  have he : 17 * (Δ : ℝ) / (200 * Fintype.card C) = 17 / (200 * Fintype.card C) * Δ := by
    ring
  unfold edgeLength
  rw [he]
  constructor <;> linarith

/-- If `ell' ≤ c * ell` on adjacent pairs then the path metrics compare the same way. -/
theorem pathMetric_le_mul (ell ell' : (V → C) → (V → C) → ℝ) {m' c : ℝ}
    (hm' : 0 ≤ m') (hc : 0 < c)
    (hlow' : ∀ X Y, hamCard X Y = 1 → m' ≤ ell' X Y)
    (hscale : ∀ X Y, hamCard X Y = 1 → ell' X Y ≤ c * ell X Y) (X Y : V → C) :
    pathMetric ell' X Y ≤ c * pathMetric ell X Y := by
  have hroute {X Y : V → C} (p : Route X Y) : p.cost ell' ≤ c * p.cost ell := by
    induction p with
    | nil => simp [Route.cost]
    | @cons X Z Y h p ih =>
      have := hscale X Z h
      simp only [Route.cost]
      nlinarith
  rw [mul_comm c]
  apply (div_le_iff₀ hc).mp
  apply le_csInf (routeCost_nonempty ell X Y)
  rintro _ ⟨p, rfl⟩
  apply (div_le_iff₀ hc).mpr
  rw [mul_comm]
  exact (pathMetric_le_cost ell' hm' hlow' p).trans (hroute p)

/-- The hard CV metric is the limit of the geometric soft metrics as `x ↓ 0`,
whenever the edge lengths are uniformly positive (`17Δ < 200q`, e.g. `q ≥ 1.809Δ`). -/
theorem geometricMetric_tendsto_hardMetric (I : PinningData V C) {Δ : ℕ}
    (hdegree : ∀ v, I.graph.degree v ≤ Δ) (hpos : (17 : ℝ) * Δ < 200 * Fintype.card C)
    (X Y : V → C) :
    Tendsto (fun x => geometricMetric I x X Y) (𝓝[>] 0) (𝓝 (hardMetric I X Y)) := by
  have hq0 : (0 : ℝ) < Fintype.card C := by
    have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    linarith
  set m : ℝ := 1 - 17 * Δ / (200 * Fintype.card C) with hmdef
  have hm : 0 < m := by
    rw [hmdef, sub_pos, div_lt_one (by positivity)]
    exact hpos
  have hb (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) := edgeLength_bounds_general I hx hdegree hq0
  have hb0 := hb 0 ⟨le_rfl, zero_le_one⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set N : ℝ := (Fintype.card V : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  set η : ℝ := ε / (N + 1) with hηdef
  have hη : 0 < η := by positivity
  have hηN : η * N < ε := by
    rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  -- Eventually the soft and hard lengths are within the factor `1 + η` on every pair.
  have hpair : ∀ p : (V → C) × (V → C), ∀ᶠ x in 𝓝[>] (0 : ℝ), hamCard p.1 p.2 = 1 →
      edgeLength I x p.1 p.2 ≤ (1 + η) * hardEdgeLength I p.1 p.2 ∧
        hardEdgeLength I p.1 p.2 ≤ (1 + η) * edgeLength I x p.1 p.2 := by
    rintro ⟨X', Y'⟩
    by_cases hadj : hamCard X' Y' = 1
    · have h0 := (hb0 X' Y' hadj).1
      rw [edgeLength_zero] at h0
      have hlim := edgeLength_tendsto I X' Y'
      have h1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), edgeLength I x X' Y' < (1 + η) * hardEdgeLength I X' Y' :=
        hlim.eventually (gt_mem_nhds (by nlinarith))
      have hlim' : Tendsto (fun x => (1 + η) * edgeLength I x X' Y') (𝓝[>] 0)
          (𝓝 ((1 + η) * hardEdgeLength I X' Y')) := hlim.const_mul _
      have h2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), hardEdgeLength I X' Y' < (1 + η) * edgeLength I x X' Y' :=
        hlim'.eventually (lt_mem_nhds (by nlinarith))
      filter_upwards [h1, h2] with x hx1 hx2
      intro _
      exact ⟨hx1.le, hx2.le⟩
    · exact Eventually.of_forall fun _ h => absurd h hadj
  have hall := Filter.eventually_all.2 hpair
  have hlt1 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
  have hgt0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  filter_upwards [hall, hlt1, hgt0] with x hxall hx1 hx0
  have hx : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0.le, hx1.le⟩
  have hlowx := fun X Y h => (hb x hx X Y h).1
  have hlow0 : ∀ X Y, hamCard X Y = 1 → m ≤ hardEdgeLength I X Y := by
    intro X Y h
    rw [← edgeLength_zero]
    exact (hb0 X Y h).1
  have hup0 : ∀ X Y, hamCard X Y = 1 → hardEdgeLength I X Y ≤ 1 := by
    intro X Y h
    rw [← edgeLength_zero]
    exact (hb0 X Y h).2
  have hA : geometricMetric I x X Y ≤ (1 + η) * hardMetric I X Y :=
    pathMetric_le_mul _ _ hm.le (by linarith) hlowx
      (fun X Y h => (hxall (X, Y) h).1) X Y
  have hB : hardMetric I X Y ≤ (1 + η) * geometricMetric I x X Y :=
    pathMetric_le_mul _ _ hm.le (by linarith) hlow0
      (fun X Y h => (hxall (X, Y) h).2) X Y
  have hcx := pathMetric_comparison (edgeLength I x) hm.le hlowx
    (fun X Y h => (hb x hx X Y h).2) X Y
  have hc0 := pathMetric_comparison (hardEdgeLength I) hm.le hlow0 hup0 X Y
  have hham := ham_le_card X Y
  have hx0' : 0 ≤ geometricMetric I x X Y :=
    (mul_nonneg hm.le (ham_nonneg X Y)).trans hcx.1
  have h00 : 0 ≤ hardMetric I X Y := (mul_nonneg hm.le (ham_nonneg X Y)).trans hc0.1
  have hcx2 : geometricMetric I x X Y ≤ ham X Y := hcx.2
  have hc02 : hardMetric I X Y ≤ ham X Y := hc0.2
  rw [Real.dist_eq, abs_lt]
  constructor <;> nlinarith

/-- The same limit under the CV hypothesis `q ≥ 1.809Δ` of `lem:cv-metric`. -/
theorem geometricMetric_tendsto_hardMetric_cv [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hdegree : ∀ v, I.graph.degree v ≤ Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (X Y : V → C) :
    Tendsto (fun x => geometricMetric I x X Y) (𝓝[>] 0) (𝓝 (hardMetric I X Y)) := by
  apply geometricMetric_tendsto_hardMetric I hdegree _ X Y
  have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
  nlinarith

/-- At `x = 1` every geometric edge length is `1`, so the metric is Hamming. -/
theorem edgeLength_one (I : PinningData V C) (X Y : V → C) : edgeLength I 1 X Y = 1 := by
  simp [edgeLength, outputScore, vertexScore]

theorem geometricMetric_one (I : PinningData V C) (X Y : V → C) :
    geometricMetric I 1 X Y = ham X Y := by
  have h := pathMetric_comparison (edgeLength I 1) zero_le_one
    (fun X Y _ => (edgeLength_one I X Y).ge) (fun X Y _ => (edgeLength_one I X Y).le) X Y
  have h1 : ham X Y ≤ geometricMetric I 1 X Y := by
    have := h.1
    rw [one_mul] at this
    exact this
  exact le_antisymm h.2 h1

/-- Under `17Δ ≤ 200q` the geometric metric is a nonnegative cost below Hamming. -/
theorem geometricMetric_nonneg_le_ham [Nonempty C] (I : PinningData V C) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) {Δ : ℕ} (hdegree : ∀ v, I.graph.degree v ≤ Δ)
    (hq : (17 : ℝ) * Δ ≤ 200 * Fintype.card C) (X Y : V → C) :
    0 ≤ geometricMetric I x X Y ∧ geometricMetric I x X Y ≤ ham X Y := by
  have hq0 : (0 : ℝ) < Fintype.card C := Nat.cast_pos.mpr Fintype.card_pos
  have hm : 0 ≤ 1 - 17 * (Δ : ℝ) / (200 * Fintype.card C) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact hq
  have hlow := fun X Y h => (edgeLength_bounds_general I hx hdegree hq0 X Y h).1
  have hup := fun X Y h => (edgeLength_bounds_general I hx hdegree hq0 X Y h).2
  exact ⟨pathMetric_nonneg _ hm hlow X Y, (pathMetric_comparison _ hm hlow hup X Y).2⟩

end MetricLimit

/-! ## Item 2: the CV kernel on `(0,1]` and the additive kernel-level drift -/

local instance closedKernelConfigDecEq : DecidableEq (V → C) := Classical.decEq _

/-- The soft CV kernel `K_{x,CV}` of `def:cv-kernel` on the closed interval: draw
independent Bernoulli`(1-x)` coins on the labelled constraints, activate the
satisfied ones, and run the hard CV flip step on the resulting list instance.
At `x = 1` no constraint is active. -/
def cvKernel [Nonempty V] [Nonempty C] (I : PinningData V C) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (X : V → C) : FinDist (V → C) :=
  (activityCoins I x hx).bind fun ω =>
    CI2ZF.Appendix.CV.hardStep (PottsCI.Vigoda.activeHardListInstance I (activatedSet I X ω)) X

theorem mem_Icc_of {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hx0.le, hx1⟩

/-- On `(0,1)` the closed kernel is the library kernel `softCVKernel`. -/
theorem cvKernel_eq_softCVKernel [Nonempty V] [Nonempty C] (I : PinningData V C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    cvKernel I x (mem_Icc_of hx0 hx1.le) = softCVKernel I x hx0 hx1 := by
  funext X
  rw [softCVKernel_eq_coin_mixture]
  rfl

/-- At `x = 1` the coins are all `false`, no constraint is active, and the
closed kernel is the hard CV step on the unconstrained instance. -/
theorem cvKernel_one [Nonempty V] [Nonempty C] (I : PinningData V C) (X : V → C) :
    cvKernel I 1 (mem_Icc_of zero_lt_one le_rfl) X =
      CI2ZF.Appendix.CV.hardStep (PottsCI.Vigoda.activeHardListInstance I ∅) X := by
  have hw (ω : I.Constraint → Bool) :
      (activityCoins I 1 (mem_Icc_of zero_lt_one le_rfl)).w ω =
        if ω = (fun _ => false) then 1 else 0 := by
    simp only [activityCoins, commonCoinLaw, productLaw, bernoulliLaw, sub_self, sub_zero]
    by_cases h : ω = fun _ => false
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨k, hk⟩ : ∃ k, ω k = true := by
        by_contra hn
        push Not at hn
        exact h (funext fun k => by simpa using hn k)
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
  have hA : activatedSet I X (fun _ => false) = ∅ := by
    ext k; simp
  apply FinDist.ext
  funext Y
  simp only [cvKernel, FinDist.bind_w, hw, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, hA]

/-- The closed kernel is stationary for the Gibbs law on all of `(0,1]`. -/
theorem cvKernel_stationary [Nonempty V] [Nonempty C] (I : PinningData V C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    FinDist.IsStationary (cvKernel I x (mem_Icc_of hx0 hx1))
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) := by
  rcases lt_or_eq_of_le hx1 with hlt | rfl
  · rw [cvKernel_eq_softCVKernel I x hx0 hlt]
    exact softCVKernel_stationary I x hx0 hlt
  · have hK : cvKernel I 1 (mem_Icc_of hx0 hx1) =
        CI2ZF.Appendix.CV.hardStep (PottsCI.Vigoda.activeHardListInstance I ∅) :=
      funext (cvKernel_one I)
    have hprop (σ : V → C) : (PottsCI.Vigoda.activeHardListInstance I ∅).IsProper σ :=
      (PottsCI.Vigoda.activeHardListInstance_isProper_iff I ∅ σ).2 (by
        intro k hk; simp at hk)
    have hne : ∃ σ : V → C, (PottsCI.Vigoda.activeHardListInstance I ∅).IsProper σ :=
      ⟨fun _ => Classical.choice inferInstance, hprop _⟩
    have hweight (σ : V → C) : I.weight 1 σ = 1 := by
      unfold PinningData.weight
      simp only [one_pow, Finset.prod_const_one, one_mul]
      apply Finset.prod_eq_one
      intro e _
      induction e using Sym2.ind with
      | _ u v => simp [PinningData.edgeFactor_mk]
    have hlaw : I.gibbs 1 hx0.le (I.partition_pos_of_parameter_pos hx0) =
        PottsCI.Vigoda.uniformProperFibre (PottsCI.Vigoda.activeHardListInstance I ∅) hne := by
      apply FinDist.ext
      funext σ
      rw [PottsCI.Vigoda.uniformProperFibre_w, if_pos (hprop σ)]
      simp only [PinningData.gibbs, PinningData.partition, hweight]
      have hfilter : (Finset.univ.filter fun Y : V → C =>
          (PottsCI.Vigoda.activeHardListInstance I ∅).IsProper Y) = Finset.univ :=
        Finset.filter_true_of_mem fun Y _ => hprop Y
      rw [hfilter]
      simp
    rw [hK, hlaw]
    exact CI2ZF.Appendix.CV.hardStep_stationary _ hne

/-- The diagonal mixture of fibrewise couplings. -/
def diagMix {Ω S T : Type*} [Fintype Ω] [Fintype S] [Fintype T] (α : FinDist Ω)
    (K : Ω → FinDist S) (L : Ω → FinDist T) (κ : ∀ ω, Coupling (K ω) (L ω)) :
    Coupling (α.bind K) (α.bind L) where
  w s t := ∑ ω, α.w ω * (κ ω).w s t
  nonneg s t := Finset.sum_nonneg fun ω _ => mul_nonneg (α.nonneg ω) ((κ ω).nonneg s t)
  sum_row s := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (κ _).sum_row]
    rfl
  sum_col t := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (κ _).sum_col]
    rfl

theorem diagMix_cost {Ω S T : Type*} [Fintype Ω] [Fintype S] [Fintype T] (α : FinDist Ω)
    (K : Ω → FinDist S) (L : Ω → FinDist T) (κ : ∀ ω, Coupling (K ω) (L ω))
    (d : S → T → ℝ) :
    (diagMix α K L κ).cost d = CI2ZF.expectReal α fun ω => (κ ω).cost d := by
  unfold Coupling.cost diagMix CI2ZF.expectReal
  simp only [Finset.sum_mul, Finset.mul_sum]
  calc ∑ s, ∑ t, ∑ ω, α.w ω * (κ ω).w s t * d s t
      = ∑ s, ∑ ω, ∑ t, α.w ω * (κ ω).w s t * d s t :=
        Finset.sum_congr rfl fun s _ => Finset.sum_comm
    _ = ∑ ω, ∑ s, ∑ t, α.w ω * (κ ω).w s t * d s t := Finset.sum_comm
    _ = _ := by simp only [mul_assoc]

/-- The explicit coupling of `thm:cv-contraction`: common coins, then the
completed hard CV component coupling on each coin outcome. -/
def cvAdjacentCoupling [Nonempty V] [Nonempty C] (I : PinningData V C) (X Y : V → C) (v : V)
    (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Coupling (cvKernel I x hx X) (cvKernel I x hx Y) :=
  diagMix (activityCoins I x hx) _ _
    (adjacentHardCoupling I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree))

theorem cvAdjacentCoupling_cost [Nonempty V] [Nonempty C] (I : PinningData V C)
    (X Y : V → C) (v : V) (hroot : X v ≠ Y v) (hagree : ∀ u, u ≠ v → X u = Y u) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (d : (V → C) → (V → C) → ℝ) :
    (cvAdjacentCoupling I X Y v hroot hagree x hx).cost d =
      averagedCost I X Y v hroot hagree (optimizedAdjacentChoices I X Y v hroot hagree) x hx d :=
  diagMix_cost _ _ _ _ d

/-- `thm:cv-contraction` in either CV regime: for every `x ∈ (0,1]` and adjacent
`X, Y` there is a coupling of the two kernel rows with
`nq (E d_x(X₁,Y₁) - d_x(X,Y)) ≤ -δ_CV Δ`. -/
theorem cv_contraction_of_regime [Nonempty V] [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hreg : Regime Δ (Fintype.card C)) (hd : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (X Y : V → C) (hXY : hamCard X Y = 1) :
    ∃ γ : Coupling (cvKernel I x (mem_Icc_of hx0 hx1) X) (cvKernel I x (mem_Icc_of hx0 hx1) Y),
      ((Fintype.card V : ℝ) * Fintype.card C) *
          (γ.cost (geometricMetric I x) - geometricMetric I x X Y) ≤ -(gap * Δ) := by
  obtain ⟨v, hv, hagree⟩ := CI2ZF.exists_unique_disagreement hXY
  refine ⟨cvAdjacentCoupling I X Y v hv hagree x (mem_Icc_of hx0 hx1), ?_⟩
  rw [cvAdjacentCoupling_cost]
  have h := averaged_geometric_drift_le I X Y v hv hagree x (mem_Icc_of hx0 hx1) hreg hd
  have hn : 0 < (Fintype.card V : ℝ) * Fintype.card C := by positivity
  have h' : averagedCost I X Y v hv hagree (optimizedAdjacentChoices I X Y v hv hagree) x
      (mem_Icc_of hx0 hx1) (geometricMetric I x) - geometricMetric I x X Y ≤
      -(gap * Δ) / ((Fintype.card V : ℝ) * Fintype.card C) := by
    rw [neg_div]; linarith
  have := mul_le_mul_of_nonneg_left h' hn.le
  rwa [mul_div_cancel₀ _ hn.ne'] at this

/-- `thm:cv-contraction` exactly as stated: `Δ ≥ 125`, `q ≥ 1.809Δ`, `x ∈ (0,1]`. -/
theorem cv_contraction [Nonempty V] [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hΔ : 125 ≤ Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (hd : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (X Y : V → C) (hXY : hamCard X Y = 1) :
    ∃ γ : Coupling (cvKernel I x (mem_Icc_of hx0 hx1) X) (cvKernel I x (mem_Icc_of hx0 hx1) Y),
      ((Fintype.card V : ℝ) * Fintype.card C) *
          (γ.cost (geometricMetric I x) - geometricMetric I x X Y) ≤ -(gap * Δ) :=
  cv_contraction_of_regime I (Or.inl ⟨hΔ, hq⟩) hd x hx0 hx1 X Y hXY

/-- The Wasserstein form: `W_{d_x}(K(X),K(Y)) ≤ d_x(X,Y) - δ_CV Δ/(nq)` on `(0,1]`. -/
theorem cv_W_drift_of_regime [Nonempty V] [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hreg : Regime Δ (Fintype.card C)) (hd : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (X Y : V → C) (hXY : hamCard X Y = 1) :
    W (geometricMetric I x) (cvKernel I x (mem_Icc_of hx0 hx1) X) (cvKernel I x (mem_Icc_of hx0 hx1) Y) ≤
      geometricMetric I x X Y - gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C) := by
  obtain ⟨v, hv, hagree⟩ := CI2ZF.exists_unique_disagreement hXY
  have hfree (u : V) : I.graph.degree u ≤ Δ := (Nat.le_add_right _ _).trans (hd u)
  have hnonneg := geometricMetric_nonneg I (mem_Icc_of hx0 hx1) hreg.degree_pos hfree hreg.colours
  apply (W_le_cost hnonneg (cvAdjacentCoupling I X Y v hv hagree x (mem_Icc_of hx0 hx1))).trans
  rw [cvAdjacentCoupling_cost]
  exact averaged_geometric_drift_le I X Y v hv hagree x (mem_Icc_of hx0 hx1) hreg hd

theorem cv_W_drift [Nonempty V] [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hΔ : 125 ≤ Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C) (hd : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (X Y : V → C) (hXY : hamCard X Y = 1) :
    W (geometricMetric I x) (cvKernel I x (mem_Icc_of hx0 hx1) X) (cvKernel I x (mem_Icc_of hx0 hx1) Y) ≤
      geometricMetric I x X Y - gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C) :=
  cv_W_drift_of_regime I (Or.inl ⟨hΔ, hq⟩) hd x hx0 hx1 X Y hXY

/-- The additive W form for the library kernel `softCVKernel` on `(0,1)`. -/
theorem softCVKernel_W_drift [Nonempty V] [Nonempty C] (I : PinningData V C) {Δ : ℕ}
    (hreg : Regime Δ (Fintype.card C)) (hd : I.DegreeBound Δ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (X Y : V → C) (hXY : hamCard X Y = 1) :
    W (geometricMetric I x) (softCVKernel I x hx0 hx1 X) (softCVKernel I x hx0 hx1 Y) ≤
      geometricMetric I x X Y - gap * Δ / ((Fintype.card V : ℝ) * Fintype.card C) := by
  rw [← cvKernel_eq_softCVKernel]
  exact cv_W_drift_of_regime I hreg hd x hx0 hx1.le X Y hXY

/-! ## Item 3: child–middle row discrepancy on `(0,1]` -/

/-- One added boundary occurrence changes each closed-interval CV row by at most
`(1-x)/(nq)` in Hamming transport. -/
theorem cvKernel_addBoundary_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (r : V) (a : C) (X : V → C)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    W ham (cvKernel I x hx X) (cvKernel (addBoundary I r a) x hx X) ≤
        (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
  let ht : 1 - x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  let p := commonCoinLaw (K := (addBoundary I r a).Constraint) (1 - x) ht
  let restrict := fun (ω : (addBoundary I r a).Constraint → Bool) (k : I.Constraint) =>
    ω (boundaryConstraintEmbedding I r a k)
  have hold : (commonCoinLaw (K := I.Constraint) (1 - x) ht).bind
      (fun ω => CI2ZF.Appendix.CV.hardStep (PottsCI.Vigoda.activeHardListInstance I (activatedSet I X ω)) X) =
      p.bind (fun ω => CI2ZF.Appendix.CV.hardStep
        (PottsCI.Vigoda.activeHardListInstance I (activatedSet I X (restrict ω))) X) := by
    rw [← map_commonCoinLaw_embedding (boundaryConstraintEmbedding I r a) (1 - x) ht]
    exact mapLaw_bind _ _ _
  change W ham ((commonCoinLaw (K := I.Constraint) (1 - x) ht).bind
      (fun ω => CI2ZF.Appendix.CV.hardStep (PottsCI.Vigoda.activeHardListInstance I (activatedSet I X ω)) X))
    (p.bind fun ω => CI2ZF.Appendix.CV.hardStep
      (PottsCI.Vigoda.activeHardListInstance (addBoundary I r a)
        (activatedSet (addBoundary I r a) X ω)) X) ≤ _
  rw [hold]
  apply (W_bind_diag ham_nonneg p _ _).trans
  calc
    _ ≤ ∑ ω, p.w ω * (if ω (freshBoundaryConstraint I r a) = true then
          1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (CI2ZF.Appendix.CV.activated_hardStep_addBoundary_W_le I r a X ω) (p.nonneg ω)
    _ = (1 - x) / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) := by
      have h := expectReal_product_coordinate
        (fun _ : (addBoundary I r a).Constraint => bernoulliLaw (1 - x) ht)
        (freshBoundaryConstraint I r a)
        (fun b : Bool => if b = true then
          1 / ((Fintype.card V : ℝ) * (Fintype.card C : ℝ)) else 0)
      simpa [p, commonCoinLaw, CI2ZF.expectReal, bernoulliLaw, div_eq_mul_inv] using h

theorem cvKernel_addBoundarySet_W_le [Nonempty V] [Nonempty C]
    (I : PinningData V C) (S : Finset V) (a : C) (X : V → C)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    W ham (cvKernel (addBoundarySet I S a) x hx X) (cvKernel I x hx X) ≤
        (1 - x) * S.card / ((Fintype.card V : ℝ) * Fintype.card C) := by
  induction S using Finset.induction_on with
  | empty => simp [W_self ham_nonneg ham_self]
  | @insert u S hu ih =>
    rw [addBoundarySet_insert I S u a hu]
    calc
      _ ≤ W ham
          (cvKernel (addBoundary (addBoundarySet I S a) u a) x hx X)
          (cvKernel (addBoundarySet I S a) x hx X) +
          W ham (cvKernel (addBoundarySet I S a) x hx X) (cvKernel I x hx X) :=
        W_triangle ham_nonneg ham_nonneg ham_nonneg ham_triangle _ _ _
      _ ≤ (1 - x) / ((Fintype.card V : ℝ) * Fintype.card C) +
          (1 - x) * S.card / ((Fintype.card V : ℝ) * Fintype.card C) := by
        apply add_le_add _ ih
        rw [W_ham_comm]
        exact cvKernel_addBoundary_W_le (addBoundarySet I S a) u a X x hx
      _ = _ := by rw [Finset.card_insert_of_notMem hu, Nat.cast_add, Nat.cast_one]; ring

section RootChild
/-- Match the decidability instance baked into `cvKernel` on subtypes. -/
local instance (priority := 2000) closedKernelPropDecEq (α : Type*) : DecidableEq α :=
  fun a b => Classical.propDecidable (a = b)

/-- `lem:cv-child-middle`, Hamming part, on `x ∈ (0,1]`. -/
theorem cv_child_middle_ham [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (c : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (σ : RootRemaining tau r → C) :
    W ham (cvKernel (rootChildData tau G r c) x (mem_Icc_of hx0 hx1) σ)
        (cvKernel (rootMiddleData tau G r) x (mem_Icc_of hx0 hx1) σ) ≤
      (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) ∧
    (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) ≤
      Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  constructor
  · rw [rootChildData_eq_addBoundarySet]
    apply (cvKernel_addBoundarySet_W_le _ _ _ _ x (mem_Icc_of hx0 hx1)).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact_mod_cast rootBoundaryVertices_card_le tau G r hdegree
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    nlinarith

/-- `lem:cv-child-middle`, child-metric part: under `q ≥ 1.809Δ` the same bound
holds for `W_{d_x^{G,τ^{r=c}}}`, on `x ∈ (0,1]`. -/
theorem cv_child_middle_metric [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (c : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (hq : (1809 / 1000 : ℝ) * Δ ≤ Fintype.card C)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1) (σ : RootRemaining tau r → C) :
    W (geometricMetric (rootChildData tau G r c) x)
        (cvKernel (rootChildData tau G r c) x (mem_Icc_of hx0 hx1) σ)
        (cvKernel (rootMiddleData tau G r) x (mem_Icc_of hx0 hx1) σ) ≤
      (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) ∧
    (1 - x) * Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) ≤
      Δ / ((Fintype.card (RootRemaining tau r) : ℝ) * Fintype.card C) := by
  obtain ⟨hH, hle⟩ := cv_child_middle_ham tau G r c hdegree x hx0 hx1 σ
  refine ⟨?_, hle⟩
  have hchild := rootChildData_degreeBound tau G r c hdegree
  have hfree (u : RootRemaining tau r) : (rootChildData tau G r c).graph.degree u ≤ Δ :=
    (Nat.le_add_right _ _).trans (hchild u)
  have hq' : (17 : ℝ) * Δ ≤ 200 * Fintype.card C := by
    have : (0 : ℝ) ≤ Δ := Nat.cast_nonneg _
    nlinarith
  have hb := geometricMetric_nonneg_le_ham (rootChildData tau G r c) (mem_Icc_of hx0 hx1) hfree hq'
  refine le_trans ?_ hH
  apply le_W
  intro γ
  exact (W_le_cost (fun X Y => (hb X Y).1) γ).trans (cost_le_cost γ (fun X Y => (hb X Y).2))

/-- At the endpoint `x = 1` the child–middle Hamming discrepancy vanishes. -/
theorem cv_child_middle_ham_one [Nonempty C]
    (tau : PartialColouring V C) (G : SimpleGraph V) (r : tau.FreeVertex)
    [Nonempty (RootRemaining tau r)] (c : C) {Δ : ℕ}
    (hdegree : ∀ v, G.degree v ≤ Δ) (σ : RootRemaining tau r → C) :
    W ham (cvKernel (rootChildData tau G r c) 1 ⟨zero_le_one, le_rfl⟩ σ)
        (cvKernel (rootMiddleData tau G r) 1 ⟨zero_le_one, le_rfl⟩ σ) = 0 := by
  have h := (cv_child_middle_ham tau G r c hdegree 1 zero_lt_one le_rfl σ).1
  rw [sub_self, zero_mul, zero_div] at h
  exact le_antisymm h (W_nonneg ham_nonneg)

end RootChild

end
end CI2ZF.Appendix.CV
