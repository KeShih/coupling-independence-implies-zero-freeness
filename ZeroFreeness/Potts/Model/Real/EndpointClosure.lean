import ZeroFreeness.Potts.Model.Real.Endpoint
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Finite endpoint closure (main text and companion, `lem:finite-endpoint-closure`)

`lem:finite-endpoint-closure` (main.tex Lemma 4.3 = companion Lemma 3.7) at
the paper's generality.

The paper's statement: on a finite space `Ω`, let two families of nonnegative
weights be continuous at `x = 0`, with positive total weights there.  Their
normalized laws `μ⁰_x, μ¹_x` converge in total variation to `μ⁰_0, μ¹_0` as
`x ↓ 0`, and for every metric `d` on `Ω`,
`W_d(μ⁰_x, μ¹_x) → W_d(μ⁰_0, μ¹_0)`.  Consequently, if
`W_d(μ⁰_x, μ¹_x) ≤ B(x)` for all small `x > 0`, then
`W_d(μ⁰_0, μ¹_0) ≤ liminf_{x↓0} B(x)`.

Formalization.
* The two families are `u v : ℝ → Ω → ℝ`.  They are only required to be
  nonnegative on a right neighbourhood `[0, ε)` of `0`
  (`∀ᶠ x in 𝓝[≥] 0, ∀ ω, 0 ≤ u x ω`), right-continuous at `0`
  (`Tendsto (u · ω) (𝓝[>] 0) (𝓝 (u 0 ω))`, implied by continuity at `0` on
  any domain containing `[0, ε)`), and to have positive total weight at
  `x = 0` only.  Positivity of the totals for small `x > 0` is *proved*
  (`eventually_admissible`).
* `normLaw w` is the normalized law `w / ∑ w` whenever `w ≥ 0` and `∑ w > 0`
  (`normLaw_w_of_weightAdmissible`); otherwise it is an arbitrary fixed law, a case
  which by `eventually_admissible` never occurs for small `x ≥ 0`.
* Total variation is `tvDistance μ ν = ½ ∑ |μ - ν|`.
* The transport cost `d` is any nonnegative cost vanishing on the diagonal and
  satisfying the triangle inequality; every metric qualifies
  (`finite_endpoint_closure_dist` states it for `dist` of a metric space).
* `liminf_{x↓0} B(x)` is `Filter.liminf B (𝓝[>] 0)` taken in `EReal`, so it
  may be `±∞`; the bound `B` may itself be `EReal`-valued.  Real-valued
  versions: `W_endpoint_le_liminf_real` (with the coboundedness hypothesis
  making the real `liminf` meaningful), `W_endpoint_le_of_tendsto` (`B` with a
  right limit at `0`), `W_endpoint_le_of_const`.

The whole lemma is `finite_endpoint_closure`.  `potts_hard_W_le_liminf`
instantiates it for the pinned Potts laws of `PinningData`, with hard
feasibility entering only through positivity of the two hard partition
functions.
-/

namespace PottsCI

open PottsCI PottsCI.FinDist Filter Topology

noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-! ## Normalized laws -/

/-- A weight vector that can be normalized: nonnegative with positive total. -/
def WeightAdmissible (w : Ω → ℝ) : Prop := (∀ ω, 0 ≤ w ω) ∧ 0 < ∑ ω, w ω

/-- The normalized law `w / ∑ w` of an admissible weight vector (and the
uniform law, as an irrelevant default, otherwise). -/
def normLaw [Nonempty Ω] (w : Ω → ℝ) : FinDist Ω := by
  classical
  exact if h : WeightAdmissible w then normalizeWeights w h.1 h.2 else FinDist.uniform Ω

lemma normLaw_of_weightAdmissible [Nonempty Ω] {w : Ω → ℝ} (h : WeightAdmissible w) :
    normLaw w = normalizeWeights w h.1 h.2 := by
  classical
  unfold normLaw
  rw [dif_pos h]

lemma normLaw_w_of_weightAdmissible [Nonempty Ω] {w : Ω → ℝ} (h : WeightAdmissible w) (ω : Ω) :
    (normLaw w).w ω = w ω / ∑ ω', w ω' := by
  rw [normLaw_of_weightAdmissible h]
  rfl

/-- Total-variation distance `½ ∑ |μ - ν|`. -/
def tvDistance (μ ν : FinDist Ω) : ℝ := l1Distance μ ν / 2

/-! ## Convergence of the normalized laws -/

section Limits

variable (w : ℝ → Ω → ℝ)

/-- Nonnegative, right-continuous weights with positive total at `0` are
admissible at `0` and at every small `x > 0`. -/
theorem eventually_admissible
    (hnn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ w x ω)
    (hcont : ∀ ω, Tendsto (fun x => w x ω) (𝓝[>] 0) (𝓝 (w 0 ω)))
    (hZ : 0 < ∑ ω, w 0 ω) :
    WeightAdmissible (w 0) ∧ ∀ᶠ x in 𝓝[>] (0 : ℝ), WeightAdmissible (w x) := by
  refine ⟨⟨hnn.self_of_nhdsWithin (Set.mem_Ici.2 le_rfl), hZ⟩, ?_⟩
  have hsum : Tendsto (fun x => ∑ ω, w x ω) (𝓝[>] 0) (𝓝 (∑ ω, w 0 ω)) :=
    tendsto_finsetSum _ fun ω _ => hcont ω
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < ∑ ω, w x ω :=
    (tendsto_order.1 hsum).1 0 hZ
  have hnn' : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ ω, 0 ≤ w x ω :=
    nhdsWithin_mono _ Set.Ioi_subset_Ici_self hnn
  filter_upwards [hnn', hpos] with x hx hxZ
  exact ⟨hx, hxZ⟩

/-- Pointwise convergence of the normalized masses. -/
theorem tendsto_normLaw_apply [Nonempty Ω]
    (hnn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ w x ω)
    (hcont : ∀ ω, Tendsto (fun x => w x ω) (𝓝[>] 0) (𝓝 (w 0 ω)))
    (hZ : 0 < ∑ ω, w 0 ω) (ω : Ω) :
    Tendsto (fun x => (normLaw (w x)).w ω) (𝓝[>] 0) (𝓝 ((normLaw (w 0)).w ω)) := by
  obtain ⟨h0, hev⟩ := eventually_admissible w hnn hcont hZ
  have hsum : Tendsto (fun x => ∑ ω, w x ω) (𝓝[>] 0) (𝓝 (∑ ω, w 0 ω)) :=
    tendsto_finsetSum _ fun ω _ => hcont ω
  rw [normLaw_w_of_weightAdmissible h0]
  refine ((hcont ω).div hsum hZ.ne').congr' ?_
  filter_upwards [hev] with x hx
  rw [normLaw_w_of_weightAdmissible hx]
  rfl

/-- Total-variation convergence of the normalized laws. -/
theorem tendsto_normLaw_tv [Nonempty Ω]
    (hnn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ w x ω)
    (hcont : ∀ ω, Tendsto (fun x => w x ω) (𝓝[>] 0) (𝓝 (w 0 ω)))
    (hZ : 0 < ∑ ω, w 0 ω) :
    Tendsto (fun x => tvDistance (normLaw (w x)) (normLaw (w 0))) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_l1Distance_of_pointwise _ _
    (tendsto_normLaw_apply w hnn hcont hZ)).div_const 2
  simpa [tvDistance] using h

end Limits

/-! ## Continuity of the transport cost -/

/-- Every cost on a finite space is bounded by the sum of its values. -/
lemma cost_le_total {d : Ω → Ω → ℝ} (hd : ∀ a b, 0 ≤ d a b) (a b : Ω) :
    d a b ≤ ∑ a', ∑ b', d a' b' := by
  classical
  calc d a b ≤ ∑ b', d a b' :=
        Finset.single_le_sum (fun b' _ => hd a b') (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', d a' b' :=
        Finset.single_le_sum (f := fun a' => ∑ b', d a' b')
          (fun a' _ => Finset.sum_nonneg fun b' _ => hd a' b') (Finset.mem_univ a)

/-- If two families of finite laws converge pointwise, their transport cost
converges, for every nonnegative cost vanishing on the diagonal and satisfying
the triangle inequality. -/
theorem tendsto_W_of_pointwise_pair {α : Type*} {l : Filter α}
    {d : Ω → Ω → ℝ} (hd : ∀ a b, 0 ≤ d a b) (hd0 : ∀ a, d a a = 0)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (μ ν : α → FinDist Ω) (μ₀ ν₀ : FinDist Ω)
    (hμ : ∀ ω, Tendsto (fun a => (μ a).w ω) l (𝓝 (μ₀.w ω)))
    (hν : ∀ ω, Tendsto (fun a => (ν a).w ω) l (𝓝 (ν₀.w ω))) :
    Tendsto (fun a => W d (μ a) (ν a)) l (𝓝 (W d μ₀ ν₀)) := by
  classical
  have hB := cost_le_total hd
  have h1 := tendsto_W_of_pointwise hd hd0 hB μ μ₀ hμ
  have h2 := tendsto_W_left_of_pointwise hd hd0 hB μ μ₀ hμ
  have h3 := tendsto_W_of_pointwise hd hd0 hB ν ν₀ hν
  have h4 := tendsto_W_left_of_pointwise hd hd0 hB ν ν₀ hν
  have hlow : Tendsto (fun a => W d μ₀ ν₀ - (W d μ₀ (μ a) + W d (ν a) ν₀)) l
      (𝓝 (W d μ₀ ν₀)) := by
    simpa using tendsto_const_nhds.sub (h2.add h3)
  have hup : Tendsto (fun a => W d μ₀ ν₀ + (W d (μ a) μ₀ + W d ν₀ (ν a))) l
      (𝓝 (W d μ₀ ν₀)) := by
    simpa using tendsto_const_nhds.add (h1.add h4)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup ?_ ?_
  · intro a
    have t1 := W_triangle hd hd hd htri μ₀ (μ a) ν₀
    have t2 := W_triangle hd hd hd htri (μ a) (ν a) ν₀
    show W d μ₀ ν₀ - (W d μ₀ (μ a) + W d (ν a) ν₀) ≤ W d (μ a) (ν a)
    linarith
  · intro a
    have t1 := W_triangle hd hd hd htri (μ a) μ₀ (ν a)
    have t2 := W_triangle hd hd hd htri μ₀ ν₀ (ν a)
    show W d (μ a) (ν a) ≤ W d μ₀ ν₀ + (W d (μ a) μ₀ + W d ν₀ (ν a))
    linarith

section TwoFamilies

variable [Nonempty Ω] (u v : ℝ → Ω → ℝ)

/-- Two-family transport convergence `W_d(μ⁰_x, μ¹_x) → W_d(μ⁰_0, μ¹_0)`. -/
theorem tendsto_W_normLaw
    (hu_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ u x ω)
    (hv_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ v x ω)
    (hu_cont : ∀ ω, Tendsto (fun x => u x ω) (𝓝[>] 0) (𝓝 (u 0 ω)))
    (hv_cont : ∀ ω, Tendsto (fun x => v x ω) (𝓝[>] 0) (𝓝 (v 0 ω)))
    (hu0 : 0 < ∑ ω, u 0 ω) (hv0 : 0 < ∑ ω, v 0 ω)
    {d : Ω → Ω → ℝ} (hd : ∀ a b, 0 ≤ d a b) (hd0 : ∀ a, d a a = 0)
    (htri : ∀ a b c, d a c ≤ d a b + d b c) :
    Tendsto (fun x => W d (normLaw (u x)) (normLaw (v x))) (𝓝[>] 0)
      (𝓝 (W d (normLaw (u 0)) (normLaw (v 0)))) :=
  tendsto_W_of_pointwise_pair hd hd0 htri _ _ _ _
    (tendsto_normLaw_apply u hu_nn hu_cont hu0)
    (tendsto_normLaw_apply v hv_nn hv_cont hv0)

/-- The closure with a varying bound: if `W_d(μ⁰_x, μ¹_x) ≤ B(x)` for all
small `x > 0`, then `W_d(μ⁰_0, μ¹_0) ≤ liminf_{x↓0} B(x)`, the `liminf` being
taken in `EReal` (so it may be `+∞`); `B` may be `EReal`-valued. -/
theorem W_endpoint_le_liminf
    (hu_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ u x ω)
    (hv_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ v x ω)
    (hu_cont : ∀ ω, Tendsto (fun x => u x ω) (𝓝[>] 0) (𝓝 (u 0 ω)))
    (hv_cont : ∀ ω, Tendsto (fun x => v x ω) (𝓝[>] 0) (𝓝 (v 0 ω)))
    (hu0 : 0 < ∑ ω, u 0 ω) (hv0 : 0 < ∑ ω, v 0 ω)
    {d : Ω → Ω → ℝ} (hd : ∀ a b, 0 ≤ d a b) (hd0 : ∀ a, d a a = 0)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (B : ℝ → EReal)
    (hB : ∀ᶠ x in 𝓝[>] (0 : ℝ), (W d (normLaw (u x)) (normLaw (v x)) : EReal) ≤ B x) :
    (W d (normLaw (u 0)) (normLaw (v 0)) : EReal) ≤ liminf B (𝓝[>] 0) := by
  have hT : Tendsto (fun x => (W d (normLaw (u x)) (normLaw (v x)) : EReal)) (𝓝[>] 0)
      (𝓝 (W d (normLaw (u 0)) (normLaw (v 0)) : EReal)) :=
    EReal.tendsto_coe.2
      (tendsto_W_normLaw u v hu_nn hv_nn hu_cont hv_cont hu0 hv0 hd hd0 htri)
  rw [← hT.liminf_eq]
  exact liminf_le_liminf hB

/-- Real-valued bound, real `liminf`: valid whenever the real `liminf` is
meaningful, i.e. `B` is not eventually above every real number
(`IsCoboundedUnder`). -/
theorem W_endpoint_le_liminf_real
    (hu_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ u x ω)
    (hv_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ v x ω)
    (hu_cont : ∀ ω, Tendsto (fun x => u x ω) (𝓝[>] 0) (𝓝 (u 0 ω)))
    (hv_cont : ∀ ω, Tendsto (fun x => v x ω) (𝓝[>] 0) (𝓝 (v 0 ω)))
    (hu0 : 0 < ∑ ω, u 0 ω) (hv0 : 0 < ∑ ω, v 0 ω)
    {d : Ω → Ω → ℝ} (hd : ∀ a b, 0 ≤ d a b) (hd0 : ∀ a, d a a = 0)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (B : ℝ → ℝ) (hcob : IsCoboundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ)) B)
    (hB : ∀ᶠ x in 𝓝[>] (0 : ℝ), W d (normLaw (u x)) (normLaw (v x)) ≤ B x) :
    W d (normLaw (u 0)) (normLaw (v 0)) ≤ liminf B (𝓝[>] 0) := by
  have hT := tendsto_W_normLaw u v hu_nn hv_nn hu_cont hv_cont hu0 hv0 hd hd0 htri
  rw [← hT.liminf_eq]
  exact liminf_le_liminf hB hT.isBoundedUnder_ge hcob

/-- A bound with a right limit `b` at `0` passes to `x = 0`. -/
theorem W_endpoint_le_of_tendsto
    (hu_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ u x ω)
    (hv_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ v x ω)
    (hu_cont : ∀ ω, Tendsto (fun x => u x ω) (𝓝[>] 0) (𝓝 (u 0 ω)))
    (hv_cont : ∀ ω, Tendsto (fun x => v x ω) (𝓝[>] 0) (𝓝 (v 0 ω)))
    (hu0 : 0 < ∑ ω, u 0 ω) (hv0 : 0 < ∑ ω, v 0 ω)
    {d : Ω → Ω → ℝ} (hd : ∀ a b, 0 ≤ d a b) (hd0 : ∀ a, d a a = 0)
    (htri : ∀ a b c, d a c ≤ d a b + d b c)
    (B : ℝ → ℝ) {b : ℝ} (hBlim : Tendsto B (𝓝[>] 0) (𝓝 b))
    (hB : ∀ᶠ x in 𝓝[>] (0 : ℝ), W d (normLaw (u x)) (normLaw (v x)) ≤ B x) :
    W d (normLaw (u 0)) (normLaw (v 0)) ≤ b :=
  le_of_tendsto_of_tendsto
    (tendsto_W_normLaw u v hu_nn hv_nn hu_cont hv_cont hu0 hv0 hd hd0 htri) hBlim hB

/-- A constant bound holding for all small `x > 0` passes to `x = 0`. -/
theorem W_endpoint_le_of_const
    (hu_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ u x ω)
    (hv_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ v x ω)
    (hu_cont : ∀ ω, Tendsto (fun x => u x ω) (𝓝[>] 0) (𝓝 (u 0 ω)))
    (hv_cont : ∀ ω, Tendsto (fun x => v x ω) (𝓝[>] 0) (𝓝 (v 0 ω)))
    (hu0 : 0 < ∑ ω, u 0 ω) (hv0 : 0 < ∑ ω, v 0 ω)
    {d : Ω → Ω → ℝ} (hd : ∀ a b, 0 ≤ d a b) (hd0 : ∀ a, d a a = 0)
    (htri : ∀ a b c, d a c ≤ d a b + d b c) {K : ℝ}
    (hK : ∀ᶠ x in 𝓝[>] (0 : ℝ), W d (normLaw (u x)) (normLaw (v x)) ≤ K) :
    W d (normLaw (u 0)) (normLaw (v 0)) ≤ K :=
  W_endpoint_le_of_tendsto u v hu_nn hv_nn hu_cont hv_cont hu0 hv0 hd hd0 htri
    (fun _ => K) tendsto_const_nhds hK

/-- **`lem:finite-endpoint-closure` (main.tex Lemma 4.3, companion Lemma 3.7),
all assertions in one statement.**  For two families of weights on a finite
space, nonnegative near `0`, right-continuous at `0`, with positive totals at
`x = 0`:
1. both families are admissible (nonnegative with positive total) at `0` and
   at every small `x > 0`, so their normalized laws are `w_x / ∑ w_x` there;
2. the normalized laws converge in total variation as `x ↓ 0`;
3. for every metric-like cost `d`, `W_d(μ⁰_x, μ¹_x) → W_d(μ⁰_0, μ¹_0)`;
4. for every such `d` and every bound `B` with `W_d(μ⁰_x, μ¹_x) ≤ B(x)` for
   small `x > 0`, `W_d(μ⁰_0, μ¹_0) ≤ liminf_{x↓0} B(x)` (in `EReal`). -/
theorem finite_endpoint_closure
    (hu_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ u x ω)
    (hv_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ v x ω)
    (hu_cont : ∀ ω, Tendsto (fun x => u x ω) (𝓝[>] 0) (𝓝 (u 0 ω)))
    (hv_cont : ∀ ω, Tendsto (fun x => v x ω) (𝓝[>] 0) (𝓝 (v 0 ω)))
    (hu0 : 0 < ∑ ω, u 0 ω) (hv0 : 0 < ∑ ω, v 0 ω) :
    (WeightAdmissible (u 0) ∧ WeightAdmissible (v 0) ∧
      ∀ᶠ x in 𝓝[>] (0 : ℝ), WeightAdmissible (u x) ∧ WeightAdmissible (v x)) ∧
    Tendsto (fun x => tvDistance (normLaw (u x)) (normLaw (u 0))) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun x => tvDistance (normLaw (v x)) (normLaw (v 0))) (𝓝[>] 0) (𝓝 0) ∧
    (∀ d : Ω → Ω → ℝ, (∀ a b, 0 ≤ d a b) → (∀ a, d a a = 0) →
      (∀ a b c, d a c ≤ d a b + d b c) →
      Tendsto (fun x => W d (normLaw (u x)) (normLaw (v x))) (𝓝[>] 0)
        (𝓝 (W d (normLaw (u 0)) (normLaw (v 0))))) ∧
    (∀ d : Ω → Ω → ℝ, (∀ a b, 0 ≤ d a b) → (∀ a, d a a = 0) →
      (∀ a b c, d a c ≤ d a b + d b c) → ∀ B : ℝ → EReal,
      (∀ᶠ x in 𝓝[>] (0 : ℝ), (W d (normLaw (u x)) (normLaw (v x)) : EReal) ≤ B x) →
      (W d (normLaw (u 0)) (normLaw (v 0)) : EReal) ≤ liminf B (𝓝[>] 0)) := by
  obtain ⟨hu0a, hua⟩ := eventually_admissible u hu_nn hu_cont hu0
  obtain ⟨hv0a, hva⟩ := eventually_admissible v hv_nn hv_cont hv0
  refine ⟨⟨hu0a, hv0a, hua.and hva⟩, tendsto_normLaw_tv u hu_nn hu_cont hu0,
    tendsto_normLaw_tv v hv_nn hv_cont hv0, ?_, ?_⟩
  · intro d hd hd0 htri
    exact tendsto_W_normLaw u v hu_nn hv_nn hu_cont hv_cont hu0 hv0 hd hd0 htri
  · intro d hd hd0 htri B hB
    exact W_endpoint_le_liminf u v hu_nn hv_nn hu_cont hv_cont hu0 hv0 hd hd0 htri B hB

/-- The metric-space form: `d = dist` for any metric on `Ω`. -/
theorem finite_endpoint_closure_dist [PseudoMetricSpace Ω]
    (hu_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ u x ω)
    (hv_nn : ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ ω, 0 ≤ v x ω)
    (hu_cont : ∀ ω, Tendsto (fun x => u x ω) (𝓝[>] 0) (𝓝 (u 0 ω)))
    (hv_cont : ∀ ω, Tendsto (fun x => v x ω) (𝓝[>] 0) (𝓝 (v 0 ω)))
    (hu0 : 0 < ∑ ω, u 0 ω) (hv0 : 0 < ∑ ω, v 0 ω) :
    Tendsto (fun x => W dist (normLaw (u x)) (normLaw (v x))) (𝓝[>] 0)
        (𝓝 (W dist (normLaw (u 0)) (normLaw (v 0)))) ∧
    ∀ B : ℝ → EReal,
      (∀ᶠ x in 𝓝[>] (0 : ℝ), (W dist (normLaw (u x)) (normLaw (v x)) : EReal) ≤ B x) →
      (W dist (normLaw (u 0)) (normLaw (v 0)) : EReal) ≤ liminf B (𝓝[>] 0) :=
  ⟨tendsto_W_normLaw (d := dist) u v hu_nn hv_nn hu_cont hv_cont hu0 hv0 (fun _ _ => dist_nonneg) dist_self
      dist_triangle,
    fun B hB => W_endpoint_le_liminf (d := dist) u v hu_nn hv_nn hu_cont hv_cont hu0 hv0
      (fun _ _ => dist_nonneg) dist_self dist_triangle B hB⟩

end TwoFamilies

/-! ## The pinned Potts instance -/

section Potts

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

lemma gibbs_eq_normLaw [Nonempty C] (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x)
    (hZ : 0 < I.partition x) : I.gibbs x hx hZ = normLaw (I.weight x) := by
  have h : WeightAdmissible (I.weight x) := ⟨I.weight_nonneg hx, hZ⟩
  ext σ
  rw [normLaw_w_of_weightAdmissible h]
  rfl

/-- The paper's use of `lem:finite-endpoint-closure` for pinned Potts laws:
if the two hard partition functions are positive and
`W_d(μ_I^x, μ_J^x) ≤ B(x)` for all small `x > 0`, then
`W_d(μ_I^0, μ_J^0) ≤ liminf_{x↓0} B(x)`. -/
theorem potts_hard_W_le_liminf [Nonempty C] (I J : PinningData V C)
    (hI : 0 < I.partition 0) (hJ : 0 < J.partition 0)
    {d : (V → C) → (V → C) → ℝ} (hd : ∀ a b, 0 ≤ d a b) (hd0 : ∀ a, d a a = 0)
    (htri : ∀ a b c, d a c ≤ d a b + d b c) (B : ℝ → EReal)
    (hB : ∀ᶠ x in 𝓝[>] (0 : ℝ), ∀ hx : 0 < x,
      (W d (I.gibbs x hx.le (I.partition_pos_of_parameter_pos hx))
        (J.gibbs x hx.le (J.partition_pos_of_parameter_pos hx)) : EReal) ≤ B x) :
    (W d (I.gibbs 0 le_rfl hI) (J.gibbs 0 le_rfl hJ) : EReal) ≤ liminf B (𝓝[>] 0) := by
  have hnn : ∀ K : PinningData V C, ∀ᶠ x in 𝓝[≥] (0 : ℝ), ∀ σ, 0 ≤ K.weight x σ :=
    fun K => eventually_nhdsWithin_of_forall fun x hx σ => K.weight_nonneg hx σ
  have hcont : ∀ K : PinningData V C, ∀ σ,
      Tendsto (fun x => K.weight x σ) (𝓝[>] 0) (𝓝 (K.weight 0 σ)) :=
    fun K σ => ((K.continuous_weight σ).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [gibbs_eq_normLaw I le_rfl hI, gibbs_eq_normLaw J le_rfl hJ]
  refine W_endpoint_le_liminf (fun x => I.weight x) (fun x => J.weight x)
    (hnn I) (hnn J) (hcont I) (hcont J) hI hJ hd hd0 htri B ?_
  filter_upwards [hB, self_mem_nhdsWithin] with x hx hxpos
  have := hx hxpos
  rwa [gibbs_eq_normLaw I, gibbs_eq_normLaw J] at this

end Potts

end

end PottsCI
