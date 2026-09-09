import CI2ZF.Coupling.Foundations.PathCoupling
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Basic

/-!
# Endpoint continuity on finite state spaces

This file isolates the finite-state limiting argument used when a positive-
temperature coupling estimate is sent to the hard endpoint.  A family of
nonnegative, unnormalised weights that converges pointwise and whose limiting
partition sum is positive has normalized laws converging pointwise and in
`ℓ¹`.  For every bounded nonnegative transport cost, the corresponding
optimal transport cost then converges to zero.

All statements are formulated for an arbitrary filter.  Taking the filter to
be `𝓝 t₀` gives continuity at a real endpoint; taking a one-sided neighbourhood
filter gives the corresponding one-sided limit.
-/

namespace PottsCI

open Finset Filter Topology

variable {S : Type*} [Fintype S]

namespace FinDist

/-- Normalize nonnegative weights of strictly positive total mass to a finite
probability distribution. -/
noncomputable def normalizeWeights (w : S → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hZ : 0 < ∑ x, w x) : FinDist S where
  w := fun x => w x / ∑ y, w y
  nonneg := fun x => div_nonneg (hw x) hZ.le
  sum_one := by
    rw [← Finset.sum_div, div_self (ne_of_gt hZ)]

@[simp]
lemma normalizeWeights_apply (w : S → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hZ : 0 < ∑ x, w x) (x : S) :
    (normalizeWeights w hw hZ).w x = w x / ∑ y, w y := rfl

/-- Normalizing the weight function of an existing finite distribution does
not change the distribution. -/
lemma normalizeWeights_self (μ : FinDist S) :
    normalizeWeights μ.w μ.nonneg (by simp [μ.sum_one]) = μ := by
  ext x
  simp [normalizeWeights_apply, μ.sum_one]

/-- The `ℓ¹` distance between the mass functions of two finite
distributions. -/
def l1Distance (μ ν : FinDist S) : ℝ := ∑ x, |μ.w x - ν.w x|

lemma l1Distance_nonneg (μ ν : FinDist S) : 0 ≤ l1Distance μ ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

@[simp]
lemma l1Distance_self (μ : FinDist S) : l1Distance μ μ = 0 := by
  simp [l1Distance]

lemma l1Distance_comm (μ ν : FinDist S) : l1Distance μ ν = l1Distance ν μ := by
  unfold l1Distance
  refine Finset.sum_congr rfl fun x _ => ?_
  exact abs_sub_comm _ _

section FilterLimits

variable {α : Type*} {l : Filter α}

/-- On a finite state space, pointwise convergence of probability masses
implies convergence in `ℓ¹`. -/
theorem tendsto_l1Distance_of_pointwise (μ : α → FinDist S) (μ₀ : FinDist S)
    (hμ : ∀ x, Tendsto (fun a => (μ a).w x) l (𝓝 (μ₀.w x))) :
    Tendsto (fun a => l1Distance (μ a) μ₀) l (𝓝 0) := by
  have hpoint : ∀ x : S,
      Tendsto (fun a => |(μ a).w x - μ₀.w x|) l (𝓝 0) := by
    intro x
    have hconst : Tendsto (fun _ : α => μ₀.w x) l (𝓝 (μ₀.w x)) :=
      tendsto_const_nhds
    simpa using ((hμ x).sub hconst).abs
  have hsum := tendsto_finsetSum (Finset.univ : Finset S) fun x _ => hpoint x
  simpa [l1Distance] using hsum

/-- The left-handed version of `tendsto_l1Distance_of_pointwise`. -/
theorem tendsto_l1Distance_of_pointwise_left (μ : α → FinDist S) (μ₀ : FinDist S)
    (hμ : ∀ x, Tendsto (fun a => (μ a).w x) l (𝓝 (μ₀.w x))) :
    Tendsto (fun a => l1Distance μ₀ (μ a)) l (𝓝 0) := by
  have hright := tendsto_l1Distance_of_pointwise μ μ₀ hμ
  have heq : (fun a => l1Distance μ₀ (μ a)) =
      (fun a => l1Distance (μ a) μ₀) := by
    funext a
    exact l1Distance_comm _ _
  rw [heq]
  exact hright

/-- Pointwise convergence of unnormalised weights implies pointwise
convergence of their normalized probability masses, provided the limiting
partition sum is positive. -/
theorem tendsto_normalizeWeights_apply (w : α → S → ℝ) (w₀ : S → ℝ)
    (hw : ∀ a x, 0 ≤ w a x) (hZ : ∀ a, 0 < ∑ x, w a x)
    (hw₀ : ∀ x, 0 ≤ w₀ x) (hZ₀ : 0 < ∑ x, w₀ x)
    (hlim : ∀ x, Tendsto (fun a => w a x) l (𝓝 (w₀ x))) (x : S) :
    Tendsto
      (fun a => (normalizeWeights (w a) (hw a) (hZ a)).w x)
      l
      (𝓝 ((normalizeWeights w₀ hw₀ hZ₀).w x)) := by
  have hsum : Tendsto (fun a => ∑ y, w a y) l (𝓝 (∑ y, w₀ y)) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset S) fun y _ => hlim y
  convert (hlim x).div hsum (ne_of_gt hZ₀) using 1 <;> rfl

/-- Pointwise convergence of unnormalised weights implies `ℓ¹` convergence of
the normalized finite distributions. -/
theorem tendsto_normalizeWeights_l1 (w : α → S → ℝ) (w₀ : S → ℝ)
    (hw : ∀ a x, 0 ≤ w a x) (hZ : ∀ a, 0 < ∑ x, w a x)
    (hw₀ : ∀ x, 0 ≤ w₀ x) (hZ₀ : 0 < ∑ x, w₀ x)
    (hlim : ∀ x, Tendsto (fun a => w a x) l (𝓝 (w₀ x))) :
    Tendsto
      (fun a => l1Distance (normalizeWeights (w a) (hw a) (hZ a))
        (normalizeWeights w₀ hw₀ hZ₀))
      l (𝓝 0) :=
  tendsto_l1Distance_of_pointwise _ _
    (tendsto_normalizeWeights_apply w w₀ hw hZ hw₀ hZ₀ hlim)

/-- Pointwise convergence of finite probability masses implies convergence in
every Wasserstein cost that is nonnegative, zero on the diagonal, and
uniformly bounded. -/
theorem tendsto_W_of_pointwise [DecidableEq S] {d : S → S → ℝ} {B : ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    (hB : ∀ x y, d x y ≤ B) (μ : α → FinDist S) (μ₀ : FinDist S)
    (hμ : ∀ x, Tendsto (fun a => (μ a).w x) l (𝓝 (μ₀.w x))) :
    Tendsto (fun a => W d (μ a) μ₀) l (𝓝 0) := by
  have hl1 := tendsto_l1Distance_of_pointwise μ μ₀ hμ
  have hu : Tendsto (fun a => B * l1Distance (μ a) μ₀ / 2) l (𝓝 0) := by
    simpa using (hl1.const_mul B).div_const 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hu ?_ ?_
  · exact Filter.Eventually.of_forall fun a => W_nonneg hd
  · exact Filter.Eventually.of_forall fun a =>
      W_le_half_l1 hd hd0 hB (μ a) μ₀

/-- The left-handed counterpart of `tendsto_W_of_pointwise`: the endpoint law
may occur in the first marginal of the transport cost. -/
theorem tendsto_W_left_of_pointwise [DecidableEq S] {d : S → S → ℝ} {B : ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    (hB : ∀ x y, d x y ≤ B) (μ : α → FinDist S) (μ₀ : FinDist S)
    (hμ : ∀ x, Tendsto (fun a => (μ a).w x) l (𝓝 (μ₀.w x))) :
    Tendsto (fun a => W d μ₀ (μ a)) l (𝓝 0) := by
  have hl1 := tendsto_l1Distance_of_pointwise_left μ μ₀ hμ
  have hu : Tendsto (fun a => B * l1Distance μ₀ (μ a) / 2) l (𝓝 0) := by
    simpa using (hl1.const_mul B).div_const 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hu ?_ ?_
  · exact Filter.Eventually.of_forall fun a => W_nonneg hd
  · exact Filter.Eventually.of_forall fun a =>
      W_le_half_l1 hd hd0 hB μ₀ (μ a)

/-- Normalized laws obtained from convergent finite weights converge in every
bounded Wasserstein cost.  This is the reusable endpoint-closure theorem. -/
theorem tendsto_normalizeWeights_W [DecidableEq S] {d : S → S → ℝ} {B : ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    (hB : ∀ x y, d x y ≤ B) (w : α → S → ℝ) (w₀ : S → ℝ)
    (hw : ∀ a x, 0 ≤ w a x) (hZ : ∀ a, 0 < ∑ x, w a x)
    (hw₀ : ∀ x, 0 ≤ w₀ x) (hZ₀ : 0 < ∑ x, w₀ x)
    (hlim : ∀ x, Tendsto (fun a => w a x) l (𝓝 (w₀ x))) :
    Tendsto
      (fun a => W d (normalizeWeights (w a) (hw a) (hZ a))
        (normalizeWeights w₀ hw₀ hZ₀))
      l (𝓝 0) :=
  tendsto_W_of_pointwise hd hd0 hB _ _
    (tendsto_normalizeWeights_apply w w₀ hw hZ hw₀ hZ₀ hlim)

/-- A uniform finite-temperature transport bound survives a finite-state
endpoint limit.  This is the final closure step used for coupling
independence at a hard endpoint. -/
theorem W_le_of_pointwise_limits [DecidableEq S] [l.NeBot]
    {d : S → S → ℝ} {B C : ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z)
    (hB : ∀ x y, d x y ≤ B)
    (μ ν : α → FinDist S) (μ₀ ν₀ : FinDist S)
    (hμ : ∀ x, Tendsto (fun a => (μ a).w x) l (𝓝 (μ₀.w x)))
    (hν : ∀ x, Tendsto (fun a => (ν a).w x) l (𝓝 (ν₀.w x)))
    (hC : ∀ᶠ a in l, W d (μ a) (ν a) ≤ C) :
    W d μ₀ ν₀ ≤ C := by
  have hleft := tendsto_W_left_of_pointwise hd hd0 hB μ μ₀ hμ
  have hright := tendsto_W_of_pointwise hd hd0 hB ν ν₀ hν
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hleftSmall : ∀ᶠ a in l, W d μ₀ (μ a) < ε / 2 :=
    (tendsto_order.mp hleft).2 (ε / 2) (half_pos hε)
  have hrightSmall : ∀ᶠ a in l, W d (ν a) ν₀ < ε / 2 :=
    (tendsto_order.mp hright).2 (ε / 2) (half_pos hε)
  have hfinal : ∀ᶠ a in l, W d μ₀ ν₀ ≤ C + ε := by
    filter_upwards [hleftSmall, hC, hrightSmall] with a hLa hCa hRa
    have hfirst := W_triangle hd hd hd htri μ₀ (μ a) ν₀
    have hsecond := W_triangle hd hd hd htri (μ a) (ν a) ν₀
    linarith
  exact (Filter.Eventually.exists hfinal).choose_spec

end FilterLimits

/-! The following wrappers spell out the most common application: a real
parameter tends to an endpoint `t₀`. -/

/-- Continuity at a real parameter of each normalized probability mass. -/
theorem continuousAt_normalizeWeights_apply (w : ℝ → S → ℝ) (t₀ : ℝ)
    (hw : ∀ t x, 0 ≤ w t x) (hZ : ∀ t, 0 < ∑ x, w t x)
    (hcont : ∀ x, ContinuousAt (fun t => w t x) t₀) (x : S) :
    ContinuousAt
      (fun t => (normalizeWeights (w t) (hw t) (hZ t)).w x) t₀ :=
  tendsto_normalizeWeights_apply w (w t₀) hw hZ (hw t₀) (hZ t₀) hcont x

/-- Continuity at a real endpoint in `ℓ¹`. -/
theorem continuousAt_normalizeWeights_l1 (w : ℝ → S → ℝ) (t₀ : ℝ)
    (hw : ∀ t x, 0 ≤ w t x) (hZ : ∀ t, 0 < ∑ x, w t x)
    (hcont : ∀ x, ContinuousAt (fun t => w t x) t₀) :
    Tendsto
      (fun t => l1Distance (normalizeWeights (w t) (hw t) (hZ t))
        (normalizeWeights (w t₀) (hw t₀) (hZ t₀)))
      (𝓝 t₀) (𝓝 0) :=
  tendsto_normalizeWeights_l1 w (w t₀) hw hZ (hw t₀) (hZ t₀) hcont

/-- Continuity at a real endpoint in every bounded Wasserstein cost. -/
theorem continuousAt_normalizeWeights_W [DecidableEq S] {d : S → S → ℝ} {B : ℝ}
    (hd : ∀ x y, 0 ≤ d x y) (hd0 : ∀ x, d x x = 0)
    (hB : ∀ x y, d x y ≤ B) (w : ℝ → S → ℝ) (t₀ : ℝ)
    (hw : ∀ t x, 0 ≤ w t x) (hZ : ∀ t, 0 < ∑ x, w t x)
    (hcont : ∀ x, ContinuousAt (fun t => w t x) t₀) :
    Tendsto
      (fun t => W d (normalizeWeights (w t) (hw t) (hZ t))
        (normalizeWeights (w t₀) (hw t₀) (hZ t₀)))
      (𝓝 t₀) (𝓝 0) :=
  tendsto_normalizeWeights_W hd hd0 hB w (w t₀) hw hZ (hw t₀) (hZ t₀) hcont

end FinDist

end PottsCI
