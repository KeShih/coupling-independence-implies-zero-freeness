import CI2ZF.Potts.Model.Real.Model
import CI2ZF.Coupling.Foundations.EndpointContinuity
import Mathlib.Tactic.Continuity

/-!
# The hard endpoint of the finite Potts model

The antiferromagnetic Potts weights are nonnegative only on the half-line
`[0, ∞)`.  Accordingly, this file treats the temperature parameter as an
element of the subtype `Set.Ici (0 : ℝ)`, rather than asserting a false
two-sided probabilistic continuation through the hard endpoint.

For a pinned finite instance satisfying the elementary hard-feasibility
assumptions, we prove that its unnormalised weights, partition function, and
normalised Gibbs law converge as `x →0` inside this subtype.  The final
theorem packages the usual endpoint-closure step for a uniform
finite-temperature Wasserstein bound.
-/

namespace PottsCI

open Finset Filter Topology

attribute [local instance] Classical.propDecidable

variable {V : Type*} {C : Type*}
variable [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace PinningData

/-- The physically relevant, nonnegative Potts parameters. -/
abbrev NonnegativeParameter : Type := Set.Ici (0 : ℝ)

/-- The hard endpoint, regarded as a point of the nonnegative half-line. -/
def hardParameter : NonnegativeParameter := ⟨0, by simp⟩

@[simp]
lemma coe_hardParameter : (hardParameter : ℝ) = 0 := rfl

variable (I : PinningData V C)

/-- The Potts weight family on its nonnegative parameter domain. -/
noncomputable def nonnegativeWeight (x : NonnegativeParameter) (σ : V → C) : ℝ :=
  I.weight (x : ℝ) σ

/-- The pinned partition function on its nonnegative parameter domain. -/
noncomputable def nonnegativePartition (x : NonnegativeParameter) : ℝ :=
  I.partition (x : ℝ)

/-- The normalized Gibbs family on `[0, ∞)`.  Hard feasibility is included
in the arguments so that positivity at `x = 0` is explicit. -/
noncomputable def nonnegativeGibbs [Nonempty C] {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (x : NonnegativeParameter) : FinDist (V → C) :=
  I.gibbs (x : ℝ) x.property (I.partition_pos x.property hdegree hcolours)

/-- The normalized hard-colouring law. -/
noncomputable def hardGibbs [Nonempty C] {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C) :
    FinDist (V → C) :=
  I.gibbs 0 le_rfl (I.partition_zero_pos hdegree hcolours)

/-! ## Continuity of the concrete Potts weights -/

omit [DecidableEq V] [Fintype C] in
lemma continuous_weight (σ : V → C) : Continuous (fun x : ℝ => I.weight x σ) := by
  unfold weight
  apply Continuous.mul
  · continuity
  · apply continuous_finsetProd
    intro e _
    induction e using Sym2.ind with
    | _ u v =>
      change Continuous (fun x : ℝ => if σ u = σ v then x else 1)
      split <;> continuity

lemma continuous_partition : Continuous I.partition := by
  unfold partition
  apply continuous_finsetSum
  intro σ _
  exact I.continuous_weight σ

omit [DecidableEq V] [Fintype C] in
/-- Every concrete Potts weight converges to its hard value along the
nonnegative half-line. -/
theorem tendsto_nonnegativeWeight_hard (σ : V → C) :
    Tendsto (fun x : NonnegativeParameter => I.nonnegativeWeight x σ)
      (nhds hardParameter) (nhds (I.weight 0 σ)) := by
  exact (I.continuous_weight σ).continuousAt.comp
    continuous_subtype_val.continuousAt

omit [DecidableEq V] [Fintype C] in
/-- Equivalently, a concrete weight converges to the indicator of hard
admissibility. -/
theorem tendsto_nonnegativeWeight_hard_indicator (σ : V → C) :
    Tendsto (fun x : NonnegativeParameter => I.nonnegativeWeight x σ)
      (nhds hardParameter) (nhds (if I.HardAdmissible σ then 1 else 0)) := by
  simpa [I.weight_zero_eq σ] using I.tendsto_nonnegativeWeight_hard σ

/-- The partition function converges to the hard partition function along the
nonnegative half-line. -/
theorem tendsto_nonnegativePartition_hard :
    Tendsto I.nonnegativePartition (nhds hardParameter) (nhds (I.partition 0)) := by
  exact I.continuous_partition.continuousAt.comp continuous_subtype_val.continuousAt

/-! ## Convergence of the normalized law -/

@[simp]
lemma nonnegativeGibbs_apply [Nonempty C] {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (x : NonnegativeParameter) (σ : V → C) :
    (I.nonnegativeGibbs hdegree hcolours x).w σ =
      I.nonnegativeWeight x σ / I.nonnegativePartition x := rfl

@[simp]
lemma hardGibbs_apply [Nonempty C] {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (σ : V → C) :
    (I.hardGibbs hdegree hcolours).w σ = I.weight 0 σ / I.partition 0 := rfl

/-- Pointwise convergence of every probability mass to the hard Gibbs law. -/
theorem tendsto_nonnegativeGibbs_apply [Nonempty C] {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    (σ : V → C) :
    Tendsto (fun x : NonnegativeParameter => (I.nonnegativeGibbs hdegree hcolours x).w σ)
      (nhds hardParameter) (nhds ((I.hardGibbs hdegree hcolours).w σ)) := by
  have hweight := I.tendsto_nonnegativeWeight_hard σ
  have hpartition := I.tendsto_nonnegativePartition_hard
  convert hweight.div hpartition (I.partition_zero_pos hdegree hcolours).ne' using 1 <;> rfl

/-- `ℓ¹` convergence of the nonnegative-temperature Gibbs laws to the hard
Gibbs law. -/
theorem tendsto_nonnegativeGibbs_l1 [Nonempty C] {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C) :
    Tendsto
      (fun x : NonnegativeParameter =>
        FinDist.l1Distance (I.nonnegativeGibbs hdegree hcolours x)
          (I.hardGibbs hdegree hcolours))
      (nhds hardParameter) (nhds 0) :=
  FinDist.tendsto_l1Distance_of_pointwise _ _
    (I.tendsto_nonnegativeGibbs_apply hdegree hcolours)

/-- Convergence to the hard Gibbs law for every bounded nonnegative transport
cost that vanishes on the diagonal. -/
theorem tendsto_nonnegativeGibbs_W [Nonempty C] {Δ : ℕ}
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C)
    {d : (V → C) → (V → C) → ℝ} {B : ℝ}
    (hd : ∀ σ τ, 0 ≤ d σ τ) (hd0 : ∀ σ, d σ σ = 0)
    (hB : ∀ σ τ, d σ τ ≤ B) :
    Tendsto
      (fun x : NonnegativeParameter =>
        FinDist.W d (I.nonnegativeGibbs hdegree hcolours x)
          (I.hardGibbs hdegree hcolours))
      (nhds hardParameter) (nhds 0) :=
  FinDist.tendsto_W_of_pointwise hd hd0 hB _ _
    (I.tendsto_nonnegativeGibbs_apply hdegree hcolours)

/-! ## Closing a finite-temperature transport estimate at `x = 0` -/

/-- A uniform transport estimate at positive Potts parameters passes to the
hard endpoint.  The explicit net `x` makes this statement independent of a
particular notation for one-sided real filters: its values lie in `[0, ∞)`,
converge to `0`, and are eventually in the physical interval `(0, 1]`.

This is the concrete Potts wrapper used when a positive-temperature coupling
bound is proved first and the normalized hard children are obtained by finite-
state closure. -/
theorem hard_W_le_of_positive_parameter_bound [Nonempty C]
    (J : PinningData V C) {Δ : ℕ}
    (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hcolours : Δ + 2 ≤ Fintype.card C)
    {A : Type*} {l : Filter A} [l.NeBot]
    (x : A → NonnegativeParameter)
    (hx : Tendsto x l (nhds hardParameter))
    (hxpos : ∀ᶠ a in l, 0 < (x a : ℝ))
    (hxunit : ∀ᶠ a in l, (x a : ℝ) ≤ 1)
    {d : (V → C) → (V → C) → ℝ} {B K : ℝ}
    (hd : ∀ σ τ, 0 ≤ d σ τ) (hd0 : ∀ σ, d σ σ = 0)
    (htri : ∀ σ τ υ, d σ υ ≤ d σ τ + d τ υ)
    (hB : ∀ σ τ, d σ τ ≤ B)
    (hsoft : ∀ y : NonnegativeParameter, 0 < (y : ℝ) → (y : ℝ) ≤ 1 →
      FinDist.W d (I.nonnegativeGibbs hdegreeI hcolours y)
        (J.nonnegativeGibbs hdegreeJ hcolours y) ≤ K) :
    FinDist.W d (I.hardGibbs hdegreeI hcolours)
      (J.hardGibbs hdegreeJ hcolours) ≤ K := by
  apply FinDist.W_le_of_pointwise_limits (l := l) hd hd0 htri hB
    (fun a => I.nonnegativeGibbs hdegreeI hcolours (x a))
    (fun a => J.nonnegativeGibbs hdegreeJ hcolours (x a))
    (I.hardGibbs hdegreeI hcolours) (J.hardGibbs hdegreeJ hcolours)
  · intro σ
    exact (I.tendsto_nonnegativeGibbs_apply hdegreeI hcolours σ).comp hx
  · intro σ
    exact (J.tendsto_nonnegativeGibbs_apply hdegreeJ hcolours σ).comp hx
  · filter_upwards [hxpos, hxunit] with a hapos haunit
    exact hsoft (x a) hapos haunit

end PinningData

end PottsCI
