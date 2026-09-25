import ZeroFreeness.Potts.Model.Real.ActiveConstraints

/-!
# The active-constraint soft kernel

This file formalizes the probabilistic composition used in the soft Potts
coupling arguments.  At a strictly positive parameter, one update first
samples the active constraints conditional on the present colouring, then
runs an arbitrary Markov kernel that preserves the uniform law on the
resulting hard fibre, and finally forgets the active set.

The proof is finite and exact.  Active sets of zero joint mass are allowed:
their transition kernel may be arbitrary, since the conditional active-set
law never selects them.  No irreducibility or reversibility assumption is
needed.
-/

namespace PottsCI

open Finset

attribute [local instance] Classical.propDecidable

variable {V C : Type*}
variable [Fintype V] [Fintype C]

namespace PinningData

variable (I : PinningData V C)

/-- A Markov kernel on colourings which stays inside a selected hard fibre
when it starts there, and preserves the uniform law on every nonempty fibre.

The support field records the intended hard dynamics explicitly.  The
stationarity proof below only consumes `stationary`; keeping both fields makes
the interface match the flip kernels used in the paper. -/
structure HardFibreKernel (A : Finset (Constraint I)) where
  kernel : (V → C) → FinDist (V → C)
  supported : ∀ σ τ, I.ActiveCompatible σ A →
    ¬ I.ActiveCompatible τ A → (kernel σ).w τ = 0
  stationary : ∀ hne : (I.compatibleColorings A).Nonempty,
    FinDist.IsStationary kernel (I.uniformHardFibre A hne)

/-- The conditional law of the active set given a colouring.  Strict
positivity of `x` makes the normalizing spin weight nonzero. -/
noncomputable def activeLawGivenSpin (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (σ : V → C) : FinDist (Finset (Constraint I)) where
  w := fun A => I.jointActiveWeight x A σ / I.weight x σ
  nonneg := fun A => div_nonneg
    (I.jointActiveWeight_nonneg hx0.le hx1.le A σ) (I.weight_pos hx0 σ).le
  sum_one := by
    rw [← Finset.sum_div, I.sum_jointActiveWeight_eq_weight]
    exact div_self (I.weight_pos hx0 σ).ne'

@[simp]
lemma activeLawGivenSpin_w (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (σ : V → C) (A : Finset (Constraint I)) :
    (I.activeLawGivenSpin x hx0 hx1 σ).w A =
      I.jointActiveWeight x A σ / I.weight x σ := rfl

/-- Sample an active set, take one step of its hard-fibre kernel, and discard
the active set.  Kernels belonging to zero-mass active sets are harmless and
may be chosen arbitrarily. -/
noncomputable def softKernel (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (H : ∀ A : Finset (Constraint I), HardFibreKernel I A) :
    (V → C) → FinDist (V → C) :=
  fun σ => (I.activeLawGivenSpin x hx0 hx1 σ).bind fun A => (H A).kernel σ

@[simp]
lemma softKernel_w (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (H : ∀ A : Finset (Constraint I), HardFibreKernel I A)
    (σ τ : V → C) :
    (I.softKernel x hx0 hx1 H σ).w τ =
      ∑ A : Finset (Constraint I),
        I.jointActiveWeight x A σ / I.weight x σ * ((H A).kernel σ).w τ := rfl

private lemma weighted_hard_step (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (H : ∀ A : Finset (Constraint I), HardFibreKernel I A)
    (A : Finset (Constraint I)) (τ : V → C) :
    (∑ σ : V → C, I.jointActiveWeight x A σ * ((H A).kernel σ).w τ) =
      I.jointActiveWeight x A τ := by
  by_cases hmass : 0 < I.activeMass x A
  · have hne : (I.compatibleColorings A).Nonempty :=
      I.compatibleColorings_nonempty_of_activeMass_pos hmass
    have hconditional :
        FinDist.IsStationary (H A).kernel
          (I.spinLawGivenActive x hx0.le hx1.le A hmass) := by
      rw [I.spinLawGivenActive_eq_uniformHardFibre hx0.le hx1.le A hmass]
      exact (H A).stationary hne
    have hcomponent := congrArg (fun μ : FinDist (V → C) => μ.w τ) hconditional
    have hnormalized :
        (∑ σ : V → C,
          I.jointActiveWeight x A σ / I.activeMass x A * ((H A).kernel σ).w τ) =
          I.jointActiveWeight x A τ / I.activeMass x A := by
      exact hcomponent
    calc
      (∑ σ : V → C,
          I.jointActiveWeight x A σ * ((H A).kernel σ).w τ) =
          I.activeMass x A *
            (∑ σ : V → C,
              I.jointActiveWeight x A σ / I.activeMass x A *
                ((H A).kernel σ).w τ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun σ _ => ?_
            field_simp
      _ = I.activeMass x A *
          (I.jointActiveWeight x A τ / I.activeMass x A) := by
            rw [hnormalized]
      _ = I.jointActiveWeight x A τ := by
            field_simp
  · have hmass0 : I.activeMass x A = 0 := by
      have hnonneg : 0 ≤ I.activeMass x A :=
        Finset.sum_nonneg fun σ _ => I.jointActiveWeight_nonneg hx0.le hx1.le A σ
      linarith
    have hjoint0 : ∀ σ : V → C, I.jointActiveWeight x A σ = 0 := by
      intro σ
      have hle : I.jointActiveWeight x A σ ≤ I.activeMass x A := by
        exact Finset.single_le_sum
          (fun ρ _ => I.jointActiveWeight_nonneg hx0.le hx1.le A ρ)
          (Finset.mem_univ σ)
      have hnonneg := I.jointActiveWeight_nonneg hx0.le hx1.le A σ
      linarith
    simp [hjoint0]

/-- The Potts Gibbs law is stationary for the active-constraint soft kernel.

This is the exact finite Gibbs-sampler composition theorem used by both soft
flip arguments: conditional hard-fibre stationarity is the only dynamical
input. -/
theorem softKernel_stationary [Nonempty C]
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (H : ∀ A : Finset (Constraint I), HardFibreKernel I A) :
    FinDist.IsStationary (I.softKernel x hx0 hx1 H)
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) := by
  apply FinDist.ext
  funext τ
  simp only [FinDist.bind_w, softKernel_w]
  let Z := I.partition x
  have hZ : 0 < Z := I.partition_pos_of_parameter_pos hx0
  change
    (∑ σ : V → C,
      I.weight x σ / Z *
        ∑ A : Finset (Constraint I),
          I.jointActiveWeight x A σ / I.weight x σ * ((H A).kernel σ).w τ) =
      I.weight x τ / Z
  calc
    (∑ σ : V → C,
        I.weight x σ / Z *
          ∑ A : Finset (Constraint I),
            I.jointActiveWeight x A σ / I.weight x σ * ((H A).kernel σ).w τ) =
        ∑ σ : V → C, ∑ A : Finset (Constraint I),
          I.jointActiveWeight x A σ * ((H A).kernel σ).w τ / Z := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun A _ => ?_
            have hw : I.weight x σ ≠ 0 := (I.weight_pos hx0 σ).ne'
            field_simp
    _ = ∑ A : Finset (Constraint I), ∑ σ : V → C,
          I.jointActiveWeight x A σ * ((H A).kernel σ).w τ / Z := by
            rw [Finset.sum_comm]
    _ = ∑ A : Finset (Constraint I),
          (∑ σ : V → C,
            I.jointActiveWeight x A σ * ((H A).kernel σ).w τ) / Z := by
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [Finset.sum_div]
    _ = ∑ A : Finset (Constraint I), I.jointActiveWeight x A τ / Z := by
            refine Finset.sum_congr rfl fun A _ => ?_
            rw [I.weighted_hard_step x hx0 hx1 H A τ]
    _ = (∑ A : Finset (Constraint I), I.jointActiveWeight x A τ) / Z := by
            rw [Finset.sum_div]
    _ = I.weight x τ / Z := by
            rw [I.sum_jointActiveWeight_eq_weight]

end PinningData

end PottsCI
