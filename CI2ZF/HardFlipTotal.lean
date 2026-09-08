import CI2ZF.HardFlipBoundary

/-!
# Concrete component-flip kernels including the empty free graph

For a nonempty free vertex set these definitions are exactly the concrete
Vigoda kernels.  For the empty vertex set the transition holds.  Stationarity
is proved in both branches.
-/

namespace PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

lemma hold_stationary (mu : FinDist (V → C)) :
    FinDist.IsStationary FinDist.pure mu := by
  apply FinDist.ext
  funext Y
  change (∑ X, mu.w X * (if Y = X then 1 else 0)) = mu.w Y
  simp [mul_ite]

/-- Hold when there is no vertex to propose; otherwise use the actual hard
component-flip kernel with a uniform vertex-colour proposal. -/
noncomputable def hardStepWithEmpty [Nonempty C]
    (F : HardListInstance V C) (X : V → C) : FinDist (V → C) :=
  if h : Nonempty V then @hardStep V C _ _ h _ F X else FinDist.pure X

@[simp] lemma hardStepWithEmpty_of_nonempty [Nonempty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) : hardStepWithEmpty F X = hardStep F X := by
  unfold hardStepWithEmpty
  exact dif_pos (inferInstance : Nonempty V)

@[simp] lemma hardStepWithEmpty_of_empty [IsEmpty V] [Nonempty C]
    (F : HardListInstance V C) (X : V → C) : hardStepWithEmpty F X = FinDist.pure X := by
  simp [hardStepWithEmpty]

theorem hardStepWithEmpty_stationary [Nonempty C]
    (F : HardListInstance V C) (hne : ∃ X : V → C, F.IsProper X) :
    FinDist.IsStationary (hardStepWithEmpty F) (uniformProperFibre F hne) := by
  by_cases h : Nonempty V
  · let := h
    have heq : hardStepWithEmpty F = hardStep F := funext (hardStepWithEmpty_of_nonempty F)
    rw [heq]
    exact hardStep_stationary F hne
  · have hkernel : hardStepWithEmpty F = FinDist.pure := by
      funext X
      simp [hardStepWithEmpty, h]
    rw [hkernel]
    exact hold_stationary _

/-- The concrete soft update, including the empty free-vertex hold case. -/
noncomputable def softVigodaKernelWithEmpty [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (V → C) → FinDist (V → C) :=
  if h : Nonempty V then @softVigodaKernel V C _ _ h _ I x hx0 hx1 else FinDist.pure

@[simp] lemma softVigodaKernelWithEmpty_of_nonempty [Nonempty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softVigodaKernelWithEmpty I x hx0 hx1 = softVigodaKernel I x hx0 hx1 := by
  unfold softVigodaKernelWithEmpty
  exact dif_pos (inferInstance : Nonempty V)

@[simp] lemma softVigodaKernelWithEmpty_of_empty [IsEmpty V] [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    softVigodaKernelWithEmpty I x hx0 hx1 = FinDist.pure := by
  simp [softVigodaKernelWithEmpty]

theorem softVigodaKernelWithEmpty_stationary [Nonempty C]
    (I : PinningData V C) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    FinDist.IsStationary (softVigodaKernelWithEmpty I x hx0 hx1)
      (I.gibbs x hx0.le (I.partition_pos_of_parameter_pos hx0)) := by
  by_cases h : Nonempty V
  · let := h
    rw [softVigodaKernelWithEmpty_of_nonempty]
    exact softVigodaKernel_stationary I x hx0 hx1
  · rw [softVigodaKernelWithEmpty, dif_neg h]
    exact hold_stationary _

end PottsCI.Vigoda
