import CI2ZF.Coupling.Vigoda.ActivationAverage
import CI2ZF.Coupling.Vigoda.CouplingIndependence

/-!
# The conditional hard-coupling estimate

The proposition below concerns the concrete hard flip kernels obtained
from the same activation coins. From it, all activation averaging and
soft adjacent-state contraction are already theorems.
-/

namespace CI2ZF

open scoped BigOperators
open PottsCI PottsCI.FinDist PottsCI.Vigoda
attribute [local instance] Classical.propDecidable

noncomputable section

variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]

/-- The conditional hard one-step estimate at a unique disagreement.
This is an explicit proposition, discharged by
`conditionalHardCouplingEstimate` in `PottsCITheorem`; its body uses the actual kernels and activation sets. -/
def ConditionalHardCouplingEstimate (I : PinningData V C) : Prop :=
  ∀ (X Y : V → C) (v : V), X v ≠ Y v → (∀ u, u ≠ v → X u = Y u) →
  ∀ ω : I.Constraint → Bool,
    ((Fintype.card V : ℝ) * Fintype.card C) *
      (W ham (hardStep (activeHardListInstance I (activatedSet I X ω)) X)
        (hardStep (activeHardListInstance I (activatedSet I Y ω)) Y) - 1) ≤
    (11 / 6 : ℝ) * rootFreeCoinCount I v ω - rootCommonListCount I X Y v ω

omit [Fintype C] [Nonempty V] [Nonempty C] in
/-- The unique disagreement vertex needed by the hard local estimate is
extracted from Hamming adjacency, rather than imposed as another assumption. -/
theorem exists_unique_disagreement {X Y : V → C} (hXY : hamCard X Y = 1) :
    ∃ v, X v ≠ Y v ∧ ∀ u, u ≠ v → X u = Y u := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hXY
  have hvXY : X v ≠ Y v := by
    have hm : v ∈ Finset.univ.filter (fun u => X u ≠ Y u) := by rw [hv]; simp
    exact (Finset.mem_filter.mp hm).2
  refine ⟨v, hvXY, ?_⟩
  intro u huv
  by_contra hneq
  have hm : u ∈ Finset.univ.filter (fun u => X u ≠ Y u) := by simp [hneq]
  rw [hv] at hm
  exact huv (Finset.mem_singleton.mp hm)

/-- No soft contraction assumption remains after supplying the precise
conditional hard estimate: the common-coin marginals, degree averages,
list intersection budget, and normalization have all been proved. -/
theorem soft_adjacent_contraction_of_conditional_hard (I : PinningData V C)
    {Δ : ℕ} (hdegree : I.DegreeBound Δ) (hconditional : ConditionalHardCouplingEstimate I)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (X Y : V → C) (hXY : hamCard X Y = 1) :
    W ham (softVigodaKernel I x hx0 hx1 X) (softVigodaKernel I x hx0 hx1 Y) ≤
      1 - ciDenominator (Fintype.card C) Δ x /
        ((Fintype.card V : ℝ) * Fintype.card C) := by
  obtain ⟨v, hv, hoff⟩ := exists_unique_disagreement hXY
  exact softVigoda_contraction_of_hard_estimate I X Y v x hx0 hx1 hdegree
    (hconditional X Y v hv hoff)

/-- A concrete two-child input package now needs only the hard estimate
for each child and the two rowwise boundary comparisons. -/
theorem softVigoda_inputs_of_conditional_hard (I J M : PinningData V C)
    {Δ : ℕ} (hdegreeI : I.DegreeBound Δ) (hdegreeJ : J.DegreeBound Δ)
    (hI : ConditionalHardCouplingEstimate I) (hJ : ConditionalHardCouplingEstimate J)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1)
    (hrowI : ∀ σ, W ham (softVigodaKernel I x hx0 hx1 σ)
      (softVigodaKernel M x hx0 hx1 σ) ≤
        (1 - x) * Δ / ((Fintype.card V : ℝ) * Fintype.card C))
    (hrowJ : ∀ σ, W ham (softVigodaKernel J x hx0 hx1 σ)
      (softVigodaKernel M x hx0 hx1 σ) ≤
        (1 - x) * Δ / ((Fintype.card V : ℝ) * Fintype.card C)) :
    SoftVigodaCouplingInputs I J M Δ x hx0 hx1 where
  contraction_left := soft_adjacent_contraction_of_conditional_hard I hdegreeI hI x hx0 hx1
  contraction_right := soft_adjacent_contraction_of_conditional_hard J hdegreeJ hJ x hx0 hx1
  boundary_left := hrowI
  boundary_right := hrowJ

end

end CI2ZF
