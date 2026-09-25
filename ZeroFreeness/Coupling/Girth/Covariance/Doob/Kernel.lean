import ZeroFreeness.Coupling.Girth.Covariance.Doob.Joint
import ZeroFreeness.Coupling.Girth.Covariance.Insertion.FullSource

/-! The full shell conditional source is exactly the source controlled
by sequential revelation. No product assumption is made on the shell. -/
namespace ZeroFreeness.Appendix.Girth.Doob
open scoped BigOperators
open PottsCI Finset Edge.FiniteLaw
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {Ω Λ S U O C : Type*} [Fintype Ω] [Fintype Λ] [Fintype S]
  [Fintype U] [Fintype O] [Fintype C] [DecidableEq C] [DecidableEq U] [DecidableEq S]

theorem kernel_first_mass (μ : FinDist Ω) (K : Ω → FinDist Λ) (ξ : Ω) :
    eventMass (kernelJoint μ K) (fun σ => σ.1 = ξ) = μ.w ξ := by
  simp only [eventMass, kernelJoint, Fintype.sum_prod_type, Finset.sum_ite_irrel,
    ← Finset.mul_sum, FinDist.sum_one, mul_one]
  simp

theorem conditional_kernel_first (μ : FinDist Ω) (K : Ω → FinDist Λ)
    (f : Ω × Λ → ℝ) (ξ : Ω) (hξ : 0 < μ.w ξ) :
    expectReal (conditional (kernelJoint μ K) (fun σ => σ.1 = ξ)) f =
      expectReal (K ξ) (fun t => f (ξ,t)) := by
  have hm := kernel_first_mass μ K ξ
  have hp : 0 < eventMass (kernelJoint μ K) (fun σ => σ.1 = ξ) := by rw [hm]; exact hξ
  unfold expectReal
  simp_rw [conditional_w (kernelJoint μ K) (fun σ => σ.1 = ξ) hp]
  rw [hm]
  simp only [kernelJoint, Fintype.sum_prod_type]
  simp_rw [ite_div, zero_div, ite_mul, zero_mul, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_div_cancel_left₀ _ hξ.ne']

def coordinateKeys (js : List S) : List (((S → C) × Λ) → C) :=
  js.map (fun j σ => σ.1 j)

theorem jointEvent_coordinateKeys (js : List S) (hcover : ∀ j, j ∈ js)
    (σ : (S → C) × Λ) :
    jointEvent (coordinateKeys js) σ = fun ω => ω.1 = σ.1 := by
  funext ω
  apply propext
  simp only [jointEvent, coordinateKeys, List.forall_mem_map]
  constructor
  · intro h
    funext j
    exact h j (hcover j)
  · intro h j _
    exact congrFun h j

theorem jointMean_coordinateKeys (js : List S) (hcover : ∀ j, j ∈ js)
    (μ : FinDist (S → C)) (K : (S → C) → FinDist Λ) (f : ((S → C) × Λ) → ℝ)
    (σ : (S → C) × Λ) (hσ : 0 < (kernelJoint μ K).w σ) :
    jointMean (coordinateKeys js) (kernelJoint μ K) f σ =
      expectReal (K σ.1) (fun t => f (σ.1,t)) := by
  have hξ : 0 < μ.w σ.1 := by
    exact pos_of_mul_pos_left hσ ((K σ.1).nonneg σ.2)
  unfold jointMean
  rw [jointEvent_coordinateKeys js hcover]
  exact conditional_kernel_first μ K f σ.1 hξ

theorem variance_kernel_first (μ : FinDist Ω) (K : Ω → FinDist Λ) (f : Ω → ℝ) :
    variance (kernelJoint μ K) (fun σ => f σ.1) = variance μ f := by
  simp only [variance_moment, expectReal_kernelJoint, expectReal_const]

theorem variance_jointMean_coordinateKeys (js : List S) (hcover : ∀ j, j ∈ js)
    (μ : FinDist (S → C)) (K : (S → C) → FinDist Λ) (f : ((S → C) × Λ) → ℝ) :
    variance (kernelJoint μ K) (jointMean (coordinateKeys js) (kernelJoint μ K) f) =
      variance μ (fun ξ => expectReal (K ξ) (fun t => f (ξ,t))) := by
  rw [variance_congr_support _ _ _ (jointMean_coordinateKeys js hcover μ K f)]
  exact variance_kernel_first μ K (fun ξ => expectReal (K ξ) (fun t => f (ξ,t)))

def weightedCoordinateKeys (js : List S) (a : S → ℝ) : List ((((S → C) × Λ) → C) × ℝ) :=
  js.map (fun j => ((fun σ => σ.1 j), a j))

theorem variance_conditionalSource_le (js : List S) (hcover : ∀ j, j ∈ js)
    (μ : FinDist (S → C)) (K : (S → C) → FinDist Λ) (f : ((S → C) × Λ) → ℝ)
    (a : S → ℝ) {s A : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hscore : BoundedScores s A f (weightedCoordinateKeys js a) (kernelJoint μ K)) :
    variance μ (fun ξ => expectReal (K ξ) (fun t => f (ξ,t))) ≤
      A * (js.map (fun j => a j ^ 2)).sum := by
  have h := variance_jointMean_le (weightedCoordinateKeys js a) (kernelJoint μ K) f hs hs1 hscore
  have hk : (weightedCoordinateKeys (Λ := Λ) (C := C) js a).map Prod.fst = coordinateKeys js := by
    simp only [weightedCoordinateKeys, coordinateKeys, List.map_map, Function.comp_def]
  rw [hk, variance_jointMean_coordinateKeys js hcover] at h
  simpa only [squareBudget, weightedCoordinateKeys, List.map_map, Function.comp_def] using h

theorem variance_shellSource_le (M : InsertionModel (S → C) U O C)
    (js : List S) (hcover : ∀ j, j ∈ js)
    (fU : U → C → ℝ) (fS : (S → C) → ℝ) (fO : O → ℝ) (a : S → ℝ)
    {s A : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hscore : BoundedScores s A (InsertionModel.additiveSource fU fS fO)
      (weightedCoordinateKeys js a) M.law) :
    variance M.shell (M.shellSource fU fS fO) ≤ A * (js.map (fun j => a j ^ 2)).sum := by
  have h := variance_conditionalSource_le js hcover M.shell M.conditionalLaw
    (InsertionModel.additiveSource fU fS fO) a hs hs1 hscore
  simp_rw [M.conditional_source] at h
  exact h

end
end ZeroFreeness.Appendix.Girth.Doob
