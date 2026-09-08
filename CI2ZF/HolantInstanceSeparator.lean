import CI2ZF.HolantResidualModel
import CI2ZF.HolantCouplingGibbs

/-!
# Root separator packets with actual residual exterior instances

The common shell domain is the structurally feasible zero-child support.
Both children expand on this same finite domain; impossible one-child terms
are exactly zero.  Exterior objects are actual normalized residual instances.
-/

namespace CI2ZF.Holant
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq E]

namespace NormalizedInstance

theorem oneChild_signature_eq_zeroChild_off_root (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e) (v : V) (hv : ¬ H.incidence e v) :
    (H.oneChild e he hs).signature v = (H.zeroChild e).signature v := by
  simp only [oneChild, zeroChild, if_neg hv]

theorem oneChild_value_le_zeroChild (H : NormalizedInstance V E) (e : E)
    (he : e ∈ H.edges) (hs : H.OneSurvives e) (v : V) (k : ℕ) :
    ((H.oneChild e he hs).signature v).value k ≤ ((H.zeroChild e).signature v).value k := by
  by_cases hk : k ≤ selectedDegree H.incidence (H.edges.erase e) v
  · by_cases hv : H.incidence e v
    · simpa only [oneChild, zeroChild, Signature.normalizedResidual_value, if_pos hk,
        if_pos hv, zero_add, H.normalized, div_one, Nat.add_comm] using
        (H.signature v).first_shift_le (H.normalized v) (hs v hv) k
    · rw [H.oneChild_signature_eq_zeroChild_off_root e he hs v hv]
  · simp only [oneChild, zeroChild, Signature.normalizedResidual_value, if_neg hk, le_refl]

/-- Finite structurally feasible shell configurations, with no activity test. -/
def shellStates (H : NormalizedInstance V E) (S : Finset E) : Finset (Finset E) :=
  S.powerset.filter (Feasible H.incidence (realValues H.signature))

@[simp] theorem mem_shellStates (H : NormalizedInstance V E) (S ξ : Finset E) :
    ξ ∈ H.shellStates S ↔ ξ ⊆ S ∧ Feasible H.incidence (realValues H.signature) ξ := by
  simp [shellStates]

theorem empty_mem_shellStates (H : NormalizedInstance V E) (S : Finset E) :
    ∅ ∈ H.shellStates S :=
  (H.mem_shellStates S ∅).2 ⟨Finset.empty_subset S,
    feasible_empty H.incidence _ (fun v => (H.signature v).zero_pos)⟩

end NormalizedInstance

/-- The data furnished by an interaction-graph shell around the root edge. -/
structure RootSeparator (H : NormalizedInstance V E) (e : E) where
  interior : Finset E
  shell : Finset E
  exterior : Finset E
  shell_interior : Disjoint shell interior
  shell_exterior : Disjoint shell exterior
  interior_exterior : Disjoint interior exterior
  cover : shell ∪ (interior ∪ exterior) = H.edges.erase e
  separated : EdgeSeparated H.incidence interior exterior
  root_exterior : ∀ v, ExteriorVertex H.incidence exterior v → ¬ H.incidence e v

namespace RootSeparator
variable {H : NormalizedInstance V E} {e : E}

def child (_P : RootSeparator H e) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (b : Bool) : NormalizedInstance V E := if b then H.oneChild e he hs else H.zeroChild e

@[simp] theorem child_incidence (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) : (P.child he hs b).incidence = H.incidence := by
  cases b <;> rfl

@[simp] theorem child_edges (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) : (P.child he hs b).edges = H.edges.erase e := by
  cases b <;> rfl

/-- Common domain `Xi_0`; the one-child law will have zero mass at its
structurally impossible states. -/
def states (P : RootSeparator H e) : Finset (Finset E) := (H.zeroChild e).shellStates P.shell

abbrev State (P : RootSeparator H e) := ↥P.states

theorem state_subset (P : RootSeparator H e) (ξ : P.State) : ξ.val ⊆ P.shell :=
  ((H.zeroChild e).mem_shellStates P.shell ξ.val).1 ξ.property |>.1

theorem state_feasible (P : RootSeparator H e) (ξ : P.State) :
    Feasible H.incidence (realValues (H.zeroChild e).signature) ξ.val :=
  ((H.zeroChild e).mem_shellStates P.shell ξ.val).1 ξ.property |>.2

def emptyState (P : RootSeparator H e) : P.State :=
  ⟨∅, (H.zeroChild e).empty_mem_shellStates P.shell⟩

instance (P : RootSeparator H e) : Nonempty P.State := ⟨P.emptyState⟩

theorem exterior_subset (P : RootSeparator H e) : P.exterior ⊆ (H.zeroChild e).edges := by
  rw [NormalizedInstance.zeroChild_edges, ← P.cover]
  exact Finset.subset_union_right.trans Finset.subset_union_right

theorem shell_subset (P : RootSeparator H e) : P.shell ⊆ (H.zeroChild e).edges := by
  rw [NormalizedInstance.zeroChild_edges, ← P.cover]
  exact Finset.subset_union_left

/-- The actual normalized exterior instance at a common shell state. -/
def exteriorInstance (P : RootSeparator H e) (ξ : P.State) : NormalizedInstance V E :=
  (H.zeroChild e).exteriorInstance P.exterior ξ.val
    ((H.zeroChild e).exterior_bound P.exterior ξ.val P.exterior_subset
      ((P.state_subset ξ).trans P.shell_subset)
      (P.shell_exterior.mono_left (P.state_subset ξ))) (P.state_feasible ξ)

@[simp] theorem exteriorInstance_edges (P : RootSeparator H e) (ξ : P.State) :
    (P.exteriorInstance ξ).edges = P.exterior := rfl

theorem exteriorInstance_family (P : RootSeparator H e) (F : Finset Signature)
    (hF : ∀ v, H.signature v ∈ residualFamily F) (ξ : P.State) (v : V) :
    (P.exteriorInstance ξ).signature v ∈ residualFamily F :=
  (H.zeroChild e).exteriorInstance_family F (H.zeroChild_family F hF e) _ _ _ _ v

def coefficientReal (P : RootSeparator H e) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (b : Bool) (ξ : P.State) (x : E → ℝ) : ℝ :=
  separatorCoefficient H.incidence P.interior P.exterior ξ.val
    (realValues (P.child he hs b).signature) x

def coefficientComplex (P : RootSeparator H e) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (b : Bool) (ξ : P.State) (z : E → ℂ) : ℂ :=
  separatorCoefficient H.incidence P.interior P.exterior ξ.val
    (complexValues (P.child he hs b).signature) z

/-- Exterior signatures are common to both actual children at all arguments. -/
theorem exterior_signature_common (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (ξ : Finset E) :
    exteriorSignature H.incidence P.exterior ξ (complexValues (P.child he hs b).signature) =
      exteriorSignature H.incidence P.exterior ξ (complexValues (H.zeroChild e).signature) := by
  cases b with
  | false => rfl
  | true =>
    funext v k
    unfold exteriorSignature
    split_ifs with hv
    · simp only [child, ↓reduceIte, complexValues,
        H.oneChild_signature_eq_zeroChild_off_root e he hs v (P.root_exterior v hv)]
    · rfl

/-- Structural one-child support is contained in the common zero-child support. -/
theorem survives_imp_common (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (ξ : Finset E)
    (hξ : ShellSurvives H.incidence (complexValues (P.child he hs b).signature) ξ) :
    ShellSurvives H.incidence (complexValues (H.zeroChild e).signature) ξ := by
  rw [shell_survives_iff_feasible] at hξ ⊢
  cases b with
  | false => exact hξ
  | true =>
    intro v
    exact lt_of_lt_of_le (hξ v) (H.oneChild_value_le_zeroChild e he hs v _)

/-- The finite-subset separator identity rewritten on the common typed shell
space with actual normalized residual exterior polynomials. -/
theorem complexPartition_expansion (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (z : E → ℂ) :
    (P.child he hs b).toInstance.complexPartition z =
      ∑ ξ : P.State, P.coefficientComplex he hs b ξ z *
        (P.exteriorInstance ξ).toInstance.complexPartition z := by
  unfold Instance.complexPartition
  rw [P.child_incidence, P.child_edges, ← P.cover,
    partition_separator H.incidence P.interior P.shell P.exterior _ z
      P.shell_interior P.shell_exterior P.interior_exterior P.separated
      (signature_complex_zero_tail _)]
  simp_rw [P.exterior_signature_common he hs b]
  trans ∑ ξ ∈ P.states, separatorCoefficient H.incidence P.interior P.exterior ξ
    (complexValues (P.child he hs b).signature) z *
      partition H.incidence P.exterior
        (exteriorSignature H.incidence P.exterior ξ (complexValues (H.zeroChild e).signature)) z
  · symm
    apply Finset.sum_filter_of_ne
    intro ξ _ hn
    rw [← shell_survives_iff_feasible]
    by_contra hf
    have hdead : ¬ ShellSurvives H.incidence (complexValues (P.child he hs b).signature) ξ :=
      fun h => hf (P.survives_imp_common he hs b ξ h)
    exact hn (by rw [separatorCoefficient_zero_of_not_survives _ _ _ _ _ _
      (signature_complex_zero_tail _) hdead, zero_mul])
  · rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro ξ _
    change _ = P.coefficientComplex he hs b ξ z *
      (P.exteriorInstance ξ).toInstance.complexPartition z
    have hq := (H.zeroChild e).exteriorInstance_complexPartition P.exterior ξ.val
      ((H.zeroChild e).exterior_bound P.exterior ξ.val P.exterior_subset
        ((P.state_subset ξ).trans P.shell_subset)
        (P.shell_exterior.mono_left (P.state_subset ξ))) (P.state_feasible ξ) z
    change (P.exteriorInstance ξ).toInstance.complexPartition z = _ at hq
    rw [hq]
    rfl

/-- Complex coefficients agree with their real evaluations coordinatewise. -/
theorem coefficientComplex_ofReal (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (ξ : P.State) (x : E → ℝ) :
    P.coefficientComplex he hs b ξ (fun e => (x e : ℂ)) =
      (P.coefficientReal he hs b ξ x : ℂ) := by
  simp [coefficientComplex, coefficientReal, separatorCoefficient, partition, weight,
    signatureWeight, complexValues, realValues, interiorSignature, apply_ite Complex.ofReal]

theorem realPartition_expansion (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ) :
    (P.child he hs b).toInstance.realPartition x =
      ∑ ξ : P.State, P.coefficientReal he hs b ξ x *
        (P.exteriorInstance ξ).toInstance.realPartition x := by
  have h := P.complexPartition_expansion he hs b (fun e => (x e : ℂ))
  simp_rw [Instance.complexPartition_ofReal, P.coefficientComplex_ofReal] at h
  exact_mod_cast h

theorem interior_subset (P : RootSeparator H e) : P.interior ⊆ H.edges.erase e := by
  rw [← P.cover]
  exact Finset.subset_union_left.trans Finset.subset_union_right

theorem coefficientReal_nonneg (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (ξ : P.State) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) : 0 ≤ P.coefficientReal he hs b ξ x := by
  apply separatorCoefficient_nonneg
  · exact fun v k => ((P.child he hs b).signature v).nonneg k
  · exact fun a ha => hx a (P.interior_subset ha)
  · exact fun a ha => hx a (P.shell_subset (P.state_subset ξ ha))

theorem child_real_pos (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    0 < (P.child he hs b).toInstance.realPartition x :=
  (P.child he hs b).toInstance.realPartition_pos x (by simpa using hx)

theorem exterior_real_pos (P : RootSeparator H e) (ξ : P.State) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    0 < (P.exteriorInstance ξ).toInstance.realPartition x :=
  (P.exteriorInstance ξ).toInstance.realPartition_pos x
    (fun a ha => hx a (P.exterior_subset ha))

/-- The exact real shell masses on the common feasible shell space. -/
def law (P : RootSeparator H e) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (b : Bool) (x : E → ℝ) (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) :
    PottsCI.FinDist P.State where
  w ξ := P.coefficientReal he hs b ξ x *
    (P.exteriorInstance ξ).toInstance.realPartition x /
      (P.child he hs b).toInstance.realPartition x
  nonneg ξ := div_nonneg
    (mul_nonneg (P.coefficientReal_nonneg he hs b ξ x hx) (P.exterior_real_pos ξ x hx).le)
    (P.child_real_pos he hs b x hx).le
  sum_one := by
    rw [← Finset.sum_div, ← P.realPartition_expansion he hs b x,
      div_self (P.child_real_pos he hs b x hx).ne']

/-- The additive error never divides by a local coefficient, so zero
activities and zero real local coefficients cause no singularity. -/
def localError (P : RootSeparator H e) (he : e ∈ H.edges) (hs : H.OneSurvives e)
    (b : Bool) (ξ : P.State) (x : E → ℝ) (z : E → ℂ) : ℂ :=
  (P.coefficientComplex he hs b ξ z - (P.coefficientReal he hs b ξ x : ℂ)) *
    (P.exteriorInstance ξ).toInstance.complexPartition z /
      ((P.child he hs b).toInstance.realPartition x : ℂ)

/-- The exact normalized response is `M + E`, with `M` averaged against the
actual real shell weights and `E` additive in local coefficients. -/
theorem response_eq_average_add_error (P : RootSeparator H e) (he : e ∈ H.edges)
    (hs : H.OneSurvives e) (b : Bool) (x : E → ℝ)
    (hx : ∀ a ∈ H.edges.erase e, 0 ≤ x a) (z : E → ℂ) :
    (P.child he hs b).toInstance.complexPartition z /
        ((P.child he hs b).toInstance.realPartition x : ℂ) =
      (∑ ξ : P.State, ((P.law he hs b x hx).w ξ : ℂ) *
        ((P.exteriorInstance ξ).toInstance.complexPartition z /
          ((P.exteriorInstance ξ).toInstance.realPartition x : ℂ))) +
      ∑ ξ : P.State, P.localError he hs b ξ x z := by
  rw [P.complexPartition_expansion, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ξ _
  have hq : ((P.exteriorInstance ξ).toInstance.realPartition x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (P.exterior_real_pos ξ x hx).ne'
  have hp : ((P.child he hs b).toInstance.realPartition x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (P.child_real_pos he hs b x hx).ne'
  simp only [law, localError, Complex.ofReal_div, Complex.ofReal_mul]
  field_simp
  ring

end RootSeparator
end
end CI2ZF.Holant
