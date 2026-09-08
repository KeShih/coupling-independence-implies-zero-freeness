import CI2ZF.HolantResidualModel

/-!
# Adjacent shell exteriors are children of an actual smaller instance

Fix all common selected shell edges and keep only one changed shell edge
and the exterior free.  The resulting residual instance has as its two
normalized children exactly the two exterior partition functions.  Every
normalization denominator is justified by structural feasibility, and no
activity is assumed positive.
-/
namespace CI2ZF.Holant
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [DecidableEq E]

/-- The actual edge sets for one feasible shell-coordinate change. -/
structure ShellBridgeData (H : NormalizedInstance V E) where
  exterior : Finset E
  selected : Finset E
  changed : E
  changed_not_exterior : changed ∉ exterior
  changed_not_selected : changed ∉ selected
  free_subset : insert changed exterior ⊆ H.edges
  selected_subset : selected ⊆ H.edges
  disjoint : Disjoint selected (insert changed exterior)
  feasible : Feasible H.incidence (realValues H.signature) (insert changed selected)

namespace ShellBridgeData
variable {H : NormalizedInstance V E} (D : ShellBridgeData H)

/-- Removing the changed selected bit leaves a structurally feasible shell. -/
theorem selected_feasible : Feasible H.incidence (realValues H.signature) D.selected :=
  feasible_downward H.incidence (realValues H.signature)
    (fun v _ _ hij hj => (H.signature v).initial_support hij hj)
    (Finset.subset_insert _ _) D.feasible

theorem exterior_subset : D.exterior ⊆ H.edges :=
  (Finset.subset_insert _ _).trans D.free_subset

theorem upper_selected_subset : insert D.changed D.selected ⊆ H.edges :=
  Finset.insert_subset (D.free_subset (Finset.mem_insert_self _ _)) D.selected_subset

theorem upper_disjoint : Disjoint (insert D.changed D.selected) D.exterior := by
  apply Finset.disjoint_left.mpr
  intro e he ho
  rcases Finset.mem_insert.mp he with rfl | he
  · exact D.changed_not_exterior ho
  · exact Finset.disjoint_left.mp D.disjoint he (Finset.mem_insert_of_mem ho)

/-- The bridge instance fixes common selected shell bits and leaves exactly
one shell edge and the exterior free. -/
def bridge : NormalizedInstance V E :=
  H.exteriorInstance (insert D.changed D.exterior) D.selected
    (H.exterior_bound _ _ D.free_subset D.selected_subset D.disjoint) D.selected_feasible

def lowerExterior : NormalizedInstance V E :=
  H.exteriorInstance D.exterior D.selected
    (H.exterior_bound _ _ D.exterior_subset D.selected_subset
      (D.disjoint.mono_right (Finset.subset_insert _ _))) D.selected_feasible

def upperExterior : NormalizedInstance V E :=
  H.exteriorInstance D.exterior (insert D.changed D.selected)
    (H.exterior_bound _ _ D.exterior_subset D.upper_selected_subset D.upper_disjoint) D.feasible

@[simp] theorem bridge_edges : D.bridge.edges = insert D.changed D.exterior := rfl
@[simp] theorem lowerExterior_edges : D.lowerExterior.edges = D.exterior := rfl
@[simp] theorem upperExterior_edges : D.upperExterior.edges = D.exterior := rfl

theorem changed_mem_bridge : D.changed ∈ D.bridge.edges := Finset.mem_insert_self _ _

/-- Every involved signature stays in the fixed residual family. -/
theorem bridge_family (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (v : V) : D.bridge.signature v ∈ residualFamily F :=
  H.exteriorInstance_family F hF _ _ _ _ v

theorem lowerExterior_family (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (v : V) : D.lowerExterior.signature v ∈ residualFamily F :=
  H.exteriorInstance_family F hF _ _ _ _ v

theorem upperExterior_family (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (v : V) : D.upperExterior.signature v ∈ residualFamily F :=
  H.exteriorInstance_family F hF _ _ _ _ v

/-- Structural feasibility of the upper shell makes the bridge's one-child
survive at both endpoints, even when the changed activity is zero. -/
theorem bridge_one_survives : D.bridge.OneSurvives D.changed := by
  intro v hv
  change H.incidence D.changed v at hv
  have hdeg : selectedDegree H.incidence (insert D.changed D.exterior) v =
      selectedDegree H.incidence D.exterior v + 1 := by
    simp [selectedDegree_insert H.incidence D.changed D.exterior D.changed_not_exterior, hv]
  have hn : 0 < (H.signature v).value (selectedDegree H.incidence D.selected v + 1) := by
    simpa [realValues, selectedDegree_insert H.incidence D.changed D.selected
      D.changed_not_selected, hv] using D.feasible v
  change 0 < (if 1 ≤ selectedDegree H.incidence (insert D.changed D.exterior) v then
    (H.signature v).value (selectedDegree H.incidence D.selected v + 1) /
      (H.signature v).value (selectedDegree H.incidence D.selected v) else 0)
  rw [if_pos (by omega)]
  exact div_pos hn (D.selected_feasible v)

/-- The bridge omits the original root edge, and hence is strictly smaller
than its parent. This is the required strict induction measure. -/
theorem bridge_card_lt {root : E} (hroot : root ∈ H.edges)
    (hrootfree : root ∉ insert D.changed D.exterior) : D.bridge.edges.card < H.edges.card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨D.free_subset, ?_⟩
  intro heq
  exact hrootfree ((show insert D.changed D.exterior = H.edges from heq).symm ▸ hroot)

/-- The bridge's normalized zero-child is exactly the lower exterior
polynomial, as a function of all independent complex activities. -/
theorem zeroChild_complexPartition (z : E → ℂ) :
    (D.bridge.zeroChild D.changed).toInstance.complexPartition z =
      D.lowerExterior.toInstance.complexPartition z := by
  rw [NormalizedInstance.zeroChild_complexPartition]
  change partition H.incidence ((insert D.changed D.exterior).erase D.changed)
    (complexValues D.bridge.signature) z =
      partition H.incidence D.exterior (complexValues D.lowerExterior.signature) z
  rw [Finset.erase_insert D.changed_not_exterior]
  apply partition_congr_signatures
  intro v k hk
  have hk' : k ≤ selectedDegree H.incidence (insert D.changed D.exterior) v :=
    hk.trans (selectedDegree_mono H.incidence (Finset.subset_insert _ _) v)
  simp [complexValues, bridge, lowerExterior, NormalizedInstance.exteriorInstance,
    Signature.normalizedResidual, hk, hk']

/-- The bridge's normalized one-child is exactly the upper exterior;
normalizing twice cancels the common selected-shell scalar. -/
theorem oneChild_complexPartition (z : E → ℂ) :
    (D.bridge.oneChild D.changed D.changed_mem_bridge D.bridge_one_survives).toInstance.complexPartition z =
      D.upperExterior.toInstance.complexPartition z := by
  rw [NormalizedInstance.oneChild_complexPartition]
  change partition H.incidence ((insert D.changed D.exterior).erase D.changed)
    (normalizedChildSignature H.incidence (complexValues D.bridge.signature) D.changed) z =
      partition H.incidence D.exterior (complexValues D.upperExterior.signature) z
  rw [Finset.erase_insert D.changed_not_exterior]
  apply partition_congr_signatures
  intro v k hk
  have hbase : (H.signature v).value (selectedDegree H.incidence D.selected v) ≠ 0 :=
    (D.selected_feasible v).ne'
  by_cases hv : H.incidence D.changed v
  · have hdeg : selectedDegree H.incidence (insert D.changed D.exterior) v =
        selectedDegree H.incidence D.exterior v + 1 := by
      simp [selectedDegree_insert H.incidence D.changed D.exterior D.changed_not_exterior, hv]
    have hk1 : k + 1 ≤ selectedDegree H.incidence (insert D.changed D.exterior) v := by omega
    have h1 : 1 ≤ selectedDegree H.incidence (insert D.changed D.exterior) v := by omega
    simp only [normalizedChildSignature, complexValues, bridge, upperExterior,
      NormalizedInstance.exteriorInstance, Signature.normalizedResidual,
      if_pos hk1, if_pos h1, if_pos hk, Complex.ofReal_div,
      selectedDegree_insert H.incidence D.changed D.selected D.changed_not_selected,
      if_pos hv]
    rw [div_div_div_cancel_right₀ (by exact_mod_cast hbase)]
    rw [Nat.add_assoc, Nat.add_comm k 1]
  · have hdeg : selectedDegree H.incidence (insert D.changed D.exterior) v =
        selectedDegree H.incidence D.exterior v := by
      simp [selectedDegree_insert H.incidence D.changed D.exterior D.changed_not_exterior, hv]
    simp [normalizedChildSignature, complexValues, bridge, upperExterior,
      NormalizedInstance.exteriorInstance, Signature.normalizedResidual,
      selectedDegree_insert H.incidence D.changed D.selected D.changed_not_selected,
      hv, hdeg, hk]

/-- Real normalizing denominators are identified by the same exact identities. -/
theorem zeroChild_realPartition (x : E → ℝ) :
    (D.bridge.zeroChild D.changed).toInstance.realPartition x =
      D.lowerExterior.toInstance.realPartition x := by
  apply Complex.ofReal_injective
  simpa only [← Instance.complexPartition_ofReal] using
    D.zeroChild_complexPartition (fun e => (x e : ℂ))

theorem oneChild_realPartition (x : E → ℝ) :
    (D.bridge.oneChild D.changed D.changed_mem_bridge D.bridge_one_survives).toInstance.realPartition x =
      D.upperExterior.toInstance.realPartition x := by
  apply Complex.ofReal_injective
  simpa only [← Instance.complexPartition_ofReal] using
    D.oneChild_complexPartition (fun e => (x e : ℂ))

/-- Therefore the exact normalized exterior quotient is an inductive child
quotient on a strictly smaller actual residual instance. -/
theorem exterior_quotient_eq_child_quotient (z : E → ℂ) (x : E → ℝ) :
    (D.upperExterior.toInstance.complexPartition z /
        (D.upperExterior.toInstance.realPartition x : ℂ)) /
      (D.lowerExterior.toInstance.complexPartition z /
        (D.lowerExterior.toInstance.realPartition x : ℂ)) =
    ((D.bridge.oneChild D.changed D.changed_mem_bridge D.bridge_one_survives).toInstance.complexPartition z /
        ((D.bridge.oneChild D.changed D.changed_mem_bridge D.bridge_one_survives).toInstance.realPartition x : ℂ)) /
      ((D.bridge.zeroChild D.changed).toInstance.complexPartition z /
        ((D.bridge.zeroChild D.changed).toInstance.realPartition x : ℂ)) := by
  rw [D.oneChild_complexPartition, D.zeroChild_complexPartition,
    D.oneChild_realPartition, D.zeroChild_realPartition]

end ShellBridgeData
end
end CI2ZF.Holant
