import ZeroFreeness.Holant.ShellAdjacency
import ZeroFreeness.Holant.ShellLipschitz
import ZeroFreeness.Holant.Paths

/-!
# The genuine inductive exterior response

Construct analytic normalized logarithms of the actual exterior partitions.
For two feasible shell assignments differing by one edge, their logarithm
difference is a response of an actual smaller residual instance.  Applying
the smaller-instance induction hypothesis yields the shell Lipschitz and
oscillation estimates rather than assuming those estimates.
-/
namespace ZeroFreeness.Holant
open Finset PottsCI HolantCoupling Set Metric
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

namespace RootSeparator
variable {H : NormalizedInstance V E} {e : E} (P : RootSeparator H e)

theorem exterior_parent_subset : P.exterior ⊆ H.edges :=
  P.exterior_subset.trans (Finset.erase_subset e H.edges)

theorem exterior_card_lt (he : e ∈ H.edges) : P.exterior.card < H.edges.card :=
  (Finset.card_le_card P.exterior_subset).trans_lt (H.zeroChild_card_lt e he)

/-- Turn a concrete feasible single-shell-edge insertion into bridge data. -/
def adjacentBridgeData (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) : ShellBridgeData (H.zeroChild e) where
  exterior := P.exterior
  selected := ξ.val
  changed := a
  changed_not_exterior := by
    have haS : a ∈ P.shell := P.state_subset η (by rw [hη]; simp)
    exact fun haO => Finset.disjoint_left.mp P.shell_exterior haS haO
  changed_not_selected := ha
  free_subset := by
    apply Finset.insert_subset
    · apply P.shell_subset
      exact P.state_subset η (by rw [hη]; simp)
    · exact P.exterior_subset
  selected_subset := (P.state_subset ξ).trans P.shell_subset
  disjoint := by
    apply Finset.disjoint_insert_right.mpr
    exact ⟨ha, P.shell_exterior.mono_left (P.state_subset ξ)⟩
  feasible := by
    rw [← hη]
    exact P.state_feasible η

def adjacentBridge (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) : NormalizedInstance V E :=
  (P.adjacentBridgeData ξ η a ha hη).bridge

@[simp] theorem adjacentBridge_incidence (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) :
    (P.adjacentBridge ξ η a ha hη).incidence = H.incidence := rfl

@[simp] theorem adjacentBridge_edges (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) :
    (P.adjacentBridge ξ η a ha hη).edges = insert a P.exterior := rfl

theorem adjacentBridge_subset (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) :
    (P.adjacentBridge ξ η a ha hη).edges ⊆ H.edges :=
  (P.adjacentBridgeData ξ η a ha hη).free_subset.trans (Finset.erase_subset e H.edges)

theorem adjacentBridge_card_lt (he : e ∈ H.edges) (ξ η : P.State) (a : E)
    (ha : a ∉ ξ.val) (hη : η.val = insert a ξ.val) :
    (P.adjacentBridge ξ η a ha hη).edges.card < H.edges.card :=
  (Finset.card_le_card (P.adjacentBridgeData ξ η a ha hη).free_subset).trans_lt
    (H.zeroChild_card_lt e he)

theorem adjacentBridge_family (F : Finset Signature) (hF : ∀ v, H.signature v ∈ residualFamily F)
    (ξ η : P.State) (a : E) (ha : a ∉ ξ.val) (hη : η.val = insert a ξ.val)
    (v : V) : (P.adjacentBridge ξ η a ha hη).signature v ∈ residualFamily F :=
  (P.adjacentBridgeData ξ η a ha hη).bridge_family F (H.zeroChild_family F hF e) v

theorem adjacentBridge_mem (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) : a ∈ (P.adjacentBridge ξ η a ha hη).edges :=
  (P.adjacentBridgeData ξ η a ha hη).changed_mem_bridge

theorem adjacentBridge_survives (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) : (P.adjacentBridge ξ η a ha hη).OneSurvives a :=
  (P.adjacentBridgeData ξ η a ha hη).bridge_one_survives

theorem adjacentBridge_lower_eq (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) :
    (P.adjacentBridgeData ξ η a ha hη).lowerExterior = P.exteriorInstance ξ := rfl

theorem adjacentBridge_upper_eq (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) :
    (P.adjacentBridgeData ξ η a ha hη).upperExterior = P.exteriorInstance η := by
  rcases η with ⟨η, hηstate⟩
  dsimp only at hη
  subst η
  rfl

/-- The adjacent exterior quotient is literally the bridge child quotient. -/
theorem adjacent_exterior_quotient (ξ η : P.State) (a : E) (ha : a ∉ ξ.val)
    (hη : η.val = insert a ξ.val) (z : E → ℂ) (x : E → ℝ) :
    ((P.exteriorInstance η).toInstance.complexPartition z /
      ((P.exteriorInstance η).toInstance.realPartition x : ℂ)) /
    ((P.exteriorInstance ξ).toInstance.complexPartition z /
      ((P.exteriorInstance ξ).toInstance.realPartition x : ℂ)) =
    (((P.adjacentBridge ξ η a ha hη).oneChild a (P.adjacentBridge_mem ξ η a ha hη)
      (P.adjacentBridge_survives ξ η a ha hη)).toInstance.complexPartition z /
      (((P.adjacentBridge ξ η a ha hη).oneChild a (P.adjacentBridge_mem ξ η a ha hη)
        (P.adjacentBridge_survives ξ η a ha hη)).toInstance.realPartition x : ℂ)) /
    (((P.adjacentBridge ξ η a ha hη).zeroChild a).toInstance.complexPartition z /
      (((P.adjacentBridge ξ η a ha hη).zeroChild a).toInstance.realPartition x : ℂ)) := by
  have h := (P.adjacentBridgeData ξ η a ha hη).exterior_quotient_eq_child_quotient z x
  rw [P.adjacentBridge_lower_eq, P.adjacentBridge_upper_eq] at h
  exact h

/-- Construct the analytic exterior logarithms and prove the full Hamming
response estimates from the strong-induction hypotheses on smaller instances. -/
theorem exists_inductive_exterior_logs (he : e ∈ H.edges) (F : Finset Signature)
    (hF : ∀ v, H.signature v ∈ residualFamily F) {R ε α : ℝ} (hα : 0 ≤ α)
    (p : ActivityPath H.edges R ε)
    (hsmallNZ : ∀ K : NormalizedInstance V E, K.incidence = H.incidence →
      K.edges ⊆ H.edges → K.edges.card < H.edges.card →
      (∀ v, K.signature v ∈ residualFamily F) →
      ∀ t ∈ ball (0 : ℂ) p.radius, K.toInstance.complexPartition (p.activity t) ≠ 0)
    (hsmallResponse : ∀ K : NormalizedInstance V E, K.incidence = H.incidence →
      ∀ hK : K.edges ⊆ H.edges, K.edges.card < H.edges.card →
      (∀ v, K.signature v ∈ residualFamily F) →
      ∀ a (ha : a ∈ K.edges) (hs : K.OneSurvives a),
      ResponseBound K a ha hs (p.restrict hK) α) :
    ∃ h : P.State → ℂ → ℂ,
      (∀ ξ, DifferentiableOn ℂ (h ξ) (ball 0 p.radius)) ∧
      (∀ ξ, h ξ 0 = 0) ∧
      (∀ ξ t, t ∈ ball 0 p.radius → Complex.exp (h ξ t) =
        (P.exteriorInstance ξ).toInstance.complexPartition (p.activity t) /
          ((P.exteriorInstance ξ).toInstance.realPartition p.base : ℂ)) ∧
      (∀ t ∈ ball 0 p.radius, ∀ ξ η,
        ‖h ξ t - h η t‖ ≤ α * subsetHam ξ.val η.val) ∧
      (∀ t ∈ ball 0 p.radius, ∀ ξ η,
        ‖h ξ t - h η t‖ ≤ P.shell.card * α) := by
  have hlogs : ∀ ξ : P.State, ∃ L : ℂ → ℂ,
      DifferentiableOn ℂ L (ball 0 p.radius) ∧ L 0 = 0 ∧
      ∀ t ∈ ball 0 p.radius, Complex.exp (L t) =
        (P.exteriorInstance ξ).toInstance.complexPartition (p.activity t) /
          ((P.exteriorInstance ξ).toInstance.realPartition p.base : ℂ) := by
    intro ξ
    have hn := hsmallNZ (P.exteriorInstance ξ) rfl P.exterior_parent_subset
      (P.exterior_card_lt he) (P.exteriorInstance_family F hF ξ)
    have hd := (p.restrict P.exterior_parent_subset).instance_differentiable
      (P.exteriorInstance ξ).toInstance
    obtain ⟨L, hL0, hL, heL⟩ := ZeroFreeness.exists_normalized_log_on_ball
      (fun t => (P.exteriorInstance ξ).toInstance.complexPartition (p.activity t))
      p.radius_pos hd hn
    refine ⟨L, (fun t ht => (hL t ht).differentiableAt.differentiableWithinAt), hL0, ?_⟩
    intro t ht
    rw [heL t ht]
    congr 1
    exact (p.restrict P.exterior_parent_subset).instance_at_zero (P.exteriorInstance ξ).toInstance
  choose h hd hzero hexp using hlogs
  have hstep : ∀ t ∈ ball (0 : ℂ) p.radius, ∀ ξ η : P.State, ∀ a,
      a ∉ ξ.val → η.val = insert a ξ.val → ‖h η t - h ξ t‖ ≤ α := by
    intro t ht ξ η a ha hη
    have hR := hsmallResponse (P.adjacentBridge ξ η a ha hη) rfl
      (P.adjacentBridge_subset ξ η a ha hη) (P.adjacentBridge_card_lt he ξ η a ha hη)
      (P.adjacentBridge_family F hF ξ η a ha hη)
      a (P.adjacentBridge_mem ξ η a ha hη) (P.adjacentBridge_survives ξ η a ha hη)
    apply hR (fun s => h η s - h ξ s) ((hd η).sub (hd ξ))
      (by simp [hzero]) ?_ t ht
    intro s hs
    rw [Complex.exp_sub, hexp η s hs, hexp ξ s hs]
    exact P.adjacent_exterior_quotient ξ η a ha hη (p.activity s) p.base
  refine ⟨h, hd, hzero, hexp, ?_, ?_⟩
  · intro t ht ξ η
    exact P.response_lipschitz (fun ξ => h ξ t) (hstep t ht) ξ η
  · intro t ht ξ η
    exact P.response_oscillation (fun ξ => h ξ t) hα (hstep t ht) ξ η

end RootSeparator
end
end ZeroFreeness.Holant
