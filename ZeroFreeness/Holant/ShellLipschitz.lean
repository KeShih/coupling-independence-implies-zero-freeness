import ZeroFreeness.Holant.InstanceSeparator
import ZeroFreeness.Holant.SupportGeometry
import ZeroFreeness.Holant.CouplingTransport

/-! Single-coordinate exterior estimates imply the exact Lipschitz and
oscillation bounds on the structurally feasible common shell domain. -/
namespace ZeroFreeness.Holant
open Finset PottsCI HolantCoupling
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- Convert a Boolean assignment to its selected finite subset. -/
def selectedSubset (σ : E → Bool) : Finset E := univ.filter fun e => σ e = true

@[simp] theorem mem_selectedSubset (σ : E → Bool) (e : E) :
    e ∈ selectedSubset σ ↔ σ e = true := by simp [selectedSubset]

@[simp] theorem selectedSubset_decide (S : Finset E) :
    selectedSubset (fun e => decide (e ∈ S)) = S := by
  ext e
  simp

theorem decide_selectedSubset (σ : E → Bool) :
    (fun e => decide (e ∈ selectedSubset σ)) = σ := by
  funext e
  cases he : σ e <;> simp [he]

@[simp] theorem selectedSubset_update_true (σ : E → Bool) (e : E) :
    selectedSubset (Function.update σ e true) = insert e (selectedSubset σ) := by
  ext a
  by_cases h : a = e
  · subst a
    simp
  · simp [h]

@[simp] theorem selectedSubset_update_false (σ : E → Bool) (e : E) :
    selectedSubset (Function.update σ e false) = (selectedSubset σ).erase e := by
  ext a
  by_cases h : a = e
  · subst a
    simp
  · simp [h]

/-- Exactly one of two neighboring finite subsets is obtained by adding one
edge to the other. -/
theorem selectedSubset_adjacent_insert {σ τ : E → Bool} (hd : hamCard σ τ = 1) :
    (∃ a, a ∉ selectedSubset σ ∧ selectedSubset τ = insert a (selectedSubset σ)) ∨
    (∃ a, a ∉ selectedSubset τ ∧ selectedSubset σ = insert a (selectedSubset τ)) := by
  obtain ⟨a, ht⟩ := ZeroFreeness.exists_update_of_hamCard_eq_one hd
  have hne : σ a ≠ τ a := by
    intro h
    have hfun : σ = τ := by
      rw [ht, ← h, Function.update_eq_self]
    simp [hfun, hamCard_self] at hd
  cases hσ : σ a <;> cases hτ : τ a
  · exact (hne (by simp [hσ, hτ])).elim
  · left
    refine ⟨a, by simp [hσ], ?_⟩
    rw [ht, hτ, selectedSubset_update_true]
  · right
    refine ⟨a, by simp [hτ], ?_⟩
    rw [ht, hτ, selectedSubset_update_false,
      insert_erase (by simp [hσ])]
  · exact (hne (by simp [hσ, hτ])).elim

/-- Downward closure of actual structural shell states. -/
theorem shellStates_downward (H : NormalizedInstance V E) (S : Finset E)
    {ξ η : Finset E} (hξ : ξ ∈ H.shellStates S) (hηξ : η ⊆ ξ) :
    η ∈ H.shellStates S := by
  obtain ⟨hξS, hf⟩ := (H.mem_shellStates S ξ).1 hξ
  apply (H.mem_shellStates S η).2
  refine ⟨hηξ.trans hξS, ?_⟩
  exact feasible_downward H.incidence (realValues H.signature)
    (fun v _ _ hij hj => (H.signature v).initial_support hij hj) hηξ hf

namespace RootSeparator
variable {H : NormalizedInstance V E} {e : E} (P : RootSeparator H e)

theorem states_downward {ξ η : Finset E} (hξ : ξ ∈ P.states) (hηξ : η ⊆ ξ) :
    η ∈ P.states := shellStates_downward (H.zeroChild e) P.shell hξ hηξ

/-- The concrete common shell support expressed in Boolean coordinates. -/
def booleanStates : Set (E → Bool) := {σ | selectedSubset σ ∈ P.states}

theorem booleanStates_downward : BooleanDownwardClosed P.booleanStates := by
  intro σ τ hσ hτσ
  apply P.states_downward hσ
  intro a ha
  exact (mem_selectedSubset σ a).2 (hτσ a ((mem_selectedSubset τ a).1 ha))

/-- The insertion response estimate extends to Hamming distance on the
actual common support `P.State`, using only genuine feasible states. -/
theorem response_lipschitz (h : P.State → ℂ) {α : ℝ}
    (hstep : ∀ ξ η : P.State, ∀ a, a ∉ ξ.val → η.val = insert a ξ.val →
      ‖h η - h ξ‖ ≤ α) (ξ η : P.State) :
    ‖h ξ - h η‖ ≤ α * subsetHam ξ.val η.val := by
  let f : P.booleanStates → ℂ := fun σ => h ⟨selectedSubset σ.val, σ.property⟩
  have hf : ∀ σ τ : P.booleanStates, hamCard σ.val τ.val = 1 → ‖f σ - f τ‖ ≤ α := by
    intro σ τ hd
    rcases selectedSubset_adjacent_insert hd with ⟨a, ha, heq⟩ | ⟨a, ha, heq⟩
    · simpa only [f, norm_sub_rev] using
        hstep ⟨selectedSubset σ.val, σ.property⟩ ⟨selectedSubset τ.val, τ.property⟩ a ha heq
    · exact hstep ⟨selectedSubset τ.val, τ.property⟩ ⟨selectedSubset σ.val, σ.property⟩ a ha heq
  let ξ' : P.booleanStates := ⟨fun a => decide (a ∈ ξ.val), by
    change selectedSubset (fun a => decide (a ∈ ξ.val)) ∈ P.states
    simpa only [selectedSubset_decide] using ξ.property⟩
  let η' : P.booleanStates := ⟨fun a => decide (a ∈ η.val), by
    change selectedSubset (fun a => decide (a ∈ η.val)) ∈ P.states
    simpa only [selectedSubset_decide] using η.property⟩
  have hbound := norm_sub_le_ham_on_downward_support P.booleanStates_downward f hf ξ' η'
  simpa only [f, ξ', η', selectedSubset_decide, ← subsetHam_eq_ham] using hbound

/-- Because both states select only shell edges, their ambient subset-Hamming
distance is bounded by the number of actual shell variables. -/
theorem state_subsetHam_le_card (ξ η : P.State) : subsetHam ξ.val η.val ≤ P.shell.card := by
  unfold subsetHam
  have hpoint : ∀ a, (if a ∈ ξ.val ↔ a ∈ η.val then (0 : ℝ) else 1) ≤
      if a ∈ P.shell then 1 else 0 := by
    intro a
    by_cases ha : a ∈ P.shell
    · split_ifs <;> norm_num
    · have hξ : a ∉ ξ.val := fun hx => ha (P.state_subset ξ hx)
      have hη : a ∉ η.val := fun hx => ha (P.state_subset η hx)
      simp [ha, hξ, hη]
  calc
    _ ≤ ∑ a, if a ∈ P.shell then (1 : ℝ) else 0 := sum_le_sum fun a _ => hpoint a
    _ = P.shell.card := by simp

/-- The actual shell cardinality, rather than ambient edge count, controls
the oscillation used in the complex-average estimate. -/
theorem response_oscillation (h : P.State → ℂ) {α : ℝ} (hα : 0 ≤ α)
    (hstep : ∀ ξ η : P.State, ∀ a, a ∉ ξ.val → η.val = insert a ξ.val →
      ‖h η - h ξ‖ ≤ α) (ξ η : P.State) :
    ‖h ξ - h η‖ ≤ P.shell.card * α := by
  exact (P.response_lipschitz h hstep ξ η).trans
    (by simpa [mul_comm] using mul_le_mul_of_nonneg_left (P.state_subsetHam_le_card ξ η) hα)

end RootSeparator
end
end ZeroFreeness.Holant
