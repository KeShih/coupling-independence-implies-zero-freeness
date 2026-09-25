import ZeroFreeness.Holant.Signatures
import ZeroFreeness.Holant.Model

/-!
# Uniform bounds for actual Holant coefficients

Double counting selected incidences gives total selected degree twice the
number of selected edges in a simple graph.  A single finite-family growth
constant consequently bounds coefficients independently of isolated vertices
and of the total vertex count.
-/
namespace ZeroFreeness.Holant
open Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [DecidableEq E]

/-- Count selected incidences first by vertices and then by edges. -/
theorem sum_selectedDegree_eq (inc : E → V → Prop) (S : Finset E) :
    (∑ v, selectedDegree inc S v) =
      ∑ e ∈ S, (univ.filter fun v => inc e v).card := by
  simp only [selectedDegree, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Each selected edge has two endpoints, so the total selected degree is
exactly twice the selected-edge count. -/
theorem sum_selectedDegree_eq_twice (inc : E → V → Prop) (S : Finset E)
    (htwo : ∀ e ∈ S, (univ.filter fun v => inc e v).card = 2) :
    (∑ v, selectedDegree inc S v) = 2 * S.card := by
  rw [sum_selectedDegree_eq]
  calc
    (∑ e ∈ S, (univ.filter fun v => inc e v).card) = ∑ _e ∈ S, 2 :=
      sum_congr rfl (fun e he => htwo e he)
    _ = 2 * S.card := by simp [Nat.mul_comm]

/-- The coefficient bound uses only the residual family and selected degree. -/
theorem signatureWeight_le_growthBound (F : Finset Signature)
    (inc : E → V → Prop) (g : V → Signature)
    (hg : ∀ v, g v ∈ residualFamily F) (S : Finset E) :
    signatureWeight inc (fun v => (g v).value) S ≤
      residualGrowthBound F ^ (∑ v, selectedDegree inc S v) := by
  unfold signatureWeight
  calc
    (∏ v, (g v).value (selectedDegree inc S v)) ≤
        ∏ v, residualGrowthBound F ^ selectedDegree inc S v :=
      prod_le_prod (fun v _ => (g v).nonneg _)
        (fun v _ => residual_value_le_pow_growthBound F (hg v) _)
    _ = residualGrowthBound F ^ (∑ v, selectedDegree inc S v) :=
      prod_pow_eq_pow_sum _ _ _

theorem signatureWeight_le_growthBound_twice (F : Finset Signature)
    (inc : E → V → Prop) (g : V → Signature)
    (hg : ∀ v, g v ∈ residualFamily F) (S : Finset E)
    (htwo : ∀ e ∈ S, (univ.filter fun v => inc e v).card = 2) :
    signatureWeight inc (fun v => (g v).value) S ≤
      residualGrowthBound F ^ (2 * S.card) := by
  simpa [sum_selectedDegree_eq_twice inc S htwo] using
    signatureWeight_le_growthBound F inc g hg S

theorem signatureWeight_le_growthBound_of_card (F : Finset Signature)
    (inc : E → V → Prop) (g : V → Signature)
    (hg : ∀ v, g v ∈ residualFamily F) (S : Finset E)
    (htwo : ∀ e ∈ S, (univ.filter fun v => inc e v).card = 2)
    {N : ℕ} (hN : S.card ≤ N) :
    signatureWeight inc (fun v => (g v).value) S ≤
      residualGrowthBound F ^ (2 * N) :=
  (signatureWeight_le_growthBound_twice F inc g hg S htwo).trans
    (pow_le_pow_right₀ (residualGrowthBound_one_le F) (by omega))

section Graph
variable [DecidableEq V]

/-- An actual simple-graph edge has exactly two different endpoints. -/
theorem graph_edge_two_endpoints (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    (univ.filter fun v => graphIncidence e v).card = 2 := by
  rcases e with ⟨u, v⟩
  have huv : G.Adj u v := by simpa using he
  have hs : (univ.filter fun w => graphIncidence s(u, v) w) = {u, v} := by
    ext w
    simp [graphIncidence, Sym2.mem_iff]
  rw [hs, card_pair huv.ne]

theorem graph_sum_selectedDegree (G : SimpleGraph V) (S : Finset (Sym2 V))
    (hS : S ⊆ G.edgeFinset) :
    (∑ v, selectedDegree graphIncidence S v) = 2 * S.card :=
  sum_selectedDegree_eq_twice graphIncidence S
    (fun e he => graph_edge_two_endpoints G e (hS he))

/-- Uniform coefficient bounds for the exact graph polynomial. -/
theorem graph_signatureWeight_le (F : Finset Signature) (G : SimpleGraph V)
    (g : V → Signature) (hg : ∀ v, g v ∈ residualFamily F)
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) :
    signatureWeight graphIncidence (fun v => (g v).value) S ≤
      residualGrowthBound F ^ (2 * S.card) :=
  signatureWeight_le_growthBound_twice F graphIncidence g hg S
    (fun e he => graph_edge_two_endpoints G e (hS he))

theorem graph_signatureWeight_le_of_card (F : Finset Signature) (G : SimpleGraph V)
    (g : V → Signature) (hg : ∀ v, g v ∈ residualFamily F)
    (S : Finset (Sym2 V)) (hS : S ⊆ G.edgeFinset) {N : ℕ}
    (hN : G.edgeFinset.card ≤ N) :
    signatureWeight graphIncidence (fun v => (g v).value) S ≤
      residualGrowthBound F ^ (2 * N) :=
  signatureWeight_le_growthBound_of_card F graphIncidence g hg S
    (fun e he => graph_edge_two_endpoints G e (hS he)) ((card_le_card hS).trans hN)

end Graph
end
end ZeroFreeness.Holant
