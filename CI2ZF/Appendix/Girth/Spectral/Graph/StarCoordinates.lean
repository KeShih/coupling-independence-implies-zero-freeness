import CI2ZF.Appendix.Girth.Spectral.Graph.HeatBathWeights
import CI2ZF.Appendix.Girth.Geometry

/-! Actual star coordinates and the incident weights after fixing its exterior. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace GraphStar
abbrev Leaf (I : PinningData V C) (v : V) := {u : V // I.graph.Adj v u}
local instance (priority := 2000) graphStarCoordinatesLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _
abbrev Configuration (I : PinningData V C) (v : V) := Option (Leaf I v) → C

def vertex (I : PinningData V C) (v : V) : Option (Leaf I v) → V
  | none => v
  | some u => u.val

def restrict (I : PinningData V C) (v : V) (σ : V → C) : Configuration I v :=
  fun i => σ (vertex I v i)

def extend (I : PinningData V C) (v : V) (σ : V → C) (τ : Configuration I v) : V → C :=
  fun u => if u = v then τ none else if h : I.graph.Adj v u then τ (some ⟨u,h⟩) else σ u

@[simp] theorem extend_root (I : PinningData V C) (v : V) (σ : V → C) (τ : Configuration I v) :
    extend I v σ τ v = τ none := by simp [extend]

@[simp] theorem extend_leaf (I : PinningData V C) (v : V) (σ : V → C)
    (τ : Configuration I v) (u : Leaf I v) : extend I v σ τ u.val = τ (some u) := by
  have hu : I.graph.Adj v u.val := u.property
  simp [extend, hu, Ne.symm hu.ne]

@[simp] theorem extend_outside (I : PinningData V C) (v : V) (σ : V → C)
    (τ : Configuration I v) (u : V) (hu : u ≠ v) (hv : ¬ I.graph.Adj v u) :
    extend I v σ τ u = σ u := by simp [extend, hu, hv]

@[simp] theorem extend_vertex (I : PinningData V C) (v : V) (σ : V → C)
    (τ : Configuration I v) (i : Option (Leaf I v)) : extend I v σ τ (vertex I v i) = τ i := by
  cases i with
  | none => exact extend_root I v σ τ
  | some u => exact extend_leaf I v σ τ u

@[simp] theorem restrict_extend (I : PinningData V C) (v : V) (σ : V → C)
    (τ : Configuration I v) : restrict I v (extend I v σ τ) = τ := by
  funext i
  exact extend_vertex I v σ τ i

@[simp] theorem extend_restrict (I : PinningData V C) (v : V) (σ : V → C) :
    extend I v σ (restrict I v σ) = σ := by
  funext u
  by_cases hu : u = v
  · subst u; simp [restrict, vertex]
  · by_cases hv : I.graph.Adj v u
    · simpa [restrict, vertex] using extend_leaf I v σ (restrict I v σ) ⟨u,hv⟩
    · exact extend_outside I v σ (restrict I v σ) u hu hv

@[simp] theorem extend_extend (I : PinningData V C) (v : V) (σ : V → C)
    (τ ρ : Configuration I v) : extend I v (extend I v σ τ) ρ = extend I v σ ρ := by
  funext u
  by_cases hu : u = v
  · subst u; simp
  · by_cases hv : I.graph.Adj v u
    · rw [show u = (⟨u,hv⟩ : Leaf I v).val from rfl, extend_leaf, extend_leaf]
    · rw [extend_outside I v (extend I v σ τ) ρ u hu hv,
        extend_outside I v σ τ u hu hv, extend_outside I v σ ρ u hu hv]

theorem vertex_injective (I : PinningData V C) (v : V) : Function.Injective (vertex I v) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some u => exact (u.property.ne hij).elim
  | some u =>
    cases j with
    | none => exact (u.property.ne hij.symm).elim
    | some w => exact congrArg some (Subtype.ext hij)

theorem extend_update (I : PinningData V C) (v : V) (σ : V → C)
    (τ : Configuration I v) (i : Option (Leaf I v)) (c : C) :
    extend I v σ (Function.update τ i c) = Function.update (extend I v σ τ) (vertex I v i) c := by
  funext u
  by_cases hu : u = v
  · subst u
    rw [extend_root]
    cases i with
    | none => simp [vertex]
    | some w => simp [vertex, w.property.ne]
  · by_cases hv : I.graph.Adj v u
    · have he := extend_leaf I v σ (Function.update τ i c) ⟨u,hv⟩
      rw [he, Function.update_apply, Function.update_apply]
      have hi : u = vertex I v i ↔ (some ⟨u,hv⟩ : Option (Leaf I v)) = i :=
        by
          change vertex I v (some ⟨u,hv⟩) = vertex I v i ↔ _
          exact (vertex_injective I v).eq_iff
      simp only [hi, extend_leaf I v σ τ ⟨u,hv⟩]
    · rw [extend_outside I v σ (Function.update τ i c) u hu hv]
      have hi : u ≠ vertex I v i := by
        cases i with
        | none => exact hu
        | some w => intro h; exact hv (h ▸ w.property)
      rw [Function.update_of_ne hi, extend_outside I v σ τ u hu hv]

def cavityCount (I : PinningData V C) (v : V) (σ : V → C) (u : Leaf I v) (c : C) : ℕ :=
  I.boundaryCount u.val c + (((I.graph.neighborFinset u.val).erase v).filter (fun w => σ w = c)).card

def cavityWeight (I : PinningData V C) (x : ℝ) (v : V) (σ : V → C)
    (u : Leaf I v) (c : C) : ℝ := x ^ cavityCount I v σ u c

def cavityPartition (I : PinningData V C) (x : ℝ) (v : V) (σ : V → C) (u : Leaf I v) : ℝ :=
  ∑ c, cavityWeight I x v σ u c

theorem cavityCount_extend (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (v : V) (σ : V → C) (τ : Configuration I v) (u : Leaf I v) (c : C) :
    cavityCount I v (extend I v σ τ) u c = cavityCount I v σ u c := by
  unfold cavityCount
  congr 2
  apply Finset.filter_congr
  intro w hw
  have hwv := Finset.ne_of_mem_erase hw
  have huw : I.graph.Adj u.val w := by simpa using Finset.mem_of_mem_erase hw
  rw [extend_outside I v σ τ w hwv (second_step_not_first_layer I.graph hg u.property huw)]

theorem cavityCount_sum (I : PinningData V C) (v : V) (σ : V → C) (u : Leaf I v) :
    (∑ c, cavityCount I v σ u c) + 1 = I.constraintDegree u.val := by
  unfold cavityCount PinningData.constraintDegree
  rw [Finset.sum_add_distrib]
  have h := Finset.sum_card_fiberwise_eq_card_filter ((I.graph.neighborFinset u.val).erase v)
    (Finset.univ : Finset C) σ
  simp only [Finset.mem_univ, Finset.filter_true] at h
  rw [h]
  have hv : v ∈ I.graph.neighborFinset u.val := by simpa using u.property.symm
  have hc := Finset.card_erase_add_one hv
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega

theorem cavityPartition_lower (I : PinningData V C) {x : ℝ} (hx : 0 ≤ x)
    (v : V) (σ : V → C) (u : Leaf I v) :
    (Fintype.card C : ℝ) - (1-x) * (I.constraintDegree u.val - 1 : ℝ) ≤
      cavityPartition I x v σ u := by
  have h := palette_mass_lower hx (cavityCount I v σ u)
  have he : (∑ c, (cavityCount I v σ u c : ℝ)) = I.constraintDegree u.val - 1 := by
    have hh := cavityCount_sum I v σ u
    have hr : (∑ c, (cavityCount I v σ u c : ℝ)) + 1 = I.constraintDegree u.val := by
      exact_mod_cast hh
    linarith
  simpa only [paletteWeight, cavityWeight, cavityPartition, he] using h

theorem siteCount_leaf (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (v : V) (σ : V → C) (τ : Configuration I v) (u : Leaf I v) (c : C) :
    GraphHeatBath.siteCount I (extend I v σ τ) u.val c = cavityCount I v σ u c +
      if τ none = c then 1 else 0 := by
  unfold GraphHeatBath.siteCount
  have hv : v ∈ I.graph.neighborFinset u.val := by simpa using u.property.symm
  rw [← Finset.insert_erase hv, Finset.filter_insert, extend_root]
  rw [← cavityCount_extend I hg v σ τ u c]
  unfold cavityCount
  split_ifs <;> simp [Finset.mem_filter, Nat.add_assoc]

theorem siteWeight_leaf (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (x : ℝ) (v : V) (σ : V → C) (τ : Configuration I v) (u : Leaf I v) (c : C) :
    GraphHeatBath.siteWeight I x (extend I v σ τ) u.val c = cavityWeight I x v σ u c *
      if τ none = c then x else 1 := by
  rw [GraphHeatBath.siteWeight, siteCount_leaf I hg v σ τ u c, pow_add]
  unfold cavityWeight
  split_ifs <;> simp

end GraphStar
end
end CI2ZF.Appendix.Girth
