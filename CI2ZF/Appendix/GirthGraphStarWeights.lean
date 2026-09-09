import CI2ZF.Appendix.GirthGraphStarCoordinates
import CI2ZF.Appendix.GirthGraphPositivePoincare

/-! Exact conditional-star weights, derived from all single-site Gibbs ratios. -/
namespace CI2ZF.Appendix.Girth
open scoped BigOperators
open PottsCI Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

namespace GraphStar
local instance (priority := 2000) graphStarWeightsLeafDecEq (I : PinningData V C) (v : V) : DecidableEq (Leaf I v) :=
  fun _ _ => Classical.propDecidable _

def unary (I : PinningData V C) (x : ℝ) (v : V) (c : C) : ℝ := x ^ I.boundaryCount v c

def edge (x : ℝ) (c d : C) : ℝ := if c = d then x else 1

def rawWeight (I : PinningData V C) (x : ℝ) (v : V) (σ : V → C) (τ : Configuration I v) : ℝ :=
  unary I x v (τ none) * ∏ u : Leaf I v, cavityWeight I x v σ u (τ (some u)) * edge x (τ none) (τ (some u))

theorem siteWeight_root (I : PinningData V C) (x : ℝ) (v : V) (σ : V → C)
    (τ : Configuration I v) (c : C) :
    GraphHeatBath.siteWeight I x (extend I v σ τ) v c =
      unary I x v c * ∏ u : Leaf I v, edge x c (τ (some u)) := by
  unfold GraphHeatBath.siteWeight GraphHeatBath.siteCount unary
  rw [pow_add]
  congr 1
  have hp := Finset.prod_subtype (F := inferInstanceAs (Fintype (Leaf I v))) (I.graph.neighborFinset v)
    (fun w => I.graph.mem_neighborFinset v w)
    (fun w => edge x c (extend I v σ τ w))
  rw [show (∏ u : Leaf I v, edge x c (τ (some u))) =
      ∏ u : Leaf I v, edge x c (extend I v σ τ u.val) by simp only [extend_leaf]]
  rw [← hp]
  simp only [edge]
  rw [← Finset.prod_filter]
  simp [eq_comm]

theorem rawWeight_pos (I : PinningData V C) {x : ℝ} (hx : 0 < x)
    (v : V) (σ : V → C) (τ : Configuration I v) : 0 < rawWeight I x v σ τ := by
  unfold rawWeight unary
  apply mul_pos (pow_pos hx _)
  apply Finset.prod_pos
  intro u _
  apply mul_pos (pow_pos hx _)
  unfold edge
  split_ifs <;> positivity

theorem rawWeight_extend (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (x : ℝ) (v : V) (σ : V → C) (τ ρ : Configuration I v) :
    rawWeight I x v (extend I v σ τ) ρ = rawWeight I x v σ ρ := by
  unfold rawWeight
  simp only [cavityWeight, cavityCount_extend I hg]

def rawBackground (I : PinningData V C) (x : ℝ) (v : V) (σ : V → C)
    (τ : Configuration I v) : Option (Leaf I v) → ℝ
  | none => ∏ u : Leaf I v, cavityWeight I x v σ u (τ (some u))
  | some i => unary I x v (τ none) *
      ∏ u ∈ Finset.univ.erase i, cavityWeight I x v σ u (τ (some u)) * edge x (τ none) (τ (some u))

theorem rawWeight_factorization (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (x : ℝ) (v : V) (σ : V → C) (τ : Configuration I v) (i : Option (Leaf I v)) :
    rawWeight I x v σ τ = rawBackground I x v σ τ i *
      GraphHeatBath.siteWeight I x (extend I v σ τ) (vertex I v i) (τ i) := by
  cases i with
  | none =>
    rw [vertex, siteWeight_root]
    simp only [rawWeight, rawBackground, Finset.prod_mul_distrib]
    ring
  | some u =>
    rw [vertex, siteWeight_leaf I hg]
    unfold rawWeight rawBackground edge
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ u)]
    ring

theorem rawBackground_update (I : PinningData V C) (x : ℝ) (v : V) (σ : V → C)
    (τ : Configuration I v) (i : Option (Leaf I v)) (c : C) :
    rawBackground I x v σ (Function.update τ i c) i = rawBackground I x v σ τ i := by
  cases i with
  | none => simp only [rawBackground, Function.update_of_ne (Option.some_ne_none _)]
  | some u =>
    simp only [rawBackground, Function.update_of_ne (show (none : Option (Leaf I v)) ≠ some u by simp)]
    congr 1
    apply Finset.prod_congr rfl
    intro w hw
    have hwu : some w ≠ some u := fun h => Finset.ne_of_mem_erase hw (Option.some.inj h)
    rw [Function.update_of_ne hwu]

theorem rawWeight_swap (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    (x : ℝ) (v : V) (σ : V → C) (τ : Configuration I v) (i : Option (Leaf I v)) (c : C) :
    rawWeight I x v σ (Function.update τ i c) *
      GraphHeatBath.siteWeight I x (extend I v σ τ) (vertex I v i) (τ i) =
    rawWeight I x v σ τ * GraphHeatBath.siteWeight I x (extend I v σ τ) (vertex I v i) c := by
  rw [rawWeight_factorization I hg x v σ (Function.update τ i c) i,
    rawBackground_update, extend_update, Function.update_self,
    GraphHeatBath.siteWeight_update_of_not_adj I x (extend I v σ τ)
      (vertex I v i) (vertex I v i) I.graph.irrefl,
    rawWeight_factorization I hg x v σ τ i]
  ring

theorem graph_weight_ratio_invariant (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    {x : ℝ} (hx : 0 < x) (v : V) (σ : V → C) (τ : Configuration I v)
    (i : Option (Leaf I v)) (c : C) :
    I.weight x (extend I v σ (Function.update τ i c)) /
        rawWeight I x v σ (Function.update τ i c) =
      I.weight x (extend I v σ τ) / rawWeight I x v σ τ := by
  have hw := GraphHeatBath.weight_swap I x (extend I v σ τ) (vertex I v i) c
  rw [← extend_update, extend_vertex] at hw
  have hr := rawWeight_swap I hg x v σ τ i c
  have hs : 0 < GraphHeatBath.siteWeight I x (extend I v σ τ) (vertex I v i) (τ i) := pow_pos hx _
  have hg0 := (rawWeight_pos I hx v σ τ).ne'
  have hg1 := (rawWeight_pos I hx v σ (Function.update τ i c)).ne'
  apply (div_eq_div_iff hg1 hg0).mpr
  apply (mul_right_inj' hs.ne').mp
  calc
    _ = I.weight x (extend I v σ (Function.update τ i c)) *
      (rawWeight I x v σ τ * GraphHeatBath.siteWeight I x (extend I v σ τ) (vertex I v i) (τ i)) := by ring
    _ = I.weight x (extend I v σ τ) *
      (rawWeight I x v σ τ * GraphHeatBath.siteWeight I x (extend I v σ τ) (vertex I v i) c) := by
        linear_combination rawWeight I x v σ τ * hw
    _ = _ := by rw [← hr]; ring

theorem graph_weight_cross (I : PinningData V C) (hg : 5 ≤ I.graph.egirth)
    {x : ℝ} (hx : 0 < x) (v : V) (σ : V → C) (τ ρ : Configuration I v) :
    I.weight x (extend I v σ τ) * rawWeight I x v σ ρ =
      I.weight x (extend I v σ ρ) * rawWeight I x v σ τ := by
  let : Nonempty C := ⟨σ v⟩
  have h := update_invariant_constant
    (fun τ : Configuration I v => I.weight x (extend I v σ τ) / rawWeight I x v σ τ)
    (graph_weight_ratio_invariant I hg hx v σ) τ ρ
  exact (div_eq_div_iff (rawWeight_pos I hx v σ τ).ne' (rawWeight_pos I hx v σ ρ).ne').mp h

end GraphStar
end
end CI2ZF.Appendix.Girth
