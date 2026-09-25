import ZeroFreeness.Coupling.Girth.Tree.Gibbs

/-!
# Relative SSM cannot start at distance one

Companion `appendices/high-girth.tex`, the paragraph before
`lem:hg-eventual-relative-ssm`: on a single edge, compare boundary colours
`a` and `b ≠ a`. The probability that the free endpoint has colour `a` is
`x/(q-1+x)`, respectively `1/(q-1+x)`, so the ratio is `x` (or `1/x` in the
reverse comparison).

The free endpoint is represented in the two ways used by the library:

* as the root of the finite cavity tree `CavityTree.node 0 b _` with no free
  children and boundary counts `b = 𝟙_{a}` (resp. `𝟙_{b}`); its
  `probability` is the one-site marginal used in `CLMM.TreeRelative`, and
  for `x > 0` it equals the root marginal of the actual finite tree Gibbs
  law (`CavityTree.probability_eq_gibbs`);
* as the one-free-vertex pinned system `PinningData Unit C`, the pinned
  endpoint being recorded as one boundary count, via its actual Gibbs law.

The last theorem records the consequence stated in the paper: the reverse
ratio `1/x` is unbounded on `(0,1)`, so no bound on the ratio-form relative
error at distance one holds uniformly in the activity.
-/

namespace ZeroFreeness.Appendix.Girth

open scoped BigOperators
open PottsCI ZeroFreeness.Appendix.Girth

noncomputable section

attribute [local instance] Classical.propDecidable

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Boundary counts of a free vertex whose unique pinned neighbour has
colour `a`. -/
def pinnedNeighbour (a : C) : C → ℕ := fun c => if c = a then 1 else 0

/-- The free endpoint of a single edge, as a finite cavity tree. -/
def edgeTree (a : C) : CavityTree C := .node 0 (pinnedNeighbour a) Fin.elim0

/-- The free endpoint of a single edge, as a pinned system with one free
vertex and no free edge. -/
def edgeData (a : C) : PinningData Unit C where
  graph := ⊥
  boundaryCount _ := pinnedNeighbour a

theorem sum_palette (x : ℝ) (a : C) :
    (∑ c, paletteWeight x (pinnedNeighbour a) c) = (Fintype.card C : ℝ) - 1 + x := by
  have h : (∑ c, paletteWeight x (pinnedNeighbour a) c) =
      ∑ c, ((1 : ℝ) + if c = a then x - 1 else 0) := by
    apply Finset.sum_congr rfl
    intro c _
    by_cases hc : c = a <;> simp [paletteWeight, pinnedNeighbour, hc]
  rw [h, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

omit [DecidableEq C] in
theorem denominator_pos (a : C) {x : ℝ} (hx : 0 < x) :
    0 < (Fintype.card C : ℝ) - 1 + x := by
  have : Nonempty C := ⟨a⟩
  have h1 : (1 : ℝ) ≤ Fintype.card C := by exact_mod_cast Fintype.card_pos
  linarith

theorem edgeTree_probability (x : ℝ) (a c : C) :
    (edgeTree a).probability x c =
      paletteWeight x (pinnedNeighbour a) c / ((Fintype.card C : ℝ) - 1 + x) := by
  simp only [edgeTree, CavityTree.probability, messageMarginal, messagePartition,
    messageWeight, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [sum_palette]

/-- Same boundary colour `a`: the free endpoint has colour `a` with
probability `x/(q-1+x)`. -/
theorem edgeTree_same (x : ℝ) (a : C) :
    (edgeTree a).probability x a = x / ((Fintype.card C : ℝ) - 1 + x) := by
  rw [edgeTree_probability]
  simp [paletteWeight, pinnedNeighbour]

/-- Boundary colour `b ≠ a`: the free endpoint has colour `a` with
probability `1/(q-1+x)`. -/
theorem edgeTree_other (x : ℝ) {a b : C} (hab : b ≠ a) :
    (edgeTree b).probability x a = 1 / ((Fintype.card C : ℝ) - 1 + x) := by
  rw [edgeTree_probability]
  simp [paletteWeight, pinnedNeighbour, Ne.symm hab]

/-- The two ratios of the paper: `x` and `1/x`. -/
theorem edgeTree_ratio {x : ℝ} (hx : 0 < x) {a b : C} (hab : b ≠ a) :
    (edgeTree a).probability x a / (edgeTree b).probability x a = x ∧
      (edgeTree b).probability x a / (edgeTree a).probability x a = 1 / x := by
  have hd := denominator_pos a hx
  rw [edgeTree_same, edgeTree_other x hab]
  constructor <;> field_simp

/-! ## The same computation for the actual pinned Gibbs law -/

omit [Fintype C] in
theorem edgeData_weight (x : ℝ) (a : C) (σ : Unit → C) :
    (edgeData a).weight x σ = paletteWeight x (pinnedNeighbour a) (σ ()) := by
  unfold PinningData.weight
  rw [Finset.prod_eq_one (s := (edgeData a).graph.edgeFinset)
    (fun e he => by
      have h := SimpleGraph.mem_edgeFinset.mp he
      exact absurd h (by simp [edgeData])), mul_one]
  simp [edgeData, paletteWeight]

theorem edgeData_partition (x : ℝ) (a : C) :
    (edgeData a).partition x = (Fintype.card C : ℝ) - 1 + x := by
  unfold PinningData.partition
  simp_rw [edgeData_weight]
  rw [← sum_palette x a]
  exact Fintype.sum_equiv (Equiv.funUnique Unit C) _ _ (fun σ => rfl)

theorem edgeData_partition_pos (a : C) {x : ℝ} (hx : 0 < x) :
    0 < (edgeData a).partition x := by
  rw [edgeData_partition]
  exact denominator_pos a hx

/-- Actual Gibbs law, same boundary colour: `x/(q-1+x)`. -/
theorem edgeData_same {x : ℝ} (hx : 0 < x) (a : C) :
    ((edgeData a).gibbs x hx.le (edgeData_partition_pos a hx)).w (fun _ => a) =
      x / ((Fintype.card C : ℝ) - 1 + x) := by
  change (edgeData a).weight x _ / (edgeData a).partition x = _
  rw [edgeData_weight, edgeData_partition]
  simp [paletteWeight, pinnedNeighbour]

/-- Actual Gibbs law, boundary colour `b ≠ a`: `1/(q-1+x)`. -/
theorem edgeData_other {x : ℝ} (hx : 0 < x) {a b : C} (hab : b ≠ a) :
    ((edgeData b).gibbs x hx.le (edgeData_partition_pos b hx)).w (fun _ => a) =
      1 / ((Fintype.card C : ℝ) - 1 + x) := by
  change (edgeData b).weight x _ / (edgeData b).partition x = _
  rw [edgeData_weight, edgeData_partition]
  simp [paletteWeight, pinnedNeighbour, Ne.symm hab]

/-- The ratios `x` and `1/x` for the actual Gibbs laws. -/
theorem edgeData_ratio {x : ℝ} (hx : 0 < x) {a b : C} (hab : b ≠ a) :
    ((edgeData a).gibbs x hx.le (edgeData_partition_pos a hx)).w (fun _ => a) /
        ((edgeData b).gibbs x hx.le (edgeData_partition_pos b hx)).w (fun _ => a) = x ∧
      ((edgeData b).gibbs x hx.le (edgeData_partition_pos b hx)).w (fun _ => a) /
        ((edgeData a).gibbs x hx.le (edgeData_partition_pos a hx)).w (fun _ => a) = 1 / x := by
  have hd := denominator_pos a hx
  rw [edgeData_same hx, edgeData_other hx hab]
  constructor <;> field_simp

/-- Uniform relative SSM cannot start at distance one: for two distinct
colours and every proposed error bound `M`, some activity in `(0,1)` makes
the ratio-form relative error of the single edge exceed `M`. -/
theorem no_uniform_distance_one {a b : C} (hab : b ≠ a) (M : ℝ) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧
      M < |(edgeTree b).probability x a / (edgeTree a).probability x a - 1| := by
  refine ⟨1 / (|M| + 2), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]
    linarith [abs_nonneg M]
  · have hx : (0 : ℝ) < 1 / (|M| + 2) := by positivity
    rw [(edgeTree_ratio hx hab).2]
    have he : 1 / (1 / (|M| + 2)) - 1 = |M| + 1 := by field_simp; ring
    rw [he, abs_of_pos (by positivity)]
    linarith [le_abs_self M]

end

end ZeroFreeness.Appendix.Girth
