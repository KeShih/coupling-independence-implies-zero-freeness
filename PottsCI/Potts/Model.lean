import PottsCI.FinDist
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# The finite Potts model with pinned boundary data

This file contains only the elementary model layer used by the coupling-
independence arguments.  A pinning is represented by its graph of free
vertices and, at each free vertex, the number of pinned neighbours of each
colour.  We define the soft Potts weight, partition function, normalized Gibbs
law, and the hard endpoint.

The final part proves a self-contained finite greedy list-colouring theorem and
uses it to establish hard feasibility when the number of colours is at least
the maximum constraint degree plus two.
-/

namespace PottsCI

open Finset

attribute [local instance] Classical.propDecidable

variable {V : Type*} {C : Type*}
variable [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- The data left after some vertices have been pinned: the simple graph on the
free vertices and the number of pinned neighbours of every colour. -/
structure PinningData (V C : Type*) where
  /-- The graph induced by the free vertices. -/
  graph : SimpleGraph V
  /-- `boundaryCount u c` is the number of pinned neighbours of `u` coloured
  `c`. -/
  boundaryCount : V → C → ℕ

namespace PinningData

variable (I : PinningData V C)

/-- The number of free-edge and pinned-neighbour constraints incident to `u`.
-/
noncomputable def constraintDegree (u : V) : ℕ :=
  I.graph.degree u + ∑ c, I.boundaryCount u c

/-- Every free vertex has total constraint degree at most `Δ`. -/
def DegreeBound (Δ : ℕ) : Prop := ∀ u, I.constraintDegree u ≤ Δ

/-! ## Soft Potts weights -/

/-- The antiferromagnetic Potts factor on one free edge: `x` for equal
colours, and `1` for unequal colours. -/
def edgeFactor (x : ℝ) (σ : V → C) (e : Sym2 V) : ℝ :=
  Sym2.lift
    ⟨fun u v => if σ u = σ v then x else 1, fun u v => by simp [eq_comm]⟩ e

omit [Fintype V] [DecidableEq V] [Fintype C] in
@[simp]
lemma edgeFactor_mk (x : ℝ) (σ : V → C) (u v : V) :
    edgeFactor x σ s(u, v) = if σ u = σ v then x else 1 := rfl

/-- The unnormalized Potts weight of a colouring of the free vertices. -/
noncomputable def weight (x : ℝ) (σ : V → C) : ℝ :=
  (∏ u, x ^ I.boundaryCount u (σ u)) *
    ∏ e ∈ I.graph.edgeFinset, edgeFactor x σ e

/-- The pinned Potts partition function. -/
noncomputable def partition (x : ℝ) : ℝ :=
  ∑ σ : V → C, I.weight x σ

omit [DecidableEq V] [Fintype C] in
lemma weight_nonneg {x : ℝ} (hx : 0 ≤ x) (σ : V → C) : 0 ≤ I.weight x σ := by
  unfold weight
  refine mul_nonneg (Finset.prod_nonneg fun u _ => pow_nonneg hx _)
    (Finset.prod_nonneg fun e _ => ?_)
  induction e using Sym2.ind with
  | _ u v =>
    rw [edgeFactor_mk]
    split
    · exact hx
    · exact zero_le_one

omit [DecidableEq V] [Fintype C] in
lemma weight_pos {x : ℝ} (hx : 0 < x) (σ : V → C) : 0 < I.weight x σ := by
  unfold weight
  refine mul_pos (Finset.prod_pos fun u _ => pow_pos hx _)
    (Finset.prod_pos fun e _ => ?_)
  induction e using Sym2.ind with
  | _ u v =>
    rw [edgeFactor_mk]
    split
    · exact hx
    · exact one_pos

lemma partition_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ I.partition x :=
  Finset.sum_nonneg fun σ _ => I.weight_nonneg hx σ

lemma partition_pos_of_parameter_pos [Nonempty C] {x : ℝ} (hx : 0 < x) :
    0 < I.partition x :=
  Finset.sum_pos (fun σ _ => I.weight_pos hx σ) Finset.univ_nonempty

/-- The normalized Gibbs law.  Its two proof arguments make explicit that the
parameter is nonnegative and that the normalizing partition function is
strictly positive. -/
noncomputable def gibbs (x : ℝ) (hx : 0 ≤ x) (hZ : 0 < I.partition x) :
    FinDist (V → C) where
  w := fun σ => I.weight x σ / I.partition x
  nonneg := fun σ => div_nonneg (I.weight_nonneg hx σ) hZ.le
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self hZ.ne'

/-! ## The hard endpoint -/

/-- A hard colouring is proper on the free graph and avoids every colour
already present at a pinned neighbour. -/
def HardAdmissible (σ : V → C) : Prop :=
  (∀ u v, I.graph.Adj u v → σ u ≠ σ v) ∧
    ∀ u, I.boundaryCount u (σ u) = 0

omit [DecidableEq V] [Fintype C] in
/-- At the hard endpoint the Potts weight is the indicator of hard
admissibility. -/
lemma weight_zero_eq (σ : V → C) :
    I.weight 0 σ = if I.HardAdmissible σ then 1 else 0 := by
  unfold weight
  by_cases h : I.HardAdmissible σ
  · rw [if_pos h]
    obtain ⟨hproper, hboundary⟩ := h
    have hboundaryProduct : ∏ u, (0 : ℝ) ^ I.boundaryCount u (σ u) = 1 :=
      Finset.prod_eq_one fun u _ => by rw [hboundary u, pow_zero]
    have hedgeProduct : ∏ e ∈ I.graph.edgeFinset, edgeFactor 0 σ e = 1 := by
      refine Finset.prod_eq_one fun e he => ?_
      induction e using Sym2.ind with
      | _ u v =>
        rw [SimpleGraph.mem_edgeFinset] at he
        have hadj : I.graph.Adj u v := (SimpleGraph.mem_edgeSet _).mp he
        rw [edgeFactor_mk, if_neg (hproper u v hadj)]
    rw [hboundaryProduct, hedgeProduct, one_mul]
  · rw [if_neg h]
    by_cases hproper : ∀ u v, I.graph.Adj u v → σ u ≠ σ v
    · have hboundary : ¬ ∀ u, I.boundaryCount u (σ u) = 0 :=
        fun hb => h ⟨hproper, hb⟩
      push Not at hboundary
      obtain ⟨u₀, hu₀⟩ := hboundary
      have hboundaryProduct : ∏ u, (0 : ℝ) ^ I.boundaryCount u (σ u) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ u₀) (by rw [zero_pow hu₀])
      rw [hboundaryProduct, zero_mul]
    · push Not at hproper
      obtain ⟨u, v, hadj, heq⟩ := hproper
      have hmem : s(u, v) ∈ I.graph.edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset]
        exact (SimpleGraph.mem_edgeSet _).mpr hadj
      have hedgeProduct : ∏ e ∈ I.graph.edgeFinset, edgeFactor 0 σ e = 0 :=
        Finset.prod_eq_zero hmem (by rw [edgeFactor_mk, if_pos heq])
      rw [hedgeProduct, mul_zero]

/-! ## A finite greedy list-colouring theorem -/

omit [Fintype C] in
/-- A finite simple graph is list-colourable whenever every vertex list has
more colours than the vertex degree.  This elementary theorem is stated
independently of the Potts model so that the only graph argument used for hard
feasibility is explicit. -/
lemma exists_proper_listColoring [Nonempty C] (G : SimpleGraph V) (L : V → Finset C)
    (hL : ∀ u, G.degree u + 1 ≤ (L u).card) :
    ∃ σ : V → C, (∀ u v, G.Adj u v → σ u ≠ σ v) ∧ ∀ u, σ u ∈ L u := by
  have colourSubset : ∀ s : Finset V, ∃ σ : V → C,
      (∀ u ∈ s, ∀ v ∈ s, G.Adj u v → σ u ≠ σ v) ∧
        ∀ u ∈ s, σ u ∈ L u := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => Classical.arbitrary C, by simp, by simp⟩
    | @insert u₀ s hu₀ ih =>
      obtain ⟨σ, hproper, hlist⟩ := ih
      have husedCard : ((s.filter fun v => G.Adj u₀ v).image σ).card < (L u₀).card := by
        have himage : ((s.filter fun v => G.Adj u₀ v).image σ).card ≤
            (s.filter fun v => G.Adj u₀ v).card := Finset.card_image_le
        have hneighbours : (s.filter fun v => G.Adj u₀ v).card ≤ G.degree u₀ := by
          rw [← SimpleGraph.card_neighborFinset_eq_degree]
          refine Finset.card_le_card fun v hv => ?_
          rw [SimpleGraph.mem_neighborFinset]
          exact (Finset.mem_filter.mp hv).2
        have hlistSize := hL u₀
        omega
      have hfresh : (L u₀ \ ((s.filter fun v => G.Adj u₀ v).image σ)).Nonempty := by
        rw [← Finset.card_pos]
        have hdiff := Finset.le_card_sdiff ((s.filter fun v => G.Adj u₀ v).image σ) (L u₀)
        omega
      obtain ⟨c₀, hc₀⟩ := hfresh
      have hc₀List : c₀ ∈ L u₀ := (Finset.mem_sdiff.mp hc₀).1
      have hc₀Fresh : c₀ ∉ (s.filter fun v => G.Adj u₀ v).image σ :=
        (Finset.mem_sdiff.mp hc₀).2
      refine ⟨Function.update σ u₀ c₀, ?_, ?_⟩
      · intro u hu v hv hadj
        rcases Finset.mem_insert.mp hu with rfl | hu' <;>
          rcases Finset.mem_insert.mp hv with rfl | hv'
        · exact absurd hadj G.irrefl
        · have hvne : v ≠ u := fun h => hu₀ (h ▸ hv')
          rw [Function.update_apply, Function.update_apply, if_pos rfl, if_neg hvne]
          intro hcc
          exact hc₀Fresh
            (Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv', hadj⟩, hcc.symm⟩)
        · have hune : u ≠ v := fun h => hu₀ (h ▸ hu')
          rw [Function.update_apply, Function.update_apply, if_pos rfl, if_neg hune]
          intro hcc
          exact hc₀Fresh
            (Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu', hadj.symm⟩, hcc⟩)
        · have hune : u ≠ u₀ := fun h => hu₀ (h ▸ hu')
          have hvne : v ≠ u₀ := fun h => hu₀ (h ▸ hv')
          rw [Function.update_apply, Function.update_apply, if_neg hune, if_neg hvne]
          exact hproper u hu' v hv' hadj
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu'
        · rw [Function.update_apply, if_pos rfl]
          exact hc₀List
        · have hune : u ≠ u₀ := fun h => hu₀ (h ▸ hu')
          rw [Function.update_apply, if_neg hune]
          exact hlist u hu'
  obtain ⟨σ, hproper, hlist⟩ := colourSubset Finset.univ
  exact ⟨σ,
    fun u v hadj => hproper u (Finset.mem_univ u) v (Finset.mem_univ v) hadj,
    fun u => hlist u (Finset.mem_univ u)⟩

/-- The hard effective list at `u`: the colours absent from its pinned
neighbourhood. -/
noncomputable def hardList (u : V) : Finset C :=
  Finset.univ.filter fun c => I.boundaryCount u c = 0

omit [DecidableEq V] [DecidableEq C] in
/-- Under `q ≥ Δ + 2`, every hard effective list has at least two more
colours than the free degree. -/
lemma card_hardList {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (hcolours : Δ + 2 ≤ Fintype.card C) (u : V) :
    I.graph.degree u + 2 ≤ (I.hardList u).card := by
  have hsplit : (Finset.univ.filter fun c => I.boundaryCount u c = 0).card +
      (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card = Fintype.card C := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hforbidden : (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card ≤
      ∑ c, I.boundaryCount u c := by
    calc
      (Finset.univ.filter fun c => ¬ I.boundaryCount u c = 0).card =
          ∑ c ∈ Finset.univ.filter (fun c => ¬ I.boundaryCount u c = 0), 1 := by
            rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ c ∈ Finset.univ.filter (fun c => ¬ I.boundaryCount u c = 0),
          I.boundaryCount u c := by
            refine Finset.sum_le_sum fun c hc => ?_
            have hcpos := (Finset.mem_filter.mp hc).2
            omega
      _ ≤ ∑ c, I.boundaryCount u c := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro c _ _
            exact Nat.zero_le _
  have htotal := hdegree u
  unfold constraintDegree at htotal
  unfold hardList
  omega

/-- Hard feasibility for finite pinned Potts instances. -/
lemma exists_hardAdmissible [Nonempty C] {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (hcolours : Δ + 2 ≤ Fintype.card C) :
    ∃ σ : V → C, I.HardAdmissible σ := by
  obtain ⟨σ, hproper, hlist⟩ := exists_proper_listColoring I.graph I.hardList (fun u => by
    have hsize := I.card_hardList hdegree hcolours u
    omega)
  refine ⟨σ, hproper, fun u => ?_⟩
  exact (Finset.mem_filter.mp (hlist u)).2

/-- The hard partition function is positive under `q ≥ Δ + 2`. -/
lemma partition_zero_pos [Nonempty C] {Δ : ℕ} (hdegree : I.DegreeBound Δ)
    (hcolours : Δ + 2 ≤ Fintype.card C) : 0 < I.partition 0 := by
  obtain ⟨σ₀, hσ₀⟩ := I.exists_hardAdmissible hdegree hcolours
  have hweight : I.weight 0 σ₀ = 1 := by
    rw [I.weight_zero_eq, if_pos hσ₀]
  have hle : I.weight 0 σ₀ ≤ I.partition 0 :=
    Finset.single_le_sum (f := fun σ => I.weight 0 σ)
      (fun σ _ => I.weight_nonneg le_rfl σ) (Finset.mem_univ σ₀)
  rw [hweight] at hle
  linarith

/-- Positivity of the partition function throughout the nonnegative soft
regime, including the hard endpoint under the degree and colour assumptions.
-/
lemma partition_pos [Nonempty C] {Δ : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hdegree : I.DegreeBound Δ) (hcolours : Δ + 2 ≤ Fintype.card C) :
    0 < I.partition x := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · rw [← hzero]
    exact I.partition_zero_pos hdegree hcolours
  · exact I.partition_pos_of_parameter_pos hpos

end PinningData

end PottsCI
