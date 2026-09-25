import ZeroFreeness.Potts.Geometry.Separator
import Mathlib.Combinatorics.SimpleGraph.Metric

/-! Actual BFS balls and shells, their separator decomposition, and bounded
degree volume estimates. Disconnected vertices are kept outside every ball. -/
namespace ZeroFreeness.BFS
open Finset PottsCI
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V]

def ball (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V :=
  univ.filter fun w => G.Reachable v w ∧ G.dist v w ≤ r

def shell (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V :=
  univ.filter fun w => G.Reachable v w ∧ G.dist v w = r

@[simp] lemma mem_ball {G : SimpleGraph V} {v w : V} {r : ℕ} :
    w ∈ ball G v r ↔ G.Reachable v w ∧ G.dist v w ≤ r := by simp [ball]

@[simp] lemma mem_shell {G : SimpleGraph V} {v w : V} {r : ℕ} :
    w ∈ shell G v r ↔ G.Reachable v w ∧ G.dist v w = r := by simp [shell]

lemma center_mem_ball (G : SimpleGraph V) (v : V) (r : ℕ) : v ∈ ball G v r := by
  exact mem_ball.mpr ⟨SimpleGraph.Reachable.refl v, by simp⟩

@[simp] lemma ball_zero (G : SimpleGraph V) (v : V) : ball G v 0 = {v} := by
  ext w
  simp only [mem_ball, Nat.le_zero, mem_singleton]
  constructor
  · rintro ⟨hr, hd⟩
    exact (hr.dist_eq_zero_iff.mp hd).symm
  · rintro rfl
    exact ⟨SimpleGraph.Reachable.refl _, by simp⟩

lemma ball_mono (G : SimpleGraph V) (v : V) {r s : ℕ} (hrs : r ≤ s) :
    ball G v r ⊆ ball G v s := by
  intro w hw
  exact mem_ball.mpr ⟨(mem_ball.mp hw).1, (mem_ball.mp hw).2.trans hrs⟩

lemma shells_disjoint (G : SimpleGraph V) (v : V) {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (shell G v r) (shell G v s) := by
  apply disjoint_left.mpr
  intro w hw hs
  exact hrs ((mem_shell.mp hw).2.symm.trans (mem_shell.mp hs).2)

lemma ball_succ_eq_union_shell (G : SimpleGraph V) (v : V) (r : ℕ) :
    ball G v (r + 1) = ball G v r ∪ shell G v (r + 1) := by
  ext w
  simp only [mem_ball, mem_union, mem_shell]
  constructor
  · rintro ⟨hr, hd⟩
    by_cases hle : G.dist v w ≤ r
    · exact Or.inl ⟨hr, hle⟩
    · exact Or.inr ⟨hr, by omega⟩
  · rintro (⟨hr, hd⟩ | ⟨hr, hd⟩) <;> exact ⟨hr, by omega⟩

lemma shell_succ_disjoint_ball (G : SimpleGraph V) (v : V) (r : ℕ) :
    Disjoint (shell G v (r + 1)) (ball G v r) := by
  apply disjoint_left.mpr
  intro w hw hb
  have hs := (mem_shell.mp hw).2
  have hd := (mem_ball.mp hb).2
  omega

lemma adjacent_mem_ball_succ {G : SimpleGraph V} {v u w : V} {r : ℕ}
    (hu : u ∈ ball G v r) (huw : G.Adj u w) : w ∈ ball G v (r + 1) := by
  obtain ⟨hr, hd⟩ := mem_ball.mp hu
  refine mem_ball.mpr ⟨hr.trans huw.reachable, ?_⟩
  have ht := huw.reachable.dist_triangle_right v
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr huw] at ht
  omega

/-- A shell of width one already blocks all direct inside--outside edges. -/
theorem no_edge_inside_outside {G : SimpleGraph V} {v u w : V} {r : ℕ}
    (hu : u ∈ ball G v r) (hw : w ∉ ball G v (r + 1)) : ¬ G.Adj u w :=
  fun hadj => hw (adjacent_mem_ball_succ hu hadj)

theorem walk_hits_shell {G : SimpleGraph V} {v u w : V} {r : ℕ} (p : G.Walk u w) :
    u ∈ ball G v r → w ∉ ball G v (r + 1) → ∃ s ∈ p.support, s ∈ shell G v (r + 1) := by
  induction p with
  | nil =>
    intro hi ho
    exact (ho (ball_mono G v (by omega) hi)).elim
  | @cons u z w hadj p ih =>
    intro hi ho
    by_cases hz : z ∈ ball G v r
    · obtain ⟨s, hsp, hss⟩ := ih hz ho
      exact ⟨s, by simp [hsp], hss⟩
    · have hz' := adjacent_mem_ball_succ hi hadj
      rw [ball_succ_eq_union_shell, mem_union] at hz'
      exact ⟨z, by simp, hz'.resolve_left hz⟩

/-- Every ball vertex except the center has a predecessor in the previous
ball, obtained from an actual shortest walk. -/
theorem ball_succ_eq_neighbors (G : SimpleGraph V) (v : V) (r : ℕ) :
    ball G v (r + 1) = insert v ((ball G v r).biUnion fun w => G.neighborFinset w) := by
  ext w
  constructor
  · intro hw
    obtain ⟨hr, hd⟩ := mem_ball.mp hw
    obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
    rw [SimpleGraph.dist_comm] at hp
    cases p with
    | nil => simp
    | @cons w z v hwz p =>
      have hdist : G.dist v z ≤ r := by
        have hle := SimpleGraph.dist_le p
        rw [SimpleGraph.dist_comm] at hle
        simp only [SimpleGraph.Walk.length_cons] at hp
        omega
      exact mem_insert_of_mem (mem_biUnion.mpr
        ⟨z, mem_ball.mpr ⟨p.reachable.symm, hdist⟩, by simpa using hwz.symm⟩)
  · intro hw
    rcases mem_insert.mp hw with rfl | hw
    · exact center_mem_ball G _ (r + 1)
    · obtain ⟨z, hz, hzw⟩ := mem_biUnion.mp hw
      exact adjacent_mem_ball_succ hz (by simpa using hzw)

theorem ball_card_succ_le (G : SimpleGraph V) (v : V) (r Δ : ℕ)
    (hdeg : ∀ w, G.degree w ≤ Δ) :
    (ball G v (r + 1)).card ≤ 1 + Δ * (ball G v r).card := by
  rw [ball_succ_eq_neighbors]
  calc
    _ ≤ ((ball G v r).biUnion fun w => G.neighborFinset w).card + 1 := card_insert_le _ _
    _ ≤ (∑ w ∈ ball G v r, (G.neighborFinset w).card) + 1 := Nat.add_le_add_right card_biUnion_le _
    _ ≤ (∑ _w ∈ ball G v r, Δ) + 1 := Nat.add_le_add_right
      (sum_le_sum fun w _ => by simpa using hdeg w) _
    _ = 1 + Δ * (ball G v r).card := by simp [Nat.mul_comm, Nat.add_comm]

/-- The volume bound is derived from maximum degree, without a pre-supplied
ball-size assumption. -/
theorem ball_card_le_pow (G : SimpleGraph V) (v : V) (r Δ : ℕ)
    (hdeg : ∀ w, G.degree w ≤ Δ) : (ball G v r).card ≤ (Δ + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hb := ball_card_succ_le G v r Δ hdeg
    have hp : 0 < (Δ + 1) ^ r := pow_pos (by omega) _
    rw [pow_succ]
    nlinarith

/-- The usual geometric-series volume bound, valid also at degrees zero
and one without division by `Δ - 1`. -/
theorem ball_card_le_geom (G : SimpleGraph V) (v : V) (r Δ : ℕ)
    (hdeg : ∀ w, G.degree w ≤ Δ) :
    (ball G v r).card ≤ ∑ k ∈ range (r + 1), Δ ^ k := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      _ ≤ 1 + Δ * (ball G v r).card := ball_card_succ_le G v r Δ hdeg
      _ ≤ 1 + Δ * ∑ k ∈ range (r + 1), Δ ^ k :=
        Nat.add_le_add_left (Nat.mul_le_mul_left Δ ih) 1
      _ = ∑ k ∈ range (r + 1 + 1), Δ ^ k := by
        rw [sum_range_succ' (fun k => Δ ^ k) (r + 1)]
        simp_rw [pow_succ']
        rw [← mul_sum]
        simp [Nat.add_comm]

/-- An empty shell forces the whole root component into the preceding ball. -/
theorem reachable_mem_ball_of_shell_empty (G : SimpleGraph V) (v : V) (r : ℕ)
    (hs : shell G v (r + 1) = ∅) {w : V} (hr : G.Reachable v w) :
    w ∈ ball G v r := by
  by_contra hw
  have ho : w ∉ ball G v (r + 1) := by
    simpa [ball_succ_eq_union_shell, hs] using hw
  obtain ⟨p⟩ := hr
  obtain ⟨s, _, hss⟩ := walk_hits_shell p (center_mem_ball G v r) ho
  simp [hs] at hss

theorem component_card_le_geom_of_shell_empty (G : SimpleGraph V) (v : V) (r Δ : ℕ)
    (hdeg : ∀ w, G.degree w ≤ Δ) (hs : shell G v (r + 1) = ∅) :
    (univ.filter fun w => G.Reachable v w).card ≤ ∑ k ∈ range (r + 1), Δ ^ k := by
  refine (card_le_card ?_).trans (ball_card_le_geom G v r Δ hdeg)
  intro w hw
  exact reachable_mem_ball_of_shell_empty G v r hs (mem_filter.mp hw).2

/-- Label the first `R` positive-distance shells. Vertices beyond the
chosen radius, the center, and disconnected vertices receive no label. -/
def shellLabel (G : SimpleGraph V) (v : V) (R : ℕ) (w : V) : Option (Fin R) :=
  if h : G.Reachable v w ∧ 0 < G.dist v w ∧ G.dist v w ≤ R
  then some ⟨G.dist v w - 1, by omega⟩ else none

@[simp] theorem shellLabel_eq_some_iff (G : SimpleGraph V) (v w : V)
    (R : ℕ) (i : Fin R) :
    shellLabel G v R w = some i ↔ w ∈ shell G v (i.val + 1) := by
  unfold shellLabel
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff, mem_shell]
    exact ⟨fun hi => ⟨h.1, by omega⟩, fun hi => by omega⟩
  · simp only [false_iff, mem_shell]
    rintro ⟨hr, hd⟩
    exact h ⟨hr, by omega, by omega⟩

/-- A shifted block of shells; `offset = 1` gives the paper's radii
`2, ..., R + 1`. -/
def shellLabelFrom (G : SimpleGraph V) (v : V) (offset R : ℕ) (w : V) : Option (Fin R) :=
  if h : G.Reachable v w ∧ offset < G.dist v w ∧ G.dist v w ≤ offset + R
  then some ⟨G.dist v w - (offset + 1), by omega⟩ else none

@[simp] theorem shellLabelFrom_eq_some_iff (G : SimpleGraph V) (v w : V)
    (offset R : ℕ) (i : Fin R) :
    shellLabelFrom G v offset R w = some i ↔ w ∈ shell G v (offset + i.val + 1) := by
  unfold shellLabelFrom
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff, mem_shell]
    exact ⟨fun hi => ⟨h.1, by omega⟩, fun hi => by omega⟩
  · simp only [false_iff, mem_shell]
    rintro ⟨hr, hd⟩
    exact h ⟨hr, by omega, by omega⟩

abbrev Inside (G : SimpleGraph V) (v : V) (r : ℕ) := {w : V // w ∈ ball G v r}
abbrev Shell (G : SimpleGraph V) (v : V) (r : ℕ) := {w : V // w ∈ shell G v (r + 1)}
abbrev Outside (G : SimpleGraph V) (v : V) (r : ℕ) := {w : V // w ∉ ball G v (r + 1)}
abbrev SplitVertex (G : SimpleGraph V) (v : V) (r : ℕ) :=
  ZeroFreeness.Potts.Separator.Vertex (Inside G v r) (Shell G v r) (Outside G v r)

def unsplit (G : SimpleGraph V) (v : V) (r : ℕ) : SplitVertex G v r → V :=
  Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)

def splitEquiv (G : SimpleGraph V) (v : V) (r : ℕ) : V ≃ SplitVertex G v r where
  toFun w := if hi : w ∈ ball G v r then Sum.inl ⟨w, hi⟩
    else if hb : w ∈ ball G v (r + 1) then Sum.inr (Sum.inl ⟨w, by
      rw [ball_succ_eq_union_shell, mem_union] at hb
      exact hb.resolve_left hi⟩)
    else Sum.inr (Sum.inr ⟨w, hb⟩)
  invFun := unsplit G v r
  left_inv w := by dsimp only; split_ifs <;> rfl
  right_inv z := by
    rcases z with i | s | o
    · simp [unsplit, i.property]
    · have hi : s.val ∉ ball G v r :=
        fun hs => disjoint_left.mp (shell_succ_disjoint_ball G v r) s.property hs
      have hb : s.val ∈ ball G v (r + 1) := by
        rw [ball_succ_eq_union_shell, mem_union]
        exact Or.inr s.property
      simp [unsplit, hi, hb]
    · have hi : o.val ∉ ball G v r := fun ho => o.property (ball_mono G v (by omega) ho)
      simp [unsplit, hi, o.property]

/-- Reindex the actual pinning data by its inside/shell/outside equivalence. -/
def splitPinning (I : PinningData V C) (v : V) (r : ℕ) : PinningData (SplitVertex I.graph v r) C where
  graph := I.graph.comap (unsplit I.graph v r)
  boundaryCount w := I.boundaryCount (unsplit I.graph v r w)

theorem splitPinning_separates (I : PinningData V C) (v : V) (r : ℕ) :
    ZeroFreeness.Potts.Separator.Separates (splitPinning I v r) := by
  intro u o
  change ¬ I.graph.Adj u.val o.val
  exact no_edge_inside_outside u.property o.property

end
end ZeroFreeness.BFS
