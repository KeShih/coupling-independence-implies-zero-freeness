import ZeroFreeness.Potts.Geometry.OptionBFSSplit

/-! The large-root-component branch supplies actual nonempty BFS pieces
and strictly smaller exterior instances for strong induction. -/
namespace ZeroFreeness.Potts.OptionBFS
open PottsCI Finset
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {O C : Type*} [Fintype O]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _

abbrev RootComponent (G : SimpleGraph (Option O)) := {w : Option O // G.Reachable none w}

/-- An absent shell confines every reachable vertex to the preceding ball,
so a component larger than that ball forces the shell to be nonempty. -/
theorem shell_nonempty_of_component_card_gt_ball (G : SimpleGraph (Option O)) (k : ℕ)
    (hlarge : (BFS.ball G none k).card < Fintype.card (RootComponent G)) :
    Nonempty (BFS.Shell G none k) := by
  have hs : (BFS.shell G none (k + 1)).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hc : Fintype.card (RootComponent G) ≤ Fintype.card (BFS.Inside G none k) := by
      apply Fintype.card_le_of_injective
        (fun w : RootComponent G =>
          (⟨w.val, BFS.reachable_mem_ball_of_shell_empty G none k he w.property⟩ : BFS.Inside G none k))
      intro u v huv
      exact Subtype.ext (congrArg (fun w : BFS.Inside G none k => w.val) huv)
    have hc' : Fintype.card (RootComponent G) ≤ (BFS.ball G none k).card := by
      simpa only [BFS.Inside, Fintype.card_coe] using hc
    omega
  obtain ⟨w, hw⟩ := hs
  exact ⟨⟨w, hw⟩⟩

/-- Use the genuine maximum-degree ball estimate to make every shell up to
the chosen search radius nonempty in the large-component branch. -/
theorem shell_nonempty_of_component_card_gt_geom [Fintype C]
    (I : PinningData (Option O) C) (Δ L : ℕ) (hd : I.DegreeBound Δ)
    (hlarge : (∑ j ∈ range (L + 1), Δ ^ j) < Fintype.card (RootComponent I.graph))
    (k : ℕ) (hk : k ≤ L) : Nonempty (BFS.Shell I.graph none k) := by
  apply shell_nonempty_of_component_card_gt_ball
  apply lt_of_le_of_lt _ hlarge
  apply (Finset.card_le_card (BFS.ball_mono I.graph none hk)).trans
  apply BFS.ball_card_le_geom
  intro w
  have hw := hd w
  unfold PinningData.constraintDegree at hw
  omega

/-- More generally a uniform cutoff above the geometric volume estimate
can be used for the small/large component dichotomy. -/
theorem shell_nonempty_of_component_card_gt_bound [Fintype C]
    (I : PinningData (Option O) C) (Δ L B : ℕ) (hd : I.DegreeBound Δ)
    (hB : (∑ j ∈ range (L + 1), Δ ^ j) ≤ B)
    (hlarge : B < Fintype.card (RootComponent I.graph))
    (k : ℕ) (hk : k ≤ L) : Nonempty (BFS.Shell I.graph none k) :=
  shell_nonempty_of_component_card_gt_geom I Δ L hd (hB.trans_lt hlarge) k hk

/-- The first neighbor on an actual shortest walk from the root to the
shell lies in the root-deleted inside when the inside radius is positive. -/
theorem inside_nonempty_of_shell_nonempty (G : SimpleGraph (Option O)) (k : ℕ)
    (hk : 1 ≤ k) (hs : Nonempty (BFS.Shell G none k)) : Nonempty (Inside G k) := by
  obtain ⟨⟨w, hw⟩⟩ := hs
  obtain ⟨hr, hd⟩ := BFS.mem_shell.mp hw
  obtain ⟨p, _hp⟩ := hr.exists_walk_length_eq_dist
  cases p with
  | nil => simp at hd
  | @cons _ u _ ha p =>
    cases u with
    | none => exact (ha.ne rfl).elim
    | some o =>
      refine ⟨⟨o, BFS.mem_ball.mpr ⟨ha.reachable, ?_⟩⟩⟩
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ha]
      exact hk

/-- Exact cardinal partition of the root-deleted vertex set. -/
theorem child_card_eq_sum (G : SimpleGraph (Option O)) (k : ℕ) :
    Fintype.card O = Fintype.card (Inside G k) +
      Fintype.card (BFS.Shell G none k) + Fintype.card (BFS.Outside G none k) := by
  have h := Fintype.card_congr (childEquiv G k)
  simpa only [Vertex, Separator.Vertex, Fintype.card_sum, Nat.add_assoc] using h

/-- The common exterior is smaller than the parent even if both finite
inside pieces are empty. -/
theorem outside_card_lt_parent (G : SimpleGraph (Option O)) (k : ℕ) :
    Fintype.card (BFS.Outside G none k) < Fintype.card (Option O) := by
  have h := child_card_eq_sum G k
  simp only [Fintype.card_option]
  omega

/-- A nonempty actual shell already makes the exterior smaller than each
root-deleted child. -/
theorem outside_card_lt_child (G : SimpleGraph (Option O)) (k : ℕ)
    (hs : Nonempty (BFS.Shell G none k)) :
    Fintype.card (BFS.Outside G none k) < Fintype.card O := by
  have h := child_card_eq_sum G k
  have hS := Fintype.card_pos_iff.mpr hs
  omega

/-- Temporarily unpinning one shell vertex still leaves fewer vertices
than the original parent. -/
theorem unpinOutside_card_lt_parent (G : SimpleGraph (Option O)) (k : ℕ)
    (hs : Nonempty (BFS.Shell G none k)) :
    Fintype.card (Option (BFS.Outside G none k)) < Fintype.card (Option O) := by
  have h := outside_card_lt_child G k hs
  simp only [Fintype.card_option]
  omega

/-- The stronger decrease used by the existing exterior-response lemma
follows from a real shell and a positive inside radius, without a supplied
inside-nonemptiness hypothesis. -/
theorem unpinOutside_card_lt_child (G : SimpleGraph (Option O)) (k : ℕ)
    (hk : 1 ≤ k) (hs : Nonempty (BFS.Shell G none k)) :
    Fintype.card (Option (BFS.Outside G none k)) < Fintype.card O := by
  have h := child_card_eq_sum G k
  have hS := Fintype.card_pos_iff.mpr hs
  have hI := Fintype.card_pos_iff.mpr (inside_nonempty_of_shell_nonempty G k hk hs)
  simp only [Fintype.card_option]
  omega

/-- All nonemptiness and strict-size side conditions needed by the
large-component exterior induction come from graph geometry. -/
theorem large_component_induction_pieces [Fintype C]
    (I : PinningData (Option O) C) (Δ L B : ℕ) (hd : I.DegreeBound Δ)
    (hB : (∑ j ∈ range (L + 1), Δ ^ j) ≤ B)
    (hlarge : B < Fintype.card (RootComponent I.graph))
    (k : ℕ) (hk : 1 ≤ k) (hkL : k ≤ L) :
    Nonempty (BFS.Shell I.graph none k) ∧ Nonempty (Inside I.graph k) ∧
      Fintype.card (BFS.Outside I.graph none k) < Fintype.card O ∧
      Fintype.card (Option (BFS.Outside I.graph none k)) < Fintype.card O := by
  have hs := shell_nonempty_of_component_card_gt_bound I Δ L B hd hB hlarge k hkL
  exact ⟨hs, inside_nonempty_of_shell_nonempty I.graph k hk hs,
    outside_card_lt_child I.graph k hs, unpinOutside_card_lt_child I.graph k hk hs⟩

end
end ZeroFreeness.Potts.OptionBFS
