import ZeroFreeness.Potts.Geometry.BFSShells
import ZeroFreeness.Potts.Model.OptionPinning
import ZeroFreeness.Potts.Geometry.SeparatorRelabel

/-! Split actual root-deleted children using distances in their common
parent graph. The shell and exterior retain their parent BFS vertex types. -/
namespace ZeroFreeness.Potts.OptionBFS
open PottsCI Finset Separator
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {O C : Type*} [Fintype O]
local instance (priority := 2000) : DecidableEq (Option O) := Classical.decEq _

abbrev Inside (G : SimpleGraph (Option O)) (k : ℕ) :=
  {o : O // some o ∈ BFS.ball G none k}
abbrev Vertex (G : SimpleGraph (Option O)) (k : ℕ) :=
  Separator.Vertex (Inside G k) (BFS.Shell G none k) (BFS.Outside G none k)

private def unSome (w : Option O) (hw : w ≠ none) : O :=
  match w with
  | none => False.elim (hw rfl)
  | some o => o

omit [Fintype O] in
private lemma some_unSome (w : Option O) (hw : w ≠ none) : some (unSome w hw) = w := by
  cases w with
  | none => exact (hw rfl).elim
  | some o => rfl

lemma shell_ne_none (G : SimpleGraph (Option O)) (k : ℕ) (s : BFS.Shell G none k) :
    s.val ≠ none := by
  intro he
  have hd := (BFS.mem_shell.mp s.property).2
  rw [he, SimpleGraph.dist_self] at hd
  omega

lemma outside_ne_none (G : SimpleGraph (Option O)) (k : ℕ) (o : BFS.Outside G none k) :
    o.val ≠ none := by
  intro he
  apply o.property
  rw [he]
  exact BFS.center_mem_ball G none (k + 1)

/-- The same original parent vertex, for each of the three child pieces. -/
def parentValue (G : SimpleGraph (Option O)) (k : ℕ) : Vertex G k → Option O :=
  Sum.elim (fun u => some u.val) (Sum.elim Subtype.val Subtype.val)

/-- Insert the root-deleted inside into the parent's full inside. -/
def parentEmbedding (G : SimpleGraph (Option O)) (k : ℕ) : Vertex G k → BFS.SplitVertex G none k :=
  Sum.elim (fun u => Sum.inl ⟨some u.val, u.property⟩)
    (Sum.elim (fun s => Sum.inr (Sum.inl s)) (fun o => Sum.inr (Sum.inr o)))

lemma unsplit_parentEmbedding (G : SimpleGraph (Option O)) (k : ℕ) (w : Vertex G k) :
    BFS.unsplit G none k (parentEmbedding G k w) = parentValue G k w := by
  rcases w with u | s | o <;> rfl

private def childJoin (G : SimpleGraph (Option O)) (k : ℕ) : Vertex G k → O :=
  Sum.elim Subtype.val
    (Sum.elim (fun s => unSome s.val (shell_ne_none G k s))
      (fun o => unSome o.val (outside_ne_none G k o)))

/-- The two child colorings use exactly this common three-piece state space. -/
def childEquiv (G : SimpleGraph (Option O)) (k : ℕ) : O ≃ Vertex G k where
  toFun o := if hi : some o ∈ BFS.ball G none k then Sum.inl ⟨o, hi⟩
    else if hb : some o ∈ BFS.ball G none (k + 1) then Sum.inr (Sum.inl ⟨some o, by
      rw [BFS.ball_succ_eq_union_shell, mem_union] at hb
      exact hb.resolve_left hi⟩)
    else Sum.inr (Sum.inr ⟨some o, hb⟩)
  invFun := childJoin G k
  left_inv o := by dsimp only; split_ifs <;> rfl
  right_inv w := by
    rcases w with u | s | o
    · simp [childJoin, u.property]
    · have hv := some_unSome s.val (shell_ne_none G k s)
      have hi : s.val ∉ BFS.ball G none k :=
        fun hh => disjoint_left.mp (BFS.shell_succ_disjoint_ball G none k) s.property hh
      have hb : s.val ∈ BFS.ball G none (k + 1) := by
        rw [BFS.ball_succ_eq_union_shell, mem_union]
        exact Or.inr s.property
      simp [childJoin, hv, hi, hb]
    · have hv := some_unSome o.val (outside_ne_none G k o)
      have hi : o.val ∉ BFS.ball G none k :=
        fun hh => o.property (BFS.ball_mono G none (by omega) hh)
      simp [childJoin, hv, hi, o.property]

lemma some_childEquiv_symm (G : SimpleGraph (Option O)) (k : ℕ) (w : Vertex G k) :
    some ((childEquiv G k).symm w) =
      BFS.unsplit G none k (parentEmbedding G k w) := by
  rcases w with u | s | o
  · rfl
  · exact some_unSome s.val (shell_ne_none G k s)
  · exact some_unSome o.val (outside_ne_none G k o)

@[simp] lemma some_childEquiv_symm_inside (G : SimpleGraph (Option O)) (k : ℕ)
    (u : Inside G k) : some ((childEquiv G k).symm (Sum.inl u)) = some u.val := rfl

@[simp] lemma some_childEquiv_symm_shell (G : SimpleGraph (Option O)) (k : ℕ)
    (s : BFS.Shell G none k) : some ((childEquiv G k).symm (Sum.inr (Sum.inl s))) = s.val :=
  some_unSome s.val (shell_ne_none G k s)

@[simp] lemma some_childEquiv_symm_outside (G : SimpleGraph (Option O)) (k : ℕ)
    (o : BFS.Outside G none k) : some ((childEquiv G k).symm (Sum.inr (Sum.inr o))) = o.val :=
  some_unSome o.val (outside_ne_none G k o)

variable [Fintype C]

def childSplit (I : PinningData (Option O) C) (a : C) (k : ℕ) : PinningData (Vertex I.graph k) C :=
  relabelData (optionChildData I a) (childEquiv I.graph k)

omit [Fintype C] in
lemma childSplit_adj (I : PinningData (Option O) C) (a : C) (k : ℕ)
    (u w : Vertex I.graph k) :
    (childSplit I a k).graph.Adj u w ↔ I.graph.Adj (parentValue I.graph k u) (parentValue I.graph k w) := by
  change I.graph.Adj (some ((childEquiv I.graph k).symm u))
    (some ((childEquiv I.graph k).symm w)) ↔ _
  rw [some_childEquiv_symm, some_childEquiv_symm, unsplit_parentEmbedding, unsplit_parentEmbedding]

omit [Fintype C] in
theorem childSplit_separates (I : PinningData (Option O) C) (a : C) (k : ℕ) :
    Separates (childSplit I a k) := by
  intro u o
  rw [childSplit_adj]
  exact BFS.no_edge_inside_outside u.property o.property

theorem childSplit_degreeBound (I : PinningData (Option O) C) (a : C) (k : ℕ)
    {Δ : ℕ} (hd : I.DegreeBound Δ) : (childSplit I a k).DegreeBound Δ :=
  relabelData_degreeBound (optionChildData I a) (childEquiv I.graph k)
    (optionChildData_degreeBound I hd a)

omit [Fintype C] in
theorem inside_shell_card_le_ball (G : SimpleGraph (Option O)) (k : ℕ) :
    Fintype.card (Inside G k) + Fintype.card (BFS.Shell G none k) ≤
      (BFS.ball G none (k + 1)).card := by
  have hI : Fintype.card (Inside G k) ≤ Fintype.card (BFS.Inside G none k) := by
    apply Fintype.card_le_of_injective
      (fun u : Inside G k => (⟨some u.val, u.property⟩ : BFS.Inside G none k))
    intro u v he
    apply Subtype.ext
    exact Option.some.inj (congrArg Subtype.val he)
  have hI' : Fintype.card (Inside G k) ≤ (BFS.ball G none k).card := by
    simpa only [BFS.Inside, Fintype.card_coe] using hI
  have hS : Fintype.card (BFS.Shell G none k) = (BFS.shell G none (k + 1)).card := by
    simp only [BFS.Shell, Fintype.card_coe]
  rw [hS, BFS.ball_succ_eq_union_shell,
    card_union_of_disjoint (BFS.shell_succ_disjoint_ball G none k).symm]
  exact Nat.add_le_add_right hI' _

theorem inside_shell_card_le_geom (I : PinningData (Option O) C) (k Δ : ℕ)
    (hd : I.DegreeBound Δ) :
    Fintype.card (Inside I.graph k) + Fintype.card (BFS.Shell I.graph none k) ≤
      ∑ j ∈ range (k + 1 + 1), Δ ^ j := by
  apply (inside_shell_card_le_ball I.graph k).trans
  apply BFS.ball_card_le_geom
  intro w
  have hw := hd w
  unfold PinningData.constraintDegree at hw
  omega

omit [Fintype C] in
lemma outside_not_root_adj (G : SimpleGraph (Option O)) (k : ℕ) (o : BFS.Outside G none k) :
    ¬ G.Adj none o.val := by
  intro ha
  exact o.property (BFS.adjacent_mem_ball_succ (BFS.center_mem_ball G none k) ha)

omit [Fintype C] in
lemma shell_not_root_adj (G : SimpleGraph (Option O)) (k : ℕ) (hk : 1 ≤ k)
    (s : BFS.Shell G none k) : ¬ G.Adj none s.val := by
  intro ha
  have hd := (BFS.mem_shell.mp s.property).2
  have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ha
  omega

lemma childSplit_boundary_outside (I : PinningData (Option O) C) (a c : C) (k : ℕ)
    (o : BFS.Outside I.graph none k) :
    (childSplit I a k).boundaryCount (Sum.inr (Sum.inr o)) c = I.boundaryCount o.val c := by
  change (optionChildData I a).boundaryCount ((childEquiv I.graph k).symm (Sum.inr (Sum.inr o))) c = _
  rw [optionChildData_count, some_childEquiv_symm_outside]
  simp [outside_not_root_adj I.graph k o]

lemma childSplit_boundary_shell (I : PinningData (Option O) C) (a c : C) (k : ℕ)
    (hk : 1 ≤ k) (s : BFS.Shell I.graph none k) :
    (childSplit I a k).boundaryCount (Sum.inr (Sum.inl s)) c = I.boundaryCount s.val c := by
  change (optionChildData I a).boundaryCount ((childEquiv I.graph k).symm (Sum.inr (Sum.inl s))) c = _
  rw [optionChildData_count, some_childEquiv_symm_shell]
  simp [shell_not_root_adj I.graph k hk s]

/-- Both children have precisely the parent's common exterior data. The
exterior identity is valid already at `k = 0`; the shell boundary identity
above uses `k ≥ 1`. -/
theorem childSplit_exterior_eq_parent (I : PinningData (Option O) C) (a : C) (k : ℕ)
    (ξ : BFS.Shell I.graph none k → C) :
    exteriorData (childSplit I a k) ξ = exteriorData (BFS.splitPinning I none k) ξ := by
  have hg : (exteriorData (childSplit I a k) ξ).graph =
      (exteriorData (BFS.splitPinning I none k) ξ).graph := by
    ext u v
    change (childSplit I a k).graph.Adj (Sum.inr (Sum.inr u)) (Sum.inr (Sum.inr v)) ↔
      I.graph.Adj u.val v.val
    rw [childSplit_adj]
    rfl
  have hb : (exteriorData (childSplit I a k) ξ).boundaryCount =
      (exteriorData (BFS.splitPinning I none k) ξ).boundaryCount := by
    funext o c
    change (childSplit I a k).boundaryCount (Sum.inr (Sum.inr o)) c +
        (∑ s : BFS.Shell I.graph none k,
          if (childSplit I a k).graph.Adj (Sum.inr (Sum.inl s)) (Sum.inr (Sum.inr o)) ∧ ξ s = c
            then 1 else 0) =
      I.boundaryCount o.val c +
        ∑ s : BFS.Shell I.graph none k, if I.graph.Adj s.val o.val ∧ ξ s = c then 1 else 0
    rw [childSplit_boundary_outside]
    congr 1
    apply sum_congr rfl
    intro s _
    simp only [childSplit_adj, parentValue, Sum.elim_inl, Sum.elim_inr]
  exact congrArg₂ PinningData.mk hg hb

end
end ZeroFreeness.Potts.OptionBFS
