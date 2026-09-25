import ZeroFreeness.Holant.InstanceSeparator
import ZeroFreeness.Holant.Geometry
import ZeroFreeness.Holant.CouplingTransport

/-!
# Actual shell separators and shell selection

Use a fixed ambient interaction graph and intersect its spheres with the
current free edge set. Empty current spheres are allowed.  Ambient separation
is inherited by every residual instance, and the local variable count stays
bounded by an ambient ball. Thus no metric reconstruction after deletion and
no assumed separator oracle are needed.
-/
namespace ZeroFreeness.Holant
open Finset PottsCI PottsCI.FinDist HolantCoupling
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- Every shared endpoint of distinct free edges is an ambient interaction. -/
def AmbientCompatible (H : NormalizedInstance V E) (Γ : SimpleGraph E) : Prop :=
  ∀ a ∈ H.edges, ∀ b ∈ H.edges, a ≠ b → ∀ v,
    H.incidence a v → H.incidence b v → Γ.Adj a b

def ambientInterior (H : NormalizedInstance V E) (Γ : SimpleGraph E) (e : E) (r : ℕ) :
    Finset E := (H.edges ∩ BFS.ball Γ e r).erase e

def ambientShell (H : NormalizedInstance V E) (Γ : SimpleGraph E) (e : E) (r : ℕ) :
    Finset E := H.edges ∩ BFS.shell Γ e (r + 1)

def ambientExterior (H : NormalizedInstance V E) (Γ : SimpleGraph E) (e : E) (r : ℕ) :
    Finset E := H.edges \ BFS.ball Γ e (r + 1)

@[simp] theorem mem_ambientInterior (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e a : E) (r : ℕ) : a ∈ ambientInterior H Γ e r ↔
      a ≠ e ∧ a ∈ H.edges ∧ a ∈ BFS.ball Γ e r := by simp [ambientInterior]

@[simp] theorem mem_ambientShell (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e a : E) (r : ℕ) : a ∈ ambientShell H Γ e r ↔
      a ∈ H.edges ∧ a ∈ BFS.shell Γ e (r + 1) := by simp [ambientShell]

@[simp] theorem mem_ambientExterior (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e a : E) (r : ℕ) : a ∈ ambientExterior H Γ e r ↔
      a ∈ H.edges ∧ a ∉ BFS.ball Γ e (r + 1) := by simp [ambientExterior]

theorem root_not_ambientShell (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (r : ℕ) : e ∉ ambientShell H Γ e r := by
  simp [ambientShell, BFS.mem_shell]

theorem root_not_ambientExterior (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (r : ℕ) : e ∉ ambientExterior H Γ e r := by
  simp [ambientExterior]

/-- The actual root separator, constructed from the ambient BFS sphere. -/
def ambientSeparator (H : NormalizedInstance V E) (Γ : SimpleGraph E) (e : E)
    (he : e ∈ H.edges) (hc : AmbientCompatible H Γ) (r : ℕ) : RootSeparator H e where
  interior := ambientInterior H Γ e r
  shell := ambientShell H Γ e r
  exterior := ambientExterior H Γ e r
  shell_interior := by
    apply disjoint_left.mpr
    intro a hs hi
    have hs' := ((mem_ambientShell H Γ e a r).1 hs).2
    have hi' := ((mem_ambientInterior H Γ e a r).1 hi).2.2
    exact disjoint_left.mp (BFS.shell_succ_disjoint_ball Γ e r) hs' hi'
  shell_exterior := by
    apply disjoint_left.mpr
    intro a hs ho
    have hs' := ((mem_ambientShell H Γ e a r).1 hs).2
    have ho' := ((mem_ambientExterior H Γ e a r).1 ho).2
    apply ho'
    have hsdata := BFS.mem_shell.mp hs'
    exact BFS.mem_ball.mpr ⟨hsdata.1, hsdata.2.le⟩
  interior_exterior := by
    apply disjoint_left.mpr
    intro a hi ho
    exact ((mem_ambientExterior H Γ e a r).1 ho).2
      (BFS.ball_mono Γ e (by omega) ((mem_ambientInterior H Γ e a r).1 hi).2.2)
  cover := by
    ext a
    by_cases hae : a = e
    · subst a
      simp
    · simp only [mem_union, mem_ambientShell, mem_ambientInterior,
        mem_ambientExterior, mem_erase, BFS.ball_succ_eq_union_shell,
        mem_union]
      tauto
  separated := by
    intro v a ha b hb hai hbi
    have hi := ((mem_ambientInterior H Γ e a r).1 ha).2.2
    have ho := ((mem_ambientExterior H Γ e b r).1 hb).2
    have hab : a ≠ b := by
      intro h
      subst b
      exact ho (BFS.ball_mono Γ e (by omega) hi)
    exact BFS.no_edge_inside_outside hi ho
      (hc a ((mem_ambientInterior H Γ e a r).1 ha).2.1
        b ((mem_ambientExterior H Γ e b r).1 hb).1 hab v hai hbi)
  root_exterior := by
    intro v hv hev
    obtain ⟨b, hb, hbi⟩ := hv
    have ho := ((mem_ambientExterior H Γ e b r).1 hb).2
    have heb : e ≠ b := by
      intro h
      subst b
      exact ho (BFS.center_mem_ball Γ e (r + 1))
    exact BFS.no_edge_inside_outside (BFS.center_mem_ball Γ e r) ho
      (hc e he b ((mem_ambientExterior H Γ e b r).1 hb).1 heb v hev hbi)

/-- All local inside-plus-shell edges lie in the same bounded ambient ball. -/
theorem ambient_local_subset_ball (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (r : ℕ) : ambientShell H Γ e r ∪ ambientInterior H Γ e r ⊆
      BFS.ball Γ e (r + 1) := by
  intro a ha
  rcases mem_union.mp ha with hs | hi
  · have hsdata := BFS.mem_shell.mp ((mem_ambientShell H Γ e a r).1 hs).2
    exact BFS.mem_ball.mpr ⟨hsdata.1, hsdata.2.le⟩
  · exact BFS.ball_mono Γ e (by omega) ((mem_ambientInterior H Γ e a r).1 hi).2.2

theorem ambient_local_card_le (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (r L D : ℕ) (hr : r < L) (hdeg : ∀ a, Γ.degree a ≤ D) :
    (ambientShell H Γ e r ∪ ambientInterior H Γ e r).card ≤ (D + 1) ^ L := by
  exact (card_le_card ((ambient_local_subset_ball H Γ e r).trans
    (BFS.ball_mono Γ e (by omega)))).trans (BFS.ball_card_le_pow Γ e L D hdeg)

theorem ambient_exterior_card_lt (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (he : e ∈ H.edges) (r : ℕ) :
    (ambientExterior H Γ e r).card < H.edges.card := by
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨sdiff_subset, ?_⟩
  intro h
  exact root_not_ambientExterior H Γ e r (h.symm ▸ he)

/-- Leaving one shell coordinate together with the exterior free is still
strictly smaller than the current instance, because its root is omitted. -/
theorem ambient_bridge_card_lt (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (he : e ∈ H.edges) (r : ℕ) {a : E} (ha : a ∈ ambientShell H Γ e r) :
    (insert a (ambientExterior H Γ e r)).card < H.edges.card := by
  apply card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨insert_subset ((mem_ambientShell H Γ e a r).1 ha).1 sdiff_subset, ?_⟩
  intro h
  have hm : e ∈ insert a (ambientExterior H Γ e r) := h.symm ▸ he
  rcases mem_insert.mp hm with hea | heo
  · subst a
    exact root_not_ambientShell H Γ e r ha
  · exact root_not_ambientExterior H Γ e r heo

theorem ambient_shells_disjoint (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (ambientShell H Γ e r) (ambientShell H Γ e s) :=
  (BFS.shells_disjoint Γ e (by omega : r + 1 ≠ s + 1)).mono
    inter_subset_right inter_subset_right

/-- Sum of projected subset-Hamming costs over disjoint edge sets. -/
theorem sum_subsetHam_inter_le {ι : Type*} [Fintype ι]
    (shells : ι → Finset E) (hdisj : ∀ i j, i ≠ j → Disjoint (shells i) (shells j))
    (A B : Finset E) :
    (∑ i, subsetHam (A ∩ shells i) (B ∩ shells i)) ≤ subsetHam A B := by
  classical
  unfold subsetHam
  rw [sum_comm]
  apply sum_le_sum
  intro e _
  have hcount : (∑ i, if e ∈ shells i then (1 : ℝ) else 0) ≤ 1 := by
    have hcard : (univ.filter fun i => e ∈ shells i).card ≤ 1 := by
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hij
      exact disjoint_left.mp (hdisj i j hij) (mem_filter.mp hi).2 (mem_filter.mp hj).2
    rw [sum_boole]
    exact_mod_cast hcard
  by_cases hA : e ∈ A <;> by_cases hB : e ∈ B
  · simp [Finset.mem_inter, hA, hB]
  · simpa [Finset.mem_inter, hA, hB] using hcount
  · simpa [Finset.mem_inter, hA, hB] using hcount
  · simp [Finset.mem_inter, hA, hB]

/-- A shell projection of an actual subset law. -/
def subsetShellLaw (μ : FinDist (Finset E)) (S : Finset E) : FinDist (Finset E) :=
  mapLaw μ (fun A => A ∩ S)

theorem W_subsetShellLaw_le (μ ν : FinDist (Finset E)) (S : Finset E) :
    W subsetHam (subsetShellLaw μ S) (subsetShellLaw ν S) ≤
      W (fun A B => subsetHam (A ∩ S) (B ∩ S)) μ ν :=
  W_mapLaw_le _ _ subsetHam subsetHam_nonneg

/-- The projected real Gibbs laws have one shared shell budget. This is
stated for arbitrary laws, so it applies also on zero-activity faces. -/
theorem sum_W_subsetShellLaw_le {ι : Type*} [Fintype ι]
    (μ ν : FinDist (Finset E)) (shells : ι → Finset E)
    (hdisj : ∀ i j, i ≠ j → Disjoint (shells i) (shells j)) :
    (∑ i, W subsetHam (subsetShellLaw μ (shells i)) (subsetShellLaw ν (shells i))) ≤
      W subsetHam μ ν := by
  calc
    _ ≤ ∑ i, W (fun A B => subsetHam (A ∩ shells i) (B ∩ shells i)) μ ν :=
      sum_le_sum (fun i _ => W_subsetShellLaw_le μ ν (shells i))
    _ ≤ W subsetHam μ ν :=
      ZeroFreeness.sum_W_le_W _ _ (fun _ _ _ => subsetHam_nonneg _ _)
        (sum_subsetHam_inter_le shells hdisj)

/-- Select one of the actual current-edge spheres of ambient radii `1..L`. -/
theorem exists_low_ambient_shell (H : NormalizedInstance V E) (Γ : SimpleGraph E)
    (e : E) (μ ν : FinDist (Finset E)) {L : ℕ} (hL : 0 < L) {C : ℝ}
    (hCI : W subsetHam μ ν ≤ C) :
    ∃ r : ℕ, r < L ∧
      W subsetHam (subsetShellLaw μ (ambientShell H Γ e r))
        (subsetShellLaw ν (ambientShell H Γ e r)) ≤ C / L := by
  have : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  let shells : Fin L → Finset E := fun i => ambientShell H Γ e i.val
  have hdisj : ∀ i j, i ≠ j → Disjoint (shells i) (shells j) := by
    intro i j hij
    exact ambient_shells_disjoint H Γ e (by intro h; exact hij (Fin.ext h))
  obtain ⟨i, hi⟩ := ZeroFreeness.exists_low_W_shell
    (μ := μ) (ν := ν) (fun i A B => subsetHam (A ∩ shells i) (B ∩ shells i)) subsetHam
    (fun _ _ _ => subsetHam_nonneg _ _) (sum_subsetHam_inter_le shells hdisj) hCI
  refine ⟨i.val, i.isLt, ?_⟩
  exact (W_subsetShellLaw_le μ ν (shells i)).trans (by simpa using hi)

end
end ZeroFreeness.Holant
