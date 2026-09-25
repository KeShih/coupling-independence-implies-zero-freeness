import ZeroFreeness.Coupling.Foundations.FinDist
import ZeroFreeness.Coupling.Foundations.PathCoupling
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Stationary comparison (main text, `lem:stationary-comparison`)

`lem:stationary-comparison` (main.tex, Lemma 4.2) at the paper's generality.

The paper's statement: let `d` be the shortest-path metric of a finite
connected state graph with positive edge lengths, `P, Q` Markov kernels on its
vertex set with stationary laws `ν_P, ν_Q`, `0 < κ ≤ 1`, `C ≥ 0`, and assume

* `W_d(P(ξ,·), P(ξ',·)) ≤ (1-κ) d(ξ,ξ')` for adjacent `ξ, ξ'`;
* `E_{ξ ~ ν_Q} W_d(P(ξ,·), Q(ξ,·)) ≤ C`.

Then `W_d(ν_P, ν_Q) ≤ C/κ`.

Here the state graph is a `SimpleGraph S` on a finite type `S`, edge lengths
are a function `ℓ : S → S → ℝ` (only its values on adjacent pairs matter), and
`graphPathMetric G ℓ` is the infimum of the total `ℓ`-length over all walks, i.e.
the shortest-path metric.  The main theorem is
`stationary_comparison_graphPathMetric`; it assumes exactly the paper's
hypotheses (including `C ≥ 0`, which the proof does not use).  The
generalisation `stationary_comparison_graphPathMetric_of_nonneg` only needs
nonnegative edge lengths and no sign condition on `C`.  `W_graphPathMetric_le_of_adjacent` is the path-coupling
step ("summing along shortest paths extends the first bound to all states")
for a general path metric, and `W_graphPathMetric_bind_contract` its extension to
all pairs of laws.

The paper's application (main.tex, proof of `thm:strict-ci`) uses the Hamming
metric; `graphPathMetric_hamming_eq` shows that `ham` is the shortest-path
metric of the Hamming graph (adjacency = Hamming distance one) with unit edge
lengths, and `stationary_comparison_ham` is the resulting instance.
-/

namespace PottsCI

open PottsCI PottsCI.FinDist

noncomputable section

variable {S : Type*}

/-! ## The shortest-path metric of a graph with edge lengths -/

/-- Total length of a walk, with edge lengths `ℓ`. -/
def walkLength {G : SimpleGraph S} (ℓ : S → S → ℝ) : ∀ {x y : S}, G.Walk x y → ℝ
  | _, _, SimpleGraph.Walk.nil => 0
  | u, _, @SimpleGraph.Walk.cons _ _ _ v _ _ p => ℓ u v + walkLength ℓ p

@[simp] lemma walkLength_nil {G : SimpleGraph S} (ℓ : S → S → ℝ) (x : S) :
    walkLength ℓ (SimpleGraph.Walk.nil : G.Walk x x) = 0 := rfl

@[simp] lemma walkLength_cons {G : SimpleGraph S} (ℓ : S → S → ℝ) {u v w : S}
    (h : G.Adj u v) (p : G.Walk v w) :
    walkLength ℓ (SimpleGraph.Walk.cons h p) = ℓ u v + walkLength ℓ p := rfl

lemma walkLength_append {G : SimpleGraph S} (ℓ : S → S → ℝ) {x y z : S}
    (p : G.Walk x y) (q : G.Walk y z) :
    walkLength ℓ (p.append q) = walkLength ℓ p + walkLength ℓ q := by
  induction p with
  | nil => simp [SimpleGraph.Walk.nil_append]
  | cons h p ih =>
    rw [SimpleGraph.Walk.cons_append, walkLength_cons, walkLength_cons, ih]
    ring

lemma walkLength_nonneg {G : SimpleGraph S} {ℓ : S → S → ℝ}
    (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) {x y : S} (p : G.Walk x y) :
    0 ≤ walkLength ℓ p := by
  induction p with
  | nil => simp
  | cons h p ih => rw [walkLength_cons]; exact add_nonneg (hℓ _ _ h) ih

/-- The shortest-path metric of the graph `G` with edge lengths `ℓ`: the
infimum of the lengths of all walks from `x` to `y`. -/
def graphPathMetric (G : SimpleGraph S) (ℓ : S → S → ℝ) (x y : S) : ℝ :=
  sInf (Set.range (fun p : G.Walk x y => walkLength ℓ p))

section PathMetric

variable {G : SimpleGraph S} {ℓ : S → S → ℝ}

lemma graphPathMetric_set_nonempty (hG : G.Connected) (x y : S) :
    (Set.range (fun p : G.Walk x y => walkLength ℓ p)).Nonempty := by
  obtain ⟨p⟩ := hG.preconnected x y
  exact ⟨_, ⟨p, rfl⟩⟩

lemma graphPathMetric_set_bddBelow (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (x y : S) :
    BddBelow (Set.range (fun p : G.Walk x y => walkLength ℓ p)) := by
  refine ⟨0, ?_⟩
  rintro r ⟨p, rfl⟩
  exact walkLength_nonneg hℓ p

lemma graphPathMetric_le_walkLength (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    {x y : S} (p : G.Walk x y) : graphPathMetric G ℓ x y ≤ walkLength ℓ p :=
  csInf_le (graphPathMetric_set_bddBelow hℓ x y) ⟨p, rfl⟩

lemma graphPathMetric_nonneg (hG : G.Connected) (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    (x y : S) : 0 ≤ graphPathMetric G ℓ x y := by
  refine le_csInf (graphPathMetric_set_nonempty hG x y) ?_
  rintro r ⟨p, rfl⟩
  exact walkLength_nonneg hℓ p

lemma graphPathMetric_self (hG : G.Connected) (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    (x : S) : graphPathMetric G ℓ x x = 0 :=
  le_antisymm (by simpa using graphPathMetric_le_walkLength hℓ (SimpleGraph.Walk.nil : G.Walk x x))
    (graphPathMetric_nonneg hG hℓ x x)

lemma graphPathMetric_le_length_of_adj (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    {u v : S} (h : G.Adj u v) : graphPathMetric G ℓ u v ≤ ℓ u v := by
  simpa using graphPathMetric_le_walkLength hℓ (SimpleGraph.Walk.cons h SimpleGraph.Walk.nil)

lemma graphPathMetric_triangle (hG : G.Connected) (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    (x y z : S) : graphPathMetric G ℓ x z ≤ graphPathMetric G ℓ x y + graphPathMetric G ℓ y z := by
  have hq : ∀ q : G.Walk y z, graphPathMetric G ℓ x z - walkLength ℓ q ≤ graphPathMetric G ℓ x y := by
    intro q
    refine le_csInf (graphPathMetric_set_nonempty hG x y) ?_
    rintro r ⟨p, rfl⟩
    have := graphPathMetric_le_walkLength hℓ (p.append q)
    rw [walkLength_append] at this
    linarith
  have : graphPathMetric G ℓ x z - graphPathMetric G ℓ x y ≤ graphPathMetric G ℓ y z := by
    refine le_csInf (graphPathMetric_set_nonempty hG y z) ?_
    rintro r ⟨q, rfl⟩
    have := hq q
    linarith
  linarith

/-- With positive edge lengths, distinct states are at positive distance, so
`graphPathMetric` is a genuine metric (symmetric when `ℓ` is).  This lemma is not
needed below; it records that the paper's hypotheses make `d` a metric. -/
lemma graphPathMetric_pos_of_ne [Fintype S] (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 < ℓ u v) {x y : S} (hxy : x ≠ y) :
    0 < graphPathMetric G ℓ x y := by
  classical
  have hℓ' : ∀ u v, G.Adj u v → 0 ≤ ℓ u v := fun u v h => (hℓ u v h).le
  have hfirst : ∀ q : G.Walk x y, ∃ v, G.Adj x v ∧ ℓ x v ≤ walkLength ℓ q := by
    intro q
    cases q with
    | nil => exact absurd rfl hxy
    | cons h q =>
      exact ⟨_, h, by rw [walkLength_cons]; linarith [walkLength_nonneg hℓ' q]⟩
  obtain ⟨p⟩ := hG.preconnected x y
  obtain ⟨v₀, hv₀, -⟩ := hfirst p
  let N : Finset S := Finset.univ.filter fun v => G.Adj x v
  have hN : N.Nonempty := ⟨v₀, by simp [N, hv₀]⟩
  have hm : 0 < N.inf' hN (ℓ x) :=
    (Finset.lt_inf'_iff hN).2 fun v hv => hℓ _ _ (by simpa [N] using hv)
  refine lt_of_lt_of_le hm (le_csInf (graphPathMetric_set_nonempty hG x y) ?_)
  rintro r ⟨q, rfl⟩
  obtain ⟨v, hv, hle⟩ := hfirst q
  exact (Finset.inf'_le _ (by simpa [N] using hv)).trans hle

/-! ## Path coupling for a general path metric -/

variable [Fintype S]

/-- Path coupling: an adjacent-state bound `W_d(P ξ, P ξ') ≤ c d(ξ,ξ')`
extends to all pairs of states, by summing along walks. -/
theorem W_graphPathMetric_le_of_adjacent (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (P : S → FinDist S)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hadj : ∀ ξ ξ', G.Adj ξ ξ' →
      W (graphPathMetric G ℓ) (P ξ) (P ξ') ≤ c * graphPathMetric G ℓ ξ ξ')
    (x y : S) :
    W (graphPathMetric G ℓ) (P x) (P y) ≤ c * graphPathMetric G ℓ x y := by
  classical
  have hd := graphPathMetric_nonneg hG hℓ
  have hd0 := graphPathMetric_self hG hℓ
  have htri := graphPathMetric_triangle hG hℓ
  have hwalk : ∀ {u w : S} (p : G.Walk u w),
      W (graphPathMetric G ℓ) (P u) (P w) ≤ c * walkLength ℓ p := by
    intro u w p
    induction p with
    | nil => rw [W_self hd hd0]; simp
    | @cons u v w h p ih =>
      have h1 := W_triangle hd hd hd htri (P u) (P v) (P w)
      have h2 := hadj u v h
      have h3 := graphPathMetric_le_length_of_adj hℓ h
      rw [walkLength_cons]
      nlinarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨r, ⟨p, rfl⟩, hp⟩ := exists_lt_of_csInf_lt (graphPathMetric_set_nonempty hG x y)
    (lt_add_of_pos_right (graphPathMetric G ℓ x y) hε)
  have h1 := hwalk p
  have h2 : c * walkLength ℓ p ≤ c * (graphPathMetric G ℓ x y + ε) :=
    mul_le_mul_of_nonneg_left hp.le hc0
  nlinarith

/-- Coupling the initial states: the adjacent-state bound gives contraction
`W_d(νP, ν'P) ≤ c W_d(ν, ν')` for all pairs of laws. -/
theorem W_graphPathMetric_bind_contract (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v) (P : S → FinDist S)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hadj : ∀ ξ ξ', G.Adj ξ ξ' →
      W (graphPathMetric G ℓ) (P ξ) (P ξ') ≤ c * graphPathMetric G ℓ ξ ξ')
    (α β : FinDist S) :
    W (graphPathMetric G ℓ) (α.bind P) (β.bind P) ≤ c * W (graphPathMetric G ℓ) α β :=
  W_bind_contract (graphPathMetric_nonneg hG hℓ) (graphPathMetric_nonneg hG hℓ) hc0 P
    (W_graphPathMetric_le_of_adjacent hG hℓ P hc0 hc1 hadj) α β

/-! ## Stationary comparison -/

/-- **`lem:stationary-comparison`, with nonnegative edge lengths.**
Adjacent-state contraction for `P` and a `ν_Q`-averaged one-step disagreement
bound give `W_d(ν_P, ν_Q) ≤ C/κ`. -/
theorem stationary_comparison_graphPathMetric_of_nonneg (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 ≤ ℓ u v)
    (P Q : S → FinDist S) (νP νQ : FinDist S)
    (hνP : IsStationary P νP) (hνQ : IsStationary Q νQ)
    {κ C : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hcontr : ∀ ξ ξ', G.Adj ξ ξ' →
      W (graphPathMetric G ℓ) (P ξ) (P ξ') ≤ (1 - κ) * graphPathMetric G ℓ ξ ξ')
    (havg : ∑ ξ, νQ.w ξ * W (graphPathMetric G ℓ) (P ξ) (Q ξ) ≤ C) :
    W (graphPathMetric G ℓ) νP νQ ≤ C / κ := by
  classical
  have hd := graphPathMetric_nonneg hG hℓ
  have htri := graphPathMetric_triangle hG hℓ
  have hstep : W (graphPathMetric G ℓ) νP νQ =
      W (graphPathMetric G ℓ) (νP.bind P) (νQ.bind Q) := by
    rw [hνP, hνQ]
  have h1 := W_triangle hd hd hd htri (νP.bind P) (νQ.bind P) (νQ.bind Q)
  have h2 := W_graphPathMetric_bind_contract hG hℓ P (by linarith) (by linarith) hcontr νP νQ
  have h3 := (W_bind_diag hd νQ P Q).trans havg
  rw [le_div_iff₀ hκ0]
  nlinarith

/-- **`lem:stationary-comparison` (main.tex, Lemma 4.2).**  Let `d` be the
shortest-path metric of a finite connected state graph `G` with positive edge
lengths `ℓ`, let `P, Q` be Markov kernels on its vertex set with stationary
laws `ν_P, ν_Q`, and let `0 < κ ≤ 1`.  If
`W_d(P(ξ,·), P(ξ',·)) ≤ (1-κ) d(ξ,ξ')` for adjacent `ξ, ξ'` and
`E_{ξ ~ ν_Q} W_d(P(ξ,·), Q(ξ,·)) ≤ C`, then `W_d(ν_P, ν_Q) ≤ C/κ`. -/
theorem stationary_comparison_graphPathMetric (hG : G.Connected)
    (hℓ : ∀ u v, G.Adj u v → 0 < ℓ u v)
    (P Q : S → FinDist S) (νP νQ : FinDist S)
    (hνP : IsStationary P νP) (hνQ : IsStationary Q νQ)
    {κ C : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (_hC : 0 ≤ C)
    (hcontr : ∀ ξ ξ', G.Adj ξ ξ' →
      W (graphPathMetric G ℓ) (P ξ) (P ξ') ≤ (1 - κ) * graphPathMetric G ℓ ξ ξ')
    (havg : ∑ ξ, νQ.w ξ * W (graphPathMetric G ℓ) (P ξ) (Q ξ) ≤ C) :
    W (graphPathMetric G ℓ) νP νQ ≤ C / κ :=
  stationary_comparison_graphPathMetric_of_nonneg hG (fun u v h => (hℓ u v h).le)
    P Q νP νQ hνP hνQ hκ0 hκ1 hcontr havg

end PathMetric

/-! ## The Hamming instance -/

section Hamming

variable (V C : Type*) [Fintype V] [DecidableEq V] [DecidableEq C]

/-- The Hamming graph on configurations: two configurations are adjacent when
they differ at exactly one vertex. -/
def hammingGraph : SimpleGraph (V → C) where
  Adj X Y := hamCard X Y = 1
  symm := ⟨fun X Y h => by
    rw [hamCard_comm]
    exact h⟩
  loopless := ⟨fun X h => by
    change hamCard X X = 1 at h
    rw [hamCard_self] at h
    exact absurd h (by norm_num)⟩

variable {V C}

lemma hamming_walk_of_card (k : ℕ) :
    ∀ X Y : V → C, hamCard X Y = k →
      ∃ p : (hammingGraph V C).Walk X Y, walkLength (fun _ _ => (1 : ℝ)) p = k := by
  induction k with
  | zero =>
    intro X Y h
    have := hamCard_eq_zero h
    subst this
    exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | succ k ih =>
    intro X Y h
    obtain ⟨Z, hXZ, hZY⟩ := exists_intermediate h
    obtain ⟨p, hp⟩ := ih Z Y hZY
    refine ⟨SimpleGraph.Walk.cons (show (hammingGraph V C).Adj X Z from hXZ) p, ?_⟩
    rw [walkLength_cons, hp]
    push_cast
    ring

lemma ham_le_walkLength {X Y : V → C} (p : (hammingGraph V C).Walk X Y) :
    ham X Y ≤ walkLength (fun _ _ => (1 : ℝ)) p := by
  induction p with
  | nil => simp [ham_self]
  | @cons X Z Y h p ih =>
    have ht := ham_triangle X Z Y
    have h1 : ham X Z = 1 := by
      have h' : hamCard X Z = 1 := h
      simp [ham, h']
    rw [walkLength_cons]
    linarith

lemma hammingGraph_connected [Nonempty C] : (hammingGraph V C).Connected := by
  refine ⟨fun X Y => ?_⟩
  obtain ⟨p, -⟩ := hamming_walk_of_card (hamCard X Y) X Y rfl
  exact ⟨p⟩

/-- The Hamming distance is the shortest-path metric of the Hamming graph with
unit edge lengths. -/
theorem graphPathMetric_hamming_eq [Nonempty C] (X Y : V → C) :
    graphPathMetric (hammingGraph V C) (fun _ _ => 1) X Y = ham X Y := by
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hamming_walk_of_card (hamCard X Y) X Y rfl
    have := graphPathMetric_le_walkLength (fun _ _ _ => zero_le_one) p
    rw [hp] at this
    exact this
  · refine le_csInf (graphPathMetric_set_nonempty hammingGraph_connected X Y) ?_
    rintro r ⟨p, rfl⟩
    exact ham_le_walkLength p

/-- `lem:stationary-comparison` for the Hamming metric used in the paper:
adjacent-state contraction and the `ν_Q`-averaged one-step bound. -/
theorem stationary_comparison_ham [Fintype C] [Nonempty C]
    (P Q : (V → C) → FinDist (V → C)) (νP νQ : FinDist (V → C))
    (hνP : IsStationary P νP) (hνQ : IsStationary Q νQ)
    {κ C₀ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hcontr : ∀ X Y : V → C, hamCard X Y = 1 → W ham (P X) (P Y) ≤ 1 - κ)
    (havg : ∑ X, νQ.w X * W ham (P X) (Q X) ≤ C₀) :
    W ham νP νQ ≤ C₀ / κ := by
  have hd : graphPathMetric (hammingGraph V C) (fun _ _ => 1) = ham := by
    funext X Y
    exact graphPathMetric_hamming_eq X Y
  have h := stationary_comparison_graphPathMetric_of_nonneg hammingGraph_connected
    (fun _ _ _ => zero_le_one) P Q νP νQ hνP hνQ hκ0 hκ1 (C := C₀) ?_ ?_
  · rwa [hd] at h
  · intro X Y hXY
    rw [hd]
    have h1 : ham X Y = 1 := by
      have h' : hamCard X Y = 1 := hXY
      simp [ham, h']
    rw [h1, mul_one]
    exact hcontr X Y hXY
  · rwa [hd]

end Hamming

end

end PottsCI
