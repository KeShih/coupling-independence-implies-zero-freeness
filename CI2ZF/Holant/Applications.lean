import CI2ZF.Holant.Capacities
import CI2ZF.Holant.Polytube

/-!
# Uniform Holant domains and capacity applications

`UniformGraphTubes` is the sole analytic input to this file. Its width is
chosen before the finite graph, the signature assignment, and all activity
coordinates. Only actual graph edges are constrained. The results below
give the orthant and common diagonal conclusions of `thm:holant-box`,
`cor:bmatching-short`, and `cor:bcover-short`.
-/
namespace CI2ZF.Holant
open Set Metric Finset
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u

/-- Restrict the tube to actual coordinates; unused ambient coordinates are free. -/
def edgePolytube {E : Type*} (edges : Finset E) (ε a b : ℝ) : Set (E → ℂ) :=
  (fun (z : E → ℂ) (e : {e // e ∈ edges}) => z e.val) ⁻¹'
    polytube {e // e ∈ edges} ε a b

theorem mem_edgePolytube_iff {E : Type*} (edges : Finset E)
    (z : E → ℂ) (ε a b : ℝ) :
    z ∈ edgePolytube edges ε a b ↔
      ∀ e ∈ edges, ∃ x ∈ Icc a b, ‖z e - (x : ℂ)‖ < ε := by
  constructor
  · intro hz e he
    obtain ⟨w, ⟨x, hx, rfl⟩, hw⟩ :=
      mem_thickening_iff.mp (hz ⟨e, he⟩ (mem_univ _))
    exact ⟨x, hx, by simpa [dist_eq_norm] using hw⟩
  · intro hz e _
    obtain ⟨x, hx, hzx⟩ := hz e.val e.property
    exact mem_thickening_iff.mpr
      ⟨(x : ℂ), ⟨x, hx, rfl⟩, by simpa [dist_eq_norm] using hzx⟩

theorem edgePolytube_isOpen {E : Type*} (edges : Finset E) (ε a b : ℝ) :
    IsOpen (edgePolytube edges ε a b) :=
  (polytube_isOpen {e // e ∈ edges} ε a b).preimage
    (continuous_pi fun e => continuous_apply e.val)

/-- The common real bound is chosen before the Cartesian power. -/
def edgeOrthantNeighborhood {E : Type*} (edges : Finset E)
    (width : ℝ → ℝ) : Set (E → ℂ) :=
  ⋃ R > 0, edgePolytube edges (width R) 0 R

theorem edgeOrthantNeighborhood_isOpen {E : Type*} (edges : Finset E)
    (width : ℝ → ℝ) : IsOpen (edgeOrthantNeighborhood edges width) :=
  isOpen_iUnion fun R => isOpen_iUnion fun _ => edgePolytube_isOpen edges (width R) 0 R

theorem nonnegative_mem_edgeOrthantNeighborhood {E : Type*} (edges : Finset E)
    (width : ℝ → ℝ) (hwidth : ∀ R > 0, 0 < width R)
    (x : E → ℝ) (hx : ∀ e ∈ edges, 0 ≤ x e) :
    (fun e => (x e : ℂ)) ∈ edgeOrthantNeighborhood edges width := by
  have h := nonnegative_mem_orthantNeighborhood width hwidth
    (fun e : {e // e ∈ edges} => x e.val) (fun e => hx e.val e.property)
  simpa only [edgeOrthantNeighborhood, orthantNeighborhood, edgePolytube,
    mem_iUnion, Set.mem_preimage] using h

/-- The uniform finite-graph theorem, with exactly its true-edge assumptions.
The universe is fixed while the graph size is unrestricted. -/
def UniformGraphTubes (Δ : ℕ) (F : Finset Signature) : Prop :=
  ∀ R : ℝ, 0 < R → ∃ ε : ℝ, 0 < ε ∧
    ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) →
      ∀ f : V → Signature, (∀ v, (f v).arity = G.degree v) →
        (∀ v, f v ∈ F) → ∀ z : Sym2 V → ℂ,
          (∀ e ∈ G.edgeFinset, ∃ x ∈ Icc (0 : ℝ) R,
            ‖z e - (x : ℂ)‖ < ε) →
          graphPartition G (fun v k => ((f v).value k : ℂ)) z ≠ 0

/-- One simultaneous choice of all box widths, independent of graph size. -/
def tubeWidth {Δ : ℕ} {F : Finset Signature}
    (htube : UniformGraphTubes.{u} Δ F) (R : ℝ) : ℝ :=
  if hR : 0 < R then Classical.choose (htube R hR) else 1

theorem tubeWidth_pos {Δ : ℕ} {F : Finset Signature}
    (htube : UniformGraphTubes.{u} Δ F) (R : ℝ) : 0 < tubeWidth htube R := by
  unfold tubeWidth
  split
  · exact (Classical.choose_spec (htube R ‹0 < R›)).1
  · norm_num

theorem graphPartition_ne_zero_polytube {Δ : ℕ} {F : Finset Signature}
    (htube : UniformGraphTubes.{u} Δ F) {R : ℝ} (hR : 0 < R)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (f : V → Signature)
    (harity : ∀ v, (f v).arity = G.degree v) (hf : ∀ v, f v ∈ F)
    (z : Sym2 V → ℂ) (hz : z ∈ edgePolytube G.edgeFinset (tubeWidth htube R) 0 R) :
    graphPartition G (fun v k => ((f v).value k : ℂ)) z ≠ 0 := by
  have ht := (Classical.choose_spec (htube R hR)).2 V G hΔ f harity hf z
  apply ht
  have hz' := (mem_edgePolytube_iff G.edgeFinset z (tubeWidth htube R) 0 R).mp hz
  simpa only [tubeWidth, dif_pos hR] using hz'

theorem graphPartition_ne_zero_orthant {Δ : ℕ} {F : Finset Signature}
    (htube : UniformGraphTubes.{u} Δ F)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (f : V → Signature)
    (harity : ∀ v, (f v).arity = G.degree v) (hf : ∀ v, f v ∈ F)
    (z : Sym2 V → ℂ)
    (hz : z ∈ edgeOrthantNeighborhood G.edgeFinset (tubeWidth htube)) :
    graphPartition G (fun v k => ((f v).value k : ℂ)) z ≠ 0 := by
  obtain ⟨R, hR, hz⟩ := mem_iUnion₂.mp hz
  exact graphPartition_ne_zero_polytube htube hR G hΔ f harity hf z hz

/-- The full open-orthant conclusion, with a graph-independent width function. -/
theorem graphPartition_orthant {Δ : ℕ} {F : Finset Signature}
    (htube : UniformGraphTubes.{u} Δ F)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (f : V → Signature)
    (harity : ∀ v, (f v).arity = G.degree v) (hf : ∀ v, f v ∈ F) :
    IsOpen (edgeOrthantNeighborhood G.edgeFinset (tubeWidth htube)) ∧
      (∀ x : Sym2 V → ℝ, (∀ e ∈ G.edgeFinset, 0 ≤ x e) →
        (fun e => (x e : ℂ)) ∈ edgeOrthantNeighborhood G.edgeFinset (tubeWidth htube)) ∧
      ∀ z ∈ edgeOrthantNeighborhood G.edgeFinset (tubeWidth htube),
        graphPartition G (fun v k => ((f v).value k : ℂ)) z ≠ 0 := by
  exact ⟨edgeOrthantNeighborhood_isOpen _ _,
    fun x hx => nonnegative_mem_edgeOrthantNeighborhood _ _
      (fun R _ => tubeWidth_pos htube R) x hx,
    fun z hz => graphPartition_ne_zero_orthant htube G hΔ f harity hf z hz⟩

theorem graphPartition_uniform_diagonal {Δ : ℕ} {F : Finset Signature}
    (htube : UniformGraphTubes.{u} Δ F) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, 0 ≤ x → (x : ℂ) ∈ U) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ f : V → Signature,
          (∀ v, (f v).arity = G.degree v) → (∀ v, f v ∈ F) →
          ∀ z ∈ U, graphPartition G (fun v k => ((f v).value k : ℂ)) (fun _ => z) ≠ 0 := by
  refine ⟨diagonalNeighborhood (tubeWidth htube), diagonalNeighborhood_isOpen _,
    fun x hx => nonnegative_mem_diagonalNeighborhood _
      (fun R _ => tubeWidth_pos htube R) hx, ?_⟩
  intro V _ _ G hΔ f harity hf z hz
  obtain ⟨R, hR, hz⟩ := mem_iUnion₂.mp hz
  apply graphPartition_ne_zero_polytube htube hR G hΔ f harity hf
  exact fun _ _ => hz

theorem matchingPartition_ne_zero_polytube {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ)) {R : ℝ} (hR : 0 < R)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v)
    (z : Sym2 V → ℂ) (hz : z ∈ edgePolytube G.edgeFinset (tubeWidth htube R) 0 R) :
    matchingPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  rw [matchingPartition_eq_capacity_holant graphIncidence G.edgeFinset
    (fun v => G.degree v) b hb z]
  exact graphPartition_ne_zero_polytube htube hR G hΔ
    (fun v => capacitySignature (G.degree v) (b v) (hb v)) (fun _ => rfl)
    (fun v => capacitySignature_mem_family Δ _ _ (hb v) (hΔ v)) z hz

/-- Corollary `cor:bmatching-short`: the width precedes every graph and capacity. -/
theorem matching_uniform_polytube {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ)) {R : ℝ} (hR : 0 < R) :
    ∃ ε > 0, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
        ∀ z ∈ edgePolytube G.edgeFinset ε 0 R,
          matchingPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  exact ⟨tubeWidth htube R, tubeWidth_pos htube R,
    fun _ _ _ G hΔ b hb z hz => matchingPartition_ne_zero_polytube htube hR G hΔ b hb z hz⟩

theorem matching_orthant {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ))
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v) :
    IsOpen (edgeOrthantNeighborhood G.edgeFinset (tubeWidth htube)) ∧
      (∀ x : Sym2 V → ℝ, (∀ e ∈ G.edgeFinset, 0 ≤ x e) →
        (fun e => (x e : ℂ)) ∈ edgeOrthantNeighborhood G.edgeFinset (tubeWidth htube)) ∧
      ∀ z ∈ edgeOrthantNeighborhood G.edgeFinset (tubeWidth htube),
        matchingPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  refine ⟨edgeOrthantNeighborhood_isOpen _ _,
    fun x hx => nonnegative_mem_edgeOrthantNeighborhood _ _
      (fun R _ => tubeWidth_pos htube R) x hx, ?_⟩
  intro z hz
  obtain ⟨R, hR, hz⟩ := mem_iUnion₂.mp hz
  exact matchingPartition_ne_zero_polytube htube hR G hΔ b hb z hz

theorem matching_uniform_diagonal {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ)) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, 0 ≤ x → (x : ℂ) ∈ U) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          ∀ z ∈ U, matchingPartition graphIncidence G.edgeFinset b (fun _ => z) ≠ 0 := by
  refine ⟨diagonalNeighborhood (tubeWidth htube), diagonalNeighborhood_isOpen _,
    fun x hx => nonnegative_mem_diagonalNeighborhood _
      (fun R _ => tubeWidth_pos htube R) hx, ?_⟩
  intro V _ _ G hΔ b hb z hz
  obtain ⟨R, hR, hz⟩ := mem_iUnion₂.mp hz
  exact matchingPartition_ne_zero_polytube htube hR G hΔ b hb _ (fun _ _ => hz)

/-- Positive-box domains, with both endpoints common to all coordinates. -/
def positiveOrthantNeighborhood (E : Type*) (width : ℝ → ℝ → ℝ) : Set (E → ℂ) :=
  ⋃ a > 0, ⋃ b ≥ a, polytube E (width a b) a b

def positiveDiagonalNeighborhood (width : ℝ → ℝ → ℝ) : Set ℂ :=
  ⋃ a > 0, ⋃ b ≥ a, thickening (width a b) (realInterval a b)

theorem positiveOrthantNeighborhood_isOpen (E : Type*) [Finite E]
    (width : ℝ → ℝ → ℝ) : IsOpen (positiveOrthantNeighborhood E width) :=
  isOpen_iUnion fun a => isOpen_iUnion fun _ =>
    isOpen_iUnion fun b => isOpen_iUnion fun _ => polytube_isOpen E (width a b) a b

theorem positiveDiagonalNeighborhood_isOpen (width : ℝ → ℝ → ℝ) :
    IsOpen (positiveDiagonalNeighborhood width) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_thickening

/-- A finite positive vector admits common positive lower and upper bounds,
including when the coordinate type is empty. -/
theorem positive_mem_positiveOrthantNeighborhood {E : Type*} [Fintype E]
    (width : ℝ → ℝ → ℝ) (hwidth : ∀ a > 0, ∀ b ≥ a, 0 < width a b)
    (x : E → ℝ) (hx : ∀ e, 0 < x e) :
    (fun e => (x e : ℂ)) ∈ positiveOrthantNeighborhood E width := by
  let s : ℝ := 1 + ∑ e, (x e)⁻¹
  let b : ℝ := 1 + ∑ e, x e
  have hsum : 0 ≤ ∑ e, (x e)⁻¹ := sum_nonneg (fun e _ => (inv_pos.mpr (hx e)).le)
  have hsumx : 0 ≤ ∑ e, x e := sum_nonneg (fun e _ => (hx e).le)
  have hs : 0 < s := by dsimp [s]; linarith
  have hsb : s⁻¹ ≤ b := by
    have hi : s⁻¹ ≤ (1 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by dsimp [s]; linarith)
    simp only [inv_one] at hi
    dsimp [b]
    linarith
  apply mem_iUnion₂.mpr
  refine ⟨s⁻¹, inv_pos.mpr hs, mem_iUnion₂.mpr ⟨b, hsb, ?_⟩⟩
  apply (mem_polytube_iff _ _ _ _).mpr
  refine ⟨x, ?_, fun e => by simpa using hwidth s⁻¹ (inv_pos.mpr hs) b hsb⟩
  intro e
  have hi : (x e)⁻¹ ≤ s := by
    have he := single_le_sum (fun a _ => (inv_pos.mpr (hx a)).le) (mem_univ e)
    dsimp [s]
    linarith
  have hlo : s⁻¹ ≤ x e := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hx e)) hi
  have hhi : x e ≤ b := by
    have he := single_le_sum (fun a _ => (hx a).le) (mem_univ e)
    dsimp [b]
    linarith
  exact ⟨hlo, hhi⟩

theorem positive_mem_positiveDiagonalNeighborhood (width : ℝ → ℝ → ℝ)
    (hwidth : ∀ a > 0, ∀ b ≥ a, 0 < width a b) {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ∈ positiveDiagonalNeighborhood width := by
  apply mem_iUnion₂.mpr
  refine ⟨x, hx, mem_iUnion₂.mpr ⟨x, le_rfl, ?_⟩⟩
  exact mem_thickening_iff.mpr
    ⟨(x : ℂ), ⟨x, ⟨le_rfl, le_rfl⟩, rfl⟩, by simpa using hwidth x hx x le_rfl⟩

def edgePositiveOrthantNeighborhood {E : Type*} (edges : Finset E)
    (width : ℝ → ℝ → ℝ) : Set (E → ℂ) :=
  ⋃ a > 0, ⋃ b ≥ a, edgePolytube edges (width a b) a b

theorem edgePositiveOrthantNeighborhood_isOpen {E : Type*} (edges : Finset E)
    (width : ℝ → ℝ → ℝ) : IsOpen (edgePositiveOrthantNeighborhood edges width) :=
  isOpen_iUnion fun a => isOpen_iUnion fun _ =>
    isOpen_iUnion fun b => isOpen_iUnion fun _ => edgePolytube_isOpen edges (width a b) a b

theorem positive_mem_edgePositiveOrthantNeighborhood {E : Type*} (edges : Finset E)
    (width : ℝ → ℝ → ℝ) (hwidth : ∀ a > 0, ∀ b ≥ a, 0 < width a b)
    (x : E → ℝ) (hx : ∀ e ∈ edges, 0 < x e) :
    (fun e => (x e : ℂ)) ∈ edgePositiveOrthantNeighborhood edges width := by
  have h := positive_mem_positiveOrthantNeighborhood width hwidth
    (fun e : {e // e ∈ edges} => x e.val) (fun e => hx e.val e.property)
  simpa only [edgePositiveOrthantNeighborhood, positiveOrthantNeighborhood, edgePolytube,
    mem_iUnion, Set.mem_preimage] using h

/-- A uniform reciprocal width. It can in fact be chosen independently of
the upper endpoint, a slight strengthening of the stated corollary. -/
def coverTubeWidth {Δ : ℕ} (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ))
    (a _b : ℝ) : ℝ :=
  if ha : 0 < a then
    Classical.choose (exists_reciprocal_width ha (tubeWidth_pos htube a⁻¹))
  else 1

theorem coverTubeWidth_spec {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ)) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    0 < coverTubeWidth htube a b ∧ coverTubeWidth htube a b ≤ a / 2 ∧
      2 * coverTubeWidth htube a b / a ^ 2 ≤ tubeWidth htube a⁻¹ := by
  simpa only [coverTubeWidth, dif_pos ha] using
    Classical.choose_spec (exists_reciprocal_width ha (tubeWidth_pos htube a⁻¹))

theorem coverPartition_ne_zero_polytube {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ)) {a c : ℝ} (ha : 0 < a)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v)
    (z : Sym2 V → ℂ)
    (hz : z ∈ edgePolytube G.edgeFinset (coverTubeWidth htube a c) a c) :
    coverPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  have hwidth := coverTubeWidth_spec htube ha c
  have hinv := reciprocal_polytube ha hwidth.2.1 hwidth.2.2
    (fun e : {e // e ∈ G.edgeFinset} => z e.val) hz
  have hnz : ∀ e ∈ G.edgeFinset, z e ≠ 0 := fun e he => hinv.1 ⟨e, he⟩
  have hmatch := matchingPartition_ne_zero_polytube htube (inv_pos.mpr ha) G hΔ
    (fun v => G.degree v - b v) (fun v => Nat.sub_le _ _) (fun e => (z e)⁻¹) hinv.2
  apply coverPartition_ne_zero_of_matching graphIncidence G.edgeFinset b
    (by simpa using hb) z hnz
  simpa only [selectedDegree_graph] using hmatch

/-- Corollary `cor:bcover-short` in the order `∀ a c, ∃ ε`: positive boxes have a graph- and
capacity-independent width (`cor_bcover_short` chooses `ε` before `c = λ₊`). The upper endpoint is finite because it is real. -/
theorem cover_uniform_polytube {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ))
    {a c : ℝ} (ha : 0 < a) (_hac : a ≤ c) :
    ∃ ε > 0, ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
        ∀ z ∈ edgePolytube G.edgeFinset ε a c,
          coverPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  exact ⟨coverTubeWidth htube a c, (coverTubeWidth_spec htube ha c).1,
    fun _ _ _ G hΔ b hb z hz => coverPartition_ne_zero_polytube htube ha G hΔ b hb z hz⟩

theorem cover_orthant {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ))
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v) :
    IsOpen (edgePositiveOrthantNeighborhood G.edgeFinset (coverTubeWidth htube)) ∧
      (∀ x : Sym2 V → ℝ, (∀ e ∈ G.edgeFinset, 0 < x e) →
        (fun e => (x e : ℂ)) ∈
          edgePositiveOrthantNeighborhood G.edgeFinset (coverTubeWidth htube)) ∧
      ∀ z ∈ edgePositiveOrthantNeighborhood G.edgeFinset (coverTubeWidth htube),
        coverPartition graphIncidence G.edgeFinset b z ≠ 0 := by
  refine ⟨edgePositiveOrthantNeighborhood_isOpen _ _,
    fun x hx => positive_mem_edgePositiveOrthantNeighborhood _ _
      (fun _ ha c _ => (coverTubeWidth_spec htube ha c).1) x hx, ?_⟩
  intro z hz
  obtain ⟨a, ha, hz⟩ := mem_iUnion₂.mp hz
  obtain ⟨c, _hac, hz⟩ := mem_iUnion₂.mp hz
  exact coverPartition_ne_zero_polytube htube ha G hΔ b hb z hz

theorem cover_uniform_diagonal {Δ : ℕ}
    (htube : UniformGraphTubes.{u} Δ (capacityFamily Δ)) :
    ∃ U : Set ℂ, IsOpen U ∧ (∀ x : ℝ, 0 < x → (x : ℂ) ∈ U) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          ∀ z ∈ U, coverPartition graphIncidence G.edgeFinset b (fun _ => z) ≠ 0 := by
  refine ⟨positiveDiagonalNeighborhood (coverTubeWidth htube),
    positiveDiagonalNeighborhood_isOpen _,
    fun x hx => positive_mem_positiveDiagonalNeighborhood _
      (fun _ ha c _ => (coverTubeWidth_spec htube ha c).1) hx, ?_⟩
  intro V _ _ G hΔ b hb z hz
  obtain ⟨a, ha, hz⟩ := mem_iUnion₂.mp hz
  obtain ⟨c, _hac, hz⟩ := mem_iUnion₂.mp hz
  exact coverPartition_ne_zero_polytube htube ha G hΔ b hb _ (fun _ _ => hz)

end
end CI2ZF.Holant
