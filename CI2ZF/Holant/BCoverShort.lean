import CI2ZF.Holant.Corollaries

/-!
# Corollary `cor:bcover-short` with the paper's quantifier order

The paper fixes `Δ` and `0 < λ₋ ≤ λ₊ < ∞` and asserts a width
`ε = ε(Δ, λ₋) > 0`, independent of `λ₊`, of the graph and of the demands.
`CI2ZF.Holant.bcover_uniform_polytube` states `∀ a c, ∃ ε`; here the width is
chosen before the upper endpoint `c = λ₊`.

Everything is derived from the library's proved Holant theorem
(`CI2ZF.Holant.holant_uniform_tubes`) through the library's proved reciprocal
reduction `CI2ZF.Holant.coverPartition_ne_zero_polytube`.
-/

namespace CI2ZF.Holant
open Set Metric
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The library width `bcoverWidth Δ a c` does not depend on `c`. -/
theorem bcoverWidth_upper_irrelevant (Δ : ℕ) (a c c' : ℝ) :
    bcoverWidth.{u} Δ a c = bcoverWidth.{u} Δ a c' := rfl

/-- The width of `cor:bcover-short`, a function of `(Δ, λ₋)` only. -/
def coverWidth (Δ : ℕ) (a : ℝ) : ℝ := bcoverWidth.{u} Δ a a

theorem coverWidth_pos (Δ : ℕ) {a : ℝ} (ha : 0 < a) : 0 < coverWidth.{u} Δ a :=
  (coverTubeWidth_spec (holant_uniform_tubes.{u} (capacityFamily Δ) Δ) ha a).1

/-- Zero-freeness on every positive polytube `U_ε([a,c])^E` with `ε = coverWidth Δ a`.
(The hypothesis `a ≤ c` is not even needed.) -/
theorem coverPartition_ne_zero_coverWidth (Δ : ℕ) {a : ℝ} (ha : 0 < a) (c : ℝ)
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hΔ : ∀ v, G.degree v ≤ Δ) (b : V → ℕ) (hb : ∀ v, b v ≤ G.degree v)
    (z : Sym2 V → ℂ) (hz : z ∈ edgePolytube G.edgeFinset (coverWidth.{u} Δ a) a c) :
    coverPartition graphIncidence G.edgeFinset b z ≠ 0 :=
  coverPartition_ne_zero_polytube (holant_uniform_tubes.{u} (capacityFamily Δ) Δ)
    (c := c) ha G hΔ b hb z hz

/-- **Corollary `cor:bcover-short`, first sentence, paper quantifier order.**
For every `Δ` and `λ₋ = a > 0` there is `ε > 0` such that for every `λ₊ = c ≥ a`,
every finite simple graph of maximum degree at most `Δ`, every demand vector
`0 ≤ b_v ≤ deg_G v`, and every `z ∈ U_ε([a,c])^E`, the `b`-edge-cover partition
function is nonzero. -/
theorem bcover_uniform_polytube_lower (Δ : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ ε > 0, ∀ c : ℝ, a ≤ c →
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          ∀ z ∈ edgePolytube G.edgeFinset ε a c,
            coverPartition graphIncidence G.edgeFinset b z ≠ 0 :=
  ⟨coverWidth.{u} Δ a, coverWidth_pos Δ ha, fun c _ _ _ _ G hΔ b hb z hz =>
    coverPartition_ne_zero_coverWidth Δ ha c G hΔ b hb z hz⟩

/-- **Corollary `cor:bcover-short`, complete.** One width function
`ε(Δ, ·)` of the lower endpoint only, chosen before every graph, demand vector
and upper endpoint, such that
1. `ε(Δ, a) > 0` for `a > 0`;
2. every polytube `U_{ε(Δ,a)}([a,c])^E`, `0 < a ≤ c`, is zero-free;
3. for each admissible `(G, b)`, the union
   `⋃_{0<a≤c} U_{ε(Δ,a)}([a,c])^E` is open, contains `(0,∞)^E`, and is zero-free;
4. (closing remark after the corollary) the diagonal union
   `⋃_{0<a≤c} U_{ε(Δ,a)}([a,c])` is an open subset of `ℂ` containing `(0,∞)`,
   depending only on `Δ`, on which every diagonal cover polynomial is nonzero. -/
theorem cor_bcover_short (Δ : ℕ) :
    ∃ ε : ℝ → ℝ, (∀ a > 0, 0 < ε a) ∧
      (∀ a > 0, ∀ c ≥ a,
        ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
          (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
            ∀ z ∈ edgePolytube G.edgeFinset (ε a) a c,
              coverPartition graphIncidence G.edgeFinset b z ≠ 0) ∧
      (∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          IsOpen (⋃ a > 0, ⋃ c ≥ a, edgePolytube G.edgeFinset (ε a) a c) ∧
          (∀ x : Sym2 V → ℝ, (∀ e ∈ G.edgeFinset, 0 < x e) →
            (fun e => (x e : ℂ)) ∈ ⋃ a > 0, ⋃ c ≥ a, edgePolytube G.edgeFinset (ε a) a c) ∧
          ∀ z ∈ ⋃ a > 0, ⋃ c ≥ a, edgePolytube G.edgeFinset (ε a) a c,
            coverPartition graphIncidence G.edgeFinset b z ≠ 0) ∧
      (IsOpen (⋃ a > 0, ⋃ c ≥ a, thickening (ε a) (realInterval a c)) ∧
        (∀ x : ℝ, 0 < x → (x : ℂ) ∈ ⋃ a > 0, ⋃ c ≥ a, thickening (ε a) (realInterval a c)) ∧
        ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
          (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
            ∀ z ∈ ⋃ a > 0, ⋃ c ≥ a, thickening (ε a) (realInterval a c),
              coverPartition graphIncidence G.edgeFinset b (fun _ => z) ≠ 0) := by
  have hpos : ∀ a > 0, ∀ _c ≥ a, 0 < (fun a (_ : ℝ) => coverWidth.{u} Δ a) a _c :=
    fun a ha _ _ => coverWidth_pos Δ ha
  refine ⟨coverWidth.{u} Δ, fun a ha => coverWidth_pos Δ ha,
    fun a ha c _ V _ _ G hΔ b hb z hz => coverPartition_ne_zero_coverWidth Δ ha c G hΔ b hb z hz,
    fun V _ _ G hΔ b hb => ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · exact edgePositiveOrthantNeighborhood_isOpen G.edgeFinset (fun a _ => coverWidth.{u} Δ a)
  · exact fun x hx => positive_mem_edgePositiveOrthantNeighborhood G.edgeFinset
      (fun a _ => coverWidth.{u} Δ a) hpos x hx
  · intro z hz
    obtain ⟨a, ha, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨c, _, hz⟩ := mem_iUnion₂.mp hz
    exact coverPartition_ne_zero_coverWidth Δ ha c G hΔ b hb z hz
  · exact positiveDiagonalNeighborhood_isOpen (fun a _ => coverWidth.{u} Δ a)
  · exact fun x hx => positive_mem_positiveDiagonalNeighborhood
      (fun a _ => coverWidth.{u} Δ a) hpos hx
  · intro V _ _ G hΔ b hb z hz
    obtain ⟨a, ha, hz⟩ := mem_iUnion₂.mp hz
    obtain ⟨c, _, hz⟩ := mem_iUnion₂.mp hz
    exact coverPartition_ne_zero_coverWidth Δ ha c G hΔ b hb _ (fun _ _ => hz)

/-- **Corollary `cor:bcover-short`, second sentence, intrinsic form.**
The same statement as clause 3 of `cor_bcover_short`, but in the paper's
ambient space `ℂ^E` with `E` the edge set itself (rather than the cylinder
over `ℂ^E` inside `Sym2 V → ℂ`). A point `w ∈ ℂ^E` is evaluated through its
extension by zero, which is irrelevant since the cover polynomial only reads
edge coordinates. -/
theorem cor_bcover_short_intrinsic (Δ : ℕ) :
    ∃ ε : ℝ → ℝ, (∀ a > 0, 0 < ε a) ∧
      ∀ (V : Type u) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        (∀ v, G.degree v ≤ Δ) → ∀ b : V → ℕ, (∀ v, b v ≤ G.degree v) →
          IsOpen (⋃ a > 0, ⋃ c ≥ a, polytube {e // e ∈ G.edgeFinset} (ε a) a c) ∧
          (∀ x : {e // e ∈ G.edgeFinset} → ℝ, (∀ e, 0 < x e) →
            (fun e => (x e : ℂ)) ∈
              ⋃ a > 0, ⋃ c ≥ a, polytube {e // e ∈ G.edgeFinset} (ε a) a c) ∧
          ∀ w ∈ ⋃ a > 0, ⋃ c ≥ a, polytube {e // e ∈ G.edgeFinset} (ε a) a c,
            coverPartition graphIncidence G.edgeFinset b
              (fun e => if h : e ∈ G.edgeFinset then w ⟨e, h⟩ else 0) ≠ 0 := by
  refine ⟨coverWidth.{u} Δ, fun a ha => coverWidth_pos Δ ha,
    fun V _ _ G hΔ b hb => ⟨?_, ?_, ?_⟩⟩
  · exact positiveOrthantNeighborhood_isOpen _ (fun a _ => coverWidth.{u} Δ a)
  · exact fun x hx => positive_mem_positiveOrthantNeighborhood
      (fun a _ => coverWidth.{u} Δ a) (fun a ha _ _ => coverWidth_pos Δ ha) x hx
  · intro w hw
    obtain ⟨a, ha, hw⟩ := mem_iUnion₂.mp hw
    obtain ⟨c, _, hw⟩ := mem_iUnion₂.mp hw
    apply coverPartition_ne_zero_coverWidth Δ ha c G hΔ b hb
    have hres : (fun (e : {e // e ∈ G.edgeFinset}) =>
        (fun e => if h : e ∈ G.edgeFinset then w ⟨e, h⟩ else 0) e.val) = w :=
      funext fun e => dif_pos e.property
    simp only [edgePolytube, Set.mem_preimage]
    rw [hres]
    exact hw

end
end CI2ZF.Holant
