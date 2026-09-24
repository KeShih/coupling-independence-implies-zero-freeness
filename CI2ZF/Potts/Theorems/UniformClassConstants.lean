import CI2ZF.Potts.Theorems.PositiveGraphClassTransfer
import CI2ZF.Potts.Transfer.FamilyUniformTransfer

/-!
# Class-uniform constants for `prop:ep-disc` and `lem:potts-positive-response`

In `main.tex`, `prop:ep-disc` gives `ρ₀ = ρ₀(q, Δ, C₀)` and
`lem:potts-positive-response` (restated in the companion) gives `α, ε`
depending only on `(q, Δ, δ, C)`.  The library theorems
`PinningFamily.hard_uniform_transfer` and
`GraphClass.positive_interval_zero_free_and_responses` choose these constants
after the graph class `F`.

As in `CI2ZF/LeeYang/GraphClassUniform.lean` (`ciUnionClass`), we apply the
library theorems once to the union of all induced-subgraph-closed classes
satisfying the coupling hypothesis.  This union is again a `GraphClass`, it
satisfies the same coupling bound (the bound is a statement about each
member graph), and it contains every such class.  The constants obtained
for it therefore work for every class.  `unionClass` below is the same
construction as `ciUnionClass`, for an arbitrary predicate on classes.
-/

namespace CI2ZF.Potts
open PottsCI Set Metric CI2ZF.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

universe u v

/-- The union of all graph classes satisfying a predicate. -/
def unionClass (P : GraphClass.{u} → Prop) : GraphClass.{u} where
  contains {A} _ G := ∃ F : GraphClass.{u}, P F ∧ F.contains G
  comap_mem := by
    intro A B _ _ G e hG
    obtain ⟨F, hF, hGF⟩ := hG
    exact ⟨F, hF, F.comap_mem G e hGF⟩

theorem mem_unionClass {P : GraphClass.{u} → Prop} (F : GraphClass.{u}) (hF : P F)
    {A : Type u} [Fintype A] {G : SimpleGraph A} (hG : F.contains G) :
    (unionClass P).contains G :=
  ⟨F, hF, hG⟩

/-- A union of classes with a coupling bound has the same coupling bound. -/
theorem unionClass_rootCouplingBound (C : Type v) [Fintype C]
    (x : PinningData.NonnegativeParameter) (cost : ℝ) :
    GraphClassRootCouplingBound
      (unionClass.{u} fun F => GraphClassRootCouplingBound F C x cost) C x cost := by
  intro A _ G hG tau r a b ha hb
  obtain ⟨F, hF, hGF⟩ := hG
  exact hF G hGF tau r a b ha hb

/-- The positive-interval coupling hypothesis of `lem:potts-positive-response`. -/
def PositiveIntervalCI (F : GraphClass.{u}) (C : Type v) [Fintype C] (δ cost : ℝ) : Prop :=
  ∀ (x : ℝ) (hx : 0 < x), x ∈ Icc δ 1 → GraphClassRootCouplingBound F C ⟨x, hx.le⟩ cost

theorem unionClass_positiveIntervalCI (C : Type v) [Fintype C] (δ cost : ℝ) :
    PositiveIntervalCI (unionClass.{u} fun F => PositiveIntervalCI F C δ cost) C δ cost := by
  intro x hx hxI A _ G hG tau r a b ha hb
  obtain ⟨F, hF, hGF⟩ := hG
  exact hF x hx hxI G hGF tau r a b ha hb

/-! ## `prop:ep-disc` -/

/-- The hard-endpoint disc for one original graph class (library route,
radius chosen after `F`). -/
theorem graph_class_hard_disc (F : GraphClass.{u}) (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hci : GraphClassRootCouplingBound F C PinningData.hardParameter cost) :
    ∃ ρ₀ > 0, ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
      (∀ w, G.degree w ≤ Δ) → ∀ (tau : PartialColouring V C) (z : ℂ), ‖z‖ < ρ₀ →
        normalizedPartition tau G z ≠ 0 := by
  obtain ⟨r, hr, _, _, hn, _⟩ :=
    (F.pinningFamily C).hard_uniform_transfer Δ hq cost (hci.to_pinningFamily hq)
  refine ⟨r, hr, ?_⟩
  intro V _ G hG hd tau z hz
  have h := hn (tau.toPinningData G) (F.original_pinning_mem C G hG tau)
    (tau.degreeBound_of_original G hd) z (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  rwa [pinningProductPartition_toPinningData] at h

/-- **`prop:ep-disc` with the paper's quantifier order.**  The radius
depends only on the colour type, `Δ` and `cost`; it is chosen before the
class `F`. -/
theorem uniform_hard_disc (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ) :
    ∃ ρ₀ > 0, ∀ F : GraphClass.{u},
      GraphClassRootCouplingBound F C PinningData.hardParameter cost →
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), F.contains G →
        (∀ w, G.degree w ≤ Δ) → ∀ (tau : PartialColouring V C) (z : ℂ), ‖z‖ < ρ₀ →
          normalizedPartition tau G z ≠ 0 := by
  obtain ⟨ρ₀, hρ₀, h⟩ := graph_class_hard_disc
    (unionClass.{u} fun F => GraphClassRootCouplingBound F C PinningData.hardParameter cost)
    C Δ hq cost (unionClass_rootCouplingBound C _ cost)
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro F hF V _ G hG
  exact h G (mem_unionClass (P := fun F => GraphClassRootCouplingBound F C
    PinningData.hardParameter cost) F hF hG)

/-- **`prop:ep-disc`, paper form.**  Integers `q, Δ` with `Δ ≥ 2` and
`q ≥ Δ + 1`, colours `Fin q`, and `C₀ ≥ 0`: there is `ρ₀ = ρ₀(q, Δ, C₀) > 0`
such that for every class `𝒢 ⊆ 𝒢_Δ` closed under induced subgraphs with
`C₀`-coupling independence at `x = 0`, every `G ∈ 𝒢` and every pinning,
`Z̃_G^τ(z) ≠ 0` for `|z| < ρ₀`.  (`Δ ≥ 2` and `C₀ ≥ 0` are not needed.) -/
theorem prop_ep_disc (q Δ : ℕ) (_hΔ : 2 ≤ Δ) (hq : Δ + 1 ≤ q) (C₀ : ℝ) (_hC₀ : 0 ≤ C₀) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ 𝒢 : GraphClass.{u},
      (∀ {V : Type u} [Fintype V] (G : SimpleGraph V), 𝒢.contains G → ∀ v, G.degree v ≤ Δ) →
      GraphClassRootCouplingBound 𝒢 (Fin q) PinningData.hardParameter C₀ →
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), 𝒢.contains G →
        ∀ (tau : PartialColouring V (Fin q)) (z : ℂ), ‖z‖ < ρ₀ →
          normalizedPartition tau G z ≠ 0 := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  obtain ⟨ρ₀, hρ₀, h⟩ := uniform_hard_disc.{u, 0} (Fin q) Δ (by simpa using hq) C₀
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro 𝒢 hdeg hCI V _ G hG tau z hz
  convert h 𝒢 hCI G hG (hdeg G hG) tau z hz using 2

/-! ## `lem:potts-positive-response` -/

/-- **`lem:potts-positive-response` with the paper's quantifier order.**
The radius `ε` and response bound `α` depend only on the colour type, `Δ`,
`δ` and `cost`; they are chosen before the class `F`. -/
theorem uniform_positive_response (C : Type v) [Fintype C] [Nonempty C]
    (Δ : ℕ) {δ : ℝ} (hδ : 0 < δ) (cost : ℝ) :
    ∃ ε > 0, ∃ α > 0, ∀ F : GraphClass.{u}, PositiveIntervalCI F C δ cost →
      ∀ {A : Type u} [Fintype A] (G : SimpleGraph A), F.contains G →
      (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring A C,
      (∀ x ∈ Icc δ 1, ∀ z ∈ ball (x : ℂ) ε, normalizedPartition tau G z ≠ 0) ∧
      ∀ (s : tau.FreeVertex) (a b : C), ∀ x ∈ Icc δ 1,
        HasSmallResponseLog (fun z => normalizedPartition (pinVertex tau s a) G z)
          (fun z => normalizedPartition (pinVertex tau s b) G z) (x : ℂ) ε α := by
  obtain ⟨ε, hε, α, hα, h⟩ :=
    (unionClass.{u} fun F => PositiveIntervalCI F C δ cost).positive_interval_zero_free_and_responses
      (C := C) Δ hδ cost (unionClass_positiveIntervalCI C δ cost)
  refine ⟨ε, hε, α, hα, ?_⟩
  intro F hF V _ G hG
  exact h G (mem_unionClass (P := fun F => PositiveIntervalCI F C δ cost) F hF hG)

/-- **`lem:potts-positive-response`, paper form** (main text and companion).
Integers `q ≥ 1`, `Δ ≥ 2`, colours `Fin q`, `δ ∈ (0,1]`, `C ≥ 0`: there are
`α, ε > 0` depending only on `(q, Δ, δ, C)` such that for every class
`𝒢 ⊆ 𝒢_Δ` closed under induced subgraphs with `C`-coupling independence
on `[δ,1]`, every `G ∈ 𝒢`, every pinning `τ` and every `x ∈ [δ,1]`,
`Z̃_G^τ(z) ≠ 0` for `|z - x| < ε`, and every one-vertex response has a
logarithm continued from `z = x` of modulus at most `α`.  (The paper's
`q` is the number of colours of a Potts model, so `q ≥ 1`; `Δ ≥ 2`,
`δ ≤ 1` and `C ≥ 0` are not needed.) -/
theorem lem_potts_positive_response (q Δ : ℕ) (hq : 1 ≤ q) (_hΔ : 2 ≤ Δ)
    (δ : ℝ) (hδ : 0 < δ) (_hδ1 : δ ≤ 1) (Cc : ℝ) (_hC : 0 ≤ Cc) :
    ∃ α : ℝ, 0 < α ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ 𝒢 : GraphClass.{u},
      (∀ {V : Type u} [Fintype V] (G : SimpleGraph V), 𝒢.contains G → ∀ v, G.degree v ≤ Δ) →
      PositiveIntervalCI 𝒢 (Fin q) δ Cc →
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V), 𝒢.contains G →
        ∀ tau : PartialColouring V (Fin q),
        (∀ x ∈ Icc δ 1, ∀ z : ℂ, ‖z - x‖ < ε → normalizedPartition tau G z ≠ 0) ∧
        ∀ (s : tau.FreeVertex) (a b : Fin q), ∀ x ∈ Icc δ 1,
          HasSmallResponseLog (fun z => normalizedPartition (pinVertex tau s a) G z)
            (fun z => normalizedPartition (pinVertex tau s b) G z) (x : ℂ) ε α := by
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  obtain ⟨ε, hε, α, hα, h⟩ := uniform_positive_response.{u, 0} (Fin q) Δ hδ Cc
  refine ⟨α, hα, ε, hε, ?_⟩
  intro 𝒢 hdeg hCI V _ G hG tau
  obtain ⟨hn, hr⟩ := h 𝒢 hCI G hG (hdeg G hG) tau
  refine ⟨fun x hx z hz => ?_, fun s a b x hx => ?_⟩
  · have hz' : z ∈ ball (x : ℂ) ε := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    convert hn x hx z hz' using 2
  · convert hr s a b x hx using 3

end
end CI2ZF.Potts
