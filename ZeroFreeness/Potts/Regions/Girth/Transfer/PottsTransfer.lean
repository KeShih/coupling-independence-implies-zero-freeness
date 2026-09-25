import ZeroFreeness.Coupling.CLMM.SphereEstimate
import ZeroFreeness.Potts.Regions.Girth.Transfer.Family
import ZeroFreeness.Potts.Geometry.RootOptionRelabel

/-!
# Large-girth transfer from tree decay, Potts form
(companion Lemma 6.10, `lem:hg-eventual-transfer`, narrowed)

The companion first stated the transfer for general pinning- and subgraph-closed
pairwise spin systems; it now states it for the Potts family, as here.
Both of its uses (the proofs of `thm:high-girth-soft-ci` and
`thm:bbr-large-girth-ci`) apply it to the family of normalized pinned Potts
systems at a positive activity, where every configuration has positive
weight. This file states the lemma for that family, for
activities in a set `J ⊆ (0,1]`. The theorems below state it with no
literature parameter: the CLMM Equation (10) bundle is discharged by the
proved `CLMM.literature`.

* `potts_eventual_transfer`: the lemma for activities in a set `J ⊆ (0,1]`
  on which the tree hypotheses hold with common constants, in the
  library's `Option` form (the source is `none`, the common free set is `O`).
* `potts_eventual_transfer_source`: the same with an arbitrary finite free
  vertex set `V` and an arbitrary free source vertex `r`; the two laws are
  the actual normalized Gibbs laws after pinning `r`, on `{w // w ≠ r}`.
* `potts_eventual_transfer_uniform`: `g` and `C` are chosen from
  `(q, Δ, A, B, ρ, K₀)` only, and work at every `x ∈ (0,1]` at which the tree
  hypotheses hold with these constants. This is the paper's "depending only
  on the displayed parameters (and not on `x`)".

Here `A = C_INFL`, `B = C_SM`, `ρ = 1 - δ`; `CLMM.TreeTID` is the level-ℓ tree
total-influence bound for every `ℓ ≥ 1`, and `CLMM.TreeRelative` is ratio-form
relative SSM at every distance `K = k + 2 ≥ K₀`, on every pinned Potts tree
obeying the degree budget.
-/

namespace ZeroFreeness.Appendix.Girth

open scoped BigOperators
open PottsCI PottsCI.FinDist ZeroFreeness.Potts ZeroFreeness.Appendix ZeroFreeness.Appendix.Girth

noncomputable section

attribute [local instance] Classical.propDecidable

universe u v
variable {C : Type v} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Companion Lemma 6.10 for normalized pinned Potts systems at activities
in `J ⊆ (0,1]`, with no literature hypothesis. -/
theorem potts_eventual_transfer (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (A B ρ : ℝ) (hA : 0 < A) (hB : 0 < B) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (K₀ : ℕ) (J : Set ℝ) (hJ : ∀ x ∈ J, 0 < x ∧ x ≤ 1)
    (htree : ∀ (x : ℝ) (hxJ : x ∈ J),
      CLMM.TreeTID (C := C) Δ x (hJ x hxJ).1 A ρ ∧ CLMM.TreeRelative (C := C) Δ x B ρ K₀) :
    ∃ (g : ℕ) (cost : ℝ), 3 ≤ g ∧ 0 ≤ cost ∧
      ∀ (x : ℝ) (hxJ : x ∈ J), ∀ {O : Type u} [Fintype O] (I : PinningData (Option O) C),
        I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (a b : C),
        W ham ((optionChildData I a).gibbs x (hJ x hxJ).1.le
            ((optionChildData I a).partition_pos_of_parameter_pos (hJ x hxJ).1))
          ((optionChildData I b).gibbs x (hJ x hxJ).1.le
            ((optionChildData I b).partition_pos_of_parameter_pos (hJ x hxJ).1)) ≤ cost := by
  obtain ⟨g, cost, hg, hcost, h⟩ := CLMM.eventual_transfer (CLMM.literature.{u,v} C) Δ hΔ
    A B ρ hA hB hρ hρ1 K₀ J hJ htree
  exact ⟨g, cost, hg, hcost, fun x hxJ O _ I hd hgI a b => h x hxJ I hd hgI a b _ _⟩

/-- The same statement for an arbitrary finite free vertex set and an
arbitrary free source vertex `r`: the laws are the actual normalized Gibbs
laws after additionally pinning `r` to `a`, resp. `b`, both on the common
free set `{w // w ≠ r}`. -/
theorem potts_eventual_transfer_source (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (A B ρ : ℝ) (hA : 0 < A) (hB : 0 < B) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (K₀ : ℕ) (J : Set ℝ) (hJ : ∀ x ∈ J, 0 < x ∧ x ≤ 1)
    (htree : ∀ (x : ℝ) (hxJ : x ∈ J),
      CLMM.TreeTID (C := C) Δ x (hJ x hxJ).1 A ρ ∧ CLMM.TreeRelative (C := C) Δ x B ρ K₀) :
    ∃ (g : ℕ) (cost : ℝ), 3 ≤ g ∧ 0 ≤ cost ∧
      ∀ (x : ℝ) (hxJ : x ∈ J), ∀ {V : Type u} [Fintype V] (I : PinningData V C),
        I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (r : V) (a b : C),
        W ham ((rootDeletedData I r a).gibbs x (hJ x hxJ).1.le
            ((rootDeletedData I r a).partition_pos_of_parameter_pos (hJ x hxJ).1))
          ((rootDeletedData I r b).gibbs x (hJ x hxJ).1.le
            ((rootDeletedData I r b).partition_pos_of_parameter_pos (hJ x hxJ).1)) ≤ cost := by
  obtain ⟨g, cost, hg, hcost, h⟩ :=
    potts_eventual_transfer.{u,v} Δ hΔ A B ρ hA hB hρ hρ1 K₀ J hJ htree
  refine ⟨g, cost, hg, hcost, ?_⟩
  intro x hxJ V _ I hd hgI r a b
  have hgr : (g : ℕ∞) ≤ (rootOptionData I r).graph.egirth :=
    (largeGirthFamily.{u,v} C g).relabel_mem hgI (rootOptionEquiv r)
  have h' := h x hxJ (rootOptionData I r) (rootOptionData_degreeBound I r hd) hgr a b
  rw [optionChildData_rootOptionData, optionChildData_rootOptionData] at h'
  convert h' using 3

/-- One girth threshold and one constant, depending only on
`(q, Δ, A, B, ρ, K₀)`, serve every activity `x ∈ (0,1]` at which the tree
total-influence and relative-SSM hypotheses hold with these constants. -/
theorem potts_eventual_transfer_uniform (Δ : ℕ) (hΔ : 3 ≤ Δ)
    (A B ρ : ℝ) (hA : 0 < A) (hB : 0 < B) (hρ : 0 < ρ) (hρ1 : ρ < 1) (K₀ : ℕ) :
    ∃ (g : ℕ) (cost : ℝ), 3 ≤ g ∧ 0 ≤ cost ∧
      ∀ (x : ℝ) (hx : 0 < x), x ≤ 1 →
        CLMM.TreeTID (C := C) Δ x hx A ρ → CLMM.TreeRelative (C := C) Δ x B ρ K₀ →
        ∀ {V : Type u} [Fintype V] (I : PinningData V C),
          I.DegreeBound Δ → (g : ℕ∞) ≤ I.graph.egirth → ∀ (r : V) (a b : C),
          W ham ((rootDeletedData I r a).gibbs x hx.le
              ((rootDeletedData I r a).partition_pos_of_parameter_pos hx))
            ((rootDeletedData I r b).gibbs x hx.le
              ((rootDeletedData I r b).partition_pos_of_parameter_pos hx)) ≤ cost := by
  let J : Set ℝ := {x | ∃ hx : 0 < x, x ≤ 1 ∧
    CLMM.TreeTID (C := C) Δ x hx A ρ ∧ CLMM.TreeRelative (C := C) Δ x B ρ K₀}
  have hJ : ∀ x ∈ J, 0 < x ∧ x ≤ 1 := fun x hx => ⟨hx.1, hx.2.1⟩
  obtain ⟨g, cost, hg, hcost, h⟩ := potts_eventual_transfer_source.{u,v} Δ hΔ A B ρ
    hA hB hρ hρ1 K₀ J hJ (fun x hxJ => hxJ.2.2)
  exact ⟨g, cost, hg, hcost, fun x hx hx1 hT hR V _ I hd hgI r a b =>
    h x ⟨hx, hx1, hT, hR⟩ I hd hgI r a b⟩

end

end ZeroFreeness.Appendix.Girth
