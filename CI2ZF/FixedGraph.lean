import CI2ZF.PottsModel
import CI2ZF.LocalStability

/-!
# Zero-freeness for one fixed finite Potts instance

Compactness and real-axis positivity give a complex zero-free neighborhood
for each fixed graph and partial colouring.  The radius in this module may
depend on the graph and the pinning.  In particular these results do not
establish the graph-independent radius asserted by the paper's main theorem:
that requires the coupling-independence/separator argument still to be proved.
-/

namespace CI2ZF.Potts

open PottsCI Metric

attribute [local instance] Classical.propDecidable

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-- One fixed finite graph and arbitrary pinning have a positive zero-free
radius about `[0,1]` when `q ≥ Δ+1`.  The quantifiers permit the radius to
depend on both the graph and the pinning. -/
theorem fixed_instance_zero_free [Nonempty C] (G : SimpleGraph V)
    (tau : PartialColouring V C) {Δ : ℕ} (hdegree : ∀ v, G.degree v ≤ Δ)
    (hcolours : Δ + 1 ≤ Fintype.card C) :
    ∃ ε > 0, ∀ z ∈ thickening ε pottsInterval, normalizedPartition tau G z ≠ 0 := by
  obtain ⟨ε, hε, hzero⟩ := finite_family_zero_free
    (fun _ : Unit => normalizedPartition tau G)
    (fun _ => normalizedPartition_continuous tau G)
    pottsInterval pottsInterval_isCompact (by
      intro _ w hw
      obtain ⟨x, hx, rfl⟩ := hw
      exact normalizedPartition_nonnegative_ne_zero tau G hdegree hcolours hx.1)
  exact ⟨ε, hε, hzero ()⟩

/-- The main theorem's integer threshold implies the colour slack required
by hard feasibility. -/
lemma degree_succ_le_of_vigoda {q Δ : ℕ} (hΔ : 2 ≤ Δ) (hq : 11 * Δ ≤ 6 * q) :
    Δ + 1 ≤ q := by
  omega

/-- At the paper's `q ≥ 11Δ/6` threshold, every fixed graph and pinning have
some complex zero-free neighborhood.  This is only a fixed-instance result;
its existential radius is chosen after `G` and `tau`. -/
theorem fixed_instance_zero_free_of_vigoda {q Δ : ℕ} (hΔ : 2 ≤ Δ)
    (hq : 11 * Δ ≤ 6 * q) (G : SimpleGraph V)
    (tau : PartialColouring V (Fin q)) (hdegree : ∀ v, G.degree v ≤ Δ) :
    ∃ ε > 0, ∀ z ∈ thickening ε pottsInterval, normalizedPartition tau G z ≠ 0 := by
  have hslack : Δ + 1 ≤ q := degree_succ_le_of_vigoda hΔ hq
  have hqpos : 0 < q := by omega
  let : Nonempty (Fin q) := ⟨⟨0, hqpos⟩⟩
  apply fixed_instance_zero_free G tau hdegree
  simpa only [Fintype.card_fin] using hslack

end CI2ZF.Potts
