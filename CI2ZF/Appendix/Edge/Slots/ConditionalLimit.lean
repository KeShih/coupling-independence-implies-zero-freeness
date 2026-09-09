import CI2ZF.Appendix.Edge.Slots.Conditioning

/-! Root-colour conditioning of the constructed approximants converges to
root-colour conditioning of the original finite Potts law. -/

namespace CI2ZF.Appendix.Edge.EndpointGeometry
open PottsCI PottsCI.FinDist Filter FiniteLaw FiniteSystem
open scoped BigOperators Topology
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V E C : Type*} [Fintype V] [Fintype E] [Fintype C]
local instance (priority := 2000) : DecidableEq V := Classical.decEq V
local instance (priority := 2000) : DecidableEq E := Classical.decEq E
local instance (priority := 2000) : DecidableEq C := Classical.decEq C

lemma approxColourLaw_pos [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) (φ : E → C) :
    0 < (g.approxColourLaw x hx hx1 b n).w φ := by
  rw [approxColourLaw_weight]
  exact div_pos (g.approxSlotColourFibre_pos x hx hx1 b φ n)
    (g.approxSlotSystem_partition_pos x hx hx1 b n)

lemma targetColourLaw_pos [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (b : E → C → ℕ) (φ : E → C) :
    0 < (g.targetColourLaw x hx b).w φ :=
  div_pos (g.targetColourWeight_pos hx b φ) (g.targetColourPartition_pos hx b)

lemma approxColourLaw_coordinate_pos [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) (e : E) (c : C) :
    0 < eventMass (g.approxColourLaw x hx hx1 b n) (fun φ => φ e = c) :=
  eventMass_coordinate_pos _ (g.approxColourLaw_pos x hx hx1 b n) e c

lemma targetColourLaw_coordinate_pos [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (b : E → C → ℕ) (e : E) (c : C) :
    0 < eventMass (g.targetColourLaw x hx b) (fun φ => φ e = c) :=
  eventMass_coordinate_pos _ (g.targetColourLaw_pos x hx b) e c

theorem approxRootExcludedColourLaw_tendsto [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (e : E) (c : C)
    (φ : {f : E // f ≠ e} → C) :
    Tendsto (fun n => (rootExcludedColourLaw (g.approxColourLaw x hx hx1 b n) e c).w φ)
      atTop (𝓝 ((rootExcludedColourLaw (g.targetColourLaw x hx b) e c).w φ)) := by
  apply FiniteLaw.mapLaw_tendsto
  intro ψ
  exact conditional_tendsto (g.approxColourLaw_tendsto x hx hx1 b) (fun φ => φ e = c)
    (fun n => g.approxColourLaw_coordinate_pos x hx hx1 b n e c)
    (g.targetColourLaw_coordinate_pos x hx b e c) ψ

/-- An internal finite-state root bound transfers to each actual finite-slot
root-colour law. All conditioning events have proved positive mass. -/
theorem approxRootExcludedColourLaw_W_le [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (n : ℕ) {Δ : ℕ}
    (hB : (g.approxSlotSystem x hx hx1 b n).Bounds (fun _ => ∅) Δ)
    (e : E) (c d : C) {K : ℝ}
    (hci : ∀ a a', (g.approxSlotSystem x hx hx1 b n).Compatible (fun _ => ∅) e a →
      (g.approxSlotSystem x hx hx1 b n).Compatible (fun _ => ∅) e a' →
      W ham ((g.approxSlotSystem x hx hx1 b n).pinnedLaw (fun _ => ∅) hB e a)
        ((g.approxSlotSystem x hx hx1 b n).pinnedLaw (fun _ => ∅) hB e a') ≤ K) :
    W ham (rootExcludedColourLaw (g.approxColourLaw x hx hx1 b n) e c)
      (rootExcludedColourLaw (g.approxColourLaw x hx hx1 b n) e d) ≤ K := by
  let I := g.approxSlotSystem x hx hx1 b n
  have heq : CI2ZF.mapLaw (I.validLaw (fun _ => ∅) hB) colourProjection =
      g.approxColourLaw x hx hx1 b n := rfl
  have hc' (c : C) : 0 < eventMass (I.validLaw (fun _ => ∅) hB) (fun σ => (σ e).1 = c) := by
    change 0 < eventMass (I.validLaw (fun _ => ∅) hB) (fun σ => colourProjection σ e = c)
    rw [← eventMass_mapLaw (I.validLaw (fun _ => ∅) hB) colourProjection (fun φ => φ e = c), heq]
    exact g.approxColourLaw_coordinate_pos x hx hx1 b n e c
  rw [← heq]
  exact rootExcludedColourLaw_W_le I (fun _ => ∅) hB e c d (hc' c) (hc' d) hci

/-- The finite-colour limit preserves the root-excluded transport bound. -/
theorem targetRootExcludedColourLaw_W_le [Nonempty C] (g : EndpointGeometry V E)
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (b : E → C → ℕ) (e : E) (c d : C) {K : ℝ}
    (hfinite : ∀ n, W ham (rootExcludedColourLaw (g.approxColourLaw x hx hx1 b n) e c)
      (rootExcludedColourLaw (g.approxColourLaw x hx hx1 b n) e d) ≤ K) :
    W ham (rootExcludedColourLaw (g.targetColourLaw x hx b) e c)
      (rootExcludedColourLaw (g.targetColourLaw x hx b) e d) ≤ K := by
  apply W_le_of_pointwise_limits ham_nonneg ham_self ham_triangle ham_le_card
    (fun n => rootExcludedColourLaw (g.approxColourLaw x hx hx1 b n) e c)
    (fun n => rootExcludedColourLaw (g.approxColourLaw x hx hx1 b n) e d)
    (rootExcludedColourLaw (g.targetColourLaw x hx b) e c)
    (rootExcludedColourLaw (g.targetColourLaw x hx b) e d)
    (g.approxRootExcludedColourLaw_tendsto x hx hx1 b e c)
    (g.approxRootExcludedColourLaw_tendsto x hx hx1 b e d)
  exact Filter.Eventually.of_forall hfinite

end
end CI2ZF.Appendix.Edge.EndpointGeometry
