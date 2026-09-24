import CI2ZF.Potts.Geometry.GraphClassInputs

/-! The original bounded-degree graph class and the precise external
hard-colouring input in original graph/partial-colouring notation. -/
namespace CI2ZF.Potts
open PottsCI
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v

theorem degree_comap_embedding_le {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (e : B ↪ A) (b : B) : (G.comap e).degree b ≤ G.degree (e b) := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  let f : (G.comap e).neighborSet b → G.neighborSet (e b) := fun w => ⟨e w.val, w.property⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  apply Subtype.ext
  exact e.injective (congrArg Subtype.val h)

def GraphClass.boundedDegree (Δ : ℕ) : GraphClass.{u} where
  contains G := ∀ w, G.degree w ≤ Δ
  comap_mem G e hG b := (degree_comap_embedding_le G e b).trans (hG (e b))

/-- CFFGZZ Theorem 20, only in the exact hard root-CI form required at
equality, stated on actual original graphs and arbitrary partial
colourings rather than on abstract boundary-count data. Proved for
`Δ ≥ 6` and `q ≥ 11Δ/6` as `external_critical_hard_colouring_theorem`. -/
def ExternalCriticalHardColouringTheorem (C : Type v) [Fintype C] (Δ : ℕ) : Prop :=
  ∃ cost : ℝ, GraphClassRootCouplingBound (GraphClass.boundedDegree.{u} Δ)
    C PinningData.hardParameter cost

end
end CI2ZF.Potts
