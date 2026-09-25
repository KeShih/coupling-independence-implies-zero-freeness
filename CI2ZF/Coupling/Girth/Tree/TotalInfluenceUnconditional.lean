import CI2ZF.Coupling.Girth.Tree.TotalInfluence
import CI2ZF.Coupling.Girth.Tree.InfluenceIdentity

/-! Companion Lemma 6.8, tree total-influence decay, with the proved
CLMM influence identity supplied: `total_influence_decay` without its
`CLMMInfluenceIdentity` argument. -/
namespace CI2ZF.Appendix.Girth.CavityTree
open scoped BigOperators
open Finset Set PottsCI
set_option linter.unusedSectionVars false
noncomputable section

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Companion Lemma 6.8, tree total-influence decay. -/
theorem total_influence_decay_unconditional
    {Δ : ℕ} (x : ℝ) (hx : 0 < x) (hx1 : x < 1) (hq : Δ + 3 ≤ Fintype.card C)
    (d : ℕ) (b : C → ℕ) (child : Fin d → CavityTree C)
    (hroot : d + (∑ c, b c) ≤ Δ) (ht : ∀ i, (child i).DegreeBudget Δ)
    (k : ℕ) (a z : C) :
    (CavityTree.node d b child).levelTotalVariation x hx (k + 1) a z ≤
      totalInfluenceConstant Δ (Fintype.card C) * decayRate (Fintype.card C) ^ k :=
  total_influence_decay (clmmInfluenceIdentity C) x hx hx1 hq d b child hroot ht k a z

end
end CI2ZF.Appendix.Girth.CavityTree
