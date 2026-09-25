import ZeroFreeness.LeeYang.Induction
import ZeroFreeness.LeeYang.Component
import ZeroFreeness.LeeYang.Parent
import ZeroFreeness.LeeYang.BFSResponse

/-! Hard-colouring coupling independence implies one common nonzero
field radius for every graph size, pinning and bounded field direction.
All analytic and inductive steps are proved in the imported modules. -/
namespace ZeroFreeness.LeeYang
open PottsCI ZeroFreeness.Potts
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v
variable {C : Type v} [Fintype C] [Nonempty C]

theorem uniform_curve_transfer (F : PinningFamily.{u, v} C)
    (Δ : ℕ) (hq : Δ + 1 ≤ Fintype.card C) (cost : ℝ)
    (hCI : F.RootCouplingBound Δ hq PinningData.hardParameter cost) :
    ∃ r > 0, ∀ {V : Type u} [Fintype V] (I : PinningData V C),
      F.contains I → I.DegreeBound Δ → ∀ d, DirectionBound d → CurveNonzeroOn I d r := by
  obtain ⟨L, B, hL, hcost, hB, α, ha, ha1, haB⟩ := exists_geometric_transfer_scales Δ cost
  let r := localFieldRadius B α
  have hr : 0 < r := localFieldRadius_pos B ha
  have hbase := uniform_curve_induction F Δ r α
    (fun I hI hd hNZ hRoot d hdir => by
      by_cases hsmall : Fintype.card (Component.RootComponent I.graph none) ≤ B
      · exact small_component_curve_response F I hI hd hq hsmall ha hr le_rfl hNZ d hdir
      · intro a b
        exact bfs_curve_response_step F I hI a b hd hq hL hB (Nat.lt_of_not_ge hsmall)
          hr le_rfl ha (by linarith) (by linarith) hcost (hCI I hI hd a b) hNZ hRoot d hdir)
    (fun I _ hd d hdir hchildren hresponses =>
      curveNonzeroOn_of_child_responses I hd hq d hdir
        (localFieldRadius_le_half B α) ha1 hchildren hresponses)
  exact ⟨r, hr, hbase.1⟩

end
end ZeroFreeness.LeeYang
