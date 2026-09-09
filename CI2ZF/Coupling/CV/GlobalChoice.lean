import CI2ZF.Coupling.CV.CanonicalCoupling
import CI2ZF.Coupling.Vigoda.RegularColourCharge

/-! Legal root-to-piece selectors for global CV coupling. These data contain
only graph-neighbour memberships, never a contraction or cost hypothesis. -/
namespace CI2ZF.Appendix.CV
open PottsCI PottsCI.Vigoda RootComponentGeometry
noncomputable section
set_option linter.unusedSectionVars false
variable {V C : Type*} [Fintype V] [Fintype C]

structure GlobalChoice {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) where
  left : C → V
  right : C → V
  left_mem : ∀ c, (rootNeighbours FX X v c).Nonempty → left c ∈ rootNeighbours FX X v c
  right_mem : ∀ c, (rootNeighbours FY Y v c).Nonempty → right c ∈ rootNeighbours FY Y v c

/-- Existence of legal selectors is a consequence of finite graph maxima. -/
def defaultGlobalChoice {FX FY : HardListInstance V C} {X Y : V → C} {v : V} {a b : C}
    (h : RootLocalPair FX FY X Y v a b) : GlobalChoice h where
  left := RegularColourCharge.selectedRepresentative FX X v
  right := RegularColourCharge.selectedRepresentative FY Y v
  left_mem := RegularColourCharge.selectedRepresentative_mem FX X v
  right_mem := RegularColourCharge.selectedRepresentative_mem FY Y v

end
end CI2ZF.Appendix.CV
