import ZeroFreeness.Coupling.Vigoda.HardGlobalCost

/-! Residual move-size charges on the actual regular colour blocks. -/
namespace ZeroFreeness
open PottsCI PottsCI.Vigoda
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V C : Type*} [Fintype V] [Fintype C] [Nonempty V] [Nonempty C]
local instance baselineDataConfigDecEq : DecidableEq (V → C) := Classical.decEq _

def regularBaseline (FX FY : HardListInstance V C) (X Y : V → C) (v : V) (c : C) : ℝ :=
  (∑ U ∈ regularMoveRows FX X v (Y v) c,
    (hardCommonOffRootPartial FX FY X Y v).leftResidual U * ham X U) +
  ∑ Z ∈ regularMoveRows FY Y v (X v) c,
    (hardCommonOffRootPartial FX FY X Y v).rightResidual Z * ham Y Z

end
end ZeroFreeness
