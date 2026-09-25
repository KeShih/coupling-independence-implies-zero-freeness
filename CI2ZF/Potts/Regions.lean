import CI2ZF.Potts.Regions.Edge.ZeroFree
import CI2ZF.Potts.Regions.Girth.High.Theorem
import CI2ZF.Potts.Regions.HighTemperature.ZeroFree
import CI2ZF.Potts.Regions.BBR.High
import CI2ZF.Potts.Regions.CV
import CI2ZF.Potts.Regions.NearVigoda.Theorem
import CI2ZF.Coupling.Girth.Five.ClosedPoincare
import CI2ZF.Coupling.Girth.Spectral.OperatorGap
import CI2ZF.Potts.Regions.Girth.Five.ZeroFree
import CI2ZF.Potts.Regions.Girth.Transfer.ResidualOriginal
import CI2ZF.Potts.Regions.Girth.Transfer.PottsTransfer
import CI2ZF.Potts.Regions.Girth.CommonThreshold
import CI2ZF.Coupling.Girth.Covariance.Graph.Disintegration
import CI2ZF.Coupling.Girth.Covariance.Insertion.OneEdgeOperator
import CI2ZF.Coupling.Girth.Tree.SingleEdge
import CI2ZF.Coupling.Edge.Slots.OneLabel
import CI2ZF.Potts.Theorems.CriticalScope
import CI2ZF.Coupling.BBR.RoundedInterval
import CI2ZF.Coupling.BBR.GapTwo

/-! Completed appendix regions. Each imported endpoint proves coupling
independence for the actual finite Gibbs laws, then the uniform zero-free
corollary. No endpoint takes a literature parameter; docs/appendix/STATUS.md records how the cited results are proved. -/
