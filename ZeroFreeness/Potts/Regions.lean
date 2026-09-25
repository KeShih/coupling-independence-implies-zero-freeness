import ZeroFreeness.Potts.Regions.Edge.ZeroFree
import ZeroFreeness.Potts.Regions.Girth.High.Theorem
import ZeroFreeness.Potts.Regions.HighTemperature.ZeroFree
import ZeroFreeness.Potts.Regions.BBR.High
import ZeroFreeness.Potts.Regions.CV
import ZeroFreeness.Potts.Regions.NearVigoda.Theorem
import ZeroFreeness.Coupling.Girth.Five.ClosedPoincare
import ZeroFreeness.Coupling.Girth.Spectral.OperatorGap
import ZeroFreeness.Potts.Regions.Girth.Five.ZeroFree
import ZeroFreeness.Potts.Regions.Girth.Transfer.ResidualOriginal
import ZeroFreeness.Potts.Regions.Girth.Transfer.PottsTransfer
import ZeroFreeness.Potts.Regions.Girth.CommonThreshold
import ZeroFreeness.Coupling.Girth.Covariance.Graph.Disintegration
import ZeroFreeness.Coupling.Girth.Covariance.Insertion.OneEdgeOperator
import ZeroFreeness.Coupling.Girth.Tree.SingleEdge
import ZeroFreeness.Coupling.Edge.Slots.OneLabel
import ZeroFreeness.Potts.Theorems.CriticalScope
import ZeroFreeness.Coupling.BBR.RoundedInterval
import ZeroFreeness.Coupling.BBR.GapTwo
import ZeroFreeness.Coupling.BBR.Unconditional
import ZeroFreeness.Coupling.Girth.Tree.TotalInfluenceUnconditional
import ZeroFreeness.Coupling.CLMM.TransferUnconditional

/-! Completed appendix regions. Each imported endpoint proves coupling
independence for the actual finite Gibbs laws, then the uniform zero-free
corollary. No endpoint takes a literature parameter; docs/appendix/STATUS.md records how the cited results are proved. -/
