import ZeroFreeness.Coupling.CV.Arithmetic
import ZeroFreeness.Coupling.CV.Certificate
import ZeroFreeness.Coupling.CV.Record
import ZeroFreeness.Coupling.CV.Truncation
import ZeroFreeness.Coupling.CV.Scalar
import ZeroFreeness.Coupling.CV.Averaging
import ZeroFreeness.Coupling.CV.Kernel
import ZeroFreeness.Coupling.CV.MoveMass
import ZeroFreeness.Coupling.CV.Coupling
import ZeroFreeness.Coupling.CV.RootAllocation
import ZeroFreeness.Coupling.CV.Metric
import ZeroFreeness.Coupling.CV.Geometry
import ZeroFreeness.Coupling.CV.Boundary
import ZeroFreeness.Coupling.CV.Transport
import ZeroFreeness.Coupling.CV.Canonical
import ZeroFreeness.Coupling.CV.CanonicalCoupling
import ZeroFreeness.Coupling.CV.Rates
import ZeroFreeness.Coupling.CV.IncidenceRates
import ZeroFreeness.Coupling.CV.ComponentCharge
import ZeroFreeness.Coupling.CV.BranchEncoding
import ZeroFreeness.Coupling.CV.ActualOne
import ZeroFreeness.Coupling.CV.TwoFamily
import ZeroFreeness.Coupling.CV.TwoIncidence
import ZeroFreeness.Coupling.CV.MaxChoice
import ZeroFreeness.Coupling.CV.ActualTwo
import ZeroFreeness.Coupling.CV.SelectedChoice
import ZeroFreeness.Coupling.CV.GlobalChoice
import ZeroFreeness.Coupling.CV.RegularSupport
import ZeroFreeness.Coupling.CV.GlobalRegular
import ZeroFreeness.Coupling.CV.RootColours
import ZeroFreeness.Coupling.CV.GlobalCoupling
import ZeroFreeness.Coupling.CV.PieceSums
import ZeroFreeness.Coupling.CV.SingletonRegular
import ZeroFreeness.Coupling.CV.RegularCost
import ZeroFreeness.Coupling.CV.RootColourCharge
import ZeroFreeness.Coupling.CV.MoveClassification
import ZeroFreeness.Coupling.CV.RootCost
import ZeroFreeness.Coupling.CV.BaselinePartition
import ZeroFreeness.Coupling.CV.CouplingCharge
import ZeroFreeness.Potts.Regions.CV.ZeroFree
import ZeroFreeness.Coupling.CV.ClosedKernel
import ZeroFreeness.Coupling.CV.RootLocalStructure
import ZeroFreeness.Coupling.CV.MovePartition
import ZeroFreeness.Coupling.CV.FreshGain
import ZeroFreeness.Coupling.CV.ExpectedLoss
import ZeroFreeness.Coupling.CV.HighColours
import ZeroFreeness.Coupling.CV.Assembly

/-!
# Carlson--Vigoda appendix: complete CI and zero-free theorem

This aggregate exports the actual CV kernels, stationarity, component move
masses, full regular root matches, geometric path metric and its output-score
upper bound, child--middle discrepancy, kernel-checked low-multiplicity
certificate, infinite-multiplicity averaging bound, and continuous scalar gap.
The full global canonical coupling combines every regular and both root-colour
plans. Its Hamming drift is bounded by the actual component charge sum.
Both low-multiplicity graph-to-certificate estimates, synchronized selector
existence, and the high-multiplicity and missing-colour bounds are proved.

The activation, geometric discount and complete degree summation prove the
actual adjacent metric drift. Weighted path coupling and two-metric stationary
comparison then give CI for the real normalized root children, including both
endpoints and empty remaining graphs. `option_root_ci` has the explicit constant
`409060125/50858 < 8043.19`. `zero_free` applies the proved uniform complex
transfer for every graph size and arbitrary pinning. No external input remains.
-/
