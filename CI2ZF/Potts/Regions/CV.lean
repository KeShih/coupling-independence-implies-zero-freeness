import CI2ZF.Coupling.CV.Arithmetic
import CI2ZF.Coupling.CV.Certificate
import CI2ZF.Coupling.CV.Record
import CI2ZF.Coupling.CV.Truncation
import CI2ZF.Coupling.CV.Scalar
import CI2ZF.Coupling.CV.Averaging
import CI2ZF.Coupling.CV.Kernel
import CI2ZF.Coupling.CV.MoveMass
import CI2ZF.Coupling.CV.Coupling
import CI2ZF.Coupling.CV.RootAllocation
import CI2ZF.Coupling.CV.Metric
import CI2ZF.Coupling.CV.Geometry
import CI2ZF.Coupling.CV.Boundary
import CI2ZF.Coupling.CV.Transport
import CI2ZF.Coupling.CV.Canonical
import CI2ZF.Coupling.CV.CanonicalCoupling
import CI2ZF.Coupling.CV.Rates
import CI2ZF.Coupling.CV.IncidenceRates
import CI2ZF.Coupling.CV.ComponentCharge
import CI2ZF.Coupling.CV.BranchEncoding
import CI2ZF.Coupling.CV.ActualOne
import CI2ZF.Coupling.CV.TwoFamily
import CI2ZF.Coupling.CV.TwoIncidence
import CI2ZF.Coupling.CV.MaxChoice
import CI2ZF.Coupling.CV.ActualTwo
import CI2ZF.Coupling.CV.SelectedChoice
import CI2ZF.Coupling.CV.GlobalChoice
import CI2ZF.Coupling.CV.RegularSupport
import CI2ZF.Coupling.CV.GlobalRegular
import CI2ZF.Coupling.CV.RootColours
import CI2ZF.Coupling.CV.GlobalCoupling
import CI2ZF.Coupling.CV.PieceSums
import CI2ZF.Coupling.CV.SingletonRegular
import CI2ZF.Coupling.CV.RegularCost
import CI2ZF.Coupling.CV.RootColourCharge
import CI2ZF.Coupling.CV.MoveClassification
import CI2ZF.Coupling.CV.RootCost
import CI2ZF.Coupling.CV.BaselinePartition
import CI2ZF.Coupling.CV.CouplingCharge
import CI2ZF.Potts.Regions.CV.ZeroFree
import CI2ZF.Coupling.CV.ClosedKernel
import CI2ZF.Coupling.CV.RootLocalStructure
import CI2ZF.Coupling.CV.MovePartition
import CI2ZF.Coupling.CV.FreshGain
import CI2ZF.Coupling.CV.ExpectedLoss
import CI2ZF.Coupling.CV.HighColours
import CI2ZF.Coupling.CV.Assembly

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
