import CI2ZF.Appendix.CV.Arithmetic
import CI2ZF.Appendix.CV.Certificate
import CI2ZF.Appendix.CV.Record
import CI2ZF.Appendix.CV.Truncation
import CI2ZF.Appendix.CV.Scalar
import CI2ZF.Appendix.CV.Averaging
import CI2ZF.Appendix.CV.Kernel
import CI2ZF.Appendix.CV.MoveMass
import CI2ZF.Appendix.CV.Coupling
import CI2ZF.Appendix.CV.RootAllocation
import CI2ZF.Appendix.CV.Metric
import CI2ZF.Appendix.CV.Geometry
import CI2ZF.Appendix.CV.Boundary
import CI2ZF.Appendix.CV.Transport
import CI2ZF.Appendix.CV.Canonical
import CI2ZF.Appendix.CV.CanonicalCoupling
import CI2ZF.Appendix.CV.Rates
import CI2ZF.Appendix.CV.IncidenceRates
import CI2ZF.Appendix.CV.ComponentCharge
import CI2ZF.Appendix.CV.BranchEncoding
import CI2ZF.Appendix.CV.ActualOne
import CI2ZF.Appendix.CV.TwoFamily
import CI2ZF.Appendix.CV.TwoIncidence
import CI2ZF.Appendix.CV.MaxChoice
import CI2ZF.Appendix.CV.ActualTwo
import CI2ZF.Appendix.CV.SelectedChoice
import CI2ZF.Appendix.CV.GlobalChoice
import CI2ZF.Appendix.CV.RegularSupport
import CI2ZF.Appendix.CV.GlobalRegular
import CI2ZF.Appendix.CV.RootColours
import CI2ZF.Appendix.CV.GlobalCoupling
import CI2ZF.Appendix.CV.PieceSums
import CI2ZF.Appendix.CV.SingletonRegular
import CI2ZF.Appendix.CV.RegularCost
import CI2ZF.Appendix.CV.RootColourCharge
import CI2ZF.Appendix.CV.MoveClassification
import CI2ZF.Appendix.CV.RootCost
import CI2ZF.Appendix.CV.BaselinePartition
import CI2ZF.Appendix.CV.CouplingCharge
import CI2ZF.Appendix.CV.ZeroFree

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
