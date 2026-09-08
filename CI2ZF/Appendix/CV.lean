import CI2ZF.Appendix.CVArithmetic
import CI2ZF.Appendix.CVCertificate
import CI2ZF.Appendix.CVRecord
import CI2ZF.Appendix.CVTruncation
import CI2ZF.Appendix.CVScalar
import CI2ZF.Appendix.CVAveraging
import CI2ZF.Appendix.CVKernel
import CI2ZF.Appendix.CVMoveMass
import CI2ZF.Appendix.CVCoupling
import CI2ZF.Appendix.CVRootAllocation
import CI2ZF.Appendix.CVMetric
import CI2ZF.Appendix.CVGeometry
import CI2ZF.Appendix.CVBoundary
import CI2ZF.Appendix.CVTransport
import CI2ZF.Appendix.CVCanonical
import CI2ZF.Appendix.CVCanonicalCoupling
import CI2ZF.Appendix.CVRates
import CI2ZF.Appendix.CVIncidenceRates
import CI2ZF.Appendix.CVComponentCharge
import CI2ZF.Appendix.CVBranchEncoding
import CI2ZF.Appendix.CVActualOne
import CI2ZF.Appendix.CVTwoFamily
import CI2ZF.Appendix.CVTwoIncidence
import CI2ZF.Appendix.CVMaxChoice
import CI2ZF.Appendix.CVActualTwo
import CI2ZF.Appendix.CVSelectedChoice
import CI2ZF.Appendix.CVGlobalChoice
import CI2ZF.Appendix.CVRegularSupport
import CI2ZF.Appendix.CVGlobalRegular
import CI2ZF.Appendix.CVRootColours
import CI2ZF.Appendix.CVGlobalCoupling
import CI2ZF.Appendix.CVPieceSums
import CI2ZF.Appendix.CVSingletonRegular
import CI2ZF.Appendix.CVRegularCost
import CI2ZF.Appendix.CVRootColourCharge
import CI2ZF.Appendix.CVMoveClassification
import CI2ZF.Appendix.CVRootCost
import CI2ZF.Appendix.CVBaselinePartition
import CI2ZF.Appendix.CVCouplingCharge
import CI2ZF.Appendix.CVZeroFree

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
