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

/-!
# Carlson--Vigoda appendix: proved components

This aggregate exports the actual CV kernels, stationarity, component move
masses, full regular root matches, geometric path metric and its output-score
upper bound, child--middle discrepancy, kernel-checked low-multiplicity
certificate, infinite-multiplicity averaging bound, and continuous scalar gap.
The canonical first-incidence plan is an actual CV coupling; its rates are
identified with component residuals. The high-multiplicity and missing-colour
component bounds and the one-neighbour graph-to-certificate estimate are proved.

The final geometric drift theorem is not asserted here: its remaining input
is a globally combined CV greedy coupling with the expected-discount and
record-domination/degree assembly proved for that same coupling. In particular,
no conditional drift hypothesis is presented as the appendix's final CI theorem.
-/
