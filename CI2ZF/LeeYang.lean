import CI2ZF.LeeYang.PinningRoot
import CI2ZF.LeeYang.VertexRegions
import CI2ZF.LeeYang.HighGirth
import CI2ZF.LeeYang.Edge
import CI2ZF.LeeYang.GraphClassUniform

/-!
# Main-text Lee--Yang zeros

The independent vertex-colour field theorem is exported in all three
paper regimes by `near_vigoda_vertex_field_zero_free`,
`cv_vertex_field_zero_free`, and `high_girth_original_field_transfer`.
`edge_lee_yang` exports the q ≥ 3Δ edge-colouring corollary.

The normalized partition is defined for arbitrary, possibly improper,
pinnings; the full partition is the actual sum over proper extensions.
Uniform field radii precede all graph-size, pinning and field quantifiers.

`uniform_curve_transfer` proves the hard-CI-to-field analytic induction;
`uniform_field_transfer_closed` converts it to the full multivariable
polydisc. Explicit literature inputs are precisely those already retained
by the near-Vigoda critical branch and the large-girth CI theorem.
-/
