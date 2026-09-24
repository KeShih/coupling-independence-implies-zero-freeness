# Lee–Yang color-field proof map

The three vertex-coloring regimes of the main-text `thm:lee-yang`, together
with `cor:edge-lee-yang`, are formalized using the actual multivariable
color-field partition functions in `CI2ZF/LeeYang/`. The aggregate entry
point is `CI2ZF.LeeYang`. Lean file names below are relative to
`CI2ZF/LeeYang/`.

## Partition functions and quantifiers

`normalizedFieldPartition tau G ℓ` sums over colorings of the free vertices,
retains all hard constraints on free–free and free–pinned edges, and omits
constraints between pinned vertices. It permits arbitrary improper
pinnings. `fullFieldPartition` is the actual weighted sum over all proper
extensions to the full graph.

`Pinning.lean` proves that, for a proper pinning, the full partition function
is the product of the pinned field factors and the normalized partition
function. For an improper pinning, the full partition function vanishes
identically. `PinningRoot.lean` connects the actual `pinVertex` operation to
the root-color recursion. A root color forbidden by a pinned neighbor has
zero coefficient in the parent recursion; its normalized child instance
remains defined.

Every radius is chosen before the graph, graph size, pinning, and fields.
The normalized conclusion requires only the free coordinates to satisfy
`‖ℓ v c - 1‖ ≤ θ`. The full-partition conclusion additionally requires only
that the prescribed pinned field factors be nonzero; under this hypothesis,
the full partition is nonzero exactly when the pinning is proper.
Restricting all coordinates to the same neighborhood automatically ensures
that these pinned factors are nonzero. The internal closed-polydisc result
is slightly stronger than the paper's version with strict inequalities.

## Proof chain

| Paper step | Lean files and declarations | Proved connection |
| --- | --- | --- |
| Multivariable field model | `Model.lean`, `Pinning.lean` | Actual hard-coloring support, one field factor for each free vertex, and equality of the all-one field value with the hard-coloring count. |
| Root recursion | `ModelRoot.lean`, `PinningRoot.lean` | Reindexing the finite sum over actual color configurations gives the `pinVertex` recursion with the root field factor. |
| Uniform analytic parameter | `GeometryFields.lean`, `Analytic.lean` | Entire functions along `fieldLine d z = 1 + z*d`, with every coordinate of the direction bounded in norm by 1. |
| Actual graph restrictions | `TransportRelabel.lean`, `TransportBFS.lean` | Field coordinates follow the same vertex embedding or equivalence. Actual child instances, the BFS three-way split, and temporary unpinning preserve the partition identities. |
| Uniform local radius | `LocalSupport.lean`, `Local.lean` | A monomial with at most B field factors has error at most `2^B θ`; averaging cancels the number of admissible configurations. A local coefficient with empty support at the all-one field vanishes identically for all fields. |
| Separator identity | `Separator.lean`, `SeparatorLog.lean` | The inside term includes both interior and shell field factors, while the exterior term includes the exterior fields. The actual hard shell marginal gives an exact complex exponential average, including terms with zero support. |
| Exterior logarithm bound | `Exterior.lean` | Each single-coordinate shell change corresponds to an actual smaller root-child instance. Uniqueness of the analytic branch and Hamming paths give the `α·ham` bound. |
| Small components | `Component.lean` | Actual connected-component factorization and cancellation of a common exterior factor reduce the root-response bound to local logarithm control. |
| Large components | `BFSResponse.lean` | Actual hard CI selects a shell with small Wasserstein distance. The complex-average error `2αW+α/2` closes under the uniform choice of scales. |
| Parent nonvanishing and induction | `Parent.lean`, `Induction.lean` | After a common normalization, the weighted terms for allowed root colors have positive real part. Nonvanishing and root responses are proved simultaneously by induction on the number of free vertices. |
| From CI to a uniform field neighborhood | `Transfer.lean`: `uniform_curve_transfer` | All complex-analytic obligations are discharged. Assuming `q ≥ Δ+1`, the remaining input is a uniform CI bound for the actual hard-coloring Gibbs laws. |
| Full polydisc | `Polydisc.lean`, `GraphClass.lean` | Set `θ=min(r/2,1/2)` and `d=(ℓ-1)/θ`, then substitute `z=θ` exactly. The quantifiers cover every independent vertex–color coordinate. |
| `prop:field-transfer` (Proposition 5.1) | `GraphClassUniform.lean`: `prop_field_transfer`, `uniform_graph_class_normalized_field_transfer`, `uniform_graph_class_field_transfer` | `GraphClass.lean` chooses `θ` after the graph class. Applying it once to the union `ciUnionClass` of all induced-subgraph-closed classes with `C₀`-coupling independence at `x = 0` gives `θ = θ(q, Δ, C₀) ∈ (0, 1/2]`, chosen before the class as in the paper. |

## Main-text parameter regimes

| Regime | Entry point | Cited results |
| --- | --- | --- |
| (i) `q ≥ (11/6 − 1/84000)Δ`, `Δ ≥ 2` | `VertexRegions.lean`: `near_vigoda_vertex_field_zero_free` | The three-way integer reduction uses the proved strict/CV CI bounds. The twenty critical integer pairs `(6j,11j)` use the CV contraction on the critical line, which replaces the cited CFFGZZ Theorem 20. No literature hypothesis. |
| (ii) `q ≥ 1.809Δ`, `Δ ≥ 125` | `VertexRegions.lean`: `cv_vertex_field_zero_free` | The complete actual CV coupling proof is already in the Appendix library. No cited result is used. |
| (iii) `q ≥ Δ+3`, `Δ ≥ 3`, sufficiently large girth | `HighGirth.lean`: `high_girth_original_field_transfer` | Uses the proved large-girth CI theorem from the Appendix, with CLMM Lemmas 8.7 and 5.13 and Equation (10) proved in Lean. No literature hypothesis. `high_girth_field_transfer` and the stronger residual-girth version `high_girth_residual_original_field_transfer` are also available. |
| Edge coloring, `q ≥ 3Δ`, `Δ ≥ 2` | `Edge.lean`: `edge_lee_yang` | Uses the proved CI bound for the actual line graph and endpoint geometry. No additional CWZZ or field-transfer hypothesis is assumed. |

No Lee–Yang endpoint takes a literature hypothesis. The cited results
used by regimes (i) and (iii) and their Lean proofs are described in
[cited results](external-inputs.md) and
[Appendix status](appendix/STATUS.md).

## Verification

`bash scripts/check-all.sh` builds the complete `CI2ZF` library, including
all seven Appendix regions, then audits the transitive axiom dependencies
of every imported project declaration. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. The latest build results,
source hashes, and exact coverage are recorded in
[verification manifest](verification.json).
