# Verification of the Lean formalization

> An example of what the README's verification prompt produces, run in
> Claude Code at xhigh effort in about 30 minutes. `PaperForms.lean`, which
> the report refers to, is not in the repository yet.

Checked on 2026-09-25 against `origin/main` at commit
261b3c42499dc7e3e236beef2a448201975233b8 of
https://github.com/KeShih/coupling-independence-implies-zero-freeness, in a
fresh clone. The local checkout was then 17 commits behind (at d4e5e26), but
those commits change only `README.md` and `docs/`. The Lean sources, audits,
scripts and papers are identical.

## Verdict

- No build problem and no trust-base problem.
- No zero-freeness result of either paper has a Lean statement that is weaker
  than the paper's. Every one assumes the same or less and concludes the same or
  more, over the same or a wider range of parameters.

## Build and trust base

| Check | Result |
|---|---|
| `LEAN_NUM_THREADS=2 bash scripts/check-all.sh` | `Build completed successfully (4069 jobs)`, no errors or warnings (warnings are errors); all 533 modules built |
| Repository axiom audit (`audit/All.lean`) | 11,320 declarations; only `propext`, `Classical.choice`, `Quot.sound` |
| `#print axioms` on the 23 headline theorems | only the same three axioms |
| `lake env leanchecker --fresh ZeroFreeness` | passed: every declaration, including Lean core and the imported Mathlib files, re-checked by the kernel from scratch |
| Source scan of `ZeroFreeness/` | no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`, `opaque`, custom macros or elaborators, or `debug.skipKernelTC`; the three `decide +kernel` uses are kernel-checked and add no axiom |
| Toolchain in `.tools/lean-4.33.1-darwin_aarch64` | byte-identical to the official Lean v4.33.1 darwin_aarch64 release (17,466 files) |
| Dependencies | Mathlib at tag v4.33.1 (0df444a); every package at its `lake-manifest.json` revision, unmodified; the code imports only Mathlib and Lean core |

Three modules print a note that `ring` fell back to `ring_nf`. It is cosmetic.

Timings on this machine (Apple M4, 10 cores, 24 GB), with prebuilt Mathlib:
- project build and audit: about 17 minutes wall-clock (about 32 minutes if the
  per-module times are added up; lake compiles several modules at once);
- `leanchecker --fresh`: about 10.5 minutes, 8.5 GB peak memory.

## Statements

Each result was read in the LaTeX and compared with its Lean statement,
following the definitions down to pinnings, boundary counts, the partition
polynomials, neighbourhoods, Wasserstein distance, Gibbs laws and Holant
signatures.

For the rows marked "proved" (17 Lean theorems), the paper's claim was also written in Lean with independent
definitions using only Mathlib, and proved from the repository's theorem; see
`PaperForms.lean` in this folder. There a pinning is a partial map
`V → Option (Fin q)`, `Ẑ` is the literal sum of `z^(m_G(σ) − m_G(τ))` over
colourings extending the pinning, `𝒰_ε(I)` is `{z : ∃ x ∈ I, |z − x| < ε}`,
maximum degree is `SimpleGraph.maxDegree`, and girth is `egirth` of the free
graph. Every theorem in the file depends only on the three standard axioms.

"Proved" below means proved in that file; "read" means checked by reading the
definitions.

### Main paper

| Result | Lean declaration | Check |
|---|---|---|
| `thm:intro-main` | `ZeroFreeness.Potts.potts_main_theorem` | proved |
| `lem:hard-feas`, consequence `Ẑ(0) > 0` | `ZeroFreeness.Potts.partition_zero_pos_of_succ_le` | proved |
| `thm:potts-transfer` | `ZeroFreeness.Potts.graph_class_potts_transfer_of_bounded` | read |
| `lem:potts-positive-response` | `ZeroFreeness.Potts.lem_potts_positive_response` | read |
| `prop:ep-disc` | `ZeroFreeness.Potts.prop_ep_disc` | read |
| `prop:field-transfer` | `ZeroFreeness.LeeYang.prop_field_transfer` | read |
| `thm:lee-yang` (i) | `ZeroFreeness.LeeYang.near_vigoda_vertex_field_zero_free` | proved |
| `thm:lee-yang` (ii) | `ZeroFreeness.LeeYang.cv_vertex_field_zero_free` | proved |
| `thm:lee-yang` (iii) | `ZeroFreeness.LeeYang.high_girth_original_field_transfer` | proved |
| `cor:edge-lee-yang` | `ZeroFreeness.LeeYang.edge_lee_yang` | proved |
| `thm:holant-box`, polytube | `ZeroFreeness.Holant.exists_uniform_holant_polytube` | proved |
| `thm:holant-box`, diagonal | `ZeroFreeness.Holant.holant_uniform_diagonal` | proved |
| `thm:holant-box`, orthant | `ZeroFreeness.Holant.holant_orthant` | read |
| `cor:bmatching-short` | `ZeroFreeness.Holant.bmatching_uniform_polytube` | proved |
| `cor:bcover-short` | `ZeroFreeness.Holant.cor_bcover_short` | proved |

The appendix table (`tab:appendix-extensions`) and
`rem:additional-potts-transfer` restate the companion results below.

### Companion paper

| Result | Lean declaration | Check |
|---|---|---|
| `thm:potts-transfer`, `lem:potts-positive-response` (recalled) | as in the main paper | read |
| `thm:additional-potts-zf` (i) | `ZeroFreeness.Appendix.near_vigoda_zero_free` | proved |
| `thm:additional-potts-zf` (ii) | `ZeroFreeness.Appendix.CV.zero_free` | proved |
| `thm:additional-potts-zf` (iii) | `ZeroFreeness.Appendix.Girth.high_girth_residual_original_zero_free` | proved |
| `thm:intro-bbr-interval`, including `0 < x₀ < 1` | `ZeroFreeness.Appendix.BBR.high_girth_residual_original_zero_free`, `ZeroFreeness.Appendix.BBR.start_mem` | proved |
| `cor:intro-high-temperature` | `ZeroFreeness.Appendix.high_temperature_zero_free` | proved |
| `thm:unrestricted-girth5` | `ZeroFreeness.Appendix.Girth.girth_five_residual_original_zero_free` | proved |
| `cor:soft-edge-zf` | `ZeroFreeness.Appendix.Edge.edge_potts_zero_free` | proved |

### The results checked by reading

The transfer theorem, the positive-activity lemma, the disc at 0 and the field
transfer take coupling independence over a graph class as a hypothesis.
Restating that independently would mean rebuilding the Wasserstein and Gibbs
machinery, so these were checked against the definitions
(`GraphClass`, `GraphClassRootCouplingBound`, `GraphClassTransferInputs`,
`rootChildData`, `pinVertex`, `PinningData.gibbs`, `FinDist.W`, `ham`,
`HasSmallResponseLog`).

- The coupling hypothesis matches `def:potts-ci`. The Lean version asks for the
  bound only when both conditioned laws are defined, which is a weaker
  assumption.
- Constants are chosen in the paper's order: the radius comes after the class in
  the transfer theorem, and before it in the other three.
- Each conclusion matches the paper's, including the unnormalized statement
  with the forced zero of order `m_G(τ)` at `z = 0` in the transfer theorem.

## Differences that are not mismatches

- **Graph classes.** Lean's `GraphClass` must be closed under induced subgraphs
  and relabelling (`comap_mem` along embeddings); the paper says only "closed
  under taking induced subgraphs". Coupling independence and zero-freeness do
  not depend on vertex labels, so applying the Lean theorem to the
  relabelling-closure of a paper class gives the paper's statement.
- **Lean often assumes less.**
  - The transfer theorem drops `Δ ≥ 2`.
  - Lee–Yang (i) and (ii) and the edge version use the closed polydisc
    `|λ − 1| ≤ θ`.
  - The Holant theorem allows `R = 0` and any `Δ`.
  - The high-temperature theorem does not need `x* ≤ 1`.
  - The girth-five theorem fixes an explicit degree threshold,
    `girthFiveCIThreshold δ`, where the paper says only "there is `Δ₅(δ)`".
  - Several paper-form wrappers keep unused hypotheses as `_`-named arguments.

## Reproducing

From the repository root, with prebuilt Mathlib in place:

```bash
LEAN_NUM_THREADS=2 bash scripts/check-all.sh
bash scripts/lake.sh env leanchecker --fresh ZeroFreeness
bash scripts/lake.sh env lean -DwarningAsError=true Verification/2026-09-25/PaperForms.lean
```

The last command prints the axioms of each paper-form theorem. It takes about
30 seconds once `ZeroFreeness` is built.
