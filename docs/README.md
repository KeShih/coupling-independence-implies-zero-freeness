# Documentation

This library formalizes the paper's coupling-independence and zero-free results for Potts, Holant, and independent colour fields, and the companion's further Potts regimes. Every numbered theorem, lemma, proposition and corollary of both papers has a Lean counterpart, listed in the [coverage table](coverage.json) and on the side-by-side page. Only citation-level claims remain unformalized; the [repository README](../README.md#coverage-of-the-numbered-statements) lists them. Start with the [project overview](overview.md) for the theorem scope and proof architecture.

| Guide | Contents |
| --- | --- |
| [Potts](potts.md) | Models, concrete Vigoda coupling, uniform complex transfer, and the main theorem |
| [Potts appendix](appendix/README.md) | Module navigation for all seven additional parameter regions and for the companion statements proved in dedicated modules |
| [Appendix theorem status](appendix/STATUS.md) | Regional hypotheses, proved conclusions, and the cited results each region uses |
| [Holant](holant.md) | Signature models, recursive coupling, uniform polytubes, and applications |
| [Lee–Yang colour fields](lee-yang.md) | Independent field coordinates, separator induction, and vertex- and edge-colouring corollaries |
| [Cited results](external-inputs.md) | The results cited from the literature, their Lean statements, and how each is proved |
| [Coverage table](coverage.json) | One entry for each of the 107 numbered statements of both papers, with its status and Lean names |

## Source layout

The project has one Lean library and one complete entry point, `ZeroFreeness.lean`.

| Directory | Contents |
| --- | --- |
| `ZeroFreeness/Analysis/` | Complex averages, normalized logarithms, and local stability |
| `ZeroFreeness/Coupling/Foundations/` | Finite distributions, transport, partial couplings, and shared random coins |
| `ZeroFreeness/Coupling/` | Concrete Vigoda, CV, edge-Potts, high-temperature, BBR, and girth coupling proofs; proofs of the cited CLMM and BBR results |
| `ZeroFreeness/Potts/Model/` and `Geometry/` | Real and complex partition models, pinning, graph restrictions, and separators |
| `ZeroFreeness/Potts/Transfer/` | Uniform CI-to-zero-free induction and response estimates |
| `ZeroFreeness/Potts/Theorems/` and `Regions/` | Main-text statements and all seven regional applications |
| `ZeroFreeness/LeeYang/` | Independent color-field partition functions and zero-free polydiscs |
| `ZeroFreeness/Holant/` | Symmetric log-concave Holant models, coupling, zero-free transfer, and applications |
| `audit/` | Independent kernel-axiom checks, outside the proof library |

Module paths follow this layout. Mathematical declaration names, including
`PottsCI` and `ZeroFreeness.Appendix`, are preserved so the reorganization does not
change theorem statements or proofs. The ten former import-only wrappers
have been removed; use the [module map](module-moves.tsv) when updating imports.
The detailed files retain their existing dependency graph; the directory
names describe their purpose, not a strict layering of every import.

## Verification

Run `./scripts/check-all.sh` from the repository root to build the whole library and check transitive axiom dependencies. Use `./scripts/check.sh` for the main-text proofs or `./scripts/check-appendix.sh` for the appendix regions.

The audits allow only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. The standalone Lean statements for the cited ingredients tracked in [external-inputs.md](external-inputs.md) are proved in the library, so no paper-facing theorem takes a literature hypothesis. The [verification record](verification.json) records the checked scope and source hashes. The [module migration record](module-moves.tsv) maps renamed source modules.

Return to the [repository README](../README.md) for setup and the main imports.
