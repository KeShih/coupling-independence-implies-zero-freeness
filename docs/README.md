# Documentation

This library formalizes the paper's coupling-independence and zero-free results for Potts, Holant, and independent colour fields. Start with the [project overview](overview.md) for the theorem scope and proof architecture.

| Guide | Contents |
| --- | --- |
| [Potts](potts.md) | Models, concrete Vigoda coupling, uniform complex transfer, and the main theorem |
| [Potts appendix](appendix/README.md) | Module navigation for all seven additional parameter regions |
| [Appendix theorem status](appendix/STATUS.md) | Regional hypotheses, proved conclusions, and remaining literature inputs |
| [Holant](holant.md) | Signature models, recursive coupling, uniform polytubes, and applications |
| [Lee–Yang colour fields](lee-yang.md) | Independent field coordinates, separator induction, and vertex- and edge-colouring corollaries |
| [External inputs](external-inputs.md) | Cited results represented as explicit theorem parameters and their exact scope |

## Source layout

The project has one Lean library and one complete entry point, `CI2ZF.lean`.

| Directory | Contents |
| --- | --- |
| `CI2ZF/Analysis/` | Complex averages, normalized logarithms, and local stability |
| `CI2ZF/Coupling/Foundations/` | Finite distributions, transport, partial couplings, and shared random coins |
| `CI2ZF/Coupling/` | Concrete Vigoda, CV, edge-Potts, high-temperature, BBR, and girth coupling proofs; named CLMM interfaces |
| `CI2ZF/Potts/Model/` and `Geometry/` | Real and complex partition models, pinning, graph restrictions, and separators |
| `CI2ZF/Potts/Transfer/` | Uniform CI-to-zero-free induction and response estimates |
| `CI2ZF/Potts/Theorems/` and `Regions/` | Main-text statements and all seven regional applications |
| `CI2ZF/LeeYang/` | Independent color-field partition functions and zero-free polydiscs |
| `CI2ZF/Holant/` | Symmetric log-concave Holant models, coupling, zero-free transfer, and applications |
| `audit/` | Independent kernel-axiom checks, outside the proof library |

Module paths follow this layout. Mathematical declaration names, including
`PottsCI` and `CI2ZF.Appendix`, are preserved so the reorganization does not
change theorem statements or proofs. The ten former import-only wrappers
have been removed; use the [module map](module-moves.tsv) when updating imports.
The detailed files retain their existing dependency graph; the directory
names describe their purpose, not a strict layering of every import.

## Verification

Run `./scripts/check-all.sh` from the repository root to build the whole library and check transitive axiom dependencies. Use `./scripts/check.sh` for the main-text proofs or `./scripts/check-appendix.sh` for the appendix regions.

The audits allow only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`. Literature results remain explicit mathematical hypotheses; passing the audit does not prove those hypotheses. The [verification record](verification.json) records the checked scope and source hashes. The [module migration record](module-moves.tsv) maps renamed source modules.

Return to the [repository README](../README.md) for setup and the main imports.
