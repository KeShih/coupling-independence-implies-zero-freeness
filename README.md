# Coupling Independence Implies Zero-Freeness

Lean formalization of the Potts, Lee–Yang and Holant results in
*Coupling Independence Implies Zero-Freeness*, including all seven
Appendix Potts regions. The proofs use actual finite partition functions
and choose zero-free neighborhoods uniformly over graph size and pinning.
The companion appendix paper is included as [docs/appendix.pdf](docs/appendix.pdf).

## Results

| Result | Formalized scope |
| --- | --- |
| [Potts](docs/potts.md) | A uniform zero-free neighborhood of `[0,1]` for normalized pinned models at `Δ ≥ 2`, `q ≥ 11Δ/6`, and transfer for induced-subgraph-closed graph families. |
| [Lee–Yang](docs/lee-yang.md) | Uniform polydiscs around the all-one field in all three vertex-coloring regimes and for edge coloring at `q ≥ 3Δ`. |
| [Holant](docs/holant.md) | Uniform complex neighborhoods of nonnegative activity boxes for symmetric log-concave signatures, with b-matching and b-edge-cover corollaries. |
| [Appendix Potts](docs/appendix/README.md) | Edge-Potts, high temperature, large girth, BBR, Carlson–Vigoda, near-Vigoda, and girth five. |

The strict Potts, Carlson–Vigoda, edge-coloring, high-temperature and Holant
endpoints have no external mathematical inputs. Critical Potts and the
exceptional near-Vigoda integer cases retain the cited CFFGZZ hard-coloring
CI theorem. Large-girth and BBR results retain their named CLMM/BBR
interfaces; girth five retains only the CLMM sphere-to-coupling theorem.
The Lee–Yang endpoints use the same inputs as their corresponding CI
regimes. See [external inputs](docs/external-inputs.md) for exact scopes.

## Build and verify

Requires [elan](https://github.com/leanprover/elan); `lean-toolchain` pins
Lean **4.33.1**, with mathlib **v4.33.1**.

```bash
lake exe cache get
LEAN_NUM_THREADS=2 bash scripts/check-all.sh
```

The complete library is imported by `CI2ZF`. The check treats warnings as
errors and audits transitive axiom dependencies, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. Literature inputs are explicit theorem
parameters. The [verification manifest](docs/verification.json)
records the checked sources, hashes and build results.

See the [documentation index](docs/README.md) for proof maps and navigation,
or the [proof overview](docs/overview.md) for the detailed argument.
