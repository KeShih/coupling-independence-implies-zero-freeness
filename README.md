# Coupling Independence Implies Zero-Freeness

A Lean 4 and mathlib formalization of

- Shuai Shao and Ke Shi, *Coupling Independence Implies Zero-Freeness* (2026), and
- its companion, *Further Potts Zero-Free Regions from Coupling Independence*,
  included as [docs/appendix.pdf](docs/appendix.pdf).

Every statement concerns actual finite partition functions. Potts pinnings
are arbitrary partial colourings, improper ones included, and every
zero-free radius is chosen before the graph, its size and the pinning.
Results from the literature enter as explicit theorem hypotheses, never as
axioms: the whole library depends only on Lean's standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

The [side-by-side page](https://keshih.github.io/coupling-independence-implies-zero-freeness/)
sets each paper statement beside the Lean theorem that proves it and matches
the two phrase by phrase. It also shows each theorem's axioms, literature
hypotheses and the library lemmas its proof applies, with source links
pinned to the commit. `scripts/site/build.py` generates it into
`docs/index.html` and checks every quotation against the sources.

## The main theorem

For integers `Δ ≥ 2` and `q ≥ 11Δ/6`, one radius works for every graph of
maximum degree at most `Δ` (Theorem 1.1 of the paper; universe annotations
omitted):

```lean
theorem CI2ZF.Potts.potts_main_theorem (q Δ : ℕ) (hΔ : 2 ≤ Δ) (hq : 11 * Δ ≤ 6 * q)
    (hExternal : 6 * q = 11 * Δ → ExternalCriticalHardColouringTheorem (Fin q) Δ) :
    ∃ eps > 0, UniformPottsZeroFree (Fin q) Δ eps

def CI2ZF.Potts.UniformPottsZeroFree (C : Type v) [Fintype C] (Δ : ℕ) (eps : ℝ) : Prop :=
  ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
    (∀ w, G.degree w ≤ Δ) → ∀ tau : PartialColouring V C,
    (∀ z ∈ thickening eps pottsInterval, normalizedPartition tau G z ≠ 0) ∧
    (∀ z ∈ thickening eps pottsInterval,
      fullPartition tau G z = 0 ↔ z = 0 ∧ 0 < tau.pinnedConflictCount G) ∧
    (fullPolynomial tau G).rootMultiplicity 0 = tau.pinnedConflictCount G
```

Here `pottsInterval` is `[0,1] ⊆ ℂ` and `thickening eps` is its open
`eps`-neighbourhood. The normalized pinned polynomial has no zeros there.
The ordinary pinned polynomial vanishes there only at `z = 0`, to order equal
to the number of monochromatic edges inside the pinned set, so not at all
when the pinning is proper. The hypothesis `hExternal` matters only on the
line `6q = 11Δ`, where it supplies the hard-colouring coupling bound of
Chen, Feng, Guo, Zhang and Zou. `potts_main_strict` proves the case
`11Δ < 6q` with no hypothesis.

## What is formalized

Theorem numbers follow the September 2026 versions of the two papers. Lean
names are relative to `CI2ZF`.

### Main paper

| Result | Lean | Literature hypotheses |
| --- | --- | --- |
| Thm 1.1: Potts zero-freeness near `[0,1]` for `q ≥ 11Δ/6` | `Potts.potts_main_theorem`, `Potts.potts_main_strict` | CFFGZZ Thm 20, only when `q = 11Δ/6` |
| Thm 1.2: coupling independence implies zero-freeness on induced-subgraph-closed classes | `Potts.graph_class_potts_transfer_of_bounded` | none beyond its own coupling assumptions |
| Thm 4.1, Prop 4.10, Prop 4.12: the soft flip coupling and its conditional hard estimate | `Potts.root_strict_ci`, `conditionalHardCouplingEstimate`, `Potts.root_positive_ci` | none |
| Prop 5.1, Thm 5.2: Lee–Yang polydiscs for vertex-colour fields | `LeeYang.graph_class_normalized_field_transfer`, `LeeYang.near_vigoda_vertex_field_zero_free`, `LeeYang.cv_vertex_field_zero_free`, `LeeYang.high_girth_residual_original_field_transfer` | those of the near-Vigoda and large-girth rows below |
| Cor 5.4: edge-colour fields for `q ≥ 3Δ` | `LeeYang.edge_lee_yang` | none |
| Thm 5.6, Cors 5.7 and 5.9: log-concave Holant problems, b-matchings and b-edge-covers | `Holant.exists_uniform_holant_polytube`, `Holant.bmatching_uniform_polytube`, `Holant.bcover_uniform_polytube` | none |

### Appendix A: further Potts regimes

Each regime has a coupling-independence theorem and a zero-free theorem.
Girth conditions apply only to the free graph left after pinning.

| Regime | Coupling independence | Zero-freeness | Literature hypotheses |
| --- | --- | --- | --- |
| near-Vigoda: `Δ ≥ 2`, `q ≥ (11/6 − 1/84000)Δ` | `Appendix.near_vigoda_transfer_inputs` | `Appendix.near_vigoda_zero_free` | CFFGZZ Thm 20 at `(Δ,q) = (6j,11j)`, `j ≤ 20` |
| Carlson–Vigoda: `Δ ≥ 125`, `q ≥ 1.809Δ` | `Appendix.CV.root_coupling` | `Appendix.CV.zero_free` | none |
| large girth: `Δ ≥ 3`, `q ≥ Δ + 3` | `Appendix.Girth.high_girth_coupling` | `Appendix.Girth.high_girth_residual_original_zero_free` | CLMM Lemmas 5.13 and 8.7, Eq. (10) |
| high temperature: `q > 11(1 − x₀)Δ/6`, near `[x₀,1]` | `Appendix.high_temperature_graph_coupling` | `Appendix.high_temperature_zero_free` | none |
| BBR interval: `q ≥ 3`, `Δ/q ≥ (e − 1/2)/(e − 1)`, near `[BBR.start q Δ, 1]` | `Appendix.BBR.high_girth_coupling` | `Appendix.BBR.high_girth_residual_original_zero_free` | BBR Prop 2.6(i) and Thm 2.5; CLMM Lemma 5.13, Eq. (10) |
| edge-Potts: `Δ ≥ 2`, `q ≥ 3Δ`, on line graphs | `Appendix.Edge.root_children_ci` | `Appendix.Edge.edge_potts_zero_free` | none |
| girth five: `0 < δ ≤ 1`, `Δ ≥ girthFiveCIThreshold δ`, `q ≥ (1 + δ)Δ` | `Appendix.Girth.girth_five_coupling` | `Appendix.Girth.girth_five_residual_original_zero_free` | CLMM Lemma 5.13 |

[docs/appendix/STATUS.md](docs/appendix/STATUS.md) gives the exact
hypotheses, constants and proof route of each regime, including where the
Lean proof differs from the written one.

## Literature hypotheses

The cited results are stated as Lean propositions and passed as hypotheses.

| Lean proposition | Source |
| --- | --- |
| `Potts.ExternalCriticalHardColouringTheorem` | Chen, Feng, Guo, Zhang, Zou, *Deterministic counting from coupling independence*, arXiv:2410.23225v2, Theorem 20 |
| `Appendix.CLMM.Literature`, `Appendix.Girth.SphereCouplingInput`, `Appendix.Girth.CavityTree.CLMMInfluenceIdentity` | Chen, Liu, Mani, Moitra, *Strong spatial mixing for colorings on trees and its algorithmic applications*, arXiv:2304.01954v3, Lemma 5.13, Equation (10) and Lemma 8.7 |
| `Appendix.BBR.Literature` | Bencs, Berrekkal, Regts, *Near optimal bounds for weak and strong spatial mixing for the anti-ferromagnetic Potts model on trees*, Electron. J. Probab. 30 (2025), Proposition 2.6(i) and Theorem 2.5 |

Each is a statement about actual finite Potts models, in the form the
written proofs use, and none postulates anything this repository proves.
[docs/external-inputs.md](docs/external-inputs.md) records their exact form
and scope. The axiom audit shows that nothing else is assumed; it does not,
of course, prove these hypotheses.

## Build and verify

Requires [elan](https://github.com/leanprover/elan). `lean-toolchain` pins
Lean 4.33.1 and `lakefile.toml` pins mathlib v4.33.1.

```bash
lake exe cache get
LEAN_NUM_THREADS=2 bash scripts/check-all.sh
```

`check-all.sh` builds the library with warnings treated as errors, then
checks the transitive axioms of every project declaration. A successful
run ends with

```text
Build completed successfully (4031 jobs).
Complete-library axiom audit passed: 9693 declarations; allowed dependencies used: [propext,
 Classical.choice,
 Quot.sound]
```

`scripts/check.sh` checks only the main paper and `scripts/check-appendix.sh`
only Appendix A. [docs/verification.json](docs/verification.json) records
the checked sources, their SHA-256 hashes and the last full run.

## Layout

| Path | Contents |
| --- | --- |
| `CI2ZF/Analysis/` | complex averages, analytic logarithms, local stability |
| `CI2ZF/Coupling/` | the couplings: Vigoda flips, Carlson–Vigoda, edge-Potts, high temperature, large girth, BBR, girth five |
| `CI2ZF/Potts/` | Potts models, pinnings and separators, the transfer theorem, the main theorems and the Appendix A regimes |
| `CI2ZF/LeeYang/` | colour-field partition functions and zero-free polydiscs |
| `CI2ZF/Holant/` | log-concave Holant models and their applications |
| `audit/` | axiom audits, kept outside the library |
| `docs/` | proof guides, per-result status, the verification record and the companion paper |

`CI2ZF.lean` imports the whole library. To read the proofs, start with the
[documentation index](docs/README.md) or the [proof overview](docs/overview.md).

The formalization was developed with GPT-6 Astra assistance, as disclosed in
both papers.
