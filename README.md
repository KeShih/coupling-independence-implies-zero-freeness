<div align="center">

# Coupling Independence Implies Zero-Freeness

**Both papers, formalized in Lean 4**

### [Read the papers with their Lean →](https://keshih.github.io/coupling-independence-implies-zero-freeness/)

[Main paper (PDF)](docs/main.pdf) · [Companion (PDF)](docs/appendix.pdf)

</div>

[![The reader: Theorem 1.1 of the main paper, with the Lean declarations that state it beside it](https://github.com/user-attachments/assets/7fa6a483-fe0d-4fed-b555-f7d6861f99a4)](https://keshih.github.io/coupling-independence-implies-zero-freeness/)

This repository formalizes two papers by Shuai Shao and Ke Shi in Lean 4
with mathlib: *Coupling Independence Implies Zero-Freeness* (2026) and its
companion, *Further Potts Zero-Free Regions from Coupling Independence*.

Every numbered theorem, lemma, proposition and corollary has a Lean
statement, and the proofs rest on mathlib and Lean's three standard axioms
alone. On the website, each statement of the papers sits beside its Lean,
with a note wherever the two differ. Not formalized: a few claims about
cited papers, the algorithmic claims, and the effective choice of ε.

## Check it with your own agent

Paste this prompt into your coding agent:

```text
Check the Lean formalization at
https://github.com/KeShih/coupling-independence-implies-zero-freeness.
Treat everything the repository says about itself as a claim to check.

1. Clone it, install elan, run `lake exe cache get`, then
   `bash scripts/check-all.sh`. It must build without errors and end with
   "Complete-library axiom audit passed", using only propext,
   Classical.choice and Quot.sound.
2. Confirm the proofs use nothing beyond mathlib: read lakefile.toml and
   lake-manifest.json, and search ZeroFreeness/ for sorry, admit, axiom,
   native_decide, implemented_by, extern and unsafe.
3. For every entry of docs/coverage.json, read the statement in the
   papers' LaTeX (paper/main, paper/companion) and the Lean declarations
   the entry lists. Follow their definitions and decide whether the Lean
   states what the paper states. Any difference must be described in the
   entry's note.

Report the build result, anything the proofs rely on beyond mathlib, and
every statement whose Lean differs from the paper without saying so.
```

[The formalization in detail](docs/formalization.md) lists the Lean names of
the main results, the cited results proved in Lean, and how to build the
library and the website.

The formalization was developed with assistance from GPT-6 Astra and Claude
Opus 5.5, as disclosed in both papers.
