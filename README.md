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
Verify that the Lean code in
https://github.com/KeShih/coupling-independence-implies-zero-freeness
builds with 0 sorry/admit and proves every result of its two papers,
using only mathlib and Lean's standard axioms. Trust nothing the
repository says about itself: list the results from the papers yourself,
state each one in Lean yourself, prove your statement from the
repository's theorems, and check its axioms. Report every result that is
not proved exactly as the paper states it.
```

[The formalization in detail](docs/formalization.md) lists the Lean names of
the main results, the cited results proved in Lean, and how to build the
library and the website.

The formalization was developed with assistance from GPT-6 Astra and Claude
Opus 5.5, as disclosed in both papers.
