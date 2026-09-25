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
Verify the Lean formalization at
https://github.com/KeShih/coupling-independence-implies-zero-freeness.

1. Build it and confirm that it compiles without errors, contains no
   sorry or admit, and depends only on mathlib and Lean's standard axioms
   (propext, Classical.choice, Quot.sound).
2. Read every zero-freeness result of both papers yourself, without
   relying on the repository's descriptions, and compare each with the
   Lean declaration that states it, following its definitions. The Lean
   statement must claim what the paper claims: no extra assumptions, no
   weaker conclusion, no narrower range of parameters.

Report any build or trust-base problem, and every zero-freeness result
whose Lean statement does not match the paper.
```

For a full check, replace "every zero-freeness result" with "every numbered
statement"; [docs/coverage.json](docs/coverage.json) lists all 107 with their
Lean declarations.

[The formalization in detail](docs/formalization.md) lists the Lean names of
the main results, the cited results proved in Lean, and how to build the
library and the website.

The formalization was developed with assistance from GPT-6 Astra and Claude
Opus 5.5, as disclosed in both papers.
