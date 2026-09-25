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
proves every result of its two papers (paper/, PDFs in docs/) from mathlib
alone. Trust nothing the repository says about itself; check every result.

1. Build it: `lake exe cache get`, then `bash scripts/check-all.sh`.
   Confirm lake-manifest.json pins only official mathlib.
2. List every numbered result and definition in both papers, plus the
   results claimed in the abstract and introduction.
3. For each, write the statement in Lean yourself from the paper, then
   prove it from the repository's theorem in a file that imports
   ZeroFreeness (`example : <yours> := by simpa using <theirs>`).
   Check every definition you use against the paper.
4. `#print axioms` each example: only propext, Classical.choice and
   Quot.sound may appear, and no hypothesis may assume a cited result.

Report each result as PROVED, PROVED WITH DIFFERENCES (say what) or
NOT PROVED.
```

[The formalization in detail](docs/formalization.md) lists the Lean names of
the main results, the cited results proved in Lean, and how to build the
library and the website.

The formalization was developed with assistance from GPT-6 Astra and Claude
Opus 5.5, as disclosed in both papers.
