<div align="center">

# Coupling Independence Implies Zero-Freeness

**Both papers, formalized in Lean 4**

### [Read the papers with their Lean →](https://keshih.github.io/coupling-independence-implies-zero-freeness/)

[Main paper (PDF)](docs/main.pdf) · [Companion (PDF)](docs/appendix.pdf)

</div>

[![The reader: Theorem 1.1 of the main paper, with the Lean declarations that state it beside it](https://github.com/user-attachments/assets/7fa6a483-fe0d-4fed-b555-f7d6861f99a4)](https://keshih.github.io/coupling-independence-implies-zero-freeness/)

Lean 4 formalization of two papers by Shuai Shao and Ke Shi,
*Coupling Independence Implies Zero-Freeness* and its companion,
*Further Potts Zero-Free Regions from Coupling Independence*. Every numbered
theorem, lemma, proposition and corollary has a Lean statement, proved from
mathlib and Lean's standard axioms alone.

## Check it yourself

Paste this into your coding agent:

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

> [!WARNING]
> For a full check of all 107 numbered statements, replace "zero-freeness
> result" with "numbered statement". It costs a great many tokens.

[An example report](Verification/2026-09-25/REPORT.md) from this prompt, run in
Claude Code with Claude Opus 5.5 at xhigh effort in about 30 minutes, found no
build, trust-base or statement problem.

With prebuilt mathlib the build takes about 17 minutes on an Apple M4, and
a successful `bash scripts/check-all.sh` ends with:

```text
Build completed successfully (4069 jobs).
Complete-library axiom audit passed: 11320 declarations; allowed dependencies used: [propext,
 Classical.choice,
 Quot.sound]
```

More in [the formalization in detail](docs/formalization.md). Developed with
assistance from GPT-6 Astra and Claude Opus 5.5, as disclosed in both papers.
