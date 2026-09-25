# Ancillary files

Every numbered theorem, lemma, proposition and corollary of this article and
of the main article has a
[companion Lean formalization](https://github.com/KeShih/coupling-independence-implies-zero-freeness/tree/f588c6293c1a3aa279c161c4c72f7d63540067e7),
some in an equivalent form. Its
[coverage table](https://github.com/KeShih/coupling-independence-implies-zero-freeness/blob/f588c6293c1a3aa279c161c4c72f7d63540067e7/docs/coverage.json)
lists each statement with its Lean declarations, and its
[register of cited results](https://github.com/KeShih/coupling-independence-implies-zero-freeness/blob/f588c6293c1a3aa279c161c4c72f7d63540067e7/docs/external-inputs.md)
states the Lean proofs and scope of the cited ingredients. Some internal
helper bundles take these ingredients as explicit parameters, but the
paper-facing theorems instantiate them with the proved bundles.
The programs below are independent arithmetic checks; the Lean proofs
check the required finite certificates internally and do not trust Python
output. See the companion repository's proof maps for the exact scope.

The verification programs use Python 3 and its standard library.  There
are two distinct verification tasks in the paper.

1. The strict-baseline local inequalities in Section 4 of the main article now have an analytic
   proof.  An independent arithmetic check is provided by the
   canonical standard-library Python checker [`../../verifier.py`](../../verifier.py),
   which is embedded in the PDF.  The independent ancillary checker
   [`python/local_certificate_verifier_final.py`](python/local_certificate_verifier_final.py)
   independently enumerates the same finite state space and checks the same
   inequalities as a cross-check; neither enumeration is an input to the
   analytic proof.
2. The finite low-multiplicity soft Carlson--Vigoda certificate is checked by
   [`python/soft_cv_certificate_verifier.py`](python/soft_cv_certificate_verifier.py),
   following [`CERTIFICATE_SPEC.md`](CERTIFICATE_SPEC.md).  In addition to
   the finite core, it checks subsequent scalar identities, a redundant
   critical-line integer reduction, and clearly labelled regression grids.

Run all three checkers from the project root:

```text
python3 verifier.py
python3 companion/anc/python/local_certificate_verifier_final.py
python3 companion/anc/python/soft_cv_certificate_verifier.py --check
```

The last command checks the frozen JSON certificate without rewriting it.
See [`python/README.md`](python/README.md) for exactness, expected output,
scope, and integrity checks.  File hashes for the specification, the Python
sources, and the frozen certificate are recorded in
[`SHA256SUMS`](SHA256SUMS).
