# Exact-rational certificate checkers

These Python files check the local inequalities proved analytically in the
main text and the finite/scalar certificate used in the appendix. They use
only the Python standard library, in particular
`fractions.Fraction`; all verification decisions are exact. Floating point is
used only for nonauthoritative decimal display fields in the JSON, and no
third-party package is used.

Certificate conditions are checked with explicit exceptions rather than
Python `assert` statements, so running either checker with `python3 -O` does
not disable any verification step.

## Checks

### Strict-baseline finite-case verification

The canonical independent arithmetic checker for Section 4 of the main article is the
repository-root `verifier.py`, which is embedded in the PDF.  This ancillary
script independently enumerates the same finite state space and checks the
same inequalities as a cross-check.  The main-text proof now establishes
these inequalities analytically and does not depend on enumeration.

```text
python3 local_certificate_verifier_final.py
```

Expected final line:

```text
all exact checks passed
```

The script verifies the elementary inequalities, the small regular-colour
bounds, and the one-neighbour root-colour cases in Section 4 of the main article. The
graph-theoretic component coupling is proved there and is not
delegated to this checker.

### Soft Carlson--Vigoda certificate

This is the finite certificate used in the soft Carlson--Vigoda appendix.
Its finite low-multiplicity portion follows the exact specification in
[`../CERTIFICATE_SPEC.md`](../CERTIFICATE_SPEC.md).

To regenerate the frozen JSON certificate beside the script:

```text
python3 soft_cv_certificate_verifier.py
```

To check the committed certificate without rewriting it:

```text
python3 soft_cv_certificate_verifier.py --check
```

The script exhausts the 400 one-neighbour and 193600 two-neighbour
structural states.  The source and frozen JSON retain the legacy field name
`port` only as an encoding label; mathematically these are the ordered active
root neighbours of that appendix.  The verifier
takes the worst value over every allowed maximum-component tie choice, checks the
arrangement vertices with exact rational arithmetic, and verifies the
subsequent scalar inequalities quoted in the soft Carlson--Vigoda appendix.
It also records a redundant exact check of the small integer reduction used
in the additional Potts appendix; that reduction is proved directly there.
The finite enumerations and arrangement-vertex checks are certificate steps.
The dense rational grids reported for ordered incidence, high multiplicity,
and boundary bookkeeping are regression checks against transcription errors;
they are not used to prove an inequality on a continuum.  The corresponding
uniform inequalities follow from the symbolic or analytic arguments recorded
in that appendix.
The graph-theoretic transition lemmas and the coupling-independence arguments
are proved in the appendices, not by this script.
The scalar checks and dense grids supplement the finite low-multiplicity
certificate.

## Files and integrity

The local [`SHA256SUMS`](SHA256SUMS) covers the two checkers and the frozen
JSON in this directory.  The top-level [`../SHA256SUMS`](../SHA256SUMS)
also covers the certificate specification and the repository-root checker.
Run this Python snippet from the repository root to check both manifests:

```python
from hashlib import sha256
from pathlib import Path

for manifest, base in (
    (Path("anc/SHA256SUMS"), Path(".")),
    (Path("anc/python/SHA256SUMS"), Path("anc/python")),
):
    for line in manifest.read_text().splitlines():
        expected, filename = line.split(maxsplit=1)
        actual = sha256((base / filename).read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"Hash mismatch: {base / filename}")
    print(f"{manifest}: all hashes match")
```

Regenerate each affected manifest whenever a covered file changes.
