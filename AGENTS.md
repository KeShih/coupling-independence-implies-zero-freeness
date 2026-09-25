# AGENTS.md

Guidance for coding agents working in this repository: a Lean 4 + mathlib
formalization of *Coupling Independence Implies Zero-Freeness* and its
companion, *Further Potts Zero-Free Regions from Coupling Independence*, with
their LaTeX sources, documentation and a generated website under `docs/`.

## Commands

Lean 4.33.1 and mathlib v4.33.1 are pinned (`lean-toolchain`,
`lake-manifest.json`). Use elan, and fetch prebuilt mathlib; never build
mathlib from source. There is no CI: every check below runs locally.

```bash
lake exe cache get                               # prebuilt mathlib oleans
LEAN_NUM_THREADS=2 bash scripts/check-all.sh     # build ZeroFreeness, then audit/All.lean
bash scripts/check.sh                            # main paper: Potts.Main, LeeYang, Holant + audit/Main.lean
bash scripts/check-appendix.sh                   # companion: Potts.Regions + audit/Appendix.lean
bash scripts/lake.sh build ZeroFreeness.Potts.Theorems.PottsMainTheorem  # one module and its imports
bash scripts/lake.sh env lean -DwarningAsError=true ZeroFreeness/Path/File.lean  # re-check one file
```

- Run lake through `scripts/lake.sh`. It runs from the repository root,
  sets `MATHLIB_CACHE_DIR=.cache/mathlib`, and uses the author's local
  toolchain in `.tools/` when that directory exists.
- `lake env lean` builds nothing and ignores the lakefile's
  `moreLeanArgs`. Build the file's imports first, and pass
  `-DwarningAsError=true` yourself.
- Call the scripts with `bash`: `check-appendix.sh` is not executable.
- A passing full check ends with `Build completed successfully (N jobs).`
  and `Complete-library axiom audit passed: M declarations; allowed
  dependencies used: [propext, Classical.choice, Quot.sound]`. The current
  N and M are in `docs/verification.json` (`build_jobs`,
  `audited_project_declarations`).
- `audit/CV.lean` is a standalone audit of `ZeroFreeness.Appendix.CV` that no
  script runs.

Website builds (see *Website* below):

```bash
pip install pymupdf && python3 scripts/site/build_reader.py   # docs/index.html, no Lean build needed
python3 scripts/site/build_reader.py --out /tmp/preview.html  # every check, page written elsewhere
```

## Rules the build and audits enforce

- **Warnings are errors** (`lakefile.toml`). Prefix unused hypotheses with
  `_`. Many files set `set_option linter.unusedSectionVars false`.
- **Axioms:** only `propext`, `Classical.choice` and `Quot.sound` are
  allowed. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` or
  `implemented_by`. The audits check transitive axioms, and a source scan
  recorded in `docs/verification.json` lists the forbidden constructs.
- **Namespaces:** the audits inspect only names starting with `ZeroFreeness` or
  `PottsCI`. A declaration outside those namespaces escapes the audit.
- **New modules:** a new module must be imported, directly or
  transitively, from an aggregate. The aggregates are
  `ZeroFreeness/Potts/Main.lean` (main-text Potts),
  `ZeroFreeness/Potts/Regions.lean` or `ZeroFreeness/Potts/Regions/CV.lean`
  (companion), `ZeroFreeness/LeeYang.lean` and `ZeroFreeness/Holant.lean`.
  An unimported file is neither built nor audited. Do not add import-only
  wrapper modules; ten were removed on purpose.
- **Literature hypotheses:** paper-facing theorems take none. Cited
  results are Prop-valued bundles (`Appendix.CLMM.Literature`,
  `Appendix.BBR.Literature`, `Appendix.Girth.CavityTree.CLMMInfluenceIdentity`,
  `Potts.ExternalCriticalHardColouringTheorem`), each proved in the library
  (`CLMM.literature`, `BBR.literature`, `clmmInfluenceIdentity`,
  `external_critical_hard_colouring_theorem`). Pass the proof, or use an
  `_unconditional` variant. Only the `_from_external` comparison theorems
  keep the cited premise.
- **Quantifier order is part of the claims.** Radii and constants come
  before the vertex type, graph, pinning and class (`∃ eps > 0, ∀ …`).
  Paper-form wrappers get the paper's order through `unionClass` and
  `ciUnionClass`, not by adding hypotheses.
- **Classical preamble:** match the preamble of neighbouring files
  (`attribute [local instance] Classical.propDecidable`, local
  `DecidableEq` instances). Otherwise statements about existing definitions
  elaborate with different instances.
- **Mathlib imports:** check that a mathlib module is available as a
  prebuilt olean before importing it. `Coupling/Girth/Spectral/OperatorGap.lean`
  writes out positive semidefiniteness itself for that reason.

## Architecture

- **One library, `ZeroFreeness`.** `ZeroFreeness.lean` imports
  `ZeroFreeness.Potts` (`Potts.Main` and `Potts.Regions`),
  `ZeroFreeness.LeeYang` and `ZeroFreeness.Holant`. The main-paper
  build also compiles companion code: the `q = 11Δ/6` case of Theorem 1.1
  uses `ZeroFreeness.Appendix.CV.option_root_ci_critical`, and Lee–Yang imports
  the regime endpoints.
- **Namespaces do not follow directories.** Files were moved on 2026-09-09
  and the namespaces were kept (`docs/module-moves.tsv` maps old paths to
  new):
  - Companion code in `Coupling/{CV,Girth,Edge,BBR,CLMM}` and
    `Potts/Regions` is `ZeroFreeness.Appendix.*`.
  - The legacy foundations are `PottsCI.*`: `FinDist` and `FinDist.W`,
    `ham`, `PinningData`, `PartialColouring`.
  - `Coupling/Vigoda` mixes `ZeroFreeness`, `ZeroFreeness.Potts` and
    `PottsCI.Vigoda`.

  On 2026-09-25 the library, its folder, its root namespace and the paper
  folders were renamed from `CI2ZF` to `ZeroFreeness` (`paper/main`,
  `paper/companion`). Older commits, `docs/provenance/` and
  `docs/verification.json` keep the old name.

  Find declarations with grep, not by path, since file names repeat
  (`RootCI.lean`, `ZeroFree.lean`). Do not rename namespaces to match
  directories: full names are hard-coded in `docs/coverage.json`,
  `scripts/site/common.py`, `scripts/site/build_reader.py` and the docs.
- **Two instance representations.** Paper-facing statements use
  `G : SimpleGraph V` with `tau : PartialColouring V C`, and the pinning may
  be improper. The machinery works on `PinningData V C` (free graph plus
  boundary counts), reached through `tau.toPinningData G`. Root-conditioned
  instances are `PinningData (Option O) C`, with `none` as the root and
  children `optionChildData I a`.
- **Potts pipeline:**
  1. A regime proves coupling independence (`Coupling/*`).
  2. It packages that as `TransferCouplingInputs`: a hard constant at
     `x = 0` and a constant on every `[δ,1]`.
  3. `bounded_degree_potts_transfer` (separator-shell transfer,
     `Potts/Transfer`, `Potts/Geometry`) turns the inputs into
     `∃ eps > 0, UniformPottsZeroFree C Δ eps`.

  Variants:
  - The graph-class form is `GraphClassTransferInputs` →
    `graph_class_potts_transfer_of_bounded` (`thm:potts-transfer`).
  - High temperature, BBR and girth five use positive-interval transfers.
  - `PinningFamily.*` repeats the transfer lemmas under the same short
    names for restriction-closed families.
- **Lee–Yang** runs `uniform_curve_transfer` → `uniform_field_transfer_closed`
  → `all_vertex_field_transfer`. **Holant** has its own pipeline in
  `ZeroFreeness/Holant` (`CouplingTheorem` → `UniformResponse` → `StrongInduction` →
  `Theorem` → polytube corollaries), namespaces `ZeroFreeness.Holant` and
  `ZeroFreeness.HolantCoupling`.
- **Headline statements.** Theorem 1.1 is `ZeroFreeness.Potts.potts_main_theorem`
  in `Potts/Theorems/PottsExternalTheorem.lean`. `potts_zero_free` in
  `PottsMainTheorem.lean` still takes a `CriticalHardColouringInput`. The
  companion's regimes live in `Potts/Regions/*`. `docs/formalization.md`
  maps the other results to Lean names.
- **Naming conventions:**
  - `_unconditional`: the literature bundle is discharged.
  - `_from_external`: the paper's cited route, kept for comparison.
  - `_of_bounded`: the class-wide degree premise.
  - `_original_`: the original graph with `PartialColouring` semantics.
  - `_residual_original_`: girth is required only of the free graph.

  Paper-form wrappers take colours `Fin q` and keep hypotheses the proof
  does not need as `_`-named arguments.
- **Docstrings** cite LaTeX labels in backticks (`` `lem:soft-stationary` ``),
  often with a bold lead: ``**`lem:x`, the paper's statement.**``. Cite
  labels, not numbers, because theorem numbers drift between paper
  versions. "Actual" marks concrete objects, such as actual Gibbs laws, as
  opposed to hypotheses.

## Coverage, docs and the verification record

- **`docs/coverage.json`** lists every numbered statement of both papers,
  107 in all, in source order. Each entry has `paper`, `kind`, `number`,
  `label`, `status`, `lean`, `defs`, `note` and `title`:
  - `paper` is `main` or `companion`; the companion is `appendix` in paths
    and in the `ZeroFreeness.Appendix` namespace.
  - `label` is `null` for the two unlabelled companion remarks.
  - `status` is one of the keys of `STATUSES` in `scripts/site/common.py`.
  - `lean` lists the declarations that state the result, usually one: the
    form closest to the paper, not its variants or proof ingredients.
  - `defs` lists the project definitions a reader needs to read them. Each
    needs a gloss, in `DEFINITIONS` in `scripts/site/build_reader.py` or in
    `GLOSSARY` in `scripts/site/common.py`.
  - `note` is the only prose the reader shows: how the Lean statement
    differs from the paper's, in plain words, with every caveat. It is
    empty when nothing differs.

  Both site builds stop if an entry disagrees with the LaTeX (order, kind,
  number, label) or names a missing Lean declaration. Renaming a listed
  declaration means updating `coverage.json` and the tables in the docs.
- **Scope changes propagate.** When a statement's status or scope
  changes, update:
  - its coverage note;
  - the counts and the unformalized list in `docs/formalization.md`;
  - `docs/README.md`, `docs/overview.md`, `docs/appendix/README.md`,
    `docs/appendix/STATUS.md` and `docs/external-inputs.md`;
  - any docstring that states the scope.
- **`docs/verification.json`** is a hand-maintained record of the last full
  run; no script here regenerates it. It stores plain SHA-256 hashes: every
  module, the audit files and check scripts, the ten tracked Markdown files,
  `coverage.json` with its counts, and the companion PDF. Any Lean or doc change makes it stale. The history
  refreshes it in a separate "refresh docs and record" commit after a full
  check. `closure_manifest_sha256` and `verification_log_sha256` come from
  tooling that is not in the repository. It is already stale for
  `README.md` and `docs/appendix.pdf`, so do not assume a mismatch you find
  is yours.
- **Pinned history.** The papers cite this repository at pinned commits
  (`paper/main/main.bib`, `paper/companion/anc/README.md`), so
  never rewrite the history of `main`.

## Website

GitHub Pages serves `docs/` from `main` as committed. Keep `docs/.nojekyll`.

- **`docs/index.html` (the reader)** is generated by
  `scripts/site/build_reader.py` from `paper/*/` (LaTeX with its `.bbl`),
  `docs/main.pdf` and `docs/appendix.pdf`, `docs/coverage.json`,
  `docs/verification.json` and the Lean sources. Its modules:
  - `paper_html.py` renders the LaTeX and numbers statements, equations
    and sections as LaTeX does. It checks them against `coverage.json` and
    against the PDFs' hyperref destinations (`lemma.3.6`, `equation.12`).
  - `tikz_html.py` draws TikZ figures and tikz-cd diagrams. When it cannot
    read one, it warns and cuts a PNG into `docs/figures/`; commit that PNG.
  - `richtext.py` typesets the formulas in notes and glosses.
  - `reader.html` is the template and holds all the CSS and JS.

  The Lean panel shows a statement's `lean` declarations as code, without
  docstrings, and its `defs` as rows with the paper's symbol and a gloss.

  Lean declarations are located by a regex scan, so they must start in
  column 0 inside `namespace`/`section` blocks.
- **`scripts/site/common.py`** holds the data and helpers the builders
  share: `STATUSES`, `CITED` (the cited results and the Lean theorems that
  prove them), `GLOSSARY`, `ENV_WORDS` and a few LaTeX helpers. The older
  statement checker (`docs/checker.html`, built by `build.py`) was removed
  on 2026-09-25; the reader replaces it.
- **Do not hand-edit the generated page.** Change the generator and
  rebuild.
- **Commit Lean first.** The builder refuses to run while `ZeroFreeness/` or
  `ZeroFreeness.lean` has uncommitted changes. They pin GitHub source links to
  the last commit that touched the Lean sources, and that commit must be
  pushed. Commit Lean changes first, then rebuild the pages in a follow-up
  commit.
- **New paper version:** replace `paper/main` or
  `paper/companion` (`.tex`, `.bib`, a fresh `.bbl`, `appendices/`)
  together with `docs/main.pdf` or `docs/appendix.pdf`. Update
  `coverage.json` if the numbering changed, then rerun `build_reader.py`.
  The PDF check needs every theorem-like environment to get a hyperref
  destination named `<env>.<number>`, which the papers' `aliascnt` setup
  provides.

## Workflow

Work on a branch and merge into `main` through a pull request. The history
uses merge commits titled `<subject> (#N)`. Fetch `origin/main` before
starting, because a local `main` may be stale. Commit messages have an
imperative subject and a body that explains what changed and why.
