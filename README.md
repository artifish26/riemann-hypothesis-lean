# Riemann Hypothesis Lean Formalisation

This is a curated Lean/Mathlib release exploring formal routes around the
Riemann Hypothesis.

> **This repository does not prove the Riemann Hypothesis.**

It contains checked results about multiplicity-aware zero counting,
polynomial-Gaussian zero-side summability, a selected Guinand-Weil formula,
Li/Bombieri-Lagarias equivalences, and fixed-support Burnol positivity. The
global positivity statement needed to conclude the Riemann Hypothesis remains
open and is itself RH-equivalent.

## Release scope

The principal release endpoints are documented in [CLAIMS.md](CLAIMS.md), with
their exact Lean declaration names, assumptions, source files, and limits. The
representative endpoint axiom report is defined in
`RELEASE/PublicationAxiomAudit.lean`.

The independent red-team reports under `ADVERSARIAL/` trace the release claims,
their assumptions, and their dependency boundaries. Their final verdict leaves
global Li/Weil positivity open and RH-equivalent.

The source tree is a release snapshot. Private development history and
unpublished working material are not included.

## AI provenance

This project arose from a casual experiment asking how far AI could
independently develop a substantial Lean formalisation. The implementation,
proof development, refactoring, and documentation were produced by AI. The
maintainer is a software engineer, not a mathematician, and did not author the
mathematics or Lean proofs.

AI output is not treated as mathematical evidence. The reviewable evidence is
the checked Lean source, its explicit premises, the dependency pins, successful
builds, and the repeatable axiom report. See [AI_USE.md](AI_USE.md).

## Build

Install [Elan](https://github.com/leanprover/elan) and Git, then run:

```text
lake exe cache get
lake build
lake env lean RELEASE/PublicationAxiomAudit.lean
```

The first command requires network access. Do not run `lake update` when
reproducing the release: dependency revisions are pinned in
`lake-manifest.json`.

More detail and focused build commands are in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Layout

- `RiemannHypothesisProject/` contains the release source.
- `RiemannHypothesisProject/Basic.lean` is the aggregate production import.
- `RELEASE/PublicationAxiomAudit.lean` checks representative endpoint axioms.
- `ADVERSARIAL/` contains independent claim audits and Lean audit consumers.
- `.github/workflows/release-build.yml` performs a clean GitHub Actions build.

## Attribution

The release is maintained under the pseudonym **ArtiFish26**. Citation metadata
is provided in [CITATION.cff](CITATION.cff). The source is licensed under the
Apache License 2.0; see [LICENSE](LICENSE).
