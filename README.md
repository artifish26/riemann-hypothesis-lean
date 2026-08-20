# Riemann Hypothesis Lean Formalisation

This is a curated Lean/Mathlib release exploring formal routes around the
Riemann Hypothesis.

> **This repository does not prove the Riemann Hypothesis.**

The production surface contains checked multiplicity-aware zero counting,
polynomial-Gaussian zero-side summability, a selected Guinand--Weil formula,
Li/Bombieri--Lagarias equivalences, and fixed-support Burnol positivity.
Release `v0.2.0` additionally publishes the experimental Suzuki S3 milestone:
compact-window coercivity has been connected to the genuine localized source
form and associated operator on one named interval. Global positivity remains
open and RH-equivalent.

## v0.2.0 release scope

The release has two deliberately separate surfaces:

| Surface | Status | Scope |
|---|---|---|
| Production theorem inventory | Checked | The six carried-forward results in [CLAIMS.md](CLAIMS.md); global Li/Weil positivity remains open |
| Suzuki S3 milestone | Experimental, checked and independently closed | Source-compatible coercivity and solution estimates on `I_0 = [log(2)/2, suzukiProjectAStar]`, plus compact-support source-form and associated-operator identification |
| X19B / S4 | Not started / not reached | A normalized fixed-gauge Fredholm family and bounded-window compact-parameter control are still required |
| All-radius nondegeneracy | Open / `RH_HARD` | Not part of S3; equivalent to the unresolved global step |

The exact declarations, assumptions, source files, and limitations are in
[CLAIMS.md](CLAIMS.md). The focused S3 ledger is
[RELEASE/SUZUKI_S3.md](RELEASE/SUZUKI_S3.md). Repeatable axiom reports are
defined in `RELEASE/PublicationAxiomAudit.lean` and
`RELEASE/SuzukiS3AxiomAudit.lean`.

The independent reports under `ADVERSARIAL/` trace both the production claims
and the S3 boundary. In particular, compact-window coercivity is not described
as global Weil positivity, and a bound for an admitted Fredholm solution is
not described as an existence theorem for the normalized X19B family.

The source tree is a release snapshot. Private development history and
unpublished working documents are not included.

## AI provenance

This project arose from a casual experiment asking how far AI could
independently develop a substantial Lean formalisation. The implementation,
proof development, refactoring, and documentation were produced by AI. The
maintainer is a software engineer, not a mathematician, and did not author the
mathematics or Lean proofs.

AI output is not mathematical evidence. The reviewable evidence is the checked
Lean source, explicit premises, dependency pins, exact certificate data,
successful builds, and repeatable axiom reports. See [AI_USE.md](AI_USE.md).

## Build

Install [Elan](https://github.com/leanprover/elan) and Git, then run:

```text
lake exe cache get
lake build
lake env lean RELEASE/PublicationAxiomAudit.lean
lake env lean RELEASE/SuzukiS3AxiomAudit.lean
lake env lean ADVERSARIAL/S3EndpointAudit.lean
```

The first command requires network access. Do not run `lake update` when
reproducing the release: dependency revisions are pinned in
`lake-manifest.json`. More detail is in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Layout

- `RiemannHypothesisProject/` contains the release source.
- `RiemannHypothesisProject/Basic.lean` is the aggregate production import and
  does not import `RiemannHypothesisProject/Experiments/`.
- `RiemannHypothesisProject/Experiments/M100/` contains the checked S3 source
  and its exact certificate data.
- `tools/experiments/m100/` contains the associated certificate generators and
  research probes; their output is not a release claim by itself.
- `RELEASE/` contains the claim ledger and repeatable axiom audits.
- `ADVERSARIAL/` contains independent claim audits and Lean consumers.
- `.github/workflows/release-build.yml` performs a clean tagged build.

## Attribution

The release is maintained under the pseudonym **ArtiFish26**. Citation metadata
is provided in [CITATION.cff](CITATION.cff). The source is licensed under the
Apache License 2.0; see [LICENSE](LICENSE).
