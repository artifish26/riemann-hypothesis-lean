# Riemann Hypothesis Lean Formalisation

This is a curated Lean/Mathlib release exploring formal routes around the
Riemann Hypothesis.

> **This repository does not prove the Riemann Hypothesis.**

The checked production surface contains multiplicity-aware zero counting,
polynomial-Gaussian zero-side summability, a selected Guinand--Weil formula,
Li/Bombieri--Lagarias equivalences, fixed-support Burnol positivity, and a
formal Hardy theorem proving infinitely many nontrivial zeta zeros on the
critical line. Global criterion-determining Li/Weil positivity remains open
and RH-equivalent.

## Version history

| Version | Headline | Released | Main milestone |
|---|---|---|---|
| **v0.3.0** | **Suzuki S4, Hardy infinitude, and first-crossing geometry** | 2026-08-25 | Publishes the checked compact-window S4 solution family, the production theorem that infinitely many nontrivial zeta zeros lie on the critical line, and the clearly non-Lean RIG0--RIG1 paper audit |
| **v0.2.0** | **Suzuki S3 reaches the genuine source form** | 2026-08-20 | Publishes compact-window source coercivity, source-norm solution estimates, closed-form/core completion, and associated-operator identification |
| **v0.1.1** | **Audited production claims** | 2026-07-19 | Binds the production theorem inventory to an immutable release identity and strengthens axiom and external-review documentation |
| **v0.1.0** | **Production foundations** | 2026-07-19 | First curated release of the four production streams, pinned environment, reproducibility guide, and clean-build workflow |

## v0.3.0 release scope

The release keeps checked Lean results and paper-level research conclusions
deliberately separate:

| Surface | Status | Scope |
|---|---|---|
| Production theorem inventory | Checked Lean | The carried-forward production endpoints plus Hardy's theorem that the actual nontrivial critical-line zeta-zero set is infinite |
| Suzuki S4 | Experimental, checked Lean, independently audited | On the named compact radius window and closed complex unit disk: canonical solutions, uniform norm bound `4000`, Lipschitz spectral dependence, compact image, and directed radius continuity from below |
| RIG0--RIG1 | Audited paper result, not Lean | No fixed-zero-to-crossing transport; a quantitative annular escape estimate for every vector in a hypothetical complete first-crossing kernel |
| RIG2 / global Suzuki continuation | Not admitted / frozen | The annular complement is uncontrolled and generally infinite-dimensional; no scalar or finite-dimensional reduction was found |
| Global Li/Weil positivity | Open / `RH_HARD` | The criterion-determining global class remains unresolved and equivalent to RH |

The exact declarations, assumptions, and limitations are in
[CLAIMS.md](CLAIMS.md). Focused ledgers are:

- [RELEASE/HARDY.md](RELEASE/HARDY.md);
- [RELEASE/SUZUKI_S4.md](RELEASE/SUZUKI_S4.md); and
- [RELEASE/RIGIDITY_RIG1.md](RELEASE/RIGIDITY_RIG1.md).

The independent report
[ADVERSARIAL/S4_SUZUKI_PUBLICATION_AUDIT_2026-08-21.md](ADVERSARIAL/S4_SUZUKI_PUBLICATION_AUDIT_2026-08-21.md)
checks the S4 boundary. Repeatable Lean audits are in
`RELEASE/PublicationAxiomAudit.lean`, `RELEASE/SuzukiS4AxiomAudit.lean`, and
`ADVERSARIAL/S4EndpointAudit.lean`.

The source tree is a release snapshot. Private development history and
unpublished working documents are not included.

## What changed after v0.2.0

### Production Hardy theorem

`RiemannHypothesisProject.Hardy.nontrivial_criticalLine_zetaZero_set_infinite`
proves unconditionally that the set

```text
{s : Complex | IsNontrivialZetaZero s and IsCriticalLine s}
```

is infinite. This is the classical Hardy-type partial result; it does not say
that every nontrivial zero is on the critical line.

### Suzuki S4

S4 closes X19B on the genuine source surface. Its source-package-free wrapper
exports the compact-window solution family and parameter-control theorems
without hiding the radius or closed-unit-disk restrictions. The programme was
then published and frozen because no justified all-radius propagation
mechanism emerged.

### Rigidity-first audit

RIG0 showed that a prescribed off-line zero does not canonically retain its
identity through the existential passage to a first Suzuki crossing. RIG1
nevertheless derived the quantitative conditional estimate

```text
||(I-Pi_b)u||_sigma^2
  >= lambda(b)/(lambda(b)-sigma) * ||u||_sigma^2
```

for the whole completed first-crossing kernel. This is a documentation-only
paper theorem in this release. It neither excludes a crossing nor proves RH,
and RIG2 was not admitted.

## AI provenance

This project arose from a casual experiment asking how far AI could
independently develop a substantial Lean formalisation. The implementation,
proof development, refactoring, and documentation were produced by AI. The
maintainer is a software engineer, not a mathematician, and did not author the
mathematics or Lean proofs.

AI output is not mathematical evidence. The reviewable evidence is the
checked Lean source, explicit premises, dependency pins, exact certificate
data, successful builds, and repeatable axiom reports. See
[AI_USE.md](AI_USE.md).

## Build

Install [Elan](https://github.com/leanprover/elan) and Git, then run:

```text
lake exe cache get
lake build
lake env lean RELEASE/PublicationAxiomAudit.lean
lake env lean RELEASE/SuzukiS4AxiomAudit.lean
lake env lean ADVERSARIAL/S4EndpointAudit.lean
```

The first command requires network access. Do not run `lake update` when
reproducing the release: dependency revisions are pinned in
`lake-manifest.json`. More detail is in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md).

## Layout

- `RiemannHypothesisProject/` contains the release source.
- `RiemannHypothesisProject/Basic.lean` is the aggregate production import and
  does not import `RiemannHypothesisProject/Experiments/`.
- `RiemannHypothesisProject/Hardy/` contains the checked critical-line-zero
  infinitude chain.
- `RiemannHypothesisProject/Experiments/M100/` contains the checked Suzuki
  S1--S4 source and exact certificate data.
- `tools/experiments/m100/` contains certificate generators and research
  probes; their output is not a theorem until consumed by checked Lean.
- `RELEASE/` contains claim ledgers and repeatable axiom audits.
- `ADVERSARIAL/` contains independent scope reports and Lean consumers.
- `.github/workflows/release-build.yml` performs an independent clean build.

## Attribution

The release is maintained under the pseudonym **ArtiFish26**. Citation metadata
is provided in [CITATION.cff](CITATION.cff). The source is licensed under the
Apache License 2.0; see [LICENSE](LICENSE).
