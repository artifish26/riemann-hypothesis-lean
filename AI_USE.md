# AI Use

## Nature of the project

This release comes from a casual experiment investigating how far AI could
independently develop a substantial Lean formalisation. It is not a funded or
institutional research programme.

OpenAI Codex performed the implementation work, including route exploration,
Lean proof development, theorem-shape and dependency analysis, refactoring,
build diagnosis, and documentation. The maintainer, ArtiFish26, is a software
engineer rather than a mathematician and did not author the mathematics or
Lean proofs.

## Evidentiary boundary

AI-generated prose and reasoning are not mathematical evidence. The artifacts
that can be independently checked are:

- Lean declarations accepted by the kernel;
- the explicit premises and imported dependencies of those declarations;
- the pinned dependency revisions;
- successful clean builds; and
- the repeatable `#print axioms` report in
  `RELEASE/PublicationAxiomAudit.lean`.

The release claims are deliberately narrower than the overall mathematical
goal. In particular, the repository does not prove the Riemann Hypothesis.
Global Li/Weil positivity remains open and RH-equivalent.

## Responsibility and reproducibility

ArtiFish26 maintains the release and is responsible for publication decisions
and presentation. Exact model conversations and stochastic outputs are not
claimed to be reproducible. The formal artifacts can be checked independently
by following [REPRODUCIBILITY.md](REPRODUCIBILITY.md).
