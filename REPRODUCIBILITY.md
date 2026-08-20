# Reproducibility

## Pinned environment

- Lean: `leanprover/lean4:v4.32.2`
- Mathlib revision: `905b95818eb32af7874a58b427f50c1711a5e96c`
- PrimeNumberTheoremAnd revision:
  `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`
- Lake dependency resolution: `lake-manifest.json`

## Prerequisites

Install Git and [Elan](https://github.com/leanprover/elan). Ensure `lake` is on
`PATH`. Network access is needed on the first run to obtain pinned dependencies
and Mathlib cache artifacts.

## Full reproduction

```text
git clone https://github.com/artifish26/riemann-hypothesis-lean.git
cd riemann-hypothesis-lean
git checkout v0.2.0
lake exe cache get
lake build
lake env lean RELEASE/PublicationAxiomAudit.lean
lake env lean RELEASE/SuzukiS3AxiomAudit.lean
lake env lean ADVERSARIAL/EndpointAudit.lean
lake env lean ADVERSARIAL/A4BurnolFormulaBridgeAudit.lean
lake env lean ADVERSARIAL/S3EndpointAudit.lean
```

Before the tag exists, omit the `git checkout` command. Do not run
`lake update`: the checked-in manifest pins the release dependency graph.

## Focused claim builds

```text
lake build RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiJensen
lake build RiemannHypothesisProject.GuinandWeilConcrete.MultiplicityPolynomialGaussianFormulaHandoff
lake build RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFormulaIdentity
lake build RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianDensityBridge
lake build RiemannHypothesisProject.LiCriterion.ZetaBombieriLagariasCriterion
lake build RiemannHypothesisProject.WeilPositivity.BurnolFormulaClosure
```

## Focused Suzuki S3 builds

The final source-identification and source-norm surface can be rebuilt with:

```text
lake build RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaDifferentialCoreDensity
lake build RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaFredholmUniformBound
lake build RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaClosedFormCompletion
lake build RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaIdentification
```

The exact finite certificate modules are transitive dependencies of these
targets. `tools/experiments/m100/` contains the associated generators and
research probes; their numerical output is not a theorem until consumed by the
checked Lean source.

## Axiom report

Run the release audit without adding it to the production import graph:

```text
lake env lean RELEASE/PublicationAxiomAudit.lean
```

For the listed release endpoints, the expected imported axioms are the standard
Mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`. Any
`sorryAx`, project-defined axiom, or additional unadvertised assumption is a
release blocker.

Run the experimental S3 audit separately:

```text
lake env lean RELEASE/SuzukiS3AxiomAudit.lean
```

Its output must agree with the trust boundary in `RELEASE/SUZUKI_S3.md`. In
particular, the finite certificate chain is permitted to expose only the
declared compiler-backed `native_decide` boundary in addition to standard
logical foundations. Any `sorryAx` or unlisted project axiom is a release
blocker.

## Source checks

The following source check should return no matches:

```text
rg -n "\b(sorry|admit)\b|^\s*axiom\s" RiemannHypothesisProject -g "*.lean"
```

GitHub Actions performs an independent clean Ubuntu build for pull requests to
`main`, manual workflow runs, and `v*` tags. It runs the production and S3 axiom
audits and all listed adversarial Lean consumers after the full build.
