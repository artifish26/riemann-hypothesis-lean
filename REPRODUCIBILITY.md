# Reproducibility

## Pinned environment

- Lean: `leanprover/lean4:v4.31.0`
- Mathlib revision: `db127794c79fdeb86f6b0cf6ff2c804026fbaff1`
- PrimeNumberTheoremAnd revision:
  `6739793850d3eaa031e3543ed72d7f026f8080f5`
- Lake dependency resolution: `lake-manifest.json`

## Prerequisites

Install Git and [Elan](https://github.com/leanprover/elan). Ensure `lake` is on
`PATH`. Network access is needed on the first run to obtain pinned dependencies
and Mathlib cache artifacts.

## Full reproduction

```text
git clone https://github.com/artifish26/riemann-hypothesis-lean.git
cd riemann-hypothesis-lean
git checkout v0.1.1
lake exe cache get
lake build
lake env lean RELEASE/PublicationAxiomAudit.lean
lake env lean ADVERSARIAL/EndpointAudit.lean
lake env lean ADVERSARIAL/A4BurnolFormulaBridgeAudit.lean
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

## Axiom report

Run the release audit without adding it to the production import graph:

```text
lake env lean RELEASE/PublicationAxiomAudit.lean
```

For the listed release endpoints, the expected imported axioms are the standard
Mathlib foundations `propext`, `Classical.choice`, and `Quot.sound`. Any
`sorryAx`, project-defined axiom, or additional unadvertised assumption is a
release blocker.

## Source checks

The following source check should return no matches:

```text
rg -n "\b(sorry|admit)\b|^\s*axiom\s" RiemannHypothesisProject -g "*.lean"
```

GitHub Actions performs an independent clean Ubuntu build for pull requests to
`main`, manual workflow runs, and `v*` tags.
