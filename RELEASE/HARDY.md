# Hardy Critical-Line Zero Infinitude

Status: `PRODUCTION / CHECKED`

Release: `v0.3.0`

## Result

The production endpoint
`RiemannHypothesisProject.Hardy.nontrivial_criticalLine_zetaZero_set_infinite`
proves unconditionally that

```text
{s : Complex | IsNontrivialZetaZero s and IsCriticalLine s}.Infinite.
```

It is implemented in
`RiemannHypothesisProject/Hardy/CriticalLineZeroInfinitude.lean` and exported
through `RiemannHypothesisProject/Basic.lean`.

The formal chain contains the selected Hardy programme:

```text
zeta first approximation
  -> critical-line Stirling phase
  -> oscillatory integral estimates
  -> Hardy-function normalization
  -> lower absolute-integral bound
  -> upper signed-integral bound
  -> infinitely many critical-line zeros
```

The terminal contradiction assumes finitely many positive Hardy zero heights,
deduces constant sign on every sufficiently late dyadic interval, identifies
the signed and absolute integrals there, and contradicts the checked lower and
upper bounds at an explicit sufficiently large height.

## Scope

This theorem proves that infinitely many actual nontrivial zeta zeros lie on
the critical line. It does **not** prove that every nontrivial zero lies there,
give a positive proportion, or prove RH.

The endpoint has no analytic source hypothesis, numerical certificate,
experimental import, or project-defined axiom. Its release axiom report is
part of `RELEASE/PublicationAxiomAudit.lean`.

## Development verification

The independent H4D closeout ran a warning-as-error focused check, a direct
type and axiom audit, forbidden-import and placeholder scans, and a full
`lake build`. The full build completed `3964` jobs on August 24, 2026.
