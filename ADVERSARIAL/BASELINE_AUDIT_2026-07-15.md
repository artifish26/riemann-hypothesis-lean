# Baseline Adversarial Audit - 2026-07-15

Status: `INITIAL BASELINE COMPLETE; SEMANTIC CLAIM AUDITS OPEN`

This report establishes the first independent checkpoint for the adversarial
track. It does not certify the current percentages. It records what has been
mechanically verified, what has been inspected at signature level, and what
must now be challenged theorem by theorem.

## Scope

The audit inspected the production Lean modules under
`RiemannHypothesisProject/` and the representative endpoint consumers included
in this directory.

## Mechanical Results

| ID | Check | Result | Meaning |
|---|---|---|---|
| `ADV-MECH-001` | Full `lake build` | `PASS`, 3833 jobs | The current checked dependency graph compiles |
| `ADV-MECH-002` | `sorry` / `axiom` / `admit` token scan in production `.lean` files | `PASS`, no matches | No obvious local proof hole or project axiom was found |
| `ADV-MECH-003` | Production import of audit files | `PASS`, no matches | The production/audit dependency boundary is intact |
| `ADV-MECH-004` | Representative endpoint declarations | `PASS` after `EndpointAudit.lean` | Named checkpoint declarations remain available; the core endpoints report only standard Lean/mathlib axioms |

These are necessary checks only. `ADV-MECH-002` is a lexical canary; endpoint
`#print axioms` and semantic premise tracing remain required.

The representative zero-counting, p-series, formula-identity, and Li-criterion
theorems report dependencies on `propext`, `Classical.choice`, and
`Quot.sound`. No project-specific axiom appears in those endpoint reports.
The Burnol theorem has the same axiom report, but its Binet requirement is an
explicit theorem premise and therefore remains a semantic source-closure
finding rather than an axiom finding.

## Initial Claim Triage

| Claim | Initial evidence | Current adversarial position |
|---|---|---|
| Zero-counting M100 | `exists_unconditional_canonicalMultiplicityCount_mulLog_bound` has no explicit mathematical premise and feeds inverse-square theorems | `UNVERIFIED`; strong candidate for `VERIFIED_WITH_SCOPE` after dependency/circularity audit |
| P-series M100 | Actual completed-zeta polynomial-Gaussian weights have theorem-level unconditional summability, window, and tail declarations | `UNVERIFIED`; formula receiver and normalization still need hostile inspection |
| Formula identity M100 | `guinandWeilPiEvenPolynomialGaussianLiteratureFormula` takes only the polynomial and proves the contour limit internally | `UNVERIFIED`; constants, boundary, multiplicity, and source-class scope still need independent checks |
| Positivity M90 | Criterion, formula-on-autocorrelation, continuity, and fixed-support theorem families are present | `CHALLENGED`; two named source closures remain proposition hypotheses |
| Positivity M100 | Li nonnegativity is proved equivalent to project and Mathlib RH | Correctly `OPEN`, `RH_HARD` |

No completed track is certified by this triage. Conversely, no completed track
has yet been refuted.

## Open Findings

### ADV-DOC-001 - Conflicting Current Percentages

- Severity: `P2`
- Status: `RESOLVED` on July 16, 2026
- Claim: the release documentation marks zero-counting and formula identity
  `100%`.
- Evidence: the older detailed rows `Actual zero-counting proof for chosen
  exhaustion` and `Actual formula identity for Riemann-Weil sides` still say
  `90%` and name work that later commits claim to have completed.
- Risk: readers cannot tell which status surface is authoritative.
- Required resolution: finish A1 and A3, then update the detailed rows to the
  audited verdict rather than mechanically copying the headline score.
- Score consequence: `review required`; no immediate change.

### ADV-POS-001 - Burnol M90 Has A Visible Binet Premise

- Severity: `P1`
- Status: `RESOLVED` on July 16, 2026
- Claim: Burnol fixed-support positivity is `proved` or `checked` at M90.
- Lean declaration:
  `exists_burnolFixedSupport_spectral_nonneg_of_binet`.
- Explicit premise: `hBinet : BennettGammaBinetDigammaFormula`.
- Evidence: `BennettGammaBinetDigammaFormula` is currently a proposition
  definition, and the fixed-support theorem consumes it as an argument.
- Risk: the fixed-support result is mathematically conditional inside Lean,
  even though the source theorem is classical and kept visible.
- Required resolution: either provide a checked inhabitant of the Binet
  proposition or scope M90 wording to `formalized from the named Binet source
  theorem`.
- Score consequence: `review required` for positivity M90.
- Resolution: `bennettGammaBinetDigammaFormula` inhabits the source
  proposition, and `exists_burnolFixedSupport_spectral_nonneg` consumes it
  without a Binet argument. `EndpointAudit.lean` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

### ADV-POS-002 - Prime-Moment Limit Source Closure

- Severity: `P1`
- Status: `RESOLVED` on July 16, 2026
- Claim: cutoff covariance is complete at M90.
- Lean declarations: the finite covariance algebra is unconditional, but
  `tendsto_liCutoffCovariance_of_primeMomentAsymptotics` consumes
  `BombieriLagariasPrimeMomentAsymptotic` for every required moment.
- Risk: `exact cutoff covariance` and `the regularized cutoff limit` can be
  conflated. Only the latter needs the source asymptotics.
- Required resolution: split the progress wording into unconditional finite
  covariance and conditional published moment-limit closure, or instantiate
  the moment asymptotics in Lean.
- Score consequence: `review required` for positivity M90.
- Resolution: `bombieriLagariasPrimeMomentAsymptotic` instantiates every
  moment from the pinned PNT remainder, and
  `tendsto_liCutoffCovariance_unconditional` closes the common-cutoff limit.
  `EndpointAudit.lean` reports only standard axioms for both endpoints.

### ADV-SCOPE-001 - Completed Does Not Mean Universal

- Severity: `P2`
- Status: `OPEN`
- Claim: formula identity is complete.
- Evidence: the exact advertised endpoint is the selected real-even
  polynomial-Gaussian source plus a continuously normalized residual consumer.
- Risk: `formula complete` may be read as a universal Guinand-Weil theorem on
  every conventional admissible class.
- Required resolution: A3 must decide whether `VERIFIED_WITH_SCOPE` is the
  correct final label and propagate that scope consistently.
- Score consequence: likely retain with scope; audit not complete.

## Positive Evidence Worth Preserving

The red-team posture should not erase real achievements already visible:

- the zero-counting endpoint has a concrete proof body rather than an assumed
  published `N(T)` record;
- the p-series endpoint sums the multiplicity-weighted actual
  polynomial-Gaussian completed-zeta weight;
- the formula theorem internally constructs good heights, rectangle boundary
  control, contour limits, and right-vertical evaluation;
- the Li criterion proves both directions and is instantiated for analytic
  multiplicity; and
- the docs explicitly state that M100 global positivity is RH-equivalent.

Each point remains provisional until its full adversarial batch closes.

## Next Work

1. Complete A1 on zero-counting, including import-cycle and divisor/multiplicity
   checks.
2. Use A1's exact theorem as the source for A2 p-series.
3. Run A3 independently against the formula constants and contour geometry.
4. Audit positivity M40-M90 and decide the status effect of
   `ADV-POS-001` and `ADV-POS-002`.
5. Reconcile the public claim inventory only after those verdicts are recorded.

The current production percentages remain unchanged during this baseline.
