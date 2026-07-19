# A5 Cross-Stream Reconciliation - 2026-07-16

Status: `COMPLETE`

Verdict: `FOUR-STREAM REGISTER RECONCILED; SCORES RETAINED`

## Exact Claim

A5 audits the project-wide claim that the four canonical score rows, detailed
actual-theorem rows, dependency graph, and adversarial verdicts describe the
same checked theorem state.

The reconciled scores are:

| Track | Architecture | Mathematics | Adversarial verdict |
|---|---:|---:|---|
| Zero-counting / usable growth | 100% | 100% | `ADV-ZC-M100 = VERIFIED_WITH_SCOPE` |
| P-series / zero-side summability | 100% | 100% | `ADV-PS-M100 = VERIFIED` |
| Guinand-Weil formula identity | 100% | 100% | `ADV-FI-M100 = VERIFIED` on the selected real-even source and supplied continuous-residual consumer |
| Formula-side residual positivity | 90% | 90% | `ADV-POS-M90 = VERIFIED_WITH_SCOPE`; M100 remains open |

A5 changes no percentage.

## Reconciled Dependency Table

| Edge | Status | Evidence and scope |
|---|---|---|
| Xi/Jensen growth to the canonical analytic-multiplicity count | `PROVED` | A1; unconditional coarse `O(T log T)`, not the sharp Riemann-von-Mangoldt asymptotic |
| Canonical count to polynomial-Gaussian zero-side summability | `PROVED` | A2; exact selected completed-zeta weight, windows, and tails |
| Canonical count to multiplicity-aware Li summability | `PROVED` | A1 and the M50-M60 Li consumers |
| Polynomial-Gaussian zero-side control to the selected Guinand-Weil formula | `PROVED` | A2-to-A3 formula receiver has no remaining p-series premise |
| Real-even polynomial-Gaussian formula plus Weil pairing to M80 autocorrelation identification | `PROVED` | A3 and `zetaWeilPolynomialGaussian_formula_on_autocorrelation` |
| Binet theorem to fixed-support Burnol local spectral positivity | `PROVED` | `BurnolLocalSupportUnconditional` |
| Burnol local spectral form to the direct prime/pole/Gamma residual | `PROVED` | A4; exact factor `2 * pi` on the fixed-support class |
| Fixed-support direct residual positivity | `PROVED` | `exists_burnolFixedSupport_guinandWeilBurnolLiteratureResidual_nonneg` |
| Fixed-support multiplicity-aware zero-side positivity | `CONDITIONAL(BurnolGuinandWeilSourceAssumptions)` | Entire extension, absolute zero-side summability, and the Burnol-class source formula remain explicit |
| Li cutoff covariance limit | `PROVED` | `bombieriLagariasPrimeMomentAsymptotic` supplies every moment from the pinned PNT source, and `tendsto_liCutoffCovariance_unconditional` consumes the family; this lane remains independent of `BurnolFormulaClosure` |
| Fixed-support positivity to global criterion-determining positivity | `OPEN` | No density or support-continuation theorem; M100 is RH-hard |
| Global Li/Weil positivity to RH | `PROVED AS AN EQUIVALENCE` | `mathlib_RH_iff_fullZetaLiCoefficient_nonneg`; the unconditional positivity side is open |

The M80 polynomial-Gaussian lane and M90 Burnol lane are separate
class-specific formula results. Neither is a density transport theorem between
the two classes.

## Documentation Findings

### ADV-XSTREAM-001

```text
ID: ADV-XSTREAM-001
Track: Cross-stream dependency graph
Severity: P2
Status: RESOLVED
Claim: The release labels every critical edge as PROVED, CONDITIONAL(name), or OPEN consistently with the checked consumers
Evidence: A4BurnolFormulaBridgeAudit.lean; BurnolFormulaClosure imports; theorem signatures; prior dependency graph
Verdict: DOCUMENTATION_CONFLICT -- the graph retained an OPEN M80-to-M90 edge into a proved M90 node and routed the conditional PNT cutoff lane into BurnolFormulaClosure
Corrective action: separate the polynomial-Gaussian M80 lane, Burnol direct-residual M90 lane, and PNT cutoff-limit lane; show the zero-side source package and M100 density gap explicitly
Score consequence: none
```

### ADV-XSTREAM-002

```text
ID: ADV-XSTREAM-002
Track: Adversarial finding records
Severity: P3
Status: RESOLVED
Claim: Finding records use the status vocabulary OPEN, RESOLVED, or ACCEPTED_SCOPE separately from their verdicts
Evidence: the A2-A4 finding records
Verdict: DOCUMENTATION_CONFLICT -- VERIFIED and MATHEMATICALLY_RESOLVED had been used as status values
Corrective action: retain the mathematical verdicts and normalize A2/A3 to ACCEPTED_SCOPE and A4 to RESOLVED
Score consequence: none
```

## Percentage And Scope Audit

The reconciled score tables agree exactly. Their `100%` rows name the selected
scope:

- zero-counting means the coarse count sufficient for the selected consumers,
  not exact Bellotti-Wong/HSW constants;
- p-series means the actual selected polynomial-Gaussian zero side and formula
  handoff, not a generic all-Schwartz theorem; and
- formula identity means the selected real-even polynomial-Gaussian source and
  supplied continuous-residual consumer, not universal off-axis Schwartz
  point-evaluation continuity.

The detailed `100%` component rows are explicitly artifact- or
formalization-scoped and retain a separate next-work column. Stale next-work
text around the legacy Li and support-restricted packages was reconciled with
the now-checked M50-M90 theorem families. No positivity row is labeled 100%;
global M100 positivity remains open and RH-equivalent.

## Verification

Verified on the live tree on July 16, 2026:

- `lake env lean ADVERSARIAL/EndpointAudit.lean`: `PASS`;
- `lake env lean ADVERSARIAL/A4BurnolFormulaBridgeAudit.lean`: `PASS`;
- `bombieriLagariasPrimeMomentAsymptotic` and
  `tendsto_liCutoffCovariance_unconditional` report only `propext`,
  `Classical.choice`, and `Quot.sound`;
- `lake build RiemannHypothesisProject.Basic`: `PASS` (`3902` jobs);
- `lake build`: `PASS` (`3904` jobs);
- the production placeholder scan finds no `sorry`, `axiom`, or `admit`;
- the production import scan finds no audit import; and
- `git diff --check`: `PASS` after the final documentation patch.

The source-closure pass adds the production prime-moment modules and the
unconditional cutoff consumer, so both the aggregate target and the full
build were rerun.

## Final Verdict

A1 through A5 are complete. The first three streams retain their scoped 100%
scores, positivity retains 90%, the independent PNT moment source closure is
now proved and remains separately visible, and M100 global
criterion-determining positivity remains the sole RH-hard production gate.
