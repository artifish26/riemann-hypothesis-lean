# Four-Stream Adversarial Audit Plan

Status: `COMPLETE`

This plan challenges the complete theorem route, including the remaining M100
positivity question. Its central question is:

> If a skeptical Lean mathematician ignored the progress percentages, what
> exact checked theorem would justify each gate, and what could make that
> justification fail?

The current scores remain production claims while these audits are open. The
audit is complete only when each claim has a theorem-level verdict.

## Audit Order

The default order follows mathematical dependency rather than recent activity:

1. zero-counting M100;
2. p-series M100;
3. formula identity M100;
4. positivity M40-M90; and
5. cross-stream endpoint and documentation consistency.

Zero-counting and formula identity may be audited in parallel. P-series must
consume the audited counting result. Positivity must consume the audited
formula result.

## Claim Register

| ID | Production claim | Representative checked surface | Current audit state |
|---|---|---|---|
| `ADV-ZC-M100` | Unconditional analytic-multiplicity `N(T) = O(T log T)` and inverse-square consumer | `exists_unconditional_canonicalMultiplicityCount_mulLog_bound`; `unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable` | `VERIFIED_WITH_SCOPE`; A1 complete, exact Bellotti-Wong/HSW asymptotics remain optional refinement |
| `ADV-PS-M100` | Actual polynomial-Gaussian zero side has unconditional absolute summability, windows, tails, and no remaining p-series premise in the formula handoff | `summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional`; `guinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula_of_truncatedEventualErrorEnvelope` | `VERIFIED`; A2 complete on the exact selected polynomial-Gaussian scope |
| `ADV-FI-M100` | The selected real-even polynomial-Gaussian Guinand-Weil formula is unconditional and reaches the continuous residual consumer | `guinandWeilPiEvenPolynomialGaussianLiteratureFormula`; `exists_evenPolynomialGaussianZeroSide_tendsto_continuousResidual` | `VERIFIED`; A3 complete on the exact selected source and supplied-continuous-residual scope |
| `ADV-POS-M90` | Li/Weil reductions, the polynomial-Gaussian formula-on-autocorrelation theorem, and the exact fixed-support Burnol local-form/direct-residual bridge are checked | `RHStatement_iff_fullZetaLiCoefficient_nonneg`; `zetaWeilPolynomialGaussian_formula_on_autocorrelation`; `exists_burnolFixedSupport_guinandWeilBurnolLiteratureResidual_nonneg`; `tendsto_liCutoffCovariance_unconditional` | `VERIFIED_WITH_SCOPE` at mathematics 90%: direct residual positivity is unconditional on one fixed support class; zero-side positivity retains `BurnolGuinandWeilSourceAssumptions`; the independent PNT moment closure is unconditional; M100 remains open |
| `ADV-POS-M100` | Global unconditional positivity | `mathlib_RH_iff_fullZetaLiCoefficient_nonneg` identifies the target | Correctly `OPEN` and `RH_HARD` |

The representative declaration is only the starting point. Each audit must
trace all critical transitive dependencies.

## Common Attack Protocol

Apply these checks to every claimed gate.

### A. Statement Identity

- Expand project definitions until the mathematical object is recognizable.
- Confirm that the theorem is about zeta/xi, not an abstract package, toy
  multiset, finite window, or surrogate residual.
- Confirm that the source class and quantifiers match the prose claim.
- Check whether `unconditional` means no theorem premise or merely no RH
  premise.

### B. Premise And Axiom Audit

- List every explicit theorem argument.
- Run `#print axioms` on representative endpoints.
- Trace proposition-valued source inputs to an actual inhabitant.
- Treat standard literature results as `CONDITIONAL` until formalized or
  explicitly accepted as the advertised boundary.
- Reject assumptions that restate the conclusion through another record.

### C. Index And Multiplicity Audit

- Trace conversions among all zeta zeros, nontrivial zeros, positive ordinates,
  conjugate pairs, and multiplicity-expanded indices.
- Verify analytic multiplicity is positive and preserved.
- Check that trivial-zero removal follows the completed-zeta normalization and
  does not silently discard terms.

### D. Convergence And Cutoff Audit

- Classify each sum as finite, absolutely summable, canonically star-convergent,
  or conditionally ordered.
- Check every reindexing against that classification.
- Keep common cutoffs coupled when separate pieces diverge.
- Check compact-window exhaustion, complementary tails, and limit uniqueness.
- Reject a finite calculation promoted to a global limit without a uniform
  bound.

### E. Normalization Audit

- Independently check Fourier signs and `2*pi` factors.
- Check xi/zeta shifts, analytic order, pole terms, Gamma factors, and prime
  powers.
- Check real-part extraction and conjugation pairing.
- Compare the final formula against the selected literature convention.

### F. Consumer And Circularity Audit

- Name the next theorem that consumes the result.
- Confirm the consumer does not reintroduce the discharged premise.
- Search the import and theorem dependency path for circular use of the
  explicit formula, summability, positivity, or RH.
- Confirm that an endpoint record is instantiated, not merely defined.

## Track ZC: Challenge Zero-Counting M100

### Claimed Chain

```text
xi growth -> Jensen divisor bound -> xi/zeta multiplicity equality
          -> canonical positive-ordinate N(T) = O(T log T)
          -> dyadic count -> multiplicity-aware inverse-square summability
```

### Required Attacks

1. Verify the xi growth theorem is unconditional and does not import the
   Guinand-Weil formula or RH endpoints.
2. Recheck the Jensen center, radius enlargement, nonzero center value, and
   closed-ball boundary handling.
3. Prove that the counted divisor dominates every intended nontrivial zeta
   zero with analytic multiplicity.
4. Check `analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity` at every relevant
   zero and rule out exceptional points.
5. Verify the `T log T` statement for all advertised `T >= 0`, including the
   low range absorbed into the constant.
6. Trace the bound into the exact dyadic and inverse-square consumers.
7. Confirm that `complete` means a sufficient coarse bound, not the sharp
   Riemann-von-Mangoldt asymptotic or Bellotti-Wong constants.

### Done Criterion

`ADV-ZC-M100` is `VERIFIED_WITH_SCOPE` or `VERIFIED`, with a dependency trace
showing no RH, explicit-formula, or p-series circularity.

## Track PS: Challenge P-Series M100

### Claimed Chain

```text
canonical multiplicity growth + polynomial-Gaussian strip decay
 -> absolute completed-zeta zero-weight summability
 -> compact-window convergence and complementary-tail decay
 -> literature formula handoff with no remaining p-series premise
```

### Required Attacks

1. Confirm the actual formula weight, not a majorant or toy weight, is summed.
2. Check completed-zeta normalization at every trivial zero.
3. Verify the sum carries analytic multiplicity and covers every nontrivial
   zero exactly once in the advertised representation.
4. Inspect the exponent inequality and finite low shells.
5. Check absolute summability before every unordered `tsum` or reindexing.
6. Verify arbitrary compact exhaustion windows converge and complementary
   tails vanish.
7. Inspect the formula-handoff signature: finite contour identity and error
   hypotheses may remain formula obligations, but no count, decay, summability,
   window, or tail premise may remain.
8. Confirm the route never requires generic positive-imaginary-axis decay that
   is false for the chosen source class.

### Done Criterion

`ADV-PS-M100` is verified only after the formula receiving theorem is checked
to contain no disguised p-series field.

## Track FI: Challenge Formula-Identity M100

### Claimed Chain

```text
weighted xi rectangle -> multiplicity zero sum
 -> right vertical prime/pole/Gamma evaluation
 -> good-height horizontal decay -> infinite rectangle limit
 -> real-even polynomial-Gaussian literature formula
 -> selected continuous residual consumer
```

### Required Attacks

1. Confirm the final core theorem has no explicit contour identity, boundary,
   zero-free height, error-envelope, RH, or zero-simplicity premise.
2. Audit the residue theorem hypotheses and boundary-zero avoidance rather
   than trusting the rectangle theorem name.
3. Check all four contour orientations and the left/right functional-equation
   reduction.
4. Audit the right vertical prime interchange, pole residue, Gamma integral,
   and normalization constants independently.
5. Verify good heights tend to infinity and control both horizontal sides.
6. Verify the limiting zero side is exactly the multiplicity-aware project
   side already audited in PS.
7. Confirm the theorem's source class is exactly the selected real-even
   polynomial-Gaussian class.
8. Audit the Hermite density and continuous-residual bridge separately; do not
   claim off-axis point-evaluation continuity that the bridge does not prove.
9. Confirm residual positivity is not used anywhere in the identity proof.

### Done Criterion

`ADV-FI-M100` is `VERIFIED` against the registered claim: full completion on
the explicitly selected source class and supplied continuous-residual
consumer, not a universal explicit formula for every possible test class.

## Track POS: Challenge Positivity Through M90

### Required Attacks

1. Recheck full Li coefficient existence, canonical radial ordering, and
   analytic multiplicity.
2. Audit both implications in
   `RHStatement_iff_fullZetaLiCoefficient_nonneg` for hidden symmetry or
   zero-location assumptions.
3. Verify the Weil Hermitian pairing is the actual zeta pairing and the
   Lagarias basis diagonal is exactly the full Li coefficient.
4. Check the autocorrelation theorem in the repository's Fourier convention.
5. Verify the formula evaluates the actual autocorrelation residual, not a
   finite Gram surrogate.
6. Separate unconditional finite cutoff covariance from its global limit,
   which consumes `BombieriLagariasPrimeMomentAsymptotic`.
7. Confirm the unconditional Burnol wrapper really consumes the checked
   `BennettGammaBinetDigammaFormula` inhabitant without extra axioms.
8. Require an exact theorem equating the Burnol local spectral form with the
   project-normalized formula residual or zeta pairing on that support class.
9. Confirm the one fixed support class is not promoted by density or by taking
   a union over radii.
10. Confirm every M100 candidate is classified `RH_HARD` when combined with the
   checked criterion.

### Done Criterion

`ADV-POS-M90` is `VERIFIED_WITH_SCOPE`: the local spectral form is connected
to the actual direct formula residual on the same fixed-support class, and the
zero-side theorem exposes every source premise. The current production
mathematics score is `90%`. This audit cannot close M100; global positivity is
equivalent to RH in the checked route.

The two source closures are now checked. `ADV-POS-001` is resolved by
`bennettGammaBinetDigammaFormula` and the unconditional Burnol consumers; their
focused builds pass and their axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. `ADV-POS-002` is now resolved by
`bombieriLagariasPrimeMomentAsymptotic` for every index and the unconditional
consumer `tendsto_liCutoffCovariance_unconditional`; their axiom reports also
contain only `propext`, `Classical.choice`, and `Quot.sound`.
The independent formula-identification target from `ADV-POS-003` is now
resolved by `BurnolFormulaIdentification` and `BurnolFormulaClosure`, not by
either source-closure lane.

## Cross-Stream Audit

After the four claim audits:

1. build a dependency table whose edges are `PROVED`, `CONDITIONAL(name)`, or
   `OPEN`;
2. reconcile the release claim inventory and detailed audit tables;
3. ensure every `100%` label names its scope and does not imply RH confidence;
4. test that production imports no audit files; and
5. issue one final audit report with retained, narrowed, or reduced scores.

## Execution Batches

| Batch | Work | Exit condition |
|---|---|---|
| A0 | Mechanical baseline and endpoint smoke file (`COMPLETE`) | Build, token scan, import scan, and endpoint declarations recorded |
| A1 | Zero-counting claim audit (`COMPLETE`) | `ADV-ZC-M100 = VERIFIED_WITH_SCOPE`; see `A1_ZERO_COUNTING_AUDIT_2026-07-15.md` |
| A2 | P-series claim audit (`COMPLETE`) | `ADV-PS-M100 = VERIFIED`; see `A2_P_SERIES_AUDIT_2026-07-15.md` |
| A3 | Formula identity claim audit (`COMPLETE`) | `ADV-FI-M100 = VERIFIED`; see `A3_FORMULA_IDENTITY_AUDIT_2026-07-15.md` |
| A4 | Positivity M40-M90 audit (`COMPLETE`) | `ADV-POS-M90 = VERIFIED_WITH_SCOPE`; the exact fixed-support residual bridge and source-conditional zero-side closure pass the repeatable axiom audit |
| A5 | Cross-stream reconciliation (`COMPLETE`) | Dependency graph, score tables, and finding vocabulary agree; see `A5_CROSS_STREAM_RECONCILIATION_2026-07-16.md` |

A1 through A3 completed on July 15, 2026. The p-series verdict consumes the
xi/Jensen growth family audited in A1, and the formula verdict consumes that
exact selected polynomial-Gaussian zero side. A4 then began the M40-M90
positivity classification against the audited formula identity.

A4 opened `ADV-POS-003` before final classification because the original
fixed-support theorem had no production edge to the actual Guinand-Weil
residual or zeta pairing. The smallest failing chain and interim narrowed
verdict remain recorded in
`A4_BURNOL_FORMULA_BRIDGE_FINDING_2026-07-15.md`. After the gate reopened,
`BurnolFormulaKernel`, `BurnolFormulaBridge`,
`BurnolFormulaIdentification`, and `BurnolFormulaClosure` supplied the exact
fixed-support direct residual equality, source-conditional zero-side equality,
and unconditional residual nonnegativity endpoint. The repeatable A4 audit
reports only `propext`, `Classical.choice`, and `Quot.sound` for the decisive
declarations. A4 is complete, architecture remains 90%, and positivity
mathematics is 90%; fixed-support density and M100 remain open.

A5 completed on July 16, 2026. It retained every A1-A4 verdict and score,
corrected the stale graph edge that had conflated the M80 polynomial-Gaussian
lane, the M90 Burnol direct-residual lane, and the then-conditional PNT cutoff
limit, and normalized finding-record statuses without changing their
verdicts. Production still imports no adversarial files. The complete
reconciliation is recorded in
`A5_CROSS_STREAM_RECONCILIATION_2026-07-16.md`.

## Stop Rules

Stop and open a P0/P1 finding immediately if any audit discovers:

- an unadvertised RH or critical-line premise;
- a project axiom or admitted theorem on the completed path;
- a conditional source proposition described as instantiated;
- lost analytic multiplicity;
- an unordered use of a merely conditionally convergent series;
- a formula normalization mismatch;
- a circular dependency among formula, counting, and summability; or
- a toy or finite residual substituted for the actual zeta residual.

Do not patch around the issue during discovery. Record the smallest failing
chain first so the correction can be reviewed independently.
