# A1 Zero-Counting Claim Audit - 2026-07-15

Status: `COMPLETE`

Verdict: `ADV-ZC-M100 = VERIFIED_WITH_SCOPE`

## Exact Claim

The production claim under audit is:

> Unconditional analytic-multiplicity `N(T) = O(T log T)` and inverse-square
> consumer.

The representative endpoints are:

- `exists_unconditional_canonicalMultiplicityCount_mulLog_bound`; and
- `unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable`.

The exact checked count is the canonical finite sum of analytic
multiplicities over actual Riemann-zeta zeroes satisfying
`0 < Im rho <= T`. Lean proves, with no proposition-valued mathematical
premise,

```text
exists C > 0, forall T >= 0,
  N(T) <= C * (T + 1) * (log (T + 1) + 1).
```

This is the qualitative `O(T log T)` bound needed by the selected route. It
is not the sharp Riemann-von-Mangoldt asymptotic or the explicit
Bellotti-Wong/HSW estimate.

## Dependency Verdict

| Edge | Status | Checked declaration or construction |
|---|---|---|
| Mathlib modified-theta tail to a global exponential kernel bound | `PROVED` | `exists_riemannThetaTail_global_exp_bound` |
| Folded theta Mellin integral to the entire pole-subtracted completed zeta | `PROVED` | `completedRiemannZeta₀_eq_integral_Ioi` |
| Completed-zeta growth to order-one xi sphere growth | `PROVED` | `exists_riemannXi_sphere_exp_mulLog_bound` |
| Xi sphere growth to a multiplicity-aware Jensen divisor bound | `PROVED` | `exists_riemannXi_jensen_mulLog_bound` |
| Zeta multiplicity to xi analytic order at each positive-ordinate zero | `PROVED` | `analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity` |
| Canonical positive-ordinate window to the xi divisor ball | `PROVED` | `canonicalMultiplicityCount_le_riemannXi_divisor` |
| Jensen divisor bound to global `T log T` count | `PROVED` | `exists_unconditional_canonicalMultiplicityCount_mulLog_bound` |
| Global count to dyadic `T log T` count | `PROVED` | `exists_unconditional_canonicalMultiplicityCount_dyadic_mulLog_bound` |
| Dyadic `T log T` count to the actual inverse-square height factor | `PROVED` | `unconditional_positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_mulLogCount` |
| Subquadratic sibling count to clamped inverse-square summability | `PROVED` | `unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable` |
| Clamped inverse-square summability to the paired Li consumer | `PROVED` | `summable_multiplicityWeightedZetaLiPairedSummand` |

There is no `CONDITIONAL(name)` or `OPEN` edge on the selected coarse-count
route.

## Hostile Checks

### Source And Premise Audit

The order-one source is proved from Mathlib's modified-theta estimates and
Mellin machinery. The project proof globalizes the theta tail, folds the
small-`x` integral onto `[1, infinity)`, applies the elementary
`log u <= u - 1` absorption, and packages the result as xi sphere growth.
No RH, explicit-formula, zero-simplicity, published-count, or user-supplied
source proposition occurs in the endpoint signatures.

The A1 axiom smoke check reports only `propext`, `Classical.choice`, and
`Quot.sound` for every representative source, normalization, count, dyadic,
and consumer declaration.

### Jensen Geometry And Boundary Handling

Jensen is centered at `2`, where `riemannXi_two_ne_zero` is proved from
right-half-plane zeta nonvanishing. The inner radius is `r` and the outer
radius is `2*r`, so the denominator is the fixed positive `log 2`.
For the canonical count the proof takes `r = T + 3`, which is positive for
every advertised `T >= 0`.

Mathlib's `AnalyticOnNhd.sum_divisor_le` counts the divisor on the closed
inner ball and requires analyticity on the closed outer ball, nonvanishing at
the center, and a norm bound on the outer sphere. It does not require the
outer sphere to be zero-free. Thus a zero on the inner closed-ball boundary
is counted rather than silently discarded.

Every zero in the canonical window satisfies `0 < Re rho < 1` and
`0 < Im rho <= T`. The proof obtains

```text
norm rho <= T + 1
norm (rho - 2) <= T + 3,
```

so the complete canonical window is contained in the Jensen ball.

### Multiplicity And Exceptional Points

`zetaZeroMultiplicity` is the finite natural analytic order of zeta at an
actual zero and is proved positive. The canonical `N(T)` is the finite sum of
those multiplicities, not the cardinality of distinct locations.

At a positive-ordinate zero, the local factor

```text
2 * GammaR(s)^(-1) * (s * (s - 1))^(-1)
```

is analytic and nonzero. Positive ordinate rules out `s = 0`; the checked
critical-strip facts rule out `s = 1` and give `Re s > 0`, where the real
Gamma factor is nonzero. Consequently xi and zeta have exactly the same
analytic order at every counted zero. No simplicity assumption is used.

### Low Range And Dyadic Exhaustion

The theorem covers every `T >= 0`. At `T = 0` the defining window is empty;
the regularized right side remains well-defined because it uses `T + 1`.
For the summability step, clamping the ordinate below by `1` places every
low-height zero in the zeroth dyadic shell. The exact cumulative window at
height `2^(m+1)` bounds each shell with multiplicity, so no separate
zero-free low band is assumed.

The order-one theorem directly feeds the summability of

```text
multiplicity(rho) * (Im(rho)^2 + 1/4)^(-1).
```

The clamped inverse-square endpoint used by the paired Li construction is
currently proved from the separately checked `T^(3/2)` count. That is a
stronger-than-needed sibling route, not a conditional edge. Both paths are
unconditional and preserve analytic multiplicity.

### Consumer And Circularity Audit

`summable_multiplicityWeightedZetaLiPairedSummand` consumes the clamped
inverse-square theorem as its eventual norm majorant. The Bombieri-Lagarias
summability module consumes the same theorem for reciprocal-square weights.
The polynomial-Gaussian zero side also consumes the xi/Jensen growth
certificate.

The source proof path uses the theta kernel, completed zeta, xi, analytic
orders, canonical finite windows, Jensen's divisor inequality, and elementary
dyadic summability. It does not use the Guinand-Weil formula, formula-side
positivity, Li nonnegativity, or RH. Import and source searches found no audit
dependency in production. There is therefore no
counting/formula/summability circularity on this route.

## Finding Record

```text
ID: ADV-ZC-M100
Track: Zero-counting / usable growth
Severity: P3 (scope clarification only)
Status: ACCEPTED_SCOPE
Claim: Unconditional analytic-multiplicity N(T) = O(T log T) and inverse-square consumer
Lean declaration: exists_unconditional_canonicalMultiplicityCount_mulLog_bound
Explicit premises: none
Transitive source inputs: proved Mathlib theta/Mellin facts and proved project normalization bridges
Consumer: unconditional_positiveOrdinateZetaZero_multiplicityHeightDecay_summable_of_mulLogCount; summable_multiplicityWeightedZetaLiPairedSummand
Attack: source-premise, Jensen geometry, boundary, multiplicity, exceptional-point, low-range, dyadic, consumer, and circularity audit
Evidence: A1ZeroCountingAudit.lean; focused RiemannXiJensen build; theorem-body trace recorded above
Verdict: VERIFIED_WITH_SCOPE
Corrective action: retain the coarse-count completion wording; continue to label exact Bellotti-Wong/HSW constants as optional sharp refinement
Score consequence: retain
```

## Verification

- `lake env lean ADVERSARIAL/A1ZeroCountingAudit.lean`: `PASS`.
- Focused `lake build RiemannHypothesisProject.RiemannVonMangoldt.RiemannXiJensen`:
  `PASS`, 3630 jobs.
- Full `lake build`: `PASS`, 3833 jobs.
- Representative declarations report only standard Lean/mathlib axioms.
- No production proof was changed during this audit.
