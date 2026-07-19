# A2 P-Series Claim Audit - 2026-07-15

Status: `COMPLETE`

Verdict: `ADV-PS-M100 = VERIFIED`

## Exact Claim

The production claim under audit is:

> The actual polynomial-Gaussian completed-zeta zero side has unconditional
> absolute summability, compact windows, complementary tails, and no remaining
> p-series premise in the literature formula handoff.

The representative endpoints are:

- `summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional`;
  and
- `guinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula_of_truncatedEventualErrorEnvelope`.

The checked source family is exactly

```text
p(z) * exp(-pi * z^2),  p : Polynomial Complex,
```

evaluated at the actual Riemann-Weil argument of each zeta zero. The real zero
weight is zero at trivial zeros and otherwise is the real part of this source,
multiplied by the natural-number analytic multiplicity of zeta at that zero.
This claim is about the selected polynomial-Gaussian family, not a generic
Schwartz function or an all-functions extension system.

## Dependency Verdict

| Edge | Status | Checked declaration or construction |
|---|---|---|
| Gaussian exponential to arbitrary shifted-radius decay on every bounded horizontal strip | `PROVED` | `exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip` |
| Polynomial factor absorbed by increasing the Gaussian decay order by `p.natDegree` | `PROVED` | `exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_horizontalStrip` |
| Strip decay transferred to every actual completed-zeta zero weight | `PROVED` | `norm_guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight_le_shiftedRadius` |
| Xi/Jensen to an unconditional degree-`2` canonical analytic-multiplicity growth certificate | `PROVED` | `riemannXiCanonicalMultiplicityPolynomialGrowth` |
| Eventual growth to a global dyadic bound with the finite low prefix absorbed | `PROVED` | `CanonicalMultiplicityPolynomialGrowth.exists_global_dyadic_bound` |
| Degree-`2` count plus freely selected decay order `3` to positive-half absolute summability | `PROVED` | `summable_norm_positiveOrdinateMultiplicityPolynomialGaussianZeroWeight_of_growth` |
| Positive-half sum transported to the negative half with analytic multiplicity preserved | `PROVED` | `zetaZeroMultiplicity_conj`; `CanonicalMultiplicityPolynomialGrowth.negativeOrdinate_abs_summable` |
| Remaining real-axis support confined to one fixed finite residual window | `PROVED` | `mem_closedBallZeroResidualRealAxisFinset_one_of_axis_not_trivial` |
| Positive, negative, and real-axis pieces assembled into the actual all-zero absolute sum | `PROVED` | `summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_of_growth` |
| Xi/Jensen growth instantiated at the all-zero absolute and signed endpoints | `PROVED` | `summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional`; signed sibling |
| Arbitrary compact-exhaustion windows converge and absolute complements vanish | `PROVED` | `tendsto_multiplicityPolynomialGaussianCompletedZetaZeroWindowSum_unconditional`; `tendsto_tsum_norm_multiplicityPolynomialGaussianCompletedZetaZero_compl_unconditional` |
| Formula zero-side truncation error tends to zero without a count or decay argument | `PROVED` | `tendsto_norm_guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide_sub_truncated` |
| Formula receiver retains only finite-contour/error-envelope obligations | `PROVED` | `guinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula_of_truncatedEventualErrorEnvelope` |

There is no `CONDITIONAL(name)` or `OPEN` edge in the selected p-series chain.

## Hostile Checks

### Actual Weight And Source Decay

`guinandWeilPiPolynomialGaussianCompletedZetaZeroWeight` is the weight used by
the literature formula handoff, not a shell majorant or a toy sequence. For a
nontrivial zero `rho` it is

```text
Re (p(riemannWeilZeroArgument rho) *
  exp(-pi * riemannWeilZeroArgument rho ^ 2)).
```

Nontrivial zeta zeros send the Riemann-Weil argument into the fixed horizontal
strip `|Im z| <= 1/2`. The Gaussian norm is bounded directly on each bounded
horizontal strip. The polynomial factor is absorbed by asking the Gaussian
bound for decay order `p.natDegree + k`, leaving arbitrary requested order
`k` for the product. Consequently the route does not use the false generic
positive-imaginary-axis decay property ruled out elsewhere in the project.

### Count Exponent And Low Shells

The unconditional wrapper instantiates the degree-`2` xi/Jensen growth
certificate checked during A1. The p-series proof chooses
`k = growth.degree + 1`, hence `k = 3`, and obtains the geometric shell ratio
`2^2 / 2^3 < 1`.

The source growth structure is allowed to start only above a threshold.
`exists_global_dyadic_bound` chooses a dyadic point beyond that threshold and
adds every earlier cumulative count to one nonnegative prefix constant. The
clamped height `max 1 |Im rho|` puts every low positive-ordinate zero into the
zeroth shell. Thus no low-height zero-free assertion or omitted finite sum is
needed.

The degree-`2` certificate is sufficient but not the sharp A1 order-one count.
This is an unconditional sibling from the same audited xi/Jensen source, not a
Bellotti-Wong premise. The implementation file also retains an older
`BellottiWongCanonicalMultiplicityNTTheorem` lane, but the unconditional
wrapper's proof term instantiates only `riemannXiCanonicalMultiplicityPolynomialGrowth`.

### Indexing, Multiplicity, And Trivial Zeros

`ZetaZeroSubtype` indexes each distinct actual zeta-zero location once. Every
term is then multiplied by `zetaZeroMultiplicityReal`, the positive analytic
order of zeta at that location. Conjugation is an equivalence between the
positive- and negative-ordinate subtypes; `zetaZeroMultiplicity_conj` proves
that the analytic order is unchanged by this transport.

The completed-zeta weight is definitionally zero on `IsTrivialZetaZero`.
`multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_indicator` identifies
the all-zero weight with the indicator of the raw weight on the nontrivial-zero
set. The finite and global `tsum` normalization lemmas therefore remove every
trivial-zero term and retain every nontrivial location exactly once with its
analytic multiplicity.

The proof does not assume there are no nontrivial real-axis zeros. Any such
zero has `0 < Re rho < 1`, hence norm at most `1`, so all nonzero real-axis
contributions have support in the fixed finite radius-one residual window.

### Absolute Sums, Windows, And Tails

The all-zero absolute series is proved summable before the signed series is
formed. Signed summability is obtained with `.of_norm`. Compact windows use an
abstract `ComplexCompactExhaustion` whose defining cofinality field eventually
contains every complex point. Its finite zero-subtype windows are monotone and
cofinal, so Mathlib's summable-finset limit gives convergence to the unordered
`tsum` for every such exhaustion.

For each cutoff, the total absolute sum is decomposed exactly into the finite
window plus the complementary subtype `tsum`. Subtracting the convergent
window sum proves that complementary absolute tail tends to zero. The formula
handoff bounds its signed zero-side truncation error by this absolute tail, so
no conditional ordering or uncoupled reindexing is used.

### Formula Receiver And Circularity

The eventual-envelope receiver has only these mathematical obligations:

1. a finite cutoff identity for every cutoff;
2. an eventual absolute bound on its signed contour error; and
3. convergence of the error envelope to zero.

It has no count, decay, summability, compact-window, complementary-tail, RH, or
zero-simplicity premise. The residual cutoff convergence used by the receiver
has its own unconditional inverse-square proof for the von-Mangoldt prime
series; it does not consume the zero-side p-series theorem circularly.

The selected proof path uses the concrete Gaussian source, polynomial bounds,
xi/Jensen canonical multiplicity growth, elementary dyadic summability,
conjugation, compact finiteness of zeta zeros, and summable-series limit
theorems. It does not use the Guinand-Weil identity, residual positivity, Li
nonnegativity, RH, or audit modules. The later formula
receiver consumes the completed p-series result and leaves the finite contour
identity as the formula track's separate obligation.

## Finding Record

```text
ID: ADV-PS-M100
Track: P-series / zero-side summability
Severity: P3 (dependency clarity only)
Status: ACCEPTED_SCOPE
Claim: Actual polynomial-Gaussian zero side has unconditional absolute summability, windows, tails, and no remaining p-series premise in the formula handoff
Lean declaration: summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional
Explicit premises: p : Polynomial Complex
Transitive source inputs: proved polynomial-Gaussian strip decay and proved xi/Jensen canonical multiplicity growth
Consumer: guinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula_of_truncatedEventualErrorEnvelope
Attack: actual-weight, strip-decay, exponent, finite-prefix, indexing, multiplicity, trivial-zero, real-axis, absolute-convergence, exhaustion, tail, receiver, and circularity audit
Evidence: A2PSeriesAudit.lean; theorem-body trace recorded above
Verdict: VERIFIED
Corrective action: retain the M100 score; keep the selected polynomial-Gaussian scope and the unconditional-growth-versus-legacy-Bellotti-Wong distinction explicit
Score consequence: retain
```

## Verification

- `lake env lean ADVERSARIAL/A2PSeriesAudit.lean`: `PASS`.
- Focused
  `lake build RiemannHypothesisProject.GuinandWeilConcrete.MultiplicityPolynomialGaussianFormulaHandoff`:
  `PASS`, 3680 jobs.
- Full `lake build`: `BLOCKED OUTSIDE A2`. Concurrent untracked Binet work
  imported by the modified aggregate currently fails in
  `RiemannVonMangoldt/Binet/KernelNormalization.lean` and
  `RiemannVonMangoldt/Binet/GaussDigamma.lean`. Neither file is an A2
  dependency, and the audit did not edit or revert them.
- Representative declarations report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- No production proof was changed during this audit.
