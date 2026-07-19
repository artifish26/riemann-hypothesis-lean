# A3 Formula-Identity Claim Audit - 2026-07-15

Status: `COMPLETE`

Verdict: `ADV-FI-M100 = VERIFIED`

## Exact Claim

The registered production claim is:

> The selected real-even polynomial-Gaussian Guinand-Weil formula is
> unconditional and reaches the selected continuous residual consumer.

The representative endpoints are:

- `guinandWeilPiEvenPolynomialGaussianLiteratureFormula`; and
- `exists_evenPolynomialGaussianZeroSide_tendsto_continuousResidual`.

The word `selected` is material. The core theorem proves the exact literature
formula for every source

```text
p(x^2) * exp(-pi * x^2),  p : Polynomial Real,
```

with the project's Fourier convention and analytic-multiplicity zero side.
The consumer then approximates an arbitrary real-even Schwartz function after
being supplied a continuous real-linear residual whose values on this dense
source equal the checked literature residual. It does not assert a universal
explicit formula for every Schwartz function, nor prove ordinary-Schwartz
continuity of off-axis point evaluation.

Because those qualifications were already explicit in the registered claim
and production status, the exact claim receives `VERIFIED`, rather than a new
scope reduction.

## Dependency Verdict

| Edge | Status | Checked declaration or construction |
|---|---|---|
| Entire polynomial-Gaussian contour weight with xi reflection and real conjugation symmetry | `PROVED` | `guinandWeilXiContourWeight`; its analytic, reflection, and conjugation lemmas |
| Weighted rectangle argument principle with complete analytic order at each zero | `PROVED` | `guinandWeilNormalizedRectangleIntegral_weight_mul_logDeriv_eq_sum` |
| Xi divisor support equals the finite set of xi zeros in the rectangle | `PROVED` | `riemannXiRectangleDivisorSupport`; `mem_riemannXiRectangleDivisorSupport_iff` |
| Xi analytic order equals project zeta multiplicity at every nontrivial zeta zero | `PROVED` | `analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial` |
| Four oriented sides equal the finite multiplicity-weighted xi divisor sum | `PROVED` | `guinandWeilXi_rectangleBoundary_decomposition_eq_weightedZeroSum` |
| Fixed vertical walls are zero-free; selected upper and reflected lower edges are zero-free | `PROVED` | `riemannXi_ne_zero_on_symmetric_goodHeight_rectangleBorder` and its wall lemmas |
| Cofinal good heights in `[N, N + 1]` control the logarithmic derivative | `PROVED` | `exists_fixed_canonicalXi_goodHeight_logDeriv_bound` |
| Polynomial times Gaussian decay defeats the polynomial horizontal envelope | `PROVED` | `exists_pos_const_norm_guinandWeilXiContourWeight_horizontal_le`; `exists_canonicalXi_goodHeight_both_horizontalIntegrals_tendsto_zero` |
| Finite rectangle zero sums tend to the A2-audited unordered literature zero side | `PROVED` | `tendsto_re_riemannXiRectangleWeightedZeroSum` |
| Left vertical is the reflected negative of the right and truncated right vertical tends to the complete line | `PROVED` | reflection and integrability steps in `PolynomialGaussianFormulaIdentity` |
| Shifted source integral has Fourier sample `u / (2*pi)` | `PROVED` | `integral_guinandWeilPiPolynomialGaussianSource_horizontalLine_mul_exp_eq_fourier` |
| Von-Mangoldt integral interchanges with the absolutely summable prime series | `PROVED` | `integral_shiftedPolynomialGaussian_mul_vonMangoldtLSeries_eq_primeFourierTsum` |
| Prime component has coefficient `Lambda(n)/sqrt(n)` and sample `log(n)/(2*pi)` | `PROVED` | `neg_one_div_pi_mul_re_integral_xiContourWeight_vonMangoldtLSeries_right_eq_literaturePrime` |
| Rational xi logarithmic-derivative terms equal the literature pole component | `PROVED` | `one_div_pi_mul_re_integral_xiContourWeight_rational_right_eq_literaturePole` |
| Digamma and `-log(pi)/2` terms equal the literature Gamma component | `PROVED` | `one_div_pi_mul_re_integral_xiContourWeight_archimedean_right_eq_literatureGamma` |
| Complete right vertical equals the exact literature residual | `PROVED` | `one_div_pi_mul_re_integral_xiContourWeight_logDeriv_riemannXi_right_eq_literatureResidual` |
| Infinite rectangle limit gives the premise-free selected formula | `PROVED` | `guinandWeilPiEvenPolynomialGaussianLiteratureFormula` |
| Even polynomial-Gaussians have dense range in real-even Schwartz space | `PROVED` | `denseRange_guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap` |
| Actual zero-side values converge to any continuously normalized residual extension | `PROVED` | `exists_evenPolynomialGaussianZeroSide_tendsto_continuousResidual` |

There is no `CONDITIONAL(name)` or `OPEN` edge in the exact registered
formula-identity chain.

## Hostile Checks

### Premises, Divisor, And Boundary

`guinandWeilPiEvenPolynomialGaussianLiteratureFormula` takes only
`p : Polynomial Real`. It has no contour-identity, boundary-zero, good-height,
error-envelope, RH, critical-line, or zero-simplicity proposition argument.
Those obligations are discharged in its proof.

The generic rectangle theorem makes its analytic, finite-order, support,
zero-set, and boundary-nonvanishing hypotheses explicit. Its proof subtracts
the complete analytic-order principal part at every member of the finite
zero set before integrating the analytic remainder. The xi specialization
identifies that finite set with exactly the xi zeros in the closed rectangle.
Xi has no extra zeros at `0` or `1`, and its zeros in this strip are precisely
the nontrivial zeta zeros. The theorem
`analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial` has no
ordinate-sign restriction, so every term carries full project analytic
multiplicity.

The fixed walls are `Re(s) = -1/4` and `Re(s) = 5/4`. The right wall is
zero-free in the zeta half-plane; the left wall follows from xi reflection.
The good-height construction supplies a zero-free upper edge and the
functional equation supplies the lower edge. The resulting border theorem
covers all four sides before the finite rectangle identity is applied.

### Orientations, Heights, And Infinite Zero Sum

The rectangle expansion is visibly

```text
bottom - top + right - left.
```

The contour weight obeys `H(1-s) = H(s)`, and xi and its logarithmic
derivative obey the corresponding reflection identities. After changing the
vertical parameter, the left integral is the negative of the right integral.
Thus the normalized pair contributes `(1/pi) * Re(right)` with the expected
sign.

Selected heights satisfy `N <= height N <= N + 1` eventually, so they tend to
infinity. The good-height logarithmic-derivative estimate is polynomial in
the height and the canonical multiplicity count. The contour weight is bounded
by a polynomial times `exp(-pi*T^2)`, forcing both horizontal integrals to
zero. The lower integral is also checked through reflection rather than
silently inferred from an unsigned upper bound.

Every nontrivial zero has `0 < Re(rho) < 1`, so the fixed-width rectangles
eventually contain it when their heights tend to infinity. The rectangle
finsets therefore tend cofinally to the full nontrivial-zero subtype. The
limit uses the unconditional absolute summability audited in A2 before the
unordered `tsum` is formed. The finite sums and the limiting literature zero
side use the same analytic multiplicity.

### Prime, Pole, Gamma, And Fourier Normalization

The right-wall logarithmic derivative is decomposed into the rational pole
terms, the completed Gamma term, and minus the von-Mangoldt Dirichlet series.
Each complete-line component is proved integrable and evaluated separately.

Mathlib's Fourier convention here is
`exp(-2*pi*I*x*xi)`. The horizontal contour-shift theorem therefore samples at
`u/(2*pi)`. On the right wall the `3/4` source shift and `5/4` Dirichlet-series
real part combine to the exact `1/sqrt(n)` coefficient. Consequently the
prime samples are `log(n)/(2*pi)`. Real evenness identifies the negative and
positive samples, and the normalized real part converts the two-sided form to
the literature factor `-1/pi` without an extra factor of two.

The rational integral is evaluated at the source's `+/- i/2` points and
matches the literature pole term. The archimedean logarithmic derivative is
exactly `-log(pi)/2 + digamma(s/2)/2`; its contour shift has separately proved
vanishing vertical edges and yields the literature Gamma integral. Combining
the three identities proves the complete right-vertical residual equality
used by the core theorem.

### Source, Density Consumer, And Circularity

`guinandWeilPiEvenPolynomial p` is even by construction and produces the
entire contour source `p(z^2) * exp(-pi*z^2)`. The Hermite development proves
that these sources have dense range in the real-even Schwartz submodule.
For every approximating polynomial the unconditional core formula identifies
the actual multiplicity-weighted zero side with the literature residual.

The final density theorem deliberately accepts two inputs: a continuous
real-linear `residual`, and equality of that residual with the literature
normalization on every polynomial source. Continuity then carries the checked
source values to the target real-even Schwartz function. This is the exact
advertised continuous-residual consumer. It does not separately extend raw
off-axis zero evaluation to arbitrary Schwartz functions.

The selected dependency path imports the A2 summability result, xi growth and
local good-height machinery, the weighted rectangle theorem, and the
prime/pole/Gamma normalization modules. It does not import audit files,
residual positivity, Li positivity, or an RH endpoint.
Residual nonnegativity remains a separate input to later positivity theorems.

## Finding Record

```text
ID: ADV-FI-M100
Track: Guinand-Weil formula identity
Severity: P3 (scope and normalization clarity only)
Status: ACCEPTED_SCOPE
Claim: Selected real-even polynomial-Gaussian formula is unconditional and reaches the selected continuous residual consumer
Lean declaration: guinandWeilPiEvenPolynomialGaussianLiteratureFormula
Explicit premises: p : Polynomial Real
Transitive source inputs: proved xi rectangle, good-height, A2 summability, and prime/pole/Gamma normalization theorems
Consumer: exists_evenPolynomialGaussianZeroSide_tendsto_continuousResidual
Attack: premise, residue, boundary, orientation, height, limit, multiplicity, Fourier, prime, pole, Gamma, source, density, import, axiom, and circularity audit
Evidence: A3FormulaIdentityAudit.lean; theorem-body and normalization trace recorded above
Verdict: VERIFIED
Corrective action: retain the M100 score and keep both the polynomial-Gaussian source scope and supplied-continuous-residual premise explicit
Score consequence: retain
```

One non-gating maintenance item remains. `FORMULA_IDENTITY_PLAN.md` asks for a
named `p = 1` normalization regression theorem, but the production modules do
not currently expose that specialization under a dedicated name. The general
theorem already proves it by instantiation, so this is a P3 reproducibility
improvement with no score consequence, not a missing mathematical edge.

## Verification

- `lake env lean ADVERSARIAL/A3FormulaIdentityAudit.lean`: `PASS`.
- Focused
  `lake build RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFormulaIdentity RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianDensityBridge`:
  `PASS`, 3763 jobs.
- Full `lake build`: `BLOCKED OUTSIDE A3`. Concurrent untracked Binet work
  imported by the modified aggregate currently fails in
  `RiemannVonMangoldt/Binet/KernelNormalization.lean`. That file is not an A3
  dependency, and the audit did not edit or revert it.
- Representative declarations report only `propext`, `Classical.choice`, and
  `Quot.sound`.
- No production proof was changed during this audit.
