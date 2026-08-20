# Suzuki S3 Release Audit — 2026-08-20

Verdict: `VERIFIED_WITH_SCOPE`

This audit tests the `v0.2.0` Suzuki S3 claim against the released theorem
statements, their explicit inputs, import boundary, computational trust
boundary, and stated limitations. It does not audit the open positive side of
the Riemann Hypothesis.

## Claim Under Review

The release claims a checked experimental compact-window source theorem:

```text
G_a >= (1/400000) K_a
```

on Suzuki's exact zero-mean interval source space for every
`a in I_0 = [log(2)/2, suzukiProjectAStar]`, together with quantitative
source-seminorm estimates for any solution of the declared shifted Fredholm
equation and identification of the compact-support localized Weil form and its
associated source operator.

It does not claim X19B solution existence, a normalized Fredholm family, S4,
all-radius nondegeneracy, global Weil positivity, or RH.

## Theorem Identity And Premises

The main source-form inequality is
`suzukiDF6F_interval_source_coercive` in
`SuzukiYoshidaDifferentialCoreDensity.lean`. Its statement retains two inputs:

- `SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar`; and
- `SuzukiEquation25SourceIdentityAt suzukiProjectAStar`.

The released tree contains checked inhabitants:

- `suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff`; and
- `suzukiEquation25SourceIdentityAt_proved`.

`RELEASE/SuzukiS3AxiomAudit.lean` applies those inhabitants to the source-form
inequality and to both uniform Fredholm forcing estimates. The release does
not erase the premises from historical theorem signatures; it demonstrates
their checked composition.

## Domain And Normalization

The interval carrier is `SuzukiFiniteIntervalZeroMeanL2 a`. The left form is
defined through Suzuki's positive inverse-Neumann operator `K_a`, and the right
form through source `G_a`. The DF6E bridge uses literal zero extension from the
smaller interval into the frozen endpoint and preserves the physical `L2`
vector. The result is not an estimate on an unidentified ambient space.

The checked coefficient is exactly `1/400000`. The release does not present it
as a sharp spectral bottom. S1 separately records `E >= 5I` and
`F >= (2/5)E`; B3R and B4 consume the residual/cross estimates before DF6E and
DF6F transport the result to the source surface.

## Source Form And Operator

The compact-support Burnol/Guinand--Weil source package is supplied by
`suzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions_proved`. The literal
localized pairing is identified with the corrected completed form on the
smooth core, and `exists_suzukiSourceAaSmoothCoreFormApproximation` proves that
the smooth core is a core for the shifted form topology.

Suzuki's `A_a` is characterized by the associated closed form. The release
uses `suzukiYoshidaCorrectedFormAssociatedOperator_is_sourceAa`; it does not
assert equality with a separately constructed operator having an unchecked
domain.

The closed-form theorem deliberately does not claim absolute convergence of
the literal zero series for every pair of completed-domain vectors.

## Solution-Estimate Boundary

`suzukiDF6F_sourceKSeminorm_solution_le` assumes both a source-dual forcing
bound and the equation

```text
S_(a,lambda) u = f.
```

The plus/minus Fredholm specializations retain their corresponding solution
equations. Therefore the release supports a quantitative estimate for an
admitted solution, not an existence theorem, a surjective resolvent theorem,
or an ambient bounded inverse for compact `G_a`.

This distinction is the live X19B gap.

## Computational And Import Boundary

The endpoint certificate is exact rational Lean data. Finite certificate
decisions use the declared compiler-backed `native_decide` boundary. Numerical
generators and scouts are support artifacts, not proof objects by themselves.

Production `Basic.lean` does not import `RiemannHypothesisProject/Experiments`.
The S3 source is published as an experimental namespace and changes no
production theorem score or claim.

## Remaining Open Work

X19B must still construct a type-correct fixed-gauge normalized Fredholm family
and prove uniform compact-`z` and parameter continuity/precompactness bounds on
one explicit compact window. S4 then requires a separate publication audit.

The all-radius statement `ker(G_a) = {0}` for every `a > 0` is the RH-hard
global endpoint. It is neither assumed nor proved here.

## Verdict

The S3 milestone survives the scoped audit with its compact interval, source
space, coefficient, solution-equation premises, and experimental boundary
visible. The release claim is therefore `VERIFIED_WITH_SCOPE`.

Any description of this release as an RH proof, a global positivity theorem,
an X19B solution-existence theorem, or an all-radius nondegeneracy theorem is
false.
