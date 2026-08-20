# Suzuki S3 Release Ledger

Release: `v0.2.0`

Milestone: `S3 REACHED`

Source snapshot: development commit `c858f86` (`Close DF6F analytic source
bridge`), August 20, 2026.

Programme consequence: `X19B READY / NOT STARTED`; `S4 NOT REACHED`.

Production consequence: none. Formula-side residual positivity remains at the
carried-forward `90%` engineering/mathematics status, and this release does
not prove global Weil positivity or the Riemann Hypothesis.

## Exact Scope

S3 closes the source-identification programme over

```text
I_0 = [log(2)/2, suzukiProjectAStar].
```

The checked dependency chain is

```text
S1: B3Q-G + B3F-E + B3F-F
  -> S2: B3R-E + B3R + B4
  -> DF6E: interval project-form coercivity
  -> DF6F: source form, operator, norm, and source-formula identification
  -> S3 reached
```

All S3 declarations remain in the experimental namespace
`RiemannHypothesisProject.Experiments.M100`. The aggregate production import
does not import them.

## Theorem And Assumption Ledger

| Role | Declaration | Exact result or premise |
|---|---|---|
| B2S source closure | `suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff` | Supplies the periodic-exponential graph-core source for every radius by explicit smooth boundary cutoffs. No source premise remains. |
| Equation (2.5) source closure | `suzukiEquation25SourceIdentityAt_proved` | Supplies the equation-(2.5) source identity at every positive radius. No equation-(2.5) premise remains at the inhabitant. |
| Component assembly | `suzukiYoshidaEquation25EndpointKernelEvaluation` | Assembles the eight comparison, prime, Gamma, pole, and diagonal component families at the frozen endpoint. Its historical API keeps the two source packages explicit. |
| Comparison energy | `suzukiDF6D5B3FE_even_five_mul_norm_sq_le`, `suzukiDF6D5B3FE_odd_five_mul_norm_sq_le` | `E >= 5I` on the exact matching parity-far domains. |
| Actual form order | `suzukiDF6D5B3FF_even_complete_ge_two_fifths`, `suzukiDF6D5B3FF_odd_complete_ge_two_fifths` | `F >= (2/5)E`; reciprocal `E <= (5/2)F` declarations are checked in the same module. |
| Fixed endpoint | `suzukiDF6D5B4_fixedEndpoint_coercive` | `(1/400000) * ||v||_L2^2 <= Re F(v,v)` on the whole closed endpoint domain, with the two historical source inputs explicit. |
| Window bridge | `suzukiDF6E_interval_coercive` | Literal zero extension transfers the coefficient to every radius in `I_0`; the historical source inputs remain explicit. |
| Genuine source form | `suzukiDF6F_interval_source_coercive` | `G_a >= (1/400000) K_a` on the exact zero-mean interval source space throughout `I_0`, with the two source inputs explicit and supplied by the first two declarations above. |
| Quantitative solution estimate | `suzukiDF6F_sourceKSeminorm_solution_le` | Any admitted solution below the checked shift satisfies `||u||_K <= C / (1/400000 - lambda)`. The solution equation is an explicit premise. |
| Uniform forcing estimates | `suzukiDF6F_fredholmPlus_solution_sourceKSeminorm_le_five`, `suzukiDF6F_fredholmMinus_solution_sourceKSeminorm_le_five` | The two projected Fredholm forcing families use one uniform rational source-dual bound on `I_0`; the corresponding solution equation remains a premise. |
| Compact-support source formula | `suzukiSourceAaSmoothCoreBurnolGuinandWeilAssumptions_proved` | Supplies the Burnol/Guinand--Weil source package for every smooth-core input without a replacement source assumption. |
| Closed-form equality | `suzukiSourceLocalizedWeilPairing_smoothCore_eq_correctedCompleteForm` | Identifies the literal localized smooth-core Weil pairing with the corrected completed form. |
| Form core | `exists_suzukiSourceAaSmoothCoreFormApproximation` | Every completed-domain vector has a smooth-core approximation in both the existing completion and shifted form norm. |
| Associated operator | `suzukiYoshidaCorrectedFormAssociatedOperator_is_sourceAa` | The corrected-form associated operator satisfies Suzuki's defining associated-form representation; uniqueness identifies any operator with that representation. |

`RELEASE/SuzukiS3AxiomAudit.lean` checks the exact declarations and also checks
the composition of the two source inhabitants into the interval coercivity
and uniform forcing estimates.

## Computational Trust Boundary

The frozen endpoint certificate is represented by exact rational Lean data.
The final certificate chain uses `native_decide` for declared finite decision
problems. This is a compiler-backed computational trust boundary in addition
to Lean's ordinary logical foundations. The release includes the certificate
data and supporting generators, but generated numerical output is not itself
a theorem until consumed by the checked Lean declarations.

The analytic DF6F closeout rebuilt eight live targets together (`5375` jobs)
and passed whole-word placeholder, production-import, whitespace, and diff
checks. Release `v0.2.0` additionally requires the clean tagged build and both
release axiom audits defined in this repository.

## Limitations

S3 does not prove:

- existence or uniqueness of the normalized X19B Fredholm solutions;
- a frozen gauge and normalization theorem for that family;
- uniform compact-`z` bounds or parameter precompactness;
- coercivity outside `I_0`;
- a nonzero global limit identified with a completed-zeta quotient;
- global Li/Weil positivity; or
- the Riemann Hypothesis.

The source-norm results are estimates for solutions satisfying an explicit
equation; they are not ambient bounded-inverse theorems for the compact
operator `G_a`.

## Next Release Gate

X19B must construct the actual normalized Fredholm family with one
predeclared compact window, shift, and gauge, then prove the required uniform
solution, compact-`z`, and continuity or precompactness bounds. S4 additionally
requires a separate publication audit.

The all-radius no-degeneracy statement is not X19B. It remains the post-S4
`RH_HARD` endpoint and is not a conclusion or assumption of this release.
