# A4 Finding: Burnol Local Form Is Not Connected To The Formula - 2026-07-15

Status: `RESOLVED`

Finding: `ADV-POS-003`

Severity: `P1`

## Claimed Edge

`FORMULA_POSITIVITY_PLAN.md` marks every Q7 item complete, including:

```text
Prove compatibility with Q6.
```

The surrounding production status describes M90 as formula-side residual
positivity through Burnol's fixed-support theorem. The relevant checked
endpoints are:

- `zetaWeilPolynomialGaussian_formula_on_autocorrelation`; and
- `exists_burnolFixedSupport_spectral_nonneg_of_binet`.

## Smallest Failing Chain

The M80 endpoint proves, for the special base
`zetaWeilPolynomialGaussianBase q`, that its Fourier autocorrelation is the
selected full-scale polynomial-Gaussian source and that the actual
multiplicity-aware zeta Weil pairing equals the checked literature residual.

The M90 Burnol endpoint instead concludes

```text
0 <= burnolLocalSpectralQuadraticForm g
```

for an arbitrary Schwartz base `g` supported in one fixed interval, under the
explicit premise

```text
hBinet : BennettGammaBinetDigammaFormula.
```

Here

```text
burnolLocalSpectralQuadraticForm g =
  integral t, burnolLocalCoefficient t * |Fourier g t|^2.
```

The only theorem named as a compatibility result is
`burnolLocalSpectralQuadraticForm_eq_fourierAutocorrelation`. It rewrites the
same integrand as

```text
integral t, burnolLocalCoefficient t * Re (fourierAutocorrelation g t).
```

It does not identify that integral with any of:

- `guinandWeilPiPolynomialGaussianLiteratureResidualSide`;
- `zetaWeilPairing`;
- `SchwartzWeilQuadraticFormData.quadraticForm`; or
- an actual prime/pole/Gamma formula functional on the Burnol support class.

Repository-wide reference search finds
`burnolLocalSpectralQuadraticForm` only inside `BurnolLocalSupport.lean`, its
facades, and documentation. `BurnolLocalSupport.lean` imports the Burnol local
coefficient and Fourier-autocorrelation modules, but neither the Guinand-Weil
formula nor `ZetaPolynomialGaussianFormulaBridge`.

The two checked test classes also differ. M80's formula theorem covers the
inverse-Fourier polynomial-Gaussian bases. The Burnol theorem covers arbitrary
compactly supported Schwartz bases. No checked theorem transports the formula
identity between those classes or proves the explicit formula directly on the
Burnol class.

## Verdict

The local spectral positivity theorem is a substantive conditional theorem;
this finding does not call it a toy or dispute its internal cosine/support
argument. But Lean does not currently prove that its nonnegative quantity is
the actual zeta formula residual or zero pairing advertised by the Q6-to-Q7
edge.

At discovery, therefore:

- Q7 item 6 is `UNVERIFIED`;
- the description of all seven Q7 items as complete is a
  `DOCUMENTATION_CONFLICT`;
- `ADV-POS-M90` cannot receive a final verified verdict while this bridge is
  absent; and
- the M90 mathematics score requires review after the finding is resolved.

Per the adversarial audit rules, opening this finding alone did not
mechanically change a percentage. The completed theorem/signature review and
production reconciliation below did.

## Resolution Applied

The project selected the narrow-claim resolution on July 15, 2026. The
available theorem family cannot supply the exact bridge by a normalization
adapter:

- the checked formula theorem is specialized to inverse-Fourier
  polynomial-Gaussian bases;
- the Burnol theorem accepts arbitrary compactly supported Schwartz bases; and
- the repository has no generic prime/pole/Gamma literature residual in the
  same normalization on the Burnol class.

Production documentation now describes the Burnol result only as a
source-local spectral-form theorem, with its formerly explicit Binet premise
subsequently discharged. Q7 formula compatibility and
M90 are marked open, architecture remains `90%`, and positivity mathematics is
corrected from `90%` to `80%`. The exact mathematical resolution target is
still a theorem identifying `burnolLocalSpectralQuadraticForm g` with the
actual project-normalized Guinand-Weil residual or zeta Weil pairing for every
base in the fixed-support class, with prime, pole, Gamma, Fourier, support, and
source assumptions visible.

Closing the separate Binet source premise was necessary for an unconditional
Burnol endpoint, but it does not by itself close this formula-identification
gap.

Later on July 15, `bennettGammaBinetDigammaFormula` and the unconditional
additive/multiplicative Burnol wrappers were checked. Their focused builds pass
and their endpoint axiom reports contain only `propext`, `Classical.choice`,
and `Quot.sound`. This closed the Binet premise exactly as predicted, while the
formula-identification edge remained open at that checkpoint.

## Mathematical Follow-Up

The gate was subsequently reopened and the missing theorem chain was proved.
`BurnolFormulaKernel` freezes the direct pole and residual normalizations.
`BurnolFormulaBridge` defines the Burnol Fourier-Laplace source, explicit
prime/pole/Gamma residual, and multiplicity-aware zero side; its strict support
lemmas kill every prime-power contribution. `BurnolFormulaIdentification`
proves the translated Cauchy pole identity, the exact Gamma normalization, and

```text
burnolLocalSpectralQuadraticForm g
  = 2 * pi * guinandWeilBurnolLiteratureResidualSide g.
```

The corresponding zero-side equality consumes the explicit
`BurnolGuinandWeilSourceAssumptions g`: entire extension, absolute zero-side
summability, and the source formula. `BurnolFormulaClosure` combines the direct
residual equality with the unconditional Binet-backed fixed-support theorem.
Thus `ADV-POS-003` is mathematically closed and M90 is crossed at 90% with
scope: one fixed strict-support class, no density promotion, no PNT-moment
discharge, and no M100 claim.

## Verification

- `lake env lean ADVERSARIAL/A4BurnolFormulaBridgeAudit.lean`: `PASS` after the
  mathematical follow-up.
- The decisive residual bridge, zero-side bridge, unconditional residual
  endpoint, and source-conditional zero endpoint each report only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The production consumer is now `BurnolFormulaClosure`; it imports neither
  the separate prime-moment lane nor audit modules.
- No production proof was changed while opening the original finding; the
  later reopened-gate work supplied the missing mathematics explicitly.
- Focused builds of `RiemannVonMangoldt.Binet.DigammaFormula` and
  `WeilPositivity.BurnolLocalSupportUnconditional` later passed; their endpoint
  axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Finding Record

```text
ID: ADV-POS-003
Track: Formula-side residual positivity / Burnol fixed support
Severity: P1
Status: RESOLVED
Claim: Q7 Burnol fixed-support positivity is compatible with the checked Q6 formula/autocorrelation bridge
Lean declarations: burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureResidualSide; burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureZeroSide; exists_burnolFixedSupport_guinandWeilBurnolLiteratureResidual_nonneg; exists_burnolFixedSupport_guinandWeilBurnolLiteratureZeroSide_nonneg
Explicit premise at discovery: hBinet : BennettGammaBinetDigammaFormula; later discharged by the unconditional wrapper
Transitive source inputs: checked Binet theorem for unconditional local positivity; explicit BurnolGuinandWeilSourceAssumptions only for the zero-side endpoint
Consumer: BurnolFormulaClosure combines the exact direct residual equality with unconditional fixed-support positivity
Missing edge: closed -- exact equality to 2 * pi times the direct residual, and source-conditional equality to 2 * pi times the zero side
Attack: statement identity, consumer, import, source-class, formula-normalization, and circularity audit
Evidence: A4BurnolFormulaBridgeAudit.lean; focused module builds; theorem-body and axiom trace above
Verdict: VERIFIED_WITH_SCOPE -- the mathematical bridge is checked at M90 on one fixed strict-support class
Corrective action: SUPERSEDED -- the interim narrowing remains historical; the missing theorem chain is now implemented
Score consequence: restore -- positivity architecture remains 90%; positivity mathematics changes from 80% to 90%; M100 is unchanged
```
