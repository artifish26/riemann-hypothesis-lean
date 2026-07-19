# Publication Claims

This inventory describes the production theorem scope of the curated public
release. Development history is intentionally not part of the release.

**The repository does not prove the Riemann Hypothesis.** It proves several
unconditional upstream theorems, criterion equivalences, and positivity on one
fixed support class. The global positivity statement on the right-hand side of
the Li/Weil criteria remains open and RH-equivalent.

## Release identity

This inventory is published in documentation release `v0.1.1` and is bound to
the production-theorem baseline below. The production Lean sources are
unchanged from `v0.1.0`; subsequent changes before `v0.1.1` affect repository
security and documentation only.

| Field | Release value |
| --- | --- |
| Production-theorem tag | `v0.1.0` |
| Production-theorem commit | `b215f8e9ca8e3db16e0d5902f97f8f7de537a92c` |
| Documentation release | `v0.1.1` |
| Release date | `2026-07-19` |
| Lean toolchain | `leanprover/lean4:v4.31.0` |
| Mathlib revision | `db127794c79fdeb86f6b0cf6ff2c804026fbaff1` |
| Tagged clean build | 3,904 jobs; [successful `v0.1.0` run](https://github.com/artifish26/riemann-hypothesis-lean/actions/runs/29702361253) |

The immutable `v0.1.1` GitHub release binds this inventory to its own release
commit. The explicit commit above identifies the theorem-source baseline whose
claims are inventoried here.

## Status summary

| Result | Status | Exact scope |
| --- | --- | --- |
| Multiplicity-aware zero count `O(T log T)` | Proved | Canonical positive-ordinate completed-zeta zero count with analytic multiplicity |
| Polynomial-Gaussian zero summability | Proved | Selected completed-zeta polynomial-Gaussian source family |
| Guinand-Weil formula | Proved | Real-even polynomial-Gaussian source under the fixed project Fourier convention |
| Full Li criterion | Proved equivalence | All positive-index, full multiplicity-aware zeta Li coefficients |
| Burnol positivity | Proved with restricted scope | One existentially fixed symmetric support interval |
| PNT cutoff covariance | Proved | Regularised Li cutoff covariance from the pinned PrimeNumberTheoremAnd source |
| Global Li/Weil positivity | Open | Criterion-determining global class; RH-equivalent |

The classifications below use the project's four theorem roles: source
theorem, normalisation/window/cutoff bridge, elementary cleanup estimate, and
endpoint assembly.

## 1. Multiplicity-aware zero counting

- **Claim:** the canonical positive-ordinate zeta-zero count, with analytic
  multiplicity, is `O(T log T)` in a regularised global form.
- **Lean declaration:**
  `RiemannHypothesisProject.ComplexCompactExhaustion.exists_unconditional_canonicalMultiplicityCount_mulLog_bound`.
- **File:**
  `RiemannHypothesisProject/RiemannVonMangoldt/RiemannXiJensen.lean`.
- **Exact scope:** there exists `C > 0` such that for every real `T >= 0`,
  `canonicalPositiveOrdinateZetaZeroMultiplicityCount T` is at most
  `C * (T + 1) * (log (T + 1) + 1)`.
- **Explicit assumptions:** none.
- **Classification:** endpoint assembly, consuming the proved xi-growth source
  theorem and multiplicity/window normalisation bridges.
- **Mathematical provenance:** the classical theta-Mellin representation of
  completed zeta, Jensen divisor counting, and the analytic-order
  interpretation of zero multiplicity. This is not the sharp
  Riemann-von-Mangoldt asymptotic or a Bellotti-Wong/HSW explicit estimate.
- **Release status:** checked with the scope stated above.

The associated inverse-square consumer is
`RiemannHypothesisProject.ComplexCompactExhaustion.unconditional_positiveOrdinateZetaZero_multiplicityClampedInverseSquare_summable`
in the same file. It has no explicit assumptions and retains analytic
multiplicity.

## 2. Polynomial-Gaussian zero-side summability

- **Claim:** the actual completed-zeta polynomial-Gaussian zero side is
  unconditionally absolutely summable with analytic multiplicity.
- **Lean declaration:**
  `RiemannHypothesisProject.ComplexCompactExhaustion.summable_norm_multiplicityPolynomialGaussianCompletedZetaZeroWeight_unconditional`.
- **File:**
  `RiemannHypothesisProject/GuinandWeilConcrete/UnconditionalMultiplicityPolynomialGaussianZeroSide.lean`.
- **Exact scope:** every `p : Polynomial Complex` in the selected
  polynomial-Gaussian source family.
- **Explicit assumptions:** only the polynomial parameter `p`; there is no
  counting, decay, RH, simplicity, or formula premise.
- **Classification:** endpoint assembly, consuming proved
  polynomial-Gaussian strip decay, xi/Jensen multiplicity growth, conjugation,
  finite real-axis cleanup, and summable-series bridges.
- **Mathematical provenance:** Gaussian decay plus multiplicity-aware dyadic
  zero counting; the receiving formula theorem is normalised against the
  Guinand-Weil source class below.
- **Release status:** checked with the scope stated above.

## 3. Selected Guinand-Weil formula

- **Claim:** the multiplicity-correct Guinand-Weil formula holds
  unconditionally for the selected real-even polynomial-Gaussian source.
- **Lean declaration:**
  `RiemannHypothesisProject.ComplexCompactExhaustion.guinandWeilPiEvenPolynomialGaussianLiteratureFormula`.
- **File:**
  `RiemannHypothesisProject/GuinandWeilConcrete/PolynomialGaussianFormulaIdentity.lean`.
- **Exact scope:** every `p : Polynomial Real`, through
  `guinandWeilPiEvenPolynomialGaussian p` and the fixed project Fourier
  convention.
- **Explicit assumptions:** only the polynomial parameter `p`; no RH,
  zero-simplicity, contour-identity, or error-decay premise remains in the
  endpoint.
- **Role:** primary analytic endpoint.
- **Project classification:** source theorem, assembled from the finite
  weighted xi rectangle identity, right-vertical prime/pole/Gamma evaluation,
  good-height horizontal decay, and cofinal multiplicity-normalised zero sums.
- **Primary source anchor:** A. P. Guinand, *Fourier Reciprocities and the
  Riemann Zeta-Function*, DOI
  [10.1112/plms/s2-51.6.401](https://doi.org/10.1112/plms/s2-51.6.401).
- **Release status:** checked with the scope stated above.

The continuous residual consumer is
`RiemannHypothesisProject.exists_evenPolynomialGaussianZeroSide_tendsto_continuousResidual`
in `PolynomialGaussianDensityBridge.lean`. It is a normalisation/density bridge:
it explicitly assumes a continuous real-linear residual and its equality with
the checked literature residual on the source family. It does not assume
positivity.

## 4. Full Li criterion

- **Claim:** project RH, and equivalently Mathlib's `RiemannHypothesis`, is
  equivalent to nonnegativity of every positive-index full multiplicity-aware
  zeta Li coefficient.
- **Lean declarations:**
  `RiemannHypothesisProject.ComplexCompactExhaustion.RHStatement_iff_fullZetaLiCoefficient_nonneg`
  and
  `RiemannHypothesisProject.ComplexCompactExhaustion.mathlib_RH_iff_fullZetaLiCoefficient_nonneg`.
- **File:**
  `RiemannHypothesisProject/LiCriterion/ZetaBombieriLagariasCriterion.lean`.
- **Exact scope:** `forall n : Nat, 0 < n -> 0 <= fullZetaLiCoefficient n`.
- **Explicit assumptions:** none.
- **Classification:** endpoint assembly, consuming the formalised
  Bombieri-Lagarias zero-multiset implication, zeta multiplicity and reflection,
  star convergence, and coefficient normalisation.
- **Primary source anchors:** E. Bombieri and J. C. Lagarias, *Complements to
  Li's Criterion for the Riemann Hypothesis*, DOI
  [10.1006/jnth.1999.2392](https://doi.org/10.1006/jnth.1999.2392), and J. C.
  Lagarias, *Li Coefficients for Automorphic L-Functions*,
  [arXiv:math/0404394](https://arxiv.org/abs/math/0404394).
- **Release status:** checked as an equivalence theorem, not as a proof of
  global nonnegativity.

This is an equivalence theorem. The repository does not prove its global
nonnegativity right-hand side.

## 5. Fixed-support Burnol positivity

- **Claim:** there is one fixed positive support radius on which the actual
  project-normalised prime/pole/Gamma residual is unconditionally identified
  with Burnol's local spectral form and is nonnegative.
- **Lean declaration:**
  `RiemannHypothesisProject.SchwartzLineTestFunction.exists_burnolFixedSupport_guinandWeilBurnolLiteratureResidual_nonneg`.
- **File:**
  `RiemannHypothesisProject/WeilPositivity/BurnolFormulaClosure.lean`.
- **Exact scope:** every Schwartz line test supported in one existentially
  fixed symmetric interval `[-r, r]`.
- **Explicit assumptions:** none at the residual endpoint. The support
  restriction remains in the conclusion's quantified implication.
- **Classification:** endpoint assembly, combining the unconditional Binet
  source closure, Burnol local source theorem, Fourier/support normalisation,
  and the exact `2 * pi` residual identification.
- **Primary source anchor:** J.-F. Burnol, *Sur les Formules Explicites I:
  analyse invariante*,
  [arXiv:math/0101068](https://arxiv.org/abs/math/0101068).
- **Release status:** checked with the fixed-support restriction retained.

The zero-side sibling
`RiemannHypothesisProject.SchwartzLineTestFunction.exists_burnolFixedSupport_guinandWeilBurnolLiteratureZeroSide_nonneg`
retains `BurnolGuinandWeilSourceAssumptions g`, including the entire extension,
absolute zero-side summability, and source formula. It must not be described as
an assumption-free global zero-side theorem.

## 6. Independent PNT cutoff closure

- **Claim:** the regularised Li cutoff covariance converges unconditionally
  from the pinned PrimeNumberTheoremAnd source.
- **Lean declaration:**
  `RiemannHypothesisProject.ComplexCompactExhaustion.tendsto_liCutoffCovariance_unconditional`.
- **File:**
  `RiemannHypothesisProject/LiCriterion/CutoffCovarianceUnconditional.lean`.
- **Explicit assumptions:** only the natural index parameter.
- **Classification:** endpoint assembly, consuming the proved
  Bombieri-Lagarias prime-moment asymptotic and cutoff normalisation.
- **Source anchor:** the pinned
  [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
  formalisation and Bombieri-Lagarias source above.
- **Audit verdict:** source-closure `SC100`; the lane is independent of the
  fixed-support Burnol formula-identification lane.

## 7. Open global statement

- **Claim status:** open and RH-hard.
- **Checked criterion:**
  `RiemannHypothesisProject.ComplexCompactExhaustion.mathlib_RH_iff_fullZetaLiCoefficient_nonneg`.
- **Open obligation:** unconditional global nonnegativity of all full Li
  coefficients, equivalently global Weil positivity on a criterion-determining
  class.
- **Classification:** open endpoint target.
- **Release status:** open and RH-equivalent.

Nothing in this release changes this status.

## Import and axiom boundary

`RiemannHypothesisProject/Basic.lean` imports the production surface.
`RELEASE/PublicationAxiomAudit.lean` is a repeatable, non-production consumer
that prints the axioms of the representative endpoints listed here. At the
production-theorem release commit, those endpoints report only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

This audit mechanically records the Lean dependency boundary of the selected
declarations. It does not by itself establish that every formal definition,
normalisation, or theorem statement is semantically faithful to the cited
mathematics; that remains a matter for mathematical review.

## External reviewer checklist

The most valuable bounded review targets are:

1. **Xi/Jensen growth and multiplicity bridge.** Review
   `exists_unconditional_canonicalMultiplicityCount_mulLog_bound` in
   `RiemannHypothesisProject/RiemannVonMangoldt/RiemannXiJensen.lean`, including
   the xi-growth input, Jensen divisor count, and analytic-order multiplicity
   normalisation.
2. **Guinand-Weil Fourier and Gamma normalisation.** Review
   `guinandWeilPiEvenPolynomialGaussianLiteratureFormula` in
   `RiemannHypothesisProject/GuinandWeilConcrete/PolynomialGaussianFormulaIdentity.lean`
   together with `LiteratureNormalization.lean`, especially the Fourier
   convention and prime, pole, and Gamma constants.
3. **Li starred convergence and Bombieri-Lagarias instantiation.** Review
   `RHStatement_iff_fullZetaLiCoefficient_nonneg` in
   `RiemannHypothesisProject/LiCriterion/ZetaBombieriLagariasCriterion.lean`
   together with `StarConvergence.lean`, including multiplicity expansion and
   the passage to full Li coefficients.
4. **Burnol support and residual identification.** Review
   `exists_burnolFixedSupport_guinandWeilBurnolLiteratureResidual_nonneg` in
   `RiemannHypothesisProject/WeilPositivity/BurnolFormulaClosure.lean` and
   `burnolLocalSpectralQuadraticForm_eq_two_pi_mul_guinandWeilBurnolLiteratureResidualSide`
   in `BurnolFormulaIdentification.lean`, with particular attention to the
   fixed support class and exact `2 * pi` factor.
