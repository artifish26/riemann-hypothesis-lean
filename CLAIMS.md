# Publication Claims

This inventory describes the checked production theorem scope, the separately
labelled experimental Suzuki S4 scope, and the non-Lean RIG0--RIG1 research
result in the curated public release. Development history is intentionally not
part of the release.

**The repository does not prove the Riemann Hypothesis.** It proves several
unconditional upstream theorems, criterion equivalences, positivity on one
fixed support class, infinitely many actual nontrivial critical-line zeros,
and a compact-window experimental Suzuki theorem package. The global
positivity statement on the right-hand side of the Li/Weil criteria remains
open and RH-equivalent.

## Release identity

This inventory is published in release `v0.3.0`. The tag binds the curated
source snapshot, claim inventory, axiom audits, adversarial report, and pinned
dependency graph. The development source snapshot is the post-RIG1 closeout
listed below; private working documents are not included.

| Field | Release value |
| --- | --- |
| Publication release | `v0.3.0` |
| Development source snapshot | `6bbd1d4` (`docs: consolidate RIG1 closeout status`) |
| Release date | `2026-08-25` |
| Lean toolchain | `leanprover/lean4:v4.32.2` |
| Mathlib revision | `905b95818eb32af7874a58b427f50c1711a5e96c` |
| PrimeNumberTheoremAnd revision | `6a380f0c4658c04a420a9eb00b1ed62a1e3fde01` |
| Release verification | Development full build; release production, S4, and adversarial audits; independent pull-request and tagged workflows; see `REPRODUCIBILITY.md` |

The immutable `v0.3.0` GitHub tag binds this inventory to its release commit.
The development commit identifies the upstream theorem-source state from
which the curated snapshot was produced.

## Status summary

| Result | Status | Exact scope |
| --- | --- | --- |
| Multiplicity-aware zero count `O(T log T)` | Proved | Canonical positive-ordinate completed-zeta zero count with analytic multiplicity |
| Polynomial-Gaussian zero summability | Proved | Selected completed-zeta polynomial-Gaussian source family |
| Guinand-Weil formula | Proved | Real-even polynomial-Gaussian source under the fixed project Fourier convention |
| Full Li criterion | Proved equivalence | All positive-index, full multiplicity-aware zeta Li coefficients |
| Burnol positivity | Proved with restricted scope | One existentially fixed symmetric support interval |
| PNT cutoff covariance | Proved | Regularised Li cutoff covariance from the pinned PrimeNumberTheoremAnd source |
| Infinitely many critical-line zeros | Proved | Actual nontrivial zeta-zero set on `Re(s)=1/2` is infinite |
| Suzuki S3 source theorem | Experimental, checked | Compact-window coercivity, compact-support localized Weil form, smooth form core, and associated source operator |
| Suzuki X19B / S4 | Experimental, checked | Source-package-free solution family on the named compact radius window and closed complex unit disk, with uniform bound, Lipschitz dependence, compact image, and radius continuity from below |
| RIG0--RIG1 | Paper result, audited, not Lean | No objectwise bad-zero transport; quantitative annular escape for a hypothetical full first-crossing kernel |
| RIG2 / all-radius Suzuki continuation | Not admitted / frozen | No scalar or uniformly finite-dimensional reduction of the annular complement |
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

## 7. Infinitely many critical-line zeros

- **Claim:** the set of actual nontrivial zeta zeros on the critical line is
  infinite.
- **Lean declaration:**
  `RiemannHypothesisProject.Hardy.nontrivial_criticalLine_zetaZero_set_infinite`.
- **File:**
  `RiemannHypothesisProject/Hardy/CriticalLineZeroInfinitude.lean`.
- **Exact scope:**
  `{s : Complex | IsNontrivialZetaZero s and IsCriticalLine s}.Infinite`.
- **Explicit assumptions:** none.
- **Classification:** endpoint assembly consuming the selected Hardy
  first-approximation, Stirling-phase, oscillatory-integral, normalization,
  lower-bound, and upper-bound theorem chain.
- **Release status:** production, checked.

The proof obtains a contradiction from finite positive Hardy zero heights:
continuity then forces constant sign on every sufficiently late dyadic
interval, identifying its signed and absolute integrals, while the checked
lower and upper estimates become incompatible at a sufficiently large height.
The terminal transport gives actual nontrivial zeta zeros and uses injectivity
of the critical-line parametrization.

This theorem does not say every nontrivial zero lies on the critical line and
does not imply RH. Full details are in `RELEASE/HARDY.md`.

## 8. Experimental Suzuki S3 and S4 milestones

The cumulative S3 source theorem remains checked:

- `suzukiDF6F_interval_source_coercive` proves
  `G_a >= (1/400000) K_a` on
  `SuzukiDF6EInterval = [log(2)/2, suzukiProjectAStar]` after applying the
  checked source inhabitants;
- `suzukiSourceLocalizedWeilPairing_smoothCore_eq_correctedCompleteForm` and
  `exists_suzukiSourceAaSmoothCoreFormApproximation` identify the localized
  source form and its smooth core; and
- `suzukiYoshidaCorrectedFormAssociatedOperator_is_sourceAa` identifies the
  associated source operator.

S4 closes the bounded-window X19B work on that genuine source surface.

- **Publication module:**
  `RiemannHypothesisProject/Experiments/M100/SuzukiYoshidaS4Publication.lean`.
- **Radius scope:** `a` belongs to `SuzukiDF6EInterval`.
- **Spectral scope:** `w : Complex` satisfies `||w|| <= 1`.
- **Source packages:** the publication wrapper internally instantiates
  `suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff` and
  `suzukiEquation25SourceIdentityAt_proved`; no source-package argument remains
  on the public S4 declarations.
- **Release status:** experimental, checked, compact-window only.

The principal S4 declarations are:

- `suzukiS4CompactWindowSolution`;
- `suzukiS4CompactWindowSolution_norm_le_fourThousand`, with uniform
  source-energy bound `4000`;
- `suzukiS4CompactWindowSolutionMap_lipschitz`;
- `suzukiS4CompactWindowSolutionMap_isCompact_range`; and
- `eventually_suzukiS4CompactWindowSolution_close_from_below`, after canonical
  completion transport at interior radii.

These results live in Suzuki's genuine shifted source-energy completion. They
do not assert an interval-`L2` representative for every completion vector,
all-radius nondegeneracy, a completed-zeta limit, global Weil positivity, or
RH. Full details are in `RELEASE/SUZUKI_S4.md`.

## 9. RIG0--RIG1 paper result

This part of the release is documentation, not checked Lean.

RIG0 found no objectwise invariant-preserving transport from one prescribed
off-critical zero to one Suzuki crossing mode. It did establish, on the exact
completed generalized source carrier, that the canonical annular projection
is injective on the full first-crossing kernel.

RIG1 strengthened this to the paper theorem
`FirstCrossingKernelQuantitativeAnnularEscape`. For a hypothetical first
crossing `a0`, shift `sigma < 0`, earlier radius `0 < b < a0`, and every
crossing-kernel vector `u`, it gives

```text
||(I-Pi_b)u||_sigma^2
  >= lambda(b)/(lambda(b)-sigma) * ||u||_sigma^2.
```

The theorem permits a nonzero crossing kernel and its constant may collapse as
`b` approaches `a0`. The canonical annular complement remains uncontrolled
and generally infinite-dimensional, so RIG2 was not admitted. No Lean
declaration in this release bears the paper theorem's name. See
`RELEASE/RIGIDITY_RIG1.md`.

## 10. Open global statements

- **Checked criterion:**
  `RiemannHypothesisProject.ComplexCompactExhaustion.mathlib_RH_iff_fullZetaLiCoefficient_nonneg`.
- **Open obligation:** unconditional global nonnegativity of all full Li
  coefficients, equivalently global Weil positivity on a
  criterion-determining class.
- **Classification:** open endpoint target.
- **Release status:** open and RH-equivalent.

S4 and RIG1 do not change this status. The Suzuki programme is frozen at its
compact-window theorem because no named all-radius propagation or exact
crossing-exclusion mechanism has been established.

## Import and axiom boundary

`RiemannHypothesisProject/Basic.lean` imports the production surface, including
the Hardy endpoint, but no experimental module.
`RELEASE/PublicationAxiomAudit.lean` prints the axioms of representative
production endpoints. `RELEASE/SuzukiS4AxiomAudit.lean` separately checks the
experimental S4 wrappers. The production audit reports only:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

The Suzuki certificate chain additionally retains the declared
compiler-backed `native_decide` trust boundary for exact finite decision
problems. The S4 wrappers introduce no new project axiom or source package.
The precise names emitted by the tagged audits are part of the release
verification record; see `RELEASE/SUZUKI_S4.md`.

These audits mechanically record Lean dependency boundaries. They do not by
themselves establish that every formal definition, normalization, or theorem
statement is semantically faithful to the cited mathematics. RIG1 is outside
this axiom boundary because it is explicitly a paper-only theorem.

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
5. **Hardy analytic chain and final transport.** Review
   `nontrivial_criticalLine_zetaZero_set_infinite` in
   `RiemannHypothesisProject/Hardy/CriticalLineZeroInfinitude.lean` together
   with `LowerIntegralBound.lean` and `UpperIntegralBound.lean`, especially
   the first-approximation error, phase normalization, and passage from Hardy
   zeros to actual nontrivial zeta zeros.
6. **Suzuki S4 carrier and parameter bounds.** Review
   `SuzukiYoshidaS4Publication.lean` and
   `SuzukiYoshidaX19BBoundedWindowSolutions.lean`, especially the completed
   source carrier, source-package instantiation, radius interval, complex unit
   disk, and directed completion transport.
7. **RIG1 paper derivation.** Review `RELEASE/RIGIDITY_RIG1.md` independently
   of Lean, with particular attention to the completed source domain, the
   `gbar`/`kbar` block identities, and the constant
   `lambda(b)/(lambda(b)-sigma)`.
