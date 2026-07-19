import RiemannHypothesisProject.SchwartzRiemannWeilGlobalCriterion

/-!
# Decomposed Schwartz Riemann-Weil certificate data

The global certificate is the formal endpoint, but it is too large to be a
comfortable work unit. This file splits it into smaller data packages:

* explicit-formula data: zero side, prime side, pole side, gamma side, and the
  formula identity;
* positivity data: a quadratic form, its equality with the zero side, positivity,
  and the implication from positivity to the universal local RH statement.

These packages assemble into `SchwartzRiemannWeilGlobalCriterion`, so future
analytic work can proceed in smaller checked chunks.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/-- The explicit-formula part of the Schwartz Riemann-Weil route. -/
structure SchwartzRiemannWeilExplicitFormulaData where
  zeroSide : SchwartzRiemannWeilZeroSide
  primeSide : SchwartzLineTestFunction → ℝ
  poleSide : SchwartzLineTestFunction → ℝ
  gammaSide : SchwartzLineTestFunction → ℝ
  explicitFormula :
    ∀ f : SchwartzLineTestFunction,
      zeroSide.zeroSide f = primeSide f + poleSide f + gammaSide f

namespace SchwartzRiemannWeilExplicitFormulaData

/-- Convert explicit-formula data into the global Schwartz normalization. -/
noncomputable def toGlobalExplicitFormulaNormalization
    (data : SchwartzRiemannWeilExplicitFormulaData) :
    SchwartzGlobalExplicitFormulaNormalization :=
  data.zeroSide.toGlobalExplicitFormulaNormalization
    data.primeSide data.poleSide data.gammaSide data.explicitFormula

/-- The decomposed explicit formula identifies the zero side with the residual side. -/
theorem zeroSide_eq_residualSide
    (data : SchwartzRiemannWeilExplicitFormulaData)
    (f : SchwartzLineTestFunction) :
    data.zeroSide.zeroSide f =
      (data.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f := by
  rcases data with ⟨zeroSide, primeSide, poleSide, gammaSide, explicitFormula⟩
  simpa [toGlobalExplicitFormulaNormalization,
    SchwartzRiemannWeilZeroSide.toGlobalExplicitFormulaNormalization,
    SchwartzExplicitFormulaNormalization.residualSide]
    using explicitFormula f

/-- The residual side of the decomposed explicit formula is the packaged zero side. -/
theorem residualSide_eq_zeroSide
    (data : SchwartzRiemannWeilExplicitFormulaData)
    (f : SchwartzLineTestFunction) :
    (data.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f =
      data.zeroSide.zeroSide f :=
  (data.zeroSide_eq_residualSide f).symm

/-- Compact-exhaustion zero-window sums converge to the explicit formula's zero side. -/
theorem tendsto_windowZeroSide
    (data : SchwartzRiemannWeilExplicitFormulaData)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => data.zeroSide.windowZeroSide exhaustion n f)
      atTop (𝓝 (data.zeroSide.zeroSide f)) :=
  data.zeroSide.tendsto_windowZeroSide exhaustion f

/-- Compact-exhaustion zero-window sums converge to the residual explicit-formula side. -/
theorem tendsto_windowZeroSide_residualSide
    (data : SchwartzRiemannWeilExplicitFormulaData)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => data.zeroSide.windowZeroSide exhaustion n f)
      atTop
      (𝓝 (data.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization.residualSide f)) :=
  data.toGlobalExplicitFormulaNormalization
    |>.tendsto_windowZeroSide_residualSide exhaustion f

end SchwartzRiemannWeilExplicitFormulaData

/-- The positivity part of the Schwartz Riemann-Weil route, relative to explicit-formula data. -/
structure SchwartzRiemannWeilPositivityData
    (formulaData : SchwartzRiemannWeilExplicitFormulaData) where
  quadraticForm : SchwartzLineTestFunction → ℝ
  quadraticForm_eq_zeroSide :
    ∀ f : SchwartzLineTestFunction,
      quadraticForm f = formulaData.zeroSide.zeroSide f
  positivity :
    ∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f
  positivity_implies_RHOn_univ :
    (∀ f : SchwartzLineTestFunction, 0 ≤ quadraticForm f) →
      RHOn (fun _ : ℂ => True)

namespace SchwartzRiemannWeilPositivityData

/-- Assemble explicit-formula data and positivity data into the global criterion. -/
noncomputable def toGlobalCriterion
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData) :
    SchwartzRiemannWeilGlobalCriterion where
  zeroSide := formulaData.zeroSide
  primeSide := formulaData.primeSide
  poleSide := formulaData.poleSide
  gammaSide := formulaData.gammaSide
  explicitFormula := formulaData.explicitFormula
  quadraticForm := positivityData.quadraticForm
  quadraticForm_eq_zeroSide := positivityData.quadraticForm_eq_zeroSide
  positivity := positivityData.positivity
  positivity_implies_RHOn_univ := positivityData.positivity_implies_RHOn_univ

/-- The packaged quadratic form is the residual side of the explicit formula. -/
theorem quadraticForm_eq_residualSide
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData)
    (f : SchwartzLineTestFunction) :
    positivityData.quadraticForm f =
      (formulaData.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f := by
  rw [positivityData.quadraticForm_eq_zeroSide f]
  exact formulaData.zeroSide_eq_residualSide f

/-- The residual side of the explicit formula is the packaged quadratic form. -/
theorem residualSide_eq_quadraticForm
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData)
    (f : SchwartzLineTestFunction) :
    (formulaData.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f =
      positivityData.quadraticForm f :=
  (positivityData.quadraticForm_eq_residualSide f).symm

/-- Positivity data for explicit-formula data proves universal local RH. -/
theorem RHOn_univ
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData) :
    RHOn (fun _ : ℂ => True) :=
  positivityData.toGlobalCriterion.RHOn_univ

/-- Positivity data for explicit-formula data proves the project-local RH statement. -/
theorem RHStatement
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData) :
    RiemannHypothesisProject.RHStatement :=
  positivityData.toGlobalCriterion.RHStatement

/-- Positivity data for explicit-formula data proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData) :
    RiemannHypothesis :=
  positivityData.toGlobalCriterion.mathlib_RH

/-- Compact-exhaustion zero-window sums converge to the packaged quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    {formulaData : SchwartzRiemannWeilExplicitFormulaData}
    (positivityData : SchwartzRiemannWeilPositivityData formulaData)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : ℕ => formulaData.zeroSide.windowZeroSide exhaustion n f)
      atTop (𝓝 (positivityData.quadraticForm f)) :=
  positivityData.toGlobalCriterion.tendsto_windowZeroSide_quadraticForm
    exhaustion f

end SchwartzRiemannWeilPositivityData

/-- A decomposed full certificate for the Schwartz Riemann-Weil route. -/
structure SchwartzRiemannWeilCertificateData where
  formulaData : SchwartzRiemannWeilExplicitFormulaData
  positivityData : SchwartzRiemannWeilPositivityData formulaData

namespace SchwartzRiemannWeilCertificateData

/-- Assemble decomposed certificate data into the global criterion. -/
noncomputable def toGlobalCriterion
    (certificate : SchwartzRiemannWeilCertificateData) :
    SchwartzRiemannWeilGlobalCriterion :=
  certificate.positivityData.toGlobalCriterion

/-- The certificate's quadratic form is the residual side of its explicit formula. -/
theorem quadraticForm_eq_residualSide
    (certificate : SchwartzRiemannWeilCertificateData)
    (f : SchwartzLineTestFunction) :
    certificate.positivityData.quadraticForm f =
      (certificate.formulaData.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f :=
  certificate.positivityData.quadraticForm_eq_residualSide f

/-- The residual side of the certificate's explicit formula is its quadratic form. -/
theorem residualSide_eq_quadraticForm
    (certificate : SchwartzRiemannWeilCertificateData)
    (f : SchwartzLineTestFunction) :
    (certificate.formulaData.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f =
      certificate.positivityData.quadraticForm f :=
  certificate.positivityData.residualSide_eq_quadraticForm f

/-- Decomposed certificate data proves universal local RH. -/
theorem RHOn_univ
    (certificate : SchwartzRiemannWeilCertificateData) :
    RHOn (fun _ : ℂ => True) :=
  certificate.toGlobalCriterion.RHOn_univ

/-- Decomposed certificate data proves the project-local RH statement. -/
theorem RHStatement
    (certificate : SchwartzRiemannWeilCertificateData) :
    RiemannHypothesisProject.RHStatement :=
  certificate.toGlobalCriterion.RHStatement

/-- Decomposed certificate data proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (certificate : SchwartzRiemannWeilCertificateData) :
    RiemannHypothesis :=
  certificate.toGlobalCriterion.mathlib_RH

/-- Decomposed certificate data gives convergence to the packaged quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (certificate : SchwartzRiemannWeilCertificateData)
    (exhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : ℕ =>
        certificate.formulaData.zeroSide.windowZeroSide exhaustion n f)
      atTop (𝓝 (certificate.positivityData.quadraticForm f)) :=
  certificate.toGlobalCriterion.tendsto_windowZeroSide_quadraticForm
    exhaustion f

end SchwartzRiemannWeilCertificateData

end RiemannHypothesisProject
