import RiemannHypothesisProject.SchwartzRiemannWeilTailEstimates
import RiemannHypothesisProject.SchwartzRiemannWeilCertificateData
import RiemannHypothesisProject.SchwartzRiemannWeilFormulaSides
import RiemannHypothesisProject.SchwartzRiemannWeilPositivityPackages

/-!
# Tail-estimate certificate data for the Riemann-Weil route

The separated tail-estimate interface proves that the candidate Riemann-Weil
zero weight is summable. This file packages that analytic input together with
the remaining explicit-formula and positivity data needed by the global
criterion.

The result is a more concrete endpoint: future work can supply a compact
exhaustion, a complex extension system, separated zero-counting and zero-decay
estimates, and the explicit-formula/positivity fields, then Lean assembles the
existing `SchwartzRiemannWeilCertificateData` and derives the RH consequences.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/--
Certificate data whose zero side is produced from separated polynomial
tail estimates.

This is the main end-to-end work package for the current Riemann-Weil track:
the tail estimate supplies summability of the candidate zero contribution, and
the remaining fields are exactly the explicit-formula and positivity inputs
used by the global criterion.
-/
structure SchwartzRiemannWeilTailCertificateData where
  exhaustion : ComplexCompactExhaustion
  system : SchwartzRiemannWeilExtensionSystem
  tailEstimate :
    SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system
  primeSide : SchwartzLineTestFunction -> Real
  poleSide : SchwartzLineTestFunction -> Real
  gammaSide : SchwartzLineTestFunction -> Real
  explicitFormula :
    forall f : SchwartzLineTestFunction,
      tailEstimate.toZeroSide.zeroSide f =
        primeSide f + poleSide f + gammaSide f
  quadraticForm : SchwartzLineTestFunction -> Real
  quadraticForm_eq_zeroSide :
    forall f : SchwartzLineTestFunction,
      quadraticForm f = tailEstimate.toZeroSide.zeroSide f
  positivity :
    forall f : SchwartzLineTestFunction, 0 <= quadraticForm f
  positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction, 0 <= quadraticForm f) ->
      RHOn (fun _ : Complex => True)

namespace SchwartzRiemannWeilTailCertificateData

/--
Build a tail certificate from packaged formula-side identity data and
positivity data.
-/
noncomputable def ofFormulaIdentityData
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (tailEstimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData tailEstimate.toZeroSide)
    (quadraticForm : SchwartzLineTestFunction -> Real)
    (quadraticForm_eq_zeroSide :
      forall f : SchwartzLineTestFunction,
        quadraticForm f = tailEstimate.toZeroSide.zeroSide f)
    (positivity :
      forall f : SchwartzLineTestFunction, 0 <= quadraticForm f)
    (positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction, 0 <= quadraticForm f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilTailCertificateData where
  exhaustion := exhaustion
  system := system
  tailEstimate := tailEstimate
  primeSide := formulaData.sideData.primeSide
  poleSide := formulaData.sideData.poleSide
  gammaSide := formulaData.sideData.gammaSide
  explicitFormula := fun f => by
    simpa [SchwartzRiemannWeilFormulaSideData.residualSide]
      using formulaData.explicitFormula f
  quadraticForm := quadraticForm
  quadraticForm_eq_zeroSide := quadraticForm_eq_zeroSide
  positivity := positivity
  positivity_implies_RHOn_univ := positivity_implies_RHOn_univ

/--
Build a tail certificate from packaged formula-side identity data and packaged
positivity data.
-/
noncomputable def ofFormulaIdentityAndPackagedPositivityData
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (tailEstimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData tailEstimate.toZeroSide)
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilTailCertificateData :=
  ofFormulaIdentityData tailEstimate formulaData
    packagedData.identification.quadraticData.quadraticForm
    packagedData.identification.quadraticForm_eq_zeroSide
    packagedData.positivity.positivity
    packagedData.criterion.positivity_implies_RHOn_univ

/-- The zero side produced by the separated tail estimate. -/
noncomputable def zeroSide
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilZeroSide :=
  data.tailEstimate.toZeroSide

/-- Export a tail certificate's formula fields as packaged formula-side identity data. -/
noncomputable def toFormulaIdentityData
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilFormulaIdentityData data.zeroSide where
  sideData :=
    { primeSide := data.primeSide
      poleSide := data.poleSide
      gammaSide := data.gammaSide }
  explicitFormula := fun f => by
    simpa [zeroSide, SchwartzRiemannWeilFormulaSideData.residualSide]
      using data.explicitFormula f

/-- The tail-generated zero side uses the candidate extension-system weight. -/
theorem zeroSide_weight
    (data : SchwartzRiemannWeilTailCertificateData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.tailEstimate.toZeroSide_weight f rho

/-- Compact-exhaustion sums converge for the tail-generated zero side. -/
theorem tendsto_windowZeroSide
    (data : SchwartzRiemannWeilTailCertificateData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.zeroSide.zeroSide f)) :=
  data.tailEstimate.tendsto_windowZeroSide windowExhaustion f

/-- Convert tail-generated explicit-formula data to the decomposed endpoint. -/
noncomputable def toExplicitFormulaData
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilExplicitFormulaData where
  zeroSide := data.zeroSide
  primeSide := data.primeSide
  poleSide := data.poleSide
  gammaSide := data.gammaSide
  explicitFormula := data.explicitFormula

/-- Convert tail-generated positivity data to the decomposed endpoint. -/
noncomputable def toPositivityData
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilPositivityData data.toExplicitFormulaData where
  quadraticForm := data.quadraticForm
  quadraticForm_eq_zeroSide := data.quadraticForm_eq_zeroSide
  positivity := data.positivity
  positivity_implies_RHOn_univ := data.positivity_implies_RHOn_univ

/-- Export a tail certificate's positivity fields as packaged positivity data. -/
noncomputable def toPackagedPositivityData
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilPackagedPositivityData data.toExplicitFormulaData :=
  SchwartzRiemannWeilPackagedPositivityData.ofPositivityData
    data.toPositivityData

/-- The tail certificate's quadratic form is the residual side of its explicit formula. -/
theorem quadraticForm_eq_residualSide
    (data : SchwartzRiemannWeilTailCertificateData)
    (f : SchwartzLineTestFunction) :
    data.quadraticForm f =
      (data.toExplicitFormulaData
        |>.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f :=
  data.toPositivityData.quadraticForm_eq_residualSide f

/-- The residual side of the tail certificate's explicit formula is its quadratic form. -/
theorem residualSide_eq_quadraticForm
    (data : SchwartzRiemannWeilTailCertificateData)
    (f : SchwartzLineTestFunction) :
    (data.toExplicitFormulaData
        |>.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f =
      data.quadraticForm f :=
  (data.quadraticForm_eq_residualSide f).symm

/-- Assemble tail-generated data into the decomposed Riemann-Weil certificate. -/
noncomputable def toCertificateData
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilCertificateData where
  formulaData := data.toExplicitFormulaData
  positivityData := data.toPositivityData

/-- Assemble tail-generated data into the global criterion. -/
noncomputable def toGlobalCriterion
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilGlobalCriterion :=
  data.toCertificateData.toGlobalCriterion

/-- Tail-generated certificate data proves universal local RH. -/
theorem RHOn_univ
    (data : SchwartzRiemannWeilTailCertificateData) :
    RHOn (fun _ : Complex => True) :=
  data.toGlobalCriterion.RHOn_univ

/-- Tail-generated certificate data proves the project-local RH statement. -/
theorem RHStatement
    (data : SchwartzRiemannWeilTailCertificateData) :
    RiemannHypothesisProject.RHStatement :=
  data.toGlobalCriterion.RHStatement

/-- Tail-generated certificate data proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (data : SchwartzRiemannWeilTailCertificateData) :
    RiemannHypothesis :=
  data.toGlobalCriterion.mathlib_RH

/-- Window zero sides converge to the tail-generated certificate's quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (data : SchwartzRiemannWeilTailCertificateData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.quadraticForm f)) :=
  data.toCertificateData.tendsto_windowZeroSide_quadraticForm
    windowExhaustion f

end SchwartzRiemannWeilTailCertificateData

end RiemannHypothesisProject
