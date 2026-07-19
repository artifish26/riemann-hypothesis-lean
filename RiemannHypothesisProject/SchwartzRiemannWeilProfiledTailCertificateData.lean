import RiemannHypothesisProject.SchwartzRiemannWeilProfiledTailWorkPackages

/-!
# Profiled tail-certificate data for the Riemann-Weil route

The profiled work-package layer keeps the analytic extension profile visible
while still assembling the existing tail-certificate endpoint. This module adds
the corresponding single-record certificate.

It is the compact target for the profiled route: provide a compact exhaustion,
an extension system, a profiled separated tail estimate, explicit-formula data,
and positivity data. Lean then forgets to the existing tail certificate and
derives the global criterion and RH consequences.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/--
Certificate data whose zero side is produced from a profiled separated tail
estimate.

This is the one-record version of the profiled work-package route. The
profiled tail estimate keeps normalization, symmetry, envelope growth, and
shell decay visible until the certificate is assembled.
-/
structure SchwartzRiemannWeilProfiledTailCertificateData where
  exhaustion : ComplexCompactExhaustion
  system : SchwartzRiemannWeilExtensionSystem
  profiledTailEstimate :
    SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system
  primeSide : SchwartzLineTestFunction -> Real
  poleSide : SchwartzLineTestFunction -> Real
  gammaSide : SchwartzLineTestFunction -> Real
  explicitFormula :
    forall f : SchwartzLineTestFunction,
      profiledTailEstimate.toZeroSide.zeroSide f =
        primeSide f + poleSide f + gammaSide f
  quadraticForm : SchwartzLineTestFunction -> Real
  quadraticForm_eq_zeroSide :
    forall f : SchwartzLineTestFunction,
      quadraticForm f = profiledTailEstimate.toZeroSide.zeroSide f
  positivity :
    forall f : SchwartzLineTestFunction, 0 <= quadraticForm f
  positivity_implies_RHOn_univ :
    (forall f : SchwartzLineTestFunction, 0 <= quadraticForm f) ->
      RHOn (fun _ : Complex => True)

namespace SchwartzRiemannWeilProfiledTailCertificateData

/--
Build a profiled tail certificate from packaged formula-side identity data and
positivity data.
-/
noncomputable def ofFormulaIdentityData
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (profiledTailEstimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData profiledTailEstimate.toZeroSide)
    (quadraticForm : SchwartzLineTestFunction -> Real)
    (quadraticForm_eq_zeroSide :
      forall f : SchwartzLineTestFunction,
        quadraticForm f = profiledTailEstimate.toZeroSide.zeroSide f)
    (positivity :
      forall f : SchwartzLineTestFunction, 0 <= quadraticForm f)
    (positivity_implies_RHOn_univ :
      (forall f : SchwartzLineTestFunction, 0 <= quadraticForm f) ->
        RHOn (fun _ : Complex => True)) :
    SchwartzRiemannWeilProfiledTailCertificateData where
  exhaustion := exhaustion
  system := system
  profiledTailEstimate := profiledTailEstimate
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
Build a profiled tail certificate from packaged formula-side identity data and
packaged positivity data.
-/
noncomputable def ofFormulaIdentityAndPackagedPositivityData
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (profiledTailEstimate :
      SchwartzRiemannWeilProfiledSeparatedTailEstimate exhaustion system)
    (formulaData :
      SchwartzRiemannWeilFormulaIdentityData profiledTailEstimate.toZeroSide)
    (packagedData :
      SchwartzRiemannWeilPackagedPositivityData
        formulaData.toExplicitFormulaData) :
    SchwartzRiemannWeilProfiledTailCertificateData :=
  ofFormulaIdentityData profiledTailEstimate formulaData
    packagedData.identification.quadraticData.quadraticForm
    packagedData.identification.quadraticForm_eq_zeroSide
    packagedData.positivity.positivity
    packagedData.criterion.positivity_implies_RHOn_univ

/--
Lift a generic tail certificate into the profiled endpoint using the
conservative exact-norm profile.
-/
noncomputable def ofTailCertificateData
    (data : SchwartzRiemannWeilTailCertificateData) :
    SchwartzRiemannWeilProfiledTailCertificateData where
  exhaustion := data.exhaustion
  system := data.system
  profiledTailEstimate :=
    SchwartzRiemannWeilProfiledSeparatedTailEstimate.ofSeparatedPolynomialDecayEstimate
      data.tailEstimate
  primeSide := data.primeSide
  poleSide := data.poleSide
  gammaSide := data.gammaSide
  explicitFormula := data.explicitFormula
  quadraticForm := data.quadraticForm
  quadraticForm_eq_zeroSide := data.quadraticForm_eq_zeroSide
  positivity := data.positivity
  positivity_implies_RHOn_univ := data.positivity_implies_RHOn_univ

/-- The zero side produced by the profiled separated tail estimate. -/
noncomputable def zeroSide
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilZeroSide :=
  data.profiledTailEstimate.toZeroSide

/-- Export a profiled certificate's formula fields as packaged formula-side identity data. -/
noncomputable def toFormulaIdentityData
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilFormulaIdentityData data.zeroSide where
  sideData :=
    { primeSide := data.primeSide
      poleSide := data.poleSide
      gammaSide := data.gammaSide }
  explicitFormula := fun f => by
    simpa [zeroSide, SchwartzRiemannWeilFormulaSideData.residualSide]
      using data.explicitFormula f

/-- The profiled tail-generated zero side uses the candidate extension-system weight. -/
theorem zeroSide_weight
    (data : SchwartzRiemannWeilProfiledTailCertificateData)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    data.zeroSide.weight f rho = data.system.weight f rho :=
  data.profiledTailEstimate.toZeroSide_weight f rho

/-- Compact-exhaustion sums converge for the profiled tail-generated zero side. -/
theorem tendsto_windowZeroSide
    (data : SchwartzRiemannWeilProfiledTailCertificateData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.zeroSide.zeroSide f)) :=
  data.profiledTailEstimate.tendsto_windowZeroSide windowExhaustion f

/-- Convert profiled certificate data to profiled zero data. -/
noncomputable def toProfiledTailZeroData
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilProfiledTailZeroData where
  exhaustion := data.exhaustion
  system := data.system
  profiledTailEstimate := data.profiledTailEstimate

/-- Convert profiled certificate data to profiled explicit-formula data. -/
noncomputable def toProfiledTailExplicitFormulaData
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilProfiledTailExplicitFormulaData
      data.toProfiledTailZeroData where
  primeSide := data.primeSide
  poleSide := data.poleSide
  gammaSide := data.gammaSide
  explicitFormula := data.explicitFormula

/-- Convert profiled certificate data to profiled positivity data. -/
noncomputable def toProfiledTailPositivityData
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilProfiledTailPositivityData
      data.toProfiledTailExplicitFormulaData where
  quadraticForm := data.quadraticForm
  quadraticForm_eq_zeroSide := data.quadraticForm_eq_zeroSide
  positivity := data.positivity
  positivity_implies_RHOn_univ := data.positivity_implies_RHOn_univ

/-- Export a profiled certificate's positivity fields as packaged positivity data. -/
noncomputable def toPackagedPositivityData
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilPackagedPositivityData
      data.toProfiledTailExplicitFormulaData.toRiemannWeilExplicitFormulaData :=
  SchwartzRiemannWeilPackagedPositivityData.ofPositivityData
    data.toProfiledTailPositivityData.toTailPositivityData.toRiemannWeilPositivityData

/-- Forget profiled certificate data to the generic tail certificate. -/
noncomputable def toTailCertificateData
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilTailCertificateData :=
  data.toProfiledTailPositivityData.toTailCertificateData

/-- The profiled certificate's quadratic form is the residual side of its explicit formula. -/
theorem quadraticForm_eq_residualSide
    (data : SchwartzRiemannWeilProfiledTailCertificateData)
    (f : SchwartzLineTestFunction) :
    data.quadraticForm f =
      (data.toTailCertificateData.toExplicitFormulaData
        |>.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f :=
  data.toTailCertificateData.quadraticForm_eq_residualSide f

/-- The residual side of the profiled certificate's explicit formula is its quadratic form. -/
theorem residualSide_eq_quadraticForm
    (data : SchwartzRiemannWeilProfiledTailCertificateData)
    (f : SchwartzLineTestFunction) :
    (data.toTailCertificateData.toExplicitFormulaData
        |>.toGlobalExplicitFormulaNormalization
        |>.toSchwartzExplicitFormulaNormalization).residualSide f =
      data.quadraticForm f :=
  (data.quadraticForm_eq_residualSide f).symm

/-- Convert profiled certificate data to the decomposed Riemann-Weil certificate. -/
noncomputable def toCertificateData
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilCertificateData :=
  data.toTailCertificateData.toCertificateData

/-- Assemble profiled certificate data into the global criterion. -/
noncomputable def toGlobalCriterion
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    SchwartzRiemannWeilGlobalCriterion :=
  data.toTailCertificateData.toGlobalCriterion

/-- Profiled tail-certificate data proves universal local RH. -/
theorem RHOn_univ
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    RHOn (fun _ : Complex => True) :=
  data.toGlobalCriterion.RHOn_univ

/-- Profiled tail-certificate data proves the project-local RH statement. -/
theorem RHStatement
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    RiemannHypothesisProject.RHStatement :=
  data.toGlobalCriterion.RHStatement

/-- Profiled tail-certificate data proves Mathlib's `RiemannHypothesis`. -/
theorem mathlib_RH
    (data : SchwartzRiemannWeilProfiledTailCertificateData) :
    RiemannHypothesis :=
  data.toGlobalCriterion.mathlib_RH

/-- Window zero sides converge to the profiled certificate's quadratic form. -/
theorem tendsto_windowZeroSide_quadraticForm
    (data : SchwartzRiemannWeilProfiledTailCertificateData)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => data.zeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (data.quadraticForm f)) :=
  data.toTailCertificateData.tendsto_windowZeroSide_quadraticForm
    windowExhaustion f

end SchwartzRiemannWeilProfiledTailCertificateData

end RiemannHypothesisProject
