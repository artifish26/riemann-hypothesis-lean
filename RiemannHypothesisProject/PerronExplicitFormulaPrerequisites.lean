import RiemannHypothesisProject.TruncatedRiemannVonMangoldtFormulaTarget

/-!
# Perron/contour prerequisites for a truncated explicit formula

The truncated Riemann-von Mangoldt target in this project is deliberately
small: a Chebyshev side, a finite zero window, main/pole terms, and an explicit
error.  Analytic proofs usually reach that target through several named steps:

1. Perron inversion for a Chebyshev-type side;
2. expansion of the logarithmic derivative of zeta;
3. shifting a rectangular contour and accounting for residues;
4. bounding the remaining contour and truncation error.

This file packages those steps without proving them.  The checked result is
that once these prerequisites are supplied, they assemble into the existing
`TruncatedRiemannVonMangoldtFormulaData` and
`TruncatedRiemannVonMangoldtErrorBound` records.
-/

namespace RiemannHypothesisProject

/--
The analytic prelude for a Perron-based explicit formula.

`perronIntegral` is the expression obtained by Perron inversion.  The
`logDerivativeIntegral` is the same integral after replacing the arithmetic
side by the zeta logarithmic-derivative expansion.  Future work should replace
these placeholders by actual contour integrals and prove the two identities.
-/
structure PerronExplicitFormulaPreludeData where
  chebyshevPsiSide : Real -> Real
  perronIntegral : Real -> Nat -> Real
  logDerivativeIntegral : Real -> Nat -> Real
  perron_inversion :
    forall x : Real,
      forall height : Nat,
        chebyshevPsiSide x = perronIntegral x height
  logDerivative_expansion :
    forall x : Real,
      forall height : Nat,
        perronIntegral x height = logDerivativeIntegral x height

/--
The contour-shift and residue-accounting step.

The zero residues are represented by `zeroTerm` summed over the finite
`zeroWindowData`.  The remaining contour/truncation contribution is stored as
`contourErrorSide`.
-/
structure PerronContourShiftResidueData
    (prelude : PerronExplicitFormulaPreludeData) where
  mainSide : Real -> Real
  poleSide : Real -> Real
  zeroWindowData : TruncatedRiemannVonMangoldtZeroWindowData
  zeroTerm : Real -> Nat -> ZetaZeroSubtype -> Real
  contourErrorSide : Real -> Nat -> Real
  contour_shift_residue :
    forall x : Real,
      forall height : Nat,
        prelude.logDerivativeIntegral x height =
          mainSide x +
            (zeroWindowData.heightWindow height).sum
              (fun rho : ZetaZeroSubtype => zeroTerm x height rho) +
            poleSide x +
            contourErrorSide x height

namespace PerronContourShiftResidueData

/--
Assemble the Perron, logarithmic-derivative, and contour-shift identities into
the truncated Riemann-von Mangoldt formula package.
-/
noncomputable def toTruncatedFormulaData
    {prelude : PerronExplicitFormulaPreludeData}
    (shiftData : PerronContourShiftResidueData prelude) :
    TruncatedRiemannVonMangoldtFormulaData :=
  TruncatedRiemannVonMangoldtFormulaData.ofRawSides
    prelude.chebyshevPsiSide
    shiftData.mainSide
    shiftData.poleSide
    shiftData.zeroWindowData
    shiftData.zeroTerm
    shiftData.contourErrorSide
    (fun x height => by
      calc
        prelude.chebyshevPsiSide x =
            prelude.perronIntegral x height :=
          prelude.perron_inversion x height
        _ = prelude.logDerivativeIntegral x height :=
          prelude.logDerivative_expansion x height
        _ = shiftData.mainSide x +
              (shiftData.zeroWindowData.heightWindow height).sum
                (fun rho : ZetaZeroSubtype => shiftData.zeroTerm x height rho) +
              shiftData.poleSide x +
              shiftData.contourErrorSide x height :=
          shiftData.contour_shift_residue x height)

/-- The assembled formula keeps the contour error as its explicit error side. -/
theorem toTruncatedFormulaData_errorSide
    {prelude : PerronExplicitFormulaPreludeData}
    (shiftData : PerronContourShiftResidueData prelude) :
    shiftData.toTruncatedFormulaData.sideData.errorSide =
      shiftData.contourErrorSide :=
  rfl

end PerronContourShiftResidueData

/-- An explicit envelope for the remaining contour/truncation error. -/
structure PerronContourErrorEstimateData
    {prelude : PerronExplicitFormulaPreludeData}
    (shiftData : PerronContourShiftResidueData prelude) where
  errorEnvelope : Real -> Nat -> Real
  errorEnvelope_nonneg :
    forall x : Real, forall height : Nat, 0 <= errorEnvelope x height
  abs_contourErrorSide_le :
    forall x : Real,
      forall height : Nat,
        |shiftData.contourErrorSide x height| <= errorEnvelope x height

namespace PerronContourErrorEstimateData

/--
Convert the contour-error estimate into the existing truncated-formula error
bound package.
-/
noncomputable def toTruncatedErrorBound
    {prelude : PerronExplicitFormulaPreludeData}
    {shiftData : PerronContourShiftResidueData prelude}
    (errorData : PerronContourErrorEstimateData shiftData) :
    TruncatedRiemannVonMangoldtErrorBound
      shiftData.toTruncatedFormulaData where
  errorEnvelope := errorData.errorEnvelope
  errorEnvelope_nonneg := errorData.errorEnvelope_nonneg
  abs_errorSide_le := errorData.abs_contourErrorSide_le

/-- The Perron contour envelope bounds the assembled formula error. -/
theorem abs_formulaError_le
    {prelude : PerronExplicitFormulaPreludeData}
    {shiftData : PerronContourShiftResidueData prelude}
    (errorData : PerronContourErrorEstimateData shiftData)
    (x : Real) (height : Nat) :
    |shiftData.toTruncatedFormulaData.sideData.formulaError x height| <=
      errorData.errorEnvelope x height :=
  errorData.toTruncatedErrorBound.abs_formulaError_le x height

end PerronContourErrorEstimateData

/-- A compact package containing both formula prerequisites and error control. -/
structure PerronTruncatedExplicitFormulaPackage where
  prelude : PerronExplicitFormulaPreludeData
  shiftData : PerronContourShiftResidueData prelude
  errorData : PerronContourErrorEstimateData shiftData

namespace PerronTruncatedExplicitFormulaPackage

/-- Export the truncated formula assembled from the Perron package. -/
noncomputable def toTruncatedFormulaData
    (pkg : PerronTruncatedExplicitFormulaPackage) :
    TruncatedRiemannVonMangoldtFormulaData :=
  pkg.shiftData.toTruncatedFormulaData

/-- Export the explicit error bound assembled from the Perron package. -/
noncomputable def toTruncatedErrorBound
    (pkg : PerronTruncatedExplicitFormulaPackage) :
    TruncatedRiemannVonMangoldtErrorBound
      pkg.toTruncatedFormulaData :=
  pkg.errorData.toTruncatedErrorBound

/-- The package's error envelope bounds the assembled formula error. -/
theorem abs_formulaError_le
    (pkg : PerronTruncatedExplicitFormulaPackage)
    (x : Real) (height : Nat) :
    |pkg.toTruncatedFormulaData.sideData.formulaError x height| <=
      pkg.errorData.errorEnvelope x height :=
  pkg.toTruncatedErrorBound.abs_formulaError_le x height

end PerronTruncatedExplicitFormulaPackage

end RiemannHypothesisProject
