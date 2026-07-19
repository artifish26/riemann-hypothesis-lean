import RiemannHypothesisProject.SchwartzRiemannWeilFormulaSides

/-!
# Guinand-Weil explicit-formula target

This module records a source-normalized Guinand-Weil formula target for future
analytic work.  The point is to keep the source formula and the conversion into
the project's `prime + pole + gamma` normalization separate.

No analytic formula is proved here.  Instead, the structures below name the
exact data a future formalization should provide, and Lean checks that once
those data are supplied they feed the existing Riemann-Weil formula package.
-/

namespace RiemannHypothesisProject

open Filter
open scoped Topology

/--
The four sides of a source-normalized Guinand-Weil formula.

The source zero side is kept separate from the project's chosen zero side so
that all Fourier-convention and normalization changes must be supplied as
explicit bridge theorems.
-/
structure GuinandWeilFormulaSideData where
  sourceZeroSide : SchwartzLineTestFunction -> Real
  sourcePrimeSide : SchwartzLineTestFunction -> Real
  sourcePoleSide : SchwartzLineTestFunction -> Real
  sourceGammaSide : SchwartzLineTestFunction -> Real

namespace GuinandWeilFormulaSideData

/-- The source residual side assembled from prime, pole, and gamma terms. -/
noncomputable def sourceResidualSide
    (sideData : GuinandWeilFormulaSideData)
    (f : SchwartzLineTestFunction) : Real :=
  sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
    sideData.sourceGammaSide f

/-- The source residual side is definitionally the sum of the three terms. -/
theorem sourceResidualSide_eq
    (sideData : GuinandWeilFormulaSideData)
    (f : SchwartzLineTestFunction) :
    sideData.sourceResidualSide f =
      sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
        sideData.sourceGammaSide f :=
  rfl

/-- Forget the source prefix after the normalization bridge has been fixed. -/
noncomputable def toSchwartzFormulaSideData
    (sideData : GuinandWeilFormulaSideData) :
    SchwartzRiemannWeilFormulaSideData where
  primeSide := sideData.sourcePrimeSide
  poleSide := sideData.sourcePoleSide
  gammaSide := sideData.sourceGammaSide

/-- The converted side data has the same residual expression. -/
theorem toSchwartzFormulaSideData_residualSide
    (sideData : GuinandWeilFormulaSideData)
    (f : SchwartzLineTestFunction) :
    sideData.toSchwartzFormulaSideData.residualSide f =
      sideData.sourceResidualSide f :=
  rfl

end GuinandWeilFormulaSideData

/--
The source Guinand-Weil identity before conversion to the project zero side.
-/
structure GuinandWeilFormulaIdentityData where
  sideData : GuinandWeilFormulaSideData
  sourceExplicitFormula :
    forall f : SchwartzLineTestFunction,
      sideData.sourceZeroSide f = sideData.sourceResidualSide f

namespace GuinandWeilFormulaIdentityData

/--
Build source identity data directly from the four source sides and the source
formula equality.
-/
noncomputable def ofRawSourceSides
    (sourceZeroSide sourcePrimeSide sourcePoleSide sourceGammaSide :
      SchwartzLineTestFunction -> Real)
    (sourceExplicitFormula :
      forall f : SchwartzLineTestFunction,
        sourceZeroSide f =
          sourcePrimeSide f + sourcePoleSide f + sourceGammaSide f) :
    GuinandWeilFormulaIdentityData where
  sideData :=
    { sourceZeroSide := sourceZeroSide
      sourcePrimeSide := sourcePrimeSide
      sourcePoleSide := sourcePoleSide
      sourceGammaSide := sourceGammaSide }
  sourceExplicitFormula := fun f => by
    simpa [GuinandWeilFormulaSideData.sourceResidualSide]
      using sourceExplicitFormula f

/-- Source formula data converted to project formula sides. -/
noncomputable def toFormulaSideData
    (formulaData : GuinandWeilFormulaIdentityData) :
    SchwartzRiemannWeilFormulaSideData :=
  formulaData.sideData.toSchwartzFormulaSideData

end GuinandWeilFormulaIdentityData

/--
A truncation/limit proof of a source-normalized Guinand-Weil formula.

The intended analytic use is the standard explicit-formula route: prove a
finite or truncated identity for every cutoff, then prove convergence of the
zero, prime, pole, and gamma truncations to the desired source sides.
-/
structure GuinandWeilTruncatedFormulaLimitData
    (sideData : GuinandWeilFormulaSideData) where
  truncatedZeroSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPrimeSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPoleSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedGammaSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedExplicitFormula :
    forall n : Nat,
      forall f : SchwartzLineTestFunction,
        truncatedZeroSide n f =
          truncatedPrimeSide n f + truncatedPoleSide n f +
            truncatedGammaSide n f
  tendsto_sourceZeroSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedZeroSide n f) atTop
        (nhds (sideData.sourceZeroSide f))
  tendsto_sourcePrimeSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPrimeSide n f) atTop
        (nhds (sideData.sourcePrimeSide f))
  tendsto_sourcePoleSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPoleSide n f) atTop
        (nhds (sideData.sourcePoleSide f))
  tendsto_sourceGammaSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedGammaSide n f) atTop
        (nhds (sideData.sourceGammaSide f))

namespace GuinandWeilTruncatedFormulaLimitData

/--
The limit of the truncated formula identities is the global source
Guinand-Weil formula.
-/
theorem sourceExplicitFormula
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaLimitData sideData)
    (f : SchwartzLineTestFunction) :
    sideData.sourceZeroSide f = sideData.sourceResidualSide f := by
  have hres :
      Tendsto
        (fun n : Nat =>
          limitData.truncatedPrimeSide n f +
            limitData.truncatedPoleSide n f +
              limitData.truncatedGammaSide n f)
        atTop
        (nhds
          (sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
            sideData.sourceGammaSide f)) :=
    ((limitData.tendsto_sourcePrimeSide f).add
      (limitData.tendsto_sourcePoleSide f)).add
        (limitData.tendsto_sourceGammaSide f)
  have hzero :
      Tendsto
        (fun n : Nat =>
          limitData.truncatedPrimeSide n f +
            limitData.truncatedPoleSide n f +
              limitData.truncatedGammaSide n f)
        atTop (nhds (sideData.sourceZeroSide f)) := by
    simpa [limitData.truncatedExplicitFormula] using
      limitData.tendsto_sourceZeroSide f
  have hlimit :
      sideData.sourceZeroSide f =
        sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
          sideData.sourceGammaSide f :=
    tendsto_nhds_unique hzero hres
  simpa [GuinandWeilFormulaSideData.sourceResidualSide] using hlimit

/-- Convert a truncation/limit proof into global source formula data. -/
noncomputable def toFormulaIdentityData
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaLimitData sideData) :
    GuinandWeilFormulaIdentityData where
  sideData := sideData
  sourceExplicitFormula := limitData.sourceExplicitFormula

end GuinandWeilTruncatedFormulaLimitData

/--
A truncation/limit proof of a source-normalized Guinand-Weil formula with an
explicit vanishing error term.

This is closer to the analytic contour-shift proof shape: for each cutoff one
proves a finite identity with a signed error term, then proves convergence of
the zero, prime, pole, and gamma sides together with decay of the error.
-/
structure GuinandWeilTruncatedFormulaErrorLimitData
    (sideData : GuinandWeilFormulaSideData) where
  truncatedZeroSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPrimeSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPoleSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedGammaSide : Nat -> SchwartzLineTestFunction -> Real
  truncationErrorSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedExplicitFormula :
    forall n : Nat,
      forall f : SchwartzLineTestFunction,
        truncatedZeroSide n f =
          (truncatedPrimeSide n f + truncatedPoleSide n f +
            truncatedGammaSide n f) + truncationErrorSide n f
  tendsto_sourceZeroSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedZeroSide n f) atTop
        (nhds (sideData.sourceZeroSide f))
  tendsto_sourcePrimeSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPrimeSide n f) atTop
        (nhds (sideData.sourcePrimeSide f))
  tendsto_sourcePoleSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPoleSide n f) atTop
        (nhds (sideData.sourcePoleSide f))
  tendsto_sourceGammaSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedGammaSide n f) atTop
        (nhds (sideData.sourceGammaSide f))
  tendsto_error_zero :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncationErrorSide n f) atTop (nhds 0)

namespace GuinandWeilTruncatedFormulaErrorLimitData

/--
The limit of truncated formulae with vanishing error is the global source
Guinand-Weil formula.
-/
theorem sourceExplicitFormula
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaErrorLimitData sideData)
    (f : SchwartzLineTestFunction) :
    sideData.sourceZeroSide f = sideData.sourceResidualSide f := by
  have hres :
      Tendsto
        (fun n : Nat =>
          limitData.truncatedPrimeSide n f +
            limitData.truncatedPoleSide n f +
              limitData.truncatedGammaSide n f)
        atTop
        (nhds
          (sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
            sideData.sourceGammaSide f)) :=
    ((limitData.tendsto_sourcePrimeSide f).add
      (limitData.tendsto_sourcePoleSide f)).add
        (limitData.tendsto_sourceGammaSide f)
  have hres_error :
      Tendsto
        (fun n : Nat =>
          (limitData.truncatedPrimeSide n f +
            limitData.truncatedPoleSide n f +
              limitData.truncatedGammaSide n f) +
            limitData.truncationErrorSide n f)
        atTop
        (nhds
          ((sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
            sideData.sourceGammaSide f) + 0)) :=
    hres.add (limitData.tendsto_error_zero f)
  have hzero :
      Tendsto
        (fun n : Nat =>
          (limitData.truncatedPrimeSide n f +
            limitData.truncatedPoleSide n f +
              limitData.truncatedGammaSide n f) +
            limitData.truncationErrorSide n f)
        atTop (nhds (sideData.sourceZeroSide f)) := by
    simpa [limitData.truncatedExplicitFormula] using
      limitData.tendsto_sourceZeroSide f
  have hlimit :
      sideData.sourceZeroSide f =
        (sideData.sourcePrimeSide f + sideData.sourcePoleSide f +
          sideData.sourceGammaSide f) + 0 :=
    tendsto_nhds_unique hzero hres_error
  simpa [GuinandWeilFormulaSideData.sourceResidualSide] using hlimit

/-- Convert a vanishing-error truncation proof into global source formula data. -/
noncomputable def toFormulaIdentityData
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaErrorLimitData sideData) :
    GuinandWeilFormulaIdentityData where
  sideData := sideData
  sourceExplicitFormula := limitData.sourceExplicitFormula

/-- The exact-truncation package is the zero-error special case. -/
noncomputable def ofTruncatedFormulaLimitData
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaLimitData sideData) :
    GuinandWeilTruncatedFormulaErrorLimitData sideData where
  truncatedZeroSide := limitData.truncatedZeroSide
  truncatedPrimeSide := limitData.truncatedPrimeSide
  truncatedPoleSide := limitData.truncatedPoleSide
  truncatedGammaSide := limitData.truncatedGammaSide
  truncationErrorSide := fun _ _ => 0
  truncatedExplicitFormula := by
    intro n f
    simpa using limitData.truncatedExplicitFormula n f
  tendsto_sourceZeroSide := limitData.tendsto_sourceZeroSide
  tendsto_sourcePrimeSide := limitData.tendsto_sourcePrimeSide
  tendsto_sourcePoleSide := limitData.tendsto_sourcePoleSide
  tendsto_sourceGammaSide := limitData.tendsto_sourceGammaSide
  tendsto_error_zero := by
    intro f
    exact tendsto_const_nhds

end GuinandWeilTruncatedFormulaErrorLimitData

/--
A truncation/limit proof of a source-normalized Guinand-Weil formula with an
absolute error envelope.

Analytic estimates usually bound the contour/truncation error in absolute
value.  This package asks for that bound and for the envelope to tend to zero;
Lean then derives the signed error convergence required by
`GuinandWeilTruncatedFormulaErrorLimitData`.
-/
structure GuinandWeilTruncatedFormulaErrorBoundLimitData
    (sideData : GuinandWeilFormulaSideData) where
  truncatedZeroSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPrimeSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPoleSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedGammaSide : Nat -> SchwartzLineTestFunction -> Real
  truncationErrorSide : Nat -> SchwartzLineTestFunction -> Real
  errorEnvelope : Nat -> SchwartzLineTestFunction -> Real
  truncatedExplicitFormula :
    forall n : Nat,
      forall f : SchwartzLineTestFunction,
        truncatedZeroSide n f =
          (truncatedPrimeSide n f + truncatedPoleSide n f +
            truncatedGammaSide n f) + truncationErrorSide n f
  abs_truncationErrorSide_le :
    forall n : Nat,
      forall f : SchwartzLineTestFunction,
        |truncationErrorSide n f| <= errorEnvelope n f
  tendsto_sourceZeroSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedZeroSide n f) atTop
        (nhds (sideData.sourceZeroSide f))
  tendsto_sourcePrimeSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPrimeSide n f) atTop
        (nhds (sideData.sourcePrimeSide f))
  tendsto_sourcePoleSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPoleSide n f) atTop
        (nhds (sideData.sourcePoleSide f))
  tendsto_sourceGammaSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedGammaSide n f) atTop
        (nhds (sideData.sourceGammaSide f))
  tendsto_errorEnvelope_zero :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => errorEnvelope n f) atTop (nhds 0)

namespace GuinandWeilTruncatedFormulaErrorBoundLimitData

/-- An absolute error envelope tending to zero forces the signed error to tend to zero. -/
theorem tendsto_error_zero
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaErrorBoundLimitData sideData)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => limitData.truncationErrorSide n f) atTop (nhds 0) := by
  have habs :
      Tendsto (fun n : Nat => |limitData.truncationErrorSide n f|)
        atTop (nhds 0) :=
    squeeze_zero
      (fun n : Nat => abs_nonneg (limitData.truncationErrorSide n f))
      (fun n : Nat => limitData.abs_truncationErrorSide_le n f)
      (limitData.tendsto_errorEnvelope_zero f)
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

/-- Convert an absolute-error-bound package into a signed-error-limit package. -/
noncomputable def toErrorLimitData
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaErrorBoundLimitData sideData) :
    GuinandWeilTruncatedFormulaErrorLimitData sideData where
  truncatedZeroSide := limitData.truncatedZeroSide
  truncatedPrimeSide := limitData.truncatedPrimeSide
  truncatedPoleSide := limitData.truncatedPoleSide
  truncatedGammaSide := limitData.truncatedGammaSide
  truncationErrorSide := limitData.truncationErrorSide
  truncatedExplicitFormula := limitData.truncatedExplicitFormula
  tendsto_sourceZeroSide := limitData.tendsto_sourceZeroSide
  tendsto_sourcePrimeSide := limitData.tendsto_sourcePrimeSide
  tendsto_sourcePoleSide := limitData.tendsto_sourcePoleSide
  tendsto_sourceGammaSide := limitData.tendsto_sourceGammaSide
  tendsto_error_zero := limitData.tendsto_error_zero

/-- Convert an absolute-error-bound proof into global source formula data. -/
noncomputable def toFormulaIdentityData
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaErrorBoundLimitData sideData) :
    GuinandWeilFormulaIdentityData :=
  limitData.toErrorLimitData.toFormulaIdentityData

/-- The vanishing signed-error package is an absolute-error package using `|error|`. -/
noncomputable def ofErrorLimitData
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaErrorLimitData sideData) :
    GuinandWeilTruncatedFormulaErrorBoundLimitData sideData where
  truncatedZeroSide := limitData.truncatedZeroSide
  truncatedPrimeSide := limitData.truncatedPrimeSide
  truncatedPoleSide := limitData.truncatedPoleSide
  truncatedGammaSide := limitData.truncatedGammaSide
  truncationErrorSide := limitData.truncationErrorSide
  errorEnvelope := fun n f => |limitData.truncationErrorSide n f|
  truncatedExplicitFormula := limitData.truncatedExplicitFormula
  abs_truncationErrorSide_le := by
    intro n f
    rfl
  tendsto_sourceZeroSide := limitData.tendsto_sourceZeroSide
  tendsto_sourcePrimeSide := limitData.tendsto_sourcePrimeSide
  tendsto_sourcePoleSide := limitData.tendsto_sourcePoleSide
  tendsto_sourceGammaSide := limitData.tendsto_sourceGammaSide
  tendsto_errorEnvelope_zero := by
    intro f
    simpa using (limitData.tendsto_error_zero f).abs

end GuinandWeilTruncatedFormulaErrorBoundLimitData

/--
A truncation/limit proof of a source-normalized Guinand-Weil formula with an
eventual absolute error envelope.

This matches the common analytic situation where the explicit error estimate
is only stated for sufficiently large cutoffs.  The finite cutoff identity is
still required for every cutoff, but the absolute error bound only has to hold
eventually for each test function.
-/
structure GuinandWeilTruncatedFormulaEventualErrorBoundLimitData
    (sideData : GuinandWeilFormulaSideData) where
  truncatedZeroSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPrimeSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedPoleSide : Nat -> SchwartzLineTestFunction -> Real
  truncatedGammaSide : Nat -> SchwartzLineTestFunction -> Real
  truncationErrorSide : Nat -> SchwartzLineTestFunction -> Real
  errorEnvelope : Nat -> SchwartzLineTestFunction -> Real
  truncatedExplicitFormula :
    forall n : Nat,
      forall f : SchwartzLineTestFunction,
        truncatedZeroSide n f =
          (truncatedPrimeSide n f + truncatedPoleSide n f +
            truncatedGammaSide n f) + truncationErrorSide n f
  eventually_abs_truncationErrorSide_le :
    forall f : SchwartzLineTestFunction,
      ∀ᶠ n : Nat in atTop,
        |truncationErrorSide n f| <= errorEnvelope n f
  tendsto_sourceZeroSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedZeroSide n f) atTop
        (nhds (sideData.sourceZeroSide f))
  tendsto_sourcePrimeSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPrimeSide n f) atTop
        (nhds (sideData.sourcePrimeSide f))
  tendsto_sourcePoleSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedPoleSide n f) atTop
        (nhds (sideData.sourcePoleSide f))
  tendsto_sourceGammaSide :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => truncatedGammaSide n f) atTop
        (nhds (sideData.sourceGammaSide f))
  tendsto_errorEnvelope_zero :
    forall f : SchwartzLineTestFunction,
      Tendsto (fun n : Nat => errorEnvelope n f) atTop (nhds 0)

namespace GuinandWeilTruncatedFormulaEventualErrorBoundLimitData

/--
An eventually valid absolute error envelope tending to zero forces the signed
error to tend to zero.
-/
theorem tendsto_error_zero
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaEventualErrorBoundLimitData sideData)
    (f : SchwartzLineTestFunction) :
    Tendsto (fun n : Nat => limitData.truncationErrorSide n f) atTop (nhds 0) := by
  have habs :
      Tendsto (fun n : Nat => |limitData.truncationErrorSide n f|)
        atTop (nhds 0) :=
    squeeze_zero'
      (Eventually.of_forall
        (fun n : Nat => abs_nonneg (limitData.truncationErrorSide n f)))
      (limitData.eventually_abs_truncationErrorSide_le f)
      (limitData.tendsto_errorEnvelope_zero f)
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

/-- Convert an eventual absolute-error-bound package into a signed-error-limit package. -/
noncomputable def toErrorLimitData
    {sideData : GuinandWeilFormulaSideData}
    (limitData :
      GuinandWeilTruncatedFormulaEventualErrorBoundLimitData sideData) :
    GuinandWeilTruncatedFormulaErrorLimitData sideData where
  truncatedZeroSide := limitData.truncatedZeroSide
  truncatedPrimeSide := limitData.truncatedPrimeSide
  truncatedPoleSide := limitData.truncatedPoleSide
  truncatedGammaSide := limitData.truncatedGammaSide
  truncationErrorSide := limitData.truncationErrorSide
  truncatedExplicitFormula := limitData.truncatedExplicitFormula
  tendsto_sourceZeroSide := limitData.tendsto_sourceZeroSide
  tendsto_sourcePrimeSide := limitData.tendsto_sourcePrimeSide
  tendsto_sourcePoleSide := limitData.tendsto_sourcePoleSide
  tendsto_sourceGammaSide := limitData.tendsto_sourceGammaSide
  tendsto_error_zero := limitData.tendsto_error_zero

/-- Convert an eventual absolute-error-bound proof into global source formula data. -/
noncomputable def toFormulaIdentityData
    {sideData : GuinandWeilFormulaSideData}
    (limitData :
      GuinandWeilTruncatedFormulaEventualErrorBoundLimitData sideData) :
    GuinandWeilFormulaIdentityData :=
  limitData.toErrorLimitData.toFormulaIdentityData

/-- A pointwise absolute-error package is an eventual absolute-error package. -/
noncomputable def ofErrorBoundLimitData
    {sideData : GuinandWeilFormulaSideData}
    (limitData : GuinandWeilTruncatedFormulaErrorBoundLimitData sideData) :
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData sideData where
  truncatedZeroSide := limitData.truncatedZeroSide
  truncatedPrimeSide := limitData.truncatedPrimeSide
  truncatedPoleSide := limitData.truncatedPoleSide
  truncatedGammaSide := limitData.truncatedGammaSide
  truncationErrorSide := limitData.truncationErrorSide
  errorEnvelope := limitData.errorEnvelope
  truncatedExplicitFormula := limitData.truncatedExplicitFormula
  eventually_abs_truncationErrorSide_le := by
    intro f
    exact Eventually.of_forall (fun n => limitData.abs_truncationErrorSide_le n f)
  tendsto_sourceZeroSide := limitData.tendsto_sourceZeroSide
  tendsto_sourcePrimeSide := limitData.tendsto_sourcePrimeSide
  tendsto_sourcePoleSide := limitData.tendsto_sourcePoleSide
  tendsto_sourceGammaSide := limitData.tendsto_sourceGammaSide
  tendsto_errorEnvelope_zero := limitData.tendsto_errorEnvelope_zero

end GuinandWeilTruncatedFormulaEventualErrorBoundLimitData

/--
A normalization bridge from a source Guinand-Weil zero side to the project's
chosen Riemann-Weil zero side.

This is deliberately a separate structure: future runs should prove these
bridge equalities once, rather than hiding sign, `2 * pi`, or Fourier-convention
changes inside a long explicit-formula proof.
-/
structure GuinandWeilNormalizationBridge
    (sourceData : GuinandWeilFormulaIdentityData)
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  zeroSide_eq_sourceZeroSide :
    forall f : SchwartzLineTestFunction,
      zeroSide.zeroSide f = sourceData.sideData.sourceZeroSide f

namespace GuinandWeilNormalizationBridge

/--
Convert source-normalized Guinand-Weil data into the project's packaged formula
identity data.
-/
noncomputable def toFormulaIdentityData
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide where
  sideData := sourceData.toFormulaSideData
  explicitFormula := fun f => by
    calc
      zeroSide.zeroSide f = sourceData.sideData.sourceZeroSide f :=
        bridge.zeroSide_eq_sourceZeroSide f
      _ = sourceData.sideData.sourceResidualSide f :=
        sourceData.sourceExplicitFormula f
      _ = sourceData.toFormulaSideData.residualSide f := by
        exact (sourceData.sideData.toSchwartzFormulaSideData_residualSide f).symm

/-- The converted formula data keeps the source prime side. -/
theorem toFormulaIdentityData_primeSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    bridge.toFormulaIdentityData.sideData.primeSide =
      sourceData.sideData.sourcePrimeSide :=
  rfl

/-- The converted formula data keeps the source pole side. -/
theorem toFormulaIdentityData_poleSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    bridge.toFormulaIdentityData.sideData.poleSide =
      sourceData.sideData.sourcePoleSide :=
  rfl

/-- The converted formula data keeps the source gamma side. -/
theorem toFormulaIdentityData_gammaSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    bridge.toFormulaIdentityData.sideData.gammaSide =
      sourceData.sideData.sourceGammaSide :=
  rfl

/-- The converted project residual side is the source residual side. -/
theorem toFormulaIdentityData_residualSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    bridge.toFormulaIdentityData.sideData.residualSide f =
      sourceData.sideData.sourceResidualSide f :=
  rfl

/--
The normalized project zero side equals the source residual side. This is the
source explicit formula transported through the normalization bridge.
-/
theorem zeroSide_eq_sourceResidualSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = sourceData.sideData.sourceResidualSide f := by
  calc
    zeroSide.zeroSide f = sourceData.sideData.sourceZeroSide f :=
      bridge.zeroSide_eq_sourceZeroSide f
    _ = sourceData.sideData.sourceResidualSide f :=
      sourceData.sourceExplicitFormula f

/--
Source residual nonnegativity on an admissible class transports to formula-side
residual nonnegativity through the normalization bridge.
-/
theorem residual_nonneg_on_admissible_of_source
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceData.sideData.sourceResidualSide f) :
    forall f : SchwartzLineTestFunction,
      admissible f -> 0 <= bridge.toFormulaIdentityData.sideData.residualSide f := by
  intro f hf
  rw [bridge.toFormulaIdentityData_residualSide f]
  exact source_residual_nonneg_on_admissible f hf

/--
The project explicit formula is exactly the transported source formula, with
the final residual side rewritten into project notation.
-/
theorem toFormulaIdentityData_explicitFormula_eq_source
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      bridge.toFormulaIdentityData.sideData.residualSide f := by
  rw [bridge.toFormulaIdentityData_residualSide f]
  exact bridge.zeroSide_eq_sourceResidualSide f

end GuinandWeilNormalizationBridge

/--
A componentwise normalization bridge from source Guinand-Weil sides to the
project formula sides.

This sharper target is useful when the zero, prime, pole, and gamma sides all
need explicit convention changes, rather than only the zero side.
-/
structure GuinandWeilComponentwiseNormalizationBridge
    (sourceData : GuinandWeilFormulaIdentityData)
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sideData : SchwartzRiemannWeilFormulaSideData
  zeroSide_eq_sourceZeroSide :
    forall f : SchwartzLineTestFunction,
      zeroSide.zeroSide f = sourceData.sideData.sourceZeroSide f
  primeSide_eq_sourcePrimeSide :
    forall f : SchwartzLineTestFunction,
      sideData.primeSide f = sourceData.sideData.sourcePrimeSide f
  poleSide_eq_sourcePoleSide :
    forall f : SchwartzLineTestFunction,
      sideData.poleSide f = sourceData.sideData.sourcePoleSide f
  gammaSide_eq_sourceGammaSide :
    forall f : SchwartzLineTestFunction,
      sideData.gammaSide f = sourceData.sideData.sourceGammaSide f

namespace GuinandWeilComponentwiseNormalizationBridge

/-- A componentwise bridge forgets to the older zero-side-only normalization bridge. -/
noncomputable def toZeroSideNormalizationBridge
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide) :
    GuinandWeilNormalizationBridge sourceData zeroSide where
  zeroSide_eq_sourceZeroSide := bridge.zeroSide_eq_sourceZeroSide

/--
The older zero-side normalization bridge is the special case where project
prime, pole, and gamma sides are exactly the source sides.
-/
noncomputable def ofZeroSideNormalizationBridge
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge : GuinandWeilNormalizationBridge sourceData zeroSide) :
    GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide where
  sideData := sourceData.toFormulaSideData
  zeroSide_eq_sourceZeroSide := bridge.zeroSide_eq_sourceZeroSide
  primeSide_eq_sourcePrimeSide := fun _ => rfl
  poleSide_eq_sourcePoleSide := fun _ => rfl
  gammaSide_eq_sourceGammaSide := fun _ => rfl

/-- The project residual side induced by a componentwise bridge is the source residual side. -/
theorem residualSide_eq_sourceResidualSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    bridge.sideData.residualSide f =
      sourceData.sideData.sourceResidualSide f := by
  simp [SchwartzRiemannWeilFormulaSideData.residualSide,
    GuinandWeilFormulaSideData.sourceResidualSide,
    bridge.primeSide_eq_sourcePrimeSide f,
    bridge.poleSide_eq_sourcePoleSide f,
    bridge.gammaSide_eq_sourceGammaSide f]

/--
Convert componentwise source-normalized Guinand-Weil data into the project's
packaged formula identity data.
-/
noncomputable def toFormulaIdentityData
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide where
  sideData := bridge.sideData
  explicitFormula := fun f => by
    calc
      zeroSide.zeroSide f = sourceData.sideData.sourceZeroSide f :=
        bridge.zeroSide_eq_sourceZeroSide f
      _ = sourceData.sideData.sourceResidualSide f :=
        sourceData.sourceExplicitFormula f
      _ = bridge.sideData.residualSide f :=
        (bridge.residualSide_eq_sourceResidualSide f).symm

/-- The componentwise conversion keeps the explicitly supplied project side data. -/
theorem toFormulaIdentityData_sideData
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide) :
    bridge.toFormulaIdentityData.sideData = bridge.sideData :=
  rfl

/-- The componentwise conversion keeps the supplied project prime side. -/
theorem toFormulaIdentityData_primeSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    bridge.toFormulaIdentityData.sideData.primeSide f =
      sourceData.sideData.sourcePrimeSide f := by
  rw [bridge.toFormulaIdentityData_sideData]
  exact bridge.primeSide_eq_sourcePrimeSide f

/-- The componentwise conversion keeps the supplied project pole side. -/
theorem toFormulaIdentityData_poleSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    bridge.toFormulaIdentityData.sideData.poleSide f =
      sourceData.sideData.sourcePoleSide f := by
  rw [bridge.toFormulaIdentityData_sideData]
  exact bridge.poleSide_eq_sourcePoleSide f

/-- The componentwise conversion keeps the supplied project gamma side. -/
theorem toFormulaIdentityData_gammaSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    bridge.toFormulaIdentityData.sideData.gammaSide f =
      sourceData.sideData.sourceGammaSide f := by
  rw [bridge.toFormulaIdentityData_sideData]
  exact bridge.gammaSide_eq_sourceGammaSide f

/-- The converted project residual side is the source residual side. -/
theorem toFormulaIdentityData_residualSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    bridge.toFormulaIdentityData.sideData.residualSide f =
      sourceData.sideData.sourceResidualSide f :=
  bridge.residualSide_eq_sourceResidualSide f

/--
The normalized project zero side equals the source residual side. This is the
source explicit formula transported through the componentwise normalization
bridge.
-/
theorem zeroSide_eq_sourceResidualSide
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = sourceData.sideData.sourceResidualSide f := by
  calc
    zeroSide.zeroSide f = sourceData.sideData.sourceZeroSide f :=
      bridge.zeroSide_eq_sourceZeroSide f
    _ = sourceData.sideData.sourceResidualSide f :=
      sourceData.sourceExplicitFormula f

/--
Source residual nonnegativity on an admissible class transports to the
componentwise-normalized formula residual side.
-/
theorem residual_nonneg_on_admissible_of_source
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (admissible : SchwartzLineTestFunction -> Prop)
    (source_residual_nonneg_on_admissible :
      forall f : SchwartzLineTestFunction,
        admissible f -> 0 <= sourceData.sideData.sourceResidualSide f) :
    forall f : SchwartzLineTestFunction,
      admissible f ->
        0 <= bridge.toFormulaIdentityData.sideData.residualSide f := by
  intro f hf
  rw [bridge.toFormulaIdentityData_residualSide f]
  exact source_residual_nonneg_on_admissible f hf

/--
The componentwise project explicit formula is exactly the transported source
formula, with the final residual side rewritten into project notation.
-/
theorem toFormulaIdentityData_explicitFormula_eq_source
    {sourceData : GuinandWeilFormulaIdentityData}
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (bridge :
      GuinandWeilComponentwiseNormalizationBridge sourceData zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f =
      bridge.toFormulaIdentityData.sideData.residualSide f := by
  rw [bridge.toFormulaIdentityData_residualSide f]
  exact bridge.zeroSide_eq_sourceResidualSide f

end GuinandWeilComponentwiseNormalizationBridge

/--
A project-level componentwise Guinand-Weil formula package built from
truncated source identities.

This is the theorem-facing version of the explicit-formula route: the analytic
work supplies finite/truncated identities, convergence of each source side, and
componentwise normalization equalities into the project convention.  Lean then
packages the resulting project formula identity.
-/
structure GuinandWeilComponentwiseTruncatedLimitPackage
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sourceSideData : GuinandWeilFormulaSideData
  limitData : GuinandWeilTruncatedFormulaLimitData sourceSideData
  normalizationBridge :
    GuinandWeilComponentwiseNormalizationBridge
      limitData.toFormulaIdentityData zeroSide

namespace GuinandWeilComponentwiseTruncatedLimitPackage

/-- The source identity data obtained by taking limits of truncated formulae. -/
noncomputable def sourceData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide) :
    GuinandWeilFormulaIdentityData :=
  pkg.limitData.toFormulaIdentityData

/-- The source explicit formula proved by the truncation/limit package. -/
theorem sourceExplicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.sourceSideData.sourceZeroSide f =
      pkg.sourceSideData.sourceResidualSide f :=
  pkg.limitData.sourceExplicitFormula f

/-- The project formula identity data induced by the limit and normalization data. -/
noncomputable def formulaData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  pkg.normalizationBridge.toFormulaIdentityData

/-- The normalized project formula identity obtained from truncated source formulae. -/
theorem explicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = pkg.formulaData.sideData.residualSide f :=
  pkg.formulaData.explicitFormula f

/-- The project prime side is the source prime side after componentwise normalization. -/
theorem formulaData_primeSide_eq_sourcePrimeSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.primeSide f =
      pkg.sourceSideData.sourcePrimeSide f := by
  change
    pkg.normalizationBridge.toFormulaIdentityData.sideData.primeSide f =
      pkg.sourceSideData.sourcePrimeSide f
  rw [pkg.normalizationBridge.toFormulaIdentityData_sideData]
  exact pkg.normalizationBridge.primeSide_eq_sourcePrimeSide f

/-- The project pole side is the source pole side after componentwise normalization. -/
theorem formulaData_poleSide_eq_sourcePoleSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.poleSide f =
      pkg.sourceSideData.sourcePoleSide f := by
  change
    pkg.normalizationBridge.toFormulaIdentityData.sideData.poleSide f =
      pkg.sourceSideData.sourcePoleSide f
  rw [pkg.normalizationBridge.toFormulaIdentityData_sideData]
  exact pkg.normalizationBridge.poleSide_eq_sourcePoleSide f

/-- The project gamma side is the source gamma side after componentwise normalization. -/
theorem formulaData_gammaSide_eq_sourceGammaSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.gammaSide f =
      pkg.sourceSideData.sourceGammaSide f := by
  change
    pkg.normalizationBridge.toFormulaIdentityData.sideData.gammaSide f =
      pkg.sourceSideData.sourceGammaSide f
  rw [pkg.normalizationBridge.toFormulaIdentityData_sideData]
  exact pkg.normalizationBridge.gammaSide_eq_sourceGammaSide f

/-- The project residual side is the source residual side after componentwise normalization. -/
theorem formulaData_residualSide_eq_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.residualSide f =
      pkg.sourceSideData.sourceResidualSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_residualSide f

end GuinandWeilComponentwiseTruncatedLimitPackage

/--
A project-level componentwise Guinand-Weil formula package built from
truncated source identities with a signed error term tending to zero.

This is the closest current target to the contour-shift explicit-formula proof:
finite cutoff identity, side convergence, vanishing error, and componentwise
normalization are separate fields.
-/
structure GuinandWeilComponentwiseTruncatedErrorLimitPackage
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sourceSideData : GuinandWeilFormulaSideData
  errorLimitData : GuinandWeilTruncatedFormulaErrorLimitData sourceSideData
  normalizationBridge :
    GuinandWeilComponentwiseNormalizationBridge
      errorLimitData.toFormulaIdentityData zeroSide

namespace GuinandWeilComponentwiseTruncatedErrorLimitPackage

/-- The source identity data obtained by taking limits of truncated formulae with error. -/
noncomputable def sourceData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide) :
    GuinandWeilFormulaIdentityData :=
  pkg.errorLimitData.toFormulaIdentityData

/-- The source explicit formula proved by the vanishing-error package. -/
theorem sourceExplicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.sourceSideData.sourceZeroSide f =
      pkg.sourceSideData.sourceResidualSide f :=
  pkg.errorLimitData.sourceExplicitFormula f

/-- The project formula identity data induced by the error-limit and normalization data. -/
noncomputable def formulaData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  pkg.normalizationBridge.toFormulaIdentityData

/-- The normalized project formula identity obtained from truncated source formulae with error. -/
theorem explicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = pkg.formulaData.sideData.residualSide f :=
  pkg.formulaData.explicitFormula f

/-- The project prime side is the source prime side after componentwise normalization. -/
theorem formulaData_primeSide_eq_sourcePrimeSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.primeSide f =
      pkg.sourceSideData.sourcePrimeSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_primeSide f

/-- The project pole side is the source pole side after componentwise normalization. -/
theorem formulaData_poleSide_eq_sourcePoleSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.poleSide f =
      pkg.sourceSideData.sourcePoleSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_poleSide f

/-- The project gamma side is the source gamma side after componentwise normalization. -/
theorem formulaData_gammaSide_eq_sourceGammaSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.gammaSide f =
      pkg.sourceSideData.sourceGammaSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_gammaSide f

/-- The project residual side is the source residual side after componentwise normalization. -/
theorem formulaData_residualSide_eq_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.residualSide f =
      pkg.sourceSideData.sourceResidualSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_residualSide f

/--
An exact truncation/limit package is a signed-error package with identically
zero truncation error.

This lifts the data-level weakening to the componentwise package layer, so a
future exact cutoff proof can still feed APIs expecting the contour-shift
signed-error shape.
-/
noncomputable def ofTruncatedLimitPackage
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide) :
    GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide where
  sourceSideData := pkg.sourceSideData
  errorLimitData :=
    GuinandWeilTruncatedFormulaErrorLimitData.ofTruncatedFormulaLimitData
      pkg.limitData
  normalizationBridge :=
    { sideData := pkg.normalizationBridge.sideData
      zeroSide_eq_sourceZeroSide := by
        intro f
        exact pkg.normalizationBridge.zeroSide_eq_sourceZeroSide f
      primeSide_eq_sourcePrimeSide := by
        intro f
        exact pkg.normalizationBridge.primeSide_eq_sourcePrimeSide f
      poleSide_eq_sourcePoleSide := by
        intro f
        exact pkg.normalizationBridge.poleSide_eq_sourcePoleSide f
      gammaSide_eq_sourceGammaSide := by
        intro f
        exact pkg.normalizationBridge.gammaSide_eq_sourceGammaSide f }

end GuinandWeilComponentwiseTruncatedErrorLimitPackage

/--
A project-level componentwise Guinand-Weil formula package built from
truncated source identities with an absolute error envelope tending to zero.

This is the preferred target for analytic estimates stated as
`|error| <= envelope` plus `envelope -> 0`.
-/
structure GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sourceSideData : GuinandWeilFormulaSideData
  boundLimitData : GuinandWeilTruncatedFormulaErrorBoundLimitData sourceSideData
  normalizationBridge :
    GuinandWeilComponentwiseNormalizationBridge
      boundLimitData.toFormulaIdentityData zeroSide

namespace GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage

/-- The source identity data obtained from bounded-error truncated formulae. -/
noncomputable def sourceData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide) :
    GuinandWeilFormulaIdentityData :=
  pkg.boundLimitData.toFormulaIdentityData

/-- The source explicit formula proved by the bounded-error package. -/
theorem sourceExplicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.sourceSideData.sourceZeroSide f =
      pkg.sourceSideData.sourceResidualSide f :=
  pkg.boundLimitData.toFormulaIdentityData.sourceExplicitFormula f

/-- The project formula identity data induced by the bounded-error and normalization data. -/
noncomputable def formulaData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  pkg.normalizationBridge.toFormulaIdentityData

/-- The normalized project formula identity obtained from bounded-error truncated formulae. -/
theorem explicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = pkg.formulaData.sideData.residualSide f :=
  pkg.formulaData.explicitFormula f

/-- The project prime side is the source prime side after componentwise normalization. -/
theorem formulaData_primeSide_eq_sourcePrimeSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.primeSide f =
      pkg.sourceSideData.sourcePrimeSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_primeSide f

/-- The project pole side is the source pole side after componentwise normalization. -/
theorem formulaData_poleSide_eq_sourcePoleSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.poleSide f =
      pkg.sourceSideData.sourcePoleSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_poleSide f

/-- The project gamma side is the source gamma side after componentwise normalization. -/
theorem formulaData_gammaSide_eq_sourceGammaSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.gammaSide f =
      pkg.sourceSideData.sourceGammaSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_gammaSide f

/-- The project residual side is the source residual side after componentwise normalization. -/
theorem formulaData_residualSide_eq_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.residualSide f =
      pkg.sourceSideData.sourceResidualSide f := by
  simpa [formulaData, GuinandWeilTruncatedFormulaErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_residualSide f

/--
A signed-error package is an absolute-error-envelope package using the
absolute value of the signed error as the envelope.
-/
noncomputable def ofErrorLimitPackage
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide) :
    GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide where
  sourceSideData := pkg.sourceSideData
  boundLimitData :=
    GuinandWeilTruncatedFormulaErrorBoundLimitData.ofErrorLimitData
      pkg.errorLimitData
  normalizationBridge :=
    { sideData := pkg.normalizationBridge.sideData
      zeroSide_eq_sourceZeroSide := by
        intro f
        exact pkg.normalizationBridge.zeroSide_eq_sourceZeroSide f
      primeSide_eq_sourcePrimeSide := by
        intro f
        exact pkg.normalizationBridge.primeSide_eq_sourcePrimeSide f
      poleSide_eq_sourcePoleSide := by
        intro f
        exact pkg.normalizationBridge.poleSide_eq_sourcePoleSide f
      gammaSide_eq_sourceGammaSide := by
        intro f
        exact pkg.normalizationBridge.gammaSide_eq_sourceGammaSide f }

/-- An exact truncation/limit package is also an absolute-error-envelope package. -/
noncomputable def ofTruncatedLimitPackage
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide) :
    GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide :=
  ofErrorLimitPackage
    (GuinandWeilComponentwiseTruncatedErrorLimitPackage.ofTruncatedLimitPackage
      pkg)

end GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage

/--
A project-level componentwise Guinand-Weil formula package built from
truncated source identities with an eventual absolute error envelope.

This is useful when a source explicit formula only proves its error estimate
after a cutoff depending on the test function.
-/
structure GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage
    (zeroSide : SchwartzRiemannWeilZeroSide) where
  sourceSideData : GuinandWeilFormulaSideData
  eventualBoundLimitData :
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData sourceSideData
  normalizationBridge :
    GuinandWeilComponentwiseNormalizationBridge
      eventualBoundLimitData.toFormulaIdentityData zeroSide

namespace GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage

/-- The source identity data obtained from eventual bounded-error truncated formulae. -/
noncomputable def sourceData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide) :
    GuinandWeilFormulaIdentityData :=
  pkg.eventualBoundLimitData.toFormulaIdentityData

/-- The source explicit formula proved by the eventual bounded-error package. -/
theorem sourceExplicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.sourceSideData.sourceZeroSide f =
      pkg.sourceSideData.sourceResidualSide f :=
  pkg.eventualBoundLimitData.toFormulaIdentityData.sourceExplicitFormula f

/-- The project formula identity data induced by the eventual-error and normalization data. -/
noncomputable def formulaData
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide) :
    SchwartzRiemannWeilFormulaIdentityData zeroSide :=
  pkg.normalizationBridge.toFormulaIdentityData

/-- The normalized project formula identity obtained from eventual bounded-error formulae. -/
theorem explicitFormula
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    zeroSide.zeroSide f = pkg.formulaData.sideData.residualSide f :=
  pkg.formulaData.explicitFormula f

/-- The project prime side is the source prime side after componentwise normalization. -/
theorem formulaData_primeSide_eq_sourcePrimeSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.primeSide f =
      pkg.sourceSideData.sourcePrimeSide f := by
  simpa [formulaData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_primeSide f

/-- The project pole side is the source pole side after componentwise normalization. -/
theorem formulaData_poleSide_eq_sourcePoleSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.poleSide f =
      pkg.sourceSideData.sourcePoleSide f := by
  simpa [formulaData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_poleSide f

/-- The project gamma side is the source gamma side after componentwise normalization. -/
theorem formulaData_gammaSide_eq_sourceGammaSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.gammaSide f =
      pkg.sourceSideData.sourceGammaSide f := by
  simpa [formulaData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_gammaSide f

/-- The project residual side is the source residual side after componentwise normalization. -/
theorem formulaData_residualSide_eq_sourceResidualSide
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide)
    (f : SchwartzLineTestFunction) :
    pkg.formulaData.sideData.residualSide f =
      pkg.sourceSideData.sourceResidualSide f := by
  simpa [formulaData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toFormulaIdentityData,
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.toErrorLimitData,
    GuinandWeilTruncatedFormulaErrorLimitData.toFormulaIdentityData]
    using pkg.normalizationBridge.toFormulaIdentityData_residualSide f

/--
A pointwise absolute-error-envelope package is an eventual-error-envelope
package.
-/
noncomputable def ofErrorBoundLimitPackage
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage zeroSide) :
    GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide where
  sourceSideData := pkg.sourceSideData
  eventualBoundLimitData :=
    GuinandWeilTruncatedFormulaEventualErrorBoundLimitData.ofErrorBoundLimitData
      pkg.boundLimitData
  normalizationBridge :=
    { sideData := pkg.normalizationBridge.sideData
      zeroSide_eq_sourceZeroSide := by
        intro f
        exact pkg.normalizationBridge.zeroSide_eq_sourceZeroSide f
      primeSide_eq_sourcePrimeSide := by
        intro f
        exact pkg.normalizationBridge.primeSide_eq_sourcePrimeSide f
      poleSide_eq_sourcePoleSide := by
        intro f
        exact pkg.normalizationBridge.poleSide_eq_sourcePoleSide f
      gammaSide_eq_sourceGammaSide := by
        intro f
        exact pkg.normalizationBridge.gammaSide_eq_sourceGammaSide f }

/-- A signed-error package is also an eventual-error-envelope package. -/
noncomputable def ofErrorLimitPackage
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedErrorLimitPackage zeroSide) :
    GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide :=
  ofErrorBoundLimitPackage
    (GuinandWeilComponentwiseTruncatedErrorBoundLimitPackage.ofErrorLimitPackage
      pkg)

/-- An exact truncation/limit package is also an eventual-error-envelope package. -/
noncomputable def ofTruncatedLimitPackage
    {zeroSide : SchwartzRiemannWeilZeroSide}
    (pkg : GuinandWeilComponentwiseTruncatedLimitPackage zeroSide) :
    GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage zeroSide :=
  ofErrorLimitPackage
    (GuinandWeilComponentwiseTruncatedErrorLimitPackage.ofTruncatedLimitPackage
      pkg)

end GuinandWeilComponentwiseTruncatedEventualErrorBoundLimitPackage

end RiemannHypothesisProject
