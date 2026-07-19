import RiemannHypothesisProject.RiemannVonMangoldtHeightTarget

/-!
# Truncated Riemann-von Mangoldt explicit-formula target

Recent explicit-formula error-term papers suggest a useful companion to the
source-normalized Guinand-Weil target: a truncated formula for a Chebyshev
`psi`-type side, a finite zero sum up to a height cutoff, main/pole terms, and
an explicit error.

This module does not prove such a formula.  It names the data future Perron
formula and contour-shift work should provide, checks the finite zero-window
connection to the existing height-counting target, and proves that a supplied
error bound controls the difference between the Chebyshev side and the
truncated approximation.
-/

namespace RiemannHypothesisProject

/--
A finite zeta-zero window for truncated Riemann-von Mangoldt formulae.

The `heightWindow` is the finite zero set used in the truncated zero sum.  The
covering field says it is large enough to dominate the positive-ordinate
closed-ball window, so its cardinal bound can feed the existing height-counting
route.
-/
structure TruncatedRiemannVonMangoldtZeroWindowData where
  heightWindow : Nat -> Finset ZetaZeroSubtype
  covers_positiveClosedBall :
    forall n : Nat,
      ComplexCompactExhaustion.closedBallZeroPositiveOrdinateFinset n
        ⊆ heightWindow n
  windowCardBound : Nat -> Real
  windowCard_le :
    forall n : Nat,
      ((heightWindow n).card : Real) <= windowCardBound n

namespace TruncatedRiemannVonMangoldtZeroWindowData

/--
The truncated window cardinal bound also bounds the positive-ordinate
closed-ball window cardinality.
-/
theorem positiveClosedBall_card_le_windowCardBound
    (windowData : TruncatedRiemannVonMangoldtZeroWindowData)
    (n : Nat) :
    ((ComplexCompactExhaustion.closedBallZeroPositiveOrdinateFinset n).card :
        Real) <= windowData.windowCardBound n := by
  have hcard :
      (ComplexCompactExhaustion.closedBallZeroPositiveOrdinateFinset n).card <=
        (windowData.heightWindow n).card :=
    Finset.card_le_card (windowData.covers_positiveClosedBall n)
  exact le_trans (by exact_mod_cast hcard) (windowData.windowCard_le n)

/--
Turn a truncated-window bound into the positive-ordinate input for the symmetric
height-counting target, once negative-ordinate and axis/trivial bounds are
supplied.
-/
noncomputable def toSymmetricHeightCountingTarget
    (windowData : TruncatedRiemannVonMangoldtZeroWindowData)
    (cutoff : Nat)
    (axisOrTrivialBound : Nat -> Real)
    (heightEnvelopeConstant growth : Real)
    (heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant)
    (negativeWindowCard_le_windowBound :
      forall n : Nat,
        ((ComplexCompactExhaustion.closedBallZeroNegativeOrdinateFinset n).card :
            Real) <= windowData.windowCardBound n)
    (axisWindowCard_le :
      forall n : Nat,
        ((ComplexCompactExhaustion.closedBallZeroAxisOrdinateFinset n).card :
            Real) <= axisOrTrivialBound n)
    (tail_symmetricHeightEnvelope_le :
      forall n : Nat,
        windowData.windowCardBound (n + cutoff) +
            windowData.windowCardBound (n + cutoff) +
            axisOrTrivialBound (n + cutoff) <=
          heightEnvelopeConstant * |(n : Real) + 1| ^ growth) :
    ComplexCompactExhaustion.ClosedBallZeroSymmetricHeightCountingTarget :=
  ComplexCompactExhaustion.ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBounds
      cutoff
      windowData.windowCardBound
      axisOrTrivialBound
      heightEnvelopeConstant
      growth
      heightEnvelopeConstant_nonneg
      windowData.positiveClosedBall_card_le_windowCardBound
      negativeWindowCard_le_windowBound
      axisWindowCard_le
      tail_symmetricHeightEnvelope_le

end TruncatedRiemannVonMangoldtZeroWindowData

/--
The sides of a truncated Riemann-von Mangoldt formula.

The zero term may include whatever sign and normalization the chosen source
uses.  The project only fixes the finite sum and leaves every normalization as
an explicit field.
-/
structure TruncatedRiemannVonMangoldtSideData where
  chebyshevPsiSide : Real -> Real
  mainSide : Real -> Real
  poleSide : Real -> Real
  zeroWindowData : TruncatedRiemannVonMangoldtZeroWindowData
  zeroTerm : Real -> Nat -> ZetaZeroSubtype -> Real
  errorSide : Real -> Nat -> Real

namespace TruncatedRiemannVonMangoldtSideData

/-- The finite zero sum in the truncated formula. -/
noncomputable def truncatedZeroSide
    (sideData : TruncatedRiemannVonMangoldtSideData)
    (x : Real) (height : Nat) : Real :=
  (sideData.zeroWindowData.heightWindow height).sum
    (fun rho : ZetaZeroSubtype => sideData.zeroTerm x height rho)

/-- The finite approximation before the explicit error term is added. -/
noncomputable def approximatingSide
    (sideData : TruncatedRiemannVonMangoldtSideData)
    (x : Real) (height : Nat) : Real :=
  sideData.mainSide x + sideData.truncatedZeroSide x height +
    sideData.poleSide x

/-- The signed error between the Chebyshev side and the finite approximation. -/
noncomputable def formulaError
    (sideData : TruncatedRiemannVonMangoldtSideData)
    (x : Real) (height : Nat) : Real :=
  sideData.chebyshevPsiSide x - sideData.approximatingSide x height

/-- The approximation is definitionally main plus finite zero side plus pole side. -/
theorem approximatingSide_eq
    (sideData : TruncatedRiemannVonMangoldtSideData)
    (x : Real) (height : Nat) :
    sideData.approximatingSide x height =
      sideData.mainSide x + sideData.truncatedZeroSide x height +
        sideData.poleSide x :=
  rfl

end TruncatedRiemannVonMangoldtSideData

/--
A truncated Riemann-von Mangoldt formula identity.

Future analytic work should prove this from Perron formula, contour shifting,
residue computations, and estimates for the horizontal/vertical contour
contributions.
-/
structure TruncatedRiemannVonMangoldtFormulaData where
  sideData : TruncatedRiemannVonMangoldtSideData
  explicitFormula :
    forall x : Real,
      forall height : Nat,
        sideData.chebyshevPsiSide x =
          sideData.approximatingSide x height +
            sideData.errorSide x height

namespace TruncatedRiemannVonMangoldtFormulaData

/-- Build formula data directly from source sides and the source identity. -/
noncomputable def ofRawSides
    (chebyshevPsiSide mainSide poleSide : Real -> Real)
    (zeroWindowData : TruncatedRiemannVonMangoldtZeroWindowData)
    (zeroTerm : Real -> Nat -> ZetaZeroSubtype -> Real)
    (errorSide : Real -> Nat -> Real)
    (explicitFormula :
      forall x : Real,
        forall height : Nat,
          chebyshevPsiSide x =
            mainSide x +
              (zeroWindowData.heightWindow height).sum
                (fun rho : ZetaZeroSubtype => zeroTerm x height rho) +
              poleSide x +
              errorSide x height) :
    TruncatedRiemannVonMangoldtFormulaData where
  sideData :=
    { chebyshevPsiSide := chebyshevPsiSide
      mainSide := mainSide
      poleSide := poleSide
      zeroWindowData := zeroWindowData
      zeroTerm := zeroTerm
      errorSide := errorSide }
  explicitFormula := fun x height => by
    simpa [TruncatedRiemannVonMangoldtSideData.approximatingSide,
      TruncatedRiemannVonMangoldtSideData.truncatedZeroSide, add_assoc]
      using explicitFormula x height

/-- The formula error is exactly the packaged explicit error term. -/
theorem formulaError_eq_errorSide
    (formulaData : TruncatedRiemannVonMangoldtFormulaData)
    (x : Real) (height : Nat) :
    formulaData.sideData.formulaError x height =
      formulaData.sideData.errorSide x height := by
  unfold TruncatedRiemannVonMangoldtSideData.formulaError
  rw [formulaData.explicitFormula x height]
  ring

end TruncatedRiemannVonMangoldtFormulaData

/-- A bound for the explicit error in a truncated formula. -/
structure TruncatedRiemannVonMangoldtErrorBound
    (formulaData : TruncatedRiemannVonMangoldtFormulaData) where
  errorEnvelope : Real -> Nat -> Real
  errorEnvelope_nonneg :
    forall x : Real, forall height : Nat, 0 <= errorEnvelope x height
  abs_errorSide_le :
    forall x : Real,
      forall height : Nat,
        |formulaData.sideData.errorSide x height| <=
          errorEnvelope x height

namespace TruncatedRiemannVonMangoldtErrorBound

/-- The supplied error envelope bounds the actual formula error. -/
theorem abs_formulaError_le
    {formulaData : TruncatedRiemannVonMangoldtFormulaData}
    (errorBound : TruncatedRiemannVonMangoldtErrorBound formulaData)
    (x : Real) (height : Nat) :
    |formulaData.sideData.formulaError x height| <=
      errorBound.errorEnvelope x height := by
  rw [formulaData.formulaError_eq_errorSide x height]
  exact errorBound.abs_errorSide_le x height

end TruncatedRiemannVonMangoldtErrorBound

end RiemannHypothesisProject
