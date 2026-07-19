import RiemannHypothesisProject.RiemannVonMangoldt.AxisWindows

/-!
# Real-axis theorem surfaces for Riemann-von-Mangoldt cleanup

This module names the real-axis zero classification, open-unit-interval
nonvanishing, and no-residual theorem surfaces used by the axis decomposition.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open Asymptotics Filter MeasureTheory

open scoped ComplexConjugate Topology

noncomputable section

/--
All real-axis zeta zeroes are project-known trivial zeroes.

This is the natural analytic target left by the axis decomposition. Once it is
proved, the residual real-axis window vanishes in every closed-ball stage.
-/
def NoResidualRealAxisZetaZeros : Prop :=
  forall rho : ZetaZeroSubtype,
    Complex.im (rho : Complex) = 0 ->
      IsKnownTrivialAxisZetaZero rho

/--
Classical real-axis zero classification, in project vocabulary: every real
zero of the Riemann zeta function is one of the known negative-even trivial
zeroes.
-/
def RealAxisZetaZeroClassification : Prop :=
  forall s : Complex,
    IsZetaZero s ->
      Complex.im s = 0 ->
        IsTrivialZetaZero s

/--
Real-axis zero classification after the already-proved zero-free half-plane
`1 <= re s` has been removed.

This is the sharper residual analytic target: future work only has to classify
real zeta zeroes that lie strictly left of `re s = 1`; the right closed
half-plane is handled by Mathlib's nonvanishing theorem.
-/
def LeftRealAxisZetaZeroClassification : Prop :=
  forall s : Complex,
    IsZetaZero s ->
      Complex.im s = 0 ->
        s.re < 1 ->
          IsTrivialZetaZero s

/--
No real zeta zero lies in the open real interval `(0, 1)`.

Together with the checked nonpositive real-axis classification below and
Mathlib's closed right-half-plane nonvanishing theorem, this is the exact
remaining real-axis analytic gap.
-/
def OpenUnitIntervalRealAxisZetaZeroFree : Prop :=
  forall s : Complex,
    IsZetaZero s ->
      Complex.im s = 0 ->
        0 < s.re ->
          s.re < 1 ->
            False

/--
Real-variable form of the remaining real-axis gap: zeta is nonzero for
real arguments in the open interval `(0, 1)`.
-/
def OpenUnitIntervalRiemannZetaNonzero : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        Not (riemannZeta (x : Complex) = 0)

/--
Classical sign-shaped form of the remaining real-axis gap.

Mathematically `zeta x < 0` for `0 < x < 1`; since the project zeta function is
complex-valued, this source-shaped target asks only for a negative real part,
which is enough to prove nonvanishing.
-/
def OpenUnitIntervalRiemannZetaReNegative : Prop :=
  forall x : Real,
    0 < x ->
      x < 1 ->
        (riemannZeta (x : Complex)).re < 0

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
