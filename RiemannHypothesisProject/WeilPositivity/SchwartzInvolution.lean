import Mathlib.Analysis.Complex.Basic
import RiemannHypothesisProject.SchwartzLineTestFunction

/-!
# Reflection-conjugation on Schwartz line tests

The Weil involution in additive coordinates is `g★(x) = conj (g (-x))`.
It is real-linear and conjugate-linear for the natural complex scalar action.
-/

namespace RiemannHypothesisProject

namespace SchwartzLineTestFunction

/-- Reflection of the argument, packaged as a real continuous-linear map. -/
noncomputable def reflect :
    SchwartzLineTestFunction →L[Real] SchwartzLineTestFunction :=
  SchwartzMap.compCLMOfContinuousLinearEquiv Real
    (LinearIsometryEquiv.neg Real (E := Real))

@[simp]
theorem reflect_apply (f : SchwartzLineTestFunction) (x : Real) :
    reflect f x = f (-x) :=
  rfl

/-- Pointwise complex conjugation, packaged as a real continuous-linear map. -/
noncomputable def conjugate :
    SchwartzLineTestFunction →L[Real] SchwartzLineTestFunction :=
  SchwartzMap.postcompCLM (Complex.conjCLE : Complex →L[Real] Complex)

@[simp]
theorem conjugate_apply (f : SchwartzLineTestFunction) (x : Real) :
    conjugate f x = (starRingEnd Complex) (f x) :=
  rfl

/-- Weil reflection-conjugation in additive coordinates. -/
noncomputable def star :
    SchwartzLineTestFunction →L[Real] SchwartzLineTestFunction :=
  conjugate.comp reflect

@[simp]
theorem star_apply (f : SchwartzLineTestFunction) (x : Real) :
    star f x = (starRingEnd Complex) (f (-x)) :=
  rfl

@[simp]
theorem star_star (f : SchwartzLineTestFunction) :
    star (star f) = f := by
  ext x
  simp

@[simp]
theorem star_smul (c : Complex) (f : SchwartzLineTestFunction) :
    star (c • f) = (starRingEnd Complex) c • star f := by
  ext x
  simp

end SchwartzLineTestFunction

end RiemannHypothesisProject
