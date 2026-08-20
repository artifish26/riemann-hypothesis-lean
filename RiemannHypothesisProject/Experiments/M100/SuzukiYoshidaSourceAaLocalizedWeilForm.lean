import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceAaEquation25Closure
import RiemannHypothesisProject.WeilPositivity.ZetaZeroPairing
import RiemannHypothesisProject.SchwartzRiemannWeilWeight

/-!
# Literal localized Weil form for Suzuki's source `A_a`

Suzuki's equation (3.1) defines the localized closed Weil form by the
analytic-multiplicity zero sum of the Fourier values of interval-supported
vectors.  This module records that source definition independently of the
project's corrected completed form.

The form is transported along the already constructed map from the project's
completed logarithmic domain to finite-interval `L²`.  No normalization with
`suzukiYoshidaCorrectedCompleteForm` is built into the definition.  The three
remaining source inputs are therefore stated for this literal form: its
associated-operator graph, boundedness after transport, and its smooth-core
`G_a` representation.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open ComplexConjugate MeasureTheory
open scoped InnerProductSpace

attribute [local instance] Measure.Subtype.measureSpace

/-! ## Compact-interval Fourier evaluation at a complex frequency -/

/-- The `L²(-a,a)` vector whose inner product against `u` is
`∫ u(x) exp (i z x) dx`.  The conjugated frequency is forced by Mathlib's
conjugate-linear-first inner-product convention. -/
def suzukiFiniteIntervalComplexExponential
    (a : Real) (z : Complex) : SuzukiFiniteIntervalL2 a :=
  suzukiFiniteIntervalContinuousToL2 a
    ⟨fun x => Complex.exp
        (-Complex.I * conj z * (x.1 : Complex)), by fun_prop⟩

/-- Entire Fourier evaluation of an interval `L²` vector.  Compact support
makes this a bounded evaluation functional at every complex frequency. -/
def suzukiFiniteIntervalFourierValue
    (a : Real) (u : SuzukiFiniteIntervalL2 a) (z : Complex) : Complex :=
  inner Complex (suzukiFiniteIntervalComplexExponential a z) u

/-- The inner-product definition has Suzuki's literal Fourier-integral
normalization. -/
theorem suzukiFiniteIntervalFourierValue_eq_integral
    (a : Real) (u : SuzukiFiniteIntervalL2 a) (z : Complex) :
    suzukiFiniteIntervalFourierValue a u z =
      ∫ x : SuzukiFiniteInterval a,
        Complex.exp (Complex.I * z * (x.1 : Complex)) * u x := by
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    ⟨by
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
      exact measure_Icc_lt_top⟩
  rw [suzukiFiniteIntervalFourierValue, MeasureTheory.L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (⟨fun x => Complex.exp
          (-Complex.I * conj z * (x.1 : Complex)), by fun_prop⟩ :
        C(SuzukiFiniteInterval a, Complex))] with x hx
  rw [suzukiFiniteIntervalComplexExponential,
    suzukiFiniteIntervalContinuousToL2, hx]
  change (u x) * conj (Complex.exp
      (-Complex.I * conj z * (x.1 : Complex))) =
    Complex.exp (Complex.I * z * (x.1 : Complex)) * u x
  rw [← Complex.exp_conj]
  have harg :
      conj (-Complex.I * conj z * (x.1 : Complex)) =
        Complex.I * z * (x.1 : Complex) := by
    simp
  rw [harg]
  ring

theorem suzukiFiniteIntervalFourierValue_add
    (a : Real) (u v : SuzukiFiniteIntervalL2 a) (z : Complex) :
    suzukiFiniteIntervalFourierValue a (u + v) z =
      suzukiFiniteIntervalFourierValue a u z +
        suzukiFiniteIntervalFourierValue a v z := by
  simp [suzukiFiniteIntervalFourierValue, inner_add_right]

theorem suzukiFiniteIntervalFourierValue_smul
    (a : Real) (c : Complex) (u : SuzukiFiniteIntervalL2 a) (z : Complex) :
    suzukiFiniteIntervalFourierValue a (c • u) z =
      c * suzukiFiniteIntervalFourierValue a u z := by
  simp [suzukiFiniteIntervalFourierValue, inner_smul_right]

/-! ## Suzuki's zero coordinate and literal zero-side form -/

/-- Suzuki indexes the zeros of `z ↦ ξ(1/2 - i z)`.  This is the negative of
the project's Riemann--Weil zero coordinate. -/
def suzukiSourceGammaArgument (rho : Complex) : Complex :=
  -riemannWeilZeroArgument rho

theorem suzukiSourceGammaArgument_eq
    (rho : Complex) :
    suzukiSourceGammaArgument rho =
      Complex.I * (rho - (1 / 2 : Complex)) := by
  unfold suzukiSourceGammaArgument riemannWeilZeroArgument
  field_simp [Complex.I_ne_zero]
  rw [Complex.I_sq]
  ring

/-- The entire transform of a finite-interval vector, expressed as a function
of a zeta zero rather than Suzuki's spectral coordinate. -/
def suzukiSourceWeilTransform
    (a : Real) (u : SuzukiFiniteIntervalL2 a) : Complex → Complex :=
  fun rho => suzukiFiniteIntervalFourierValue a u
    (suzukiSourceGammaArgument rho)

/-- Suzuki's literal localized Weil pairing, using the project's checked
analytic-multiplicity grouping of the zeta zeros.  This is the polarized form
of Suzuki's equation (3.1). -/
def suzukiSourceLocalizedWeilPairing
    (a : Real) (u v : SuzukiFiniteIntervalL2 a) : Complex :=
  ComplexCompactExhaustion.zetaWeilPairing
    (suzukiSourceWeilTransform a u)
    (suzukiSourceWeilTransform a v)

theorem suzukiSourceLocalizedWeilPairing_conj_symm
    (a : Real) (u v : SuzukiFiniteIntervalL2 a) :
    suzukiSourceLocalizedWeilPairing a u v =
      conj (suzukiSourceLocalizedWeilPairing a v u) := by
  exact ComplexCompactExhaustion.zetaWeilPairing_conj_symm
    (suzukiSourceWeilTransform a u)
    (suzukiSourceWeilTransform a v)

/-! ## Transport to the completed source-form domain -/

/-- The literal source localized Weil form at the frozen endpoint, transported
to the completed form domain but not identified with the project form.

Suzuki's convention makes `Q_W(v₁,v₂)` linear in `v₁`, whereas Mathlib's
`inner` is conjugate-linear in its first argument.  The transported
operator-facing form therefore reverses the two arguments. -/
def suzukiSourceAaLocalizedWeilForm : SuzukiSourceAaClosedForm :=
  fun u v => suzukiSourceLocalizedWeilPairing suzukiProjectAStar
    (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v)
    (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)

theorem suzukiSourceAaLocalizedWeilForm_conj_symm
    (u v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiSourceAaLocalizedWeilForm u v =
      conj (suzukiSourceAaLocalizedWeilForm v u) := by
  exact suzukiSourceLocalizedWeilPairing_conj_symm
    suzukiProjectAStar
    (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v)
    (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u)

/-- Exact source theorem still required from the independent closed-form
construction: `A_a` is represented by the literal zero-side form. -/
def SuzukiSourceAaLocalizedWeilAssociatedRepresentation
    (A : SuzukiSourceAaOperator) : Prop :=
  SuzukiSourceAaAssociatedSourceFormRepresentation A
    suzukiSourceAaLocalizedWeilForm

/-- The transported form domain must consist of vectors for which Suzuki's
literal zero-side pairing is genuinely summable.  This condition is kept
separate from Lean's totalized `tsum`. -/
def SuzukiSourceAaLocalizedWeilPairingSummable : Prop :=
  ∀ u v : SuzukiYoshidaCorrectedCommonFormDomain,
    Summable (ComplexCompactExhaustion.zetaWeilPairingSummand
      (suzukiSourceWeilTransform suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 u))
      (suzukiSourceWeilTransform suzukiProjectAStar
        (suzukiLogRadiusLinearCompletionToFiniteIntervalL2 v)))

/-- Exact transported bounded-form theorem still required for the literal
zero-side form.  It includes the source-domain summability which Lean's
totalized `tsum` does not record by itself. -/
def SuzukiSourceAaLocalizedWeilFormBounded : Prop :=
  SuzukiSourceAaLocalizedWeilPairingSummable ∧
    SuzukiSourceAaClosedFormBoundedRealBilinear
      suzukiSourceAaLocalizedWeilForm

/-- Exact smooth-core theorem still required for the literal zero-side form. -/
def SuzukiSourceAaLocalizedWeilFormCoreGRepresentation : Prop :=
  SuzukiSourceAaClosedFormCoreGRepresentation
    suzukiSourceAaLocalizedWeilForm

/-! ## Exact-form endpoint receivers -/

/-- Once the three independent source theorems are proved for the literal
localized Weil form, the source operator is the checked project operator. -/
theorem sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_of_localizedWeilForm
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hbounded : SuzukiSourceAaLocalizedWeilFormBounded)
    (hcore : SuzukiSourceAaLocalizedWeilFormCoreGRepresentation) :
    A = suzukiYoshidaCorrectedFormAssociatedOperator :=
  sourceAa_eq_suzukiYoshidaCorrectedFormAssociatedOperator_proved
    A suzukiSourceAaLocalizedWeilForm hsourceGraph hbounded.2 hcore

/-- The same three literal-form inputs give the source operator's
self-adjointness. -/
theorem sourceAa_isSelfAdjoint_of_localizedWeilForm
    (A : SuzukiSourceAaOperator)
    (hsourceGraph : SuzukiSourceAaLocalizedWeilAssociatedRepresentation A)
    (hbounded : SuzukiSourceAaLocalizedWeilFormBounded)
    (hcore : SuzukiSourceAaLocalizedWeilFormCoreGRepresentation) :
    IsSelfAdjoint A :=
  sourceAa_isSelfAdjoint_proved
    A suzukiSourceAaLocalizedWeilForm hsourceGraph hbounded.2 hcore

end

end RiemannHypothesisProject.Experiments.M100
