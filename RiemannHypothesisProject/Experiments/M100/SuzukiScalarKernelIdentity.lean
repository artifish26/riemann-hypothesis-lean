import RiemannHypothesisProject.Experiments.M100.SuzukiScalarKernelBridge
import RiemannHypothesisProject.RiemannVonMangoldt.Binet.GaussDigammaHolomorphic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# M100-X14 Suzuki scalar kernel identity

This experimental module proves the arithmetic component identities needed
to discharge `SuzukiScalarKernelIdentityAt`.  It imports the normalization
and continuity surface from `SuzukiScalarKernelBridge` and introduces no
positivity, zero-location, spectral, or operator assumptions.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open MeasureTheory
open SchwartzLineTestFunction
open scoped ComplexConjugate Convolution FourierTransform

noncomputable section

/-- One literature-normalized prime term on the scaled project base is
exactly the pair of source-autocorrelation samples in Suzuki's convention. -/
theorem guinandWeilLiteraturePrimeTerm_suzukiProjectBase
    (v : SchwartzLineTestFunction) (n : Nat) :
    guinandWeilLiteraturePrimeTerm
        (fourierAutocorrelation (suzukiProjectBase v)) n =
      -(ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
        ((autocorrelation v (Real.log (n : Real))).re +
          (autocorrelation v (-Real.log (n : Real))).re) := by
  rw [guinandWeilLiteraturePrimeTerm]
  change
    -(1 / (2 * Real.pi)) *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
        (((𝓕 (fourierAutocorrelation (suzukiProjectBase v)))
            (Real.log (n : Real) / (2 * Real.pi))).re +
          ((𝓕 (fourierAutocorrelation (suzukiProjectBase v)))
            (-Real.log (n : Real) / (2 * Real.pi))).re) = _
  rw [
    fourier_fourierAutocorrelation_apply,
    fourier_fourierAutocorrelation_apply,
    autocorrelation_suzukiProjectBase,
    suzukiProjectBase_apply, suzukiProjectBase_apply]
  unfold suzukiCoordinateScale suzukiTwoPi
  push_cast
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  field_simp [Real.pi_ne_zero]

/-- The full normalized prime side is the source-coordinate
autocorrelation sampling series. -/
theorem guinandWeilLiteraturePrimeSide_suzukiProjectBase
    (v : SchwartzLineTestFunction) :
    guinandWeilLiteraturePrimeSide
        (fourierAutocorrelation (suzukiProjectBase v)) =
      ∑' n : Nat,
        -(ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
          ((autocorrelation v (Real.log (n : Real))).re +
            (autocorrelation v (-Real.log (n : Real))).re) := by
  unfold guinandWeilLiteraturePrimeSide
  apply tsum_congr
  exact guinandWeilLiteraturePrimeTerm_suzukiProjectBase v

/-- The project pole side becomes Suzuki's two Fourier-Laplace evaluations
with no residual scale or reflection. -/
theorem guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase
    (v : SchwartzLineTestFunction) :
    guinandWeilBurnolLiteraturePoleSide (suzukiProjectBase v) =
      (suzukiFourierSource (autocorrelation v) (Complex.I / 2) +
        suzukiFourierSource (autocorrelation v) (-Complex.I / 2)).re := by
  rw [guinandWeilBurnolLiteraturePoleSide,
    burnolFourierLaplaceSource_suzukiProjectBase,
    burnolFourierLaplaceSource_suzukiProjectBase]

private theorem schwartz_eq_zero_at_endpoints_of_support_subset_Icc
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    v (-a) = 0 ∧ v a = 0 := by
  have hopen : IsOpen (Function.support v) := v.continuous.isOpen_support
  have hinterior : Function.support v ⊆ interior (Set.Icc (-a) a) :=
    (hopen.subset_interior_iff).2 hsupport
  constructor
  · by_contra hne
    have hmem := hinterior hne
    rw [interior_Icc] at hmem
    exact (lt_irrefl (-a)) hmem.1
  · by_contra hne
    have hmem := hinterior hne
    rw [interior_Icc] at hmem
    exact (lt_irrefl a) hmem.2

private theorem hasDerivAt_complexRealExp_mul (c x : Real) :
    HasDerivAt (fun y : Real => (Real.exp (c * y) : Complex))
      ((c : Complex) * Real.exp (c * x)) x := by
  have hlinear : HasDerivAt (fun y : Real => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hexp : HasDerivAt (fun y : Real => Real.exp (c * y))
      (Real.exp (c * x) * c) x :=
    (Real.hasDerivAt_exp (c * x)).comp x hlinear
  convert hexp.ofReal_comp using 1
  rw [← Complex.ofReal_mul]
  ring

/-- Compact support removes the boundary term when a source derivative is
paired with a real exponential on Suzuki's interval. -/
theorem setIntegral_exp_mul_deriv_eq
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (c : Real) :
    (∫ x in Set.Icc (-a) a,
        (Real.exp (c * x) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x) =
      -(c : Complex) *
        ∫ x in Set.Icc (-a) a,
          (Real.exp (c * x) : Complex) * v x := by
  rcases schwartz_eq_zero_at_endpoints_of_support_subset_Icc ha hsupport with
    ⟨hleft, hright⟩
  have hle : -a ≤ a := by linarith
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -a) (b := a)
    (u := fun x : Real => (Real.exp (c * x) : Complex))
    (v := fun x : Real => v x)
    (u' := fun x : Real => (c : Complex) * Real.exp (c * x))
    (v' := fun x : Real => SchwartzMap.derivCLM Complex Complex v x)
    (fun x _ => hasDerivAt_complexRealExp_mul c x)
    (fun x _ => by
      simpa only [SchwartzMap.derivCLM_apply] using v.hasDerivAt x)
    ((by fun_prop : Continuous (fun x : Real =>
      (c : Complex) * Real.exp (c * x))).intervalIntegrable _ _)
    ((SchwartzMap.derivCLM Complex Complex v).continuous.intervalIntegrable _ _)
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  rw [hibp, hleft, hright]
  simp only [mul_zero, sub_zero, zero_sub]
  rw [← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- The pole-only summand of Suzuki's explicit screw function. -/
def suzukiPoleScrewKernel (t : Real) : Real :=
  -4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2)

private theorem setIntegral_conj_exp_mul_deriv_eq_conj
    {a c : Real} (v : SchwartzLineTestFunction) :
    (∫ x in Set.Icc (-a) a,
        (Real.exp (c * x) : Complex) *
          conj (SchwartzMap.derivCLM Complex Complex v x)) =
      conj (∫ x in Set.Icc (-a) a,
        (Real.exp (c * x) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  change
    (Real.exp (c * x) : Complex) *
        conj (SchwartzMap.derivCLM Complex Complex v x) =
      conj ((Real.exp (c * x) : Complex) *
        SchwartzMap.derivCLM Complex Complex v x)
  rw [map_mul, Complex.conj_ofReal]

private theorem setIntegral_suzukiFiniteSquare_separable
    (a : Real) (f g : Real → Complex) :
    (∫ p in suzukiFiniteSquare a, f p.1 * g p.2) =
      (∫ x in Set.Icc (-a) a, f x) *
        ∫ y in Set.Icc (-a) a, g y := by
  simpa [suzukiFiniteSquare, MeasureTheory.Measure.volume_eq_prod] using
    (MeasureTheory.setIntegral_prod_mul f g
      (Set.Icc (-a) a) (Set.Icc (-a) a))

private theorem integrable_exp_mul_schwartz_of_support_subset_Icc
    {a c : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    Integrable (fun x : Real => (Real.exp (c * x) : Complex) * v x) := by
  have hsub : Function.support
      (fun x : Real => (Real.exp (c * x) : Complex) * v x) ⊆
        Set.Icc (-a) a := by
    intro x hx
    exact hsupport (fun hv => hx (by simp [hv]))
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  exact (by fun_prop : Continuous
      (fun x : Real => (Real.exp (c * x) : Complex) * v x)).continuousOn
    |>.integrableOn_compact isCompact_Icc

private theorem integral_exp_mul_schwartz_eq_setIntegral
    {a c : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    (∫ x : Real, (Real.exp (c * x) : Complex) * v x) =
      ∫ x in Set.Icc (-a) a, (Real.exp (c * x) : Complex) * v x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hv : v x = 0 := by
    by_contra hne
    exact hx (hsupport hne)
  simp [hv]

private theorem integral_exp_mul_star_eq_conj
    (v : SchwartzLineTestFunction) (c : Real) :
    (∫ x : Real, (Real.exp (c * x) : Complex) * star v x) =
      conj (∫ x : Real,
        (Real.exp (-c * x) : Complex) * v x) := by
  have hreflect := integral_neg_eq_self
    (f := fun x : Real =>
      (Real.exp (c * (-x)) : Complex) * conj (v x)) volume
  calc
    (∫ x : Real, (Real.exp (c * x) : Complex) * star v x) =
        ∫ x : Real,
          (Real.exp (-c * x) : Complex) * conj (v x) := by
      simpa only [star_apply, neg_neg, mul_neg, neg_mul] using hreflect
    _ = conj (∫ x : Real,
        (Real.exp (-c * x) : Complex) * v x) := by
      rw [← integral_conj]
      apply integral_congr_ae
      filter_upwards with x
      rw [map_mul, Complex.conj_ofReal]

/-- An exponentially weighted autocorrelation factors into the two
oppositely weighted source integrals. -/
theorem integral_exp_mul_autocorrelation_eq_weightedProducts
    {a c : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    (∫ x : Real,
        (Real.exp (c * x) : Complex) * autocorrelation v x) =
      (∫ x : Real, (Real.exp (c * x) : Complex) * v x) *
        conj (∫ x : Real,
          (Real.exp (-c * x) : Complex) * v x) := by
  let f : Real → Complex := fun x =>
    (Real.exp (c * x) : Complex) * v x
  let g : Real → Complex := fun x =>
    (Real.exp (c * x) : Complex) * star v x
  have hsupportStar :
      Function.support (SchwartzLineTestFunction.star v) ⊆
        Set.Icc (-a) a := by
    intro x hx
    have hv : v (-x) ≠ 0 := by
      intro hzero
      exact hx (by simp [star_apply, hzero])
    have hmem := hsupport hv
    constructor <;> linarith [hmem.1, hmem.2]
  have hf : Integrable f := by
    exact integrable_exp_mul_schwartz_of_support_subset_Icc hsupport
  have hg : Integrable g := by
    exact integrable_exp_mul_schwartz_of_support_subset_Icc hsupportStar
  have hpointwise (x : Real) :
      (Real.exp (c * x) : Complex) * autocorrelation v x =
        (f ⋆[ContinuousLinearMap.mul Complex Complex] g) x := by
    rw [autocorrelation_apply, MeasureTheory.convolution_def,
      MeasureTheory.convolution_def, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have hexp : Real.exp (c * x) =
        Real.exp (c * y) * Real.exp (c * (x - y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [f, g]
    rw [hexp]
    push_cast
    simp only [ContinuousLinearMap.mul_apply']
    ring
  calc
    (∫ x : Real,
        (Real.exp (c * x) : Complex) * autocorrelation v x) =
        ∫ x : Real,
          (f ⋆[ContinuousLinearMap.mul Complex Complex] g) x := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpointwise x
    _ = (∫ x : Real, f x) * ∫ x : Real, g x := by
      simpa using MeasureTheory.integral_convolution
        (ContinuousLinearMap.mul Complex Complex) hf hg
    _ = (∫ x : Real, (Real.exp (c * x) : Complex) * v x) *
        conj (∫ x : Real,
          (Real.exp (-c * x) : Complex) * v x) := by
      rw [integral_exp_mul_star_eq_conj]

private theorem suzukiFourierSource_autocorrelation_I_div_two
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFourierSource (autocorrelation v) (Complex.I / 2) =
      (∫ x in Set.Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * v x) *
        conj (∫ x in Set.Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * v x) := by
  rw [suzukiFourierSource]
  calc
    (∫ x : Real,
        Complex.exp ((x : Complex) * Complex.I * (Complex.I / 2)) *
          autocorrelation v x) =
        ∫ x : Real,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) *
            autocorrelation v x := by
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      rw [Complex.ofReal_exp]
      apply congrArg Complex.exp
      calc
        (x : Complex) * Complex.I * (Complex.I / 2) =
            ((x : Complex) * (1 / 2 : Complex)) * Complex.I ^ 2 := by
          ring
        _ = ((-(1 / 2 : Real) * x : Real) : Complex) := by
          rw [Complex.I_sq]
          push_cast
          ring
    _ = (∫ x : Real,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * v x) *
        conj (∫ x : Real,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * v x) := by
      simpa only [neg_neg] using
        integral_exp_mul_autocorrelation_eq_weightedProducts
          (v := v) (c := -(1 / 2 : Real)) hsupport
    _ = (∫ x in Set.Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * v x) *
        conj (∫ x in Set.Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * v x) := by
      rw [integral_exp_mul_schwartz_eq_setIntegral hsupport,
        integral_exp_mul_schwartz_eq_setIntegral hsupport]

private theorem suzukiFourierSource_autocorrelation_neg_I_div_two
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFourierSource (autocorrelation v) (-Complex.I / 2) =
      (∫ x in Set.Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * v x) *
        conj (∫ x in Set.Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * v x) := by
  rw [suzukiFourierSource]
  calc
    (∫ x : Real,
        Complex.exp ((x : Complex) * Complex.I * (-Complex.I / 2)) *
          autocorrelation v x) =
        ∫ x : Real,
          (Real.exp ((1 / 2 : Real) * x) : Complex) *
            autocorrelation v x := by
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      rw [Complex.ofReal_exp]
      apply congrArg Complex.exp
      calc
        (x : Complex) * Complex.I * (-Complex.I / 2) =
            ((x : Complex) * (-(1 / 2 : Complex))) * Complex.I ^ 2 := by
          ring
        _ = (((1 / 2 : Real) * x : Real) : Complex) := by
          rw [Complex.I_sq]
          push_cast
          ring
    _ = (∫ x : Real,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * v x) *
        conj (∫ x : Real,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * v x) := by
      simpa only [neg_neg] using
        integral_exp_mul_autocorrelation_eq_weightedProducts
          (v := v) (c := (1 / 2 : Real)) hsupport
    _ = (∫ x in Set.Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * v x) *
        conj (∫ x in Set.Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * v x) := by
      rw [integral_exp_mul_schwartz_eq_setIntegral hsupport,
        integral_exp_mul_schwartz_eq_setIntegral hsupport]

/-- The pole part of the derivative kernel pairing factors into the two
weighted source integrals appearing in the pole Fourier-Laplace values. -/
theorem suzukiFiniteKernelPairingComplex_pole_eq_weightedProducts
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFiniteKernelPairingComplex suzukiPoleScrewKernel a
        (SchwartzMap.derivCLM Complex Complex v) =
      (∫ y in Set.Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * y) : Complex) * v y) *
          conj (∫ x in Set.Icc (-a) a,
            (Real.exp ((1 / 2 : Real) * x) : Complex) * v x) +
        (∫ y in Set.Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * y) : Complex) * v y) *
          conj (∫ x in Set.Icc (-a) a,
            (Real.exp (-(1 / 2 : Real) * x) : Complex) * v x) := by
  let u : Real → Complex := fun x =>
    SchwartzMap.derivCLM Complex Complex v x
  let plusTerm : Real × Real → Complex := fun p =>
    ((Real.exp ((1 / 2 : Real) * p.1) : Complex) * conj (u p.1)) *
      ((Real.exp (-(1 / 2 : Real) * p.2) : Complex) * u p.2)
  let minusTerm : Real × Real → Complex := fun p =>
    ((Real.exp (-(1 / 2 : Real) * p.1) : Complex) * conj (u p.1)) *
      ((Real.exp ((1 / 2 : Real) * p.2) : Complex) * u p.2)
  let constantTerm : Real × Real → Complex := fun p =>
    conj (u p.1) * u p.2
  have hplus : IntegrableOn plusTerm (suzukiFiniteSquare a) := by
    exact (by fun_prop : Continuous plusTerm).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  have hminus : IntegrableOn minusTerm (suzukiFiniteSquare a) := by
    exact (by fun_prop : Continuous minusTerm).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  have hconstant : IntegrableOn constantTerm (suzukiFiniteSquare a) := by
    exact (by fun_prop : Continuous constantTerm).continuousOn
      |>.integrableOn_compact (isCompact_suzukiFiniteSquare a)
  have hexpand :
      suzukiKernelPairingIntegrand suzukiPoleScrewKernel u = fun p =>
        (-4 : Complex) * plusTerm p +
          (-4 : Complex) * minusTerm p + 8 * constantTerm p := by
    funext p
    have hexpPlus :
        Real.exp ((p.1 - p.2) / 2) =
          Real.exp ((1 / 2 : Real) * p.1) *
            Real.exp (-(1 / 2 : Real) * p.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpMinus :
        Real.exp (-(p.1 - p.2) / 2) =
          Real.exp (-(1 / 2 : Real) * p.1) *
            Real.exp ((1 / 2 : Real) * p.2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [suzukiKernelPairingIntegrand, suzukiPoleScrewKernel,
      plusTerm, minusTerm, constantTerm, u, hexpPlus, hexpMinus]
    push_cast
    ring
  rw [suzukiFiniteKernelPairingComplex, hexpand]
  change
    (∫ p in suzukiFiniteSquare a,
      ((-4 : Complex) * plusTerm p + (-4 : Complex) * minusTerm p) +
        8 * constantTerm p) = _
  have hsplitOuter :
      (∫ p in suzukiFiniteSquare a,
        ((-4 : Complex) * plusTerm p + (-4 : Complex) * minusTerm p) +
          8 * constantTerm p) =
        (∫ p in suzukiFiniteSquare a,
          (-4 : Complex) * plusTerm p + (-4 : Complex) * minusTerm p) +
        ∫ p in suzukiFiniteSquare a, 8 * constantTerm p := by
    simpa only [Pi.add_apply] using
      integral_add ((hplus.const_mul _).add (hminus.const_mul _))
        (hconstant.const_mul _)
  have hsplitInner :
      (∫ p in suzukiFiniteSquare a,
        (-4 : Complex) * plusTerm p + (-4 : Complex) * minusTerm p) =
        (∫ p in suzukiFiniteSquare a, (-4 : Complex) * plusTerm p) +
        ∫ p in suzukiFiniteSquare a, (-4 : Complex) * minusTerm p := by
    simpa only [Pi.add_apply] using
      integral_add (hplus.const_mul _) (hminus.const_mul _)
  rw [hsplitOuter, hsplitInner]
  simp only [integral_const_mul]
  rw [show (∫ p in suzukiFiniteSquare a, plusTerm p) =
      (∫ x in Set.Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * x) : Complex) * conj (u x)) *
        ∫ y in Set.Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * y) : Complex) * u y by
        simpa only [plusTerm] using
          setIntegral_suzukiFiniteSquare_separable a
            (fun x => (Real.exp ((1 / 2 : Real) * x) : Complex) * conj (u x))
            (fun y => (Real.exp (-(1 / 2 : Real) * y) : Complex) * u y),
    show (∫ p in suzukiFiniteSquare a, minusTerm p) =
      (∫ x in Set.Icc (-a) a,
          (Real.exp (-(1 / 2 : Real) * x) : Complex) * conj (u x)) *
        ∫ y in Set.Icc (-a) a,
          (Real.exp ((1 / 2 : Real) * y) : Complex) * u y by
        simpa only [minusTerm] using
          setIntegral_suzukiFiniteSquare_separable a
            (fun x => (Real.exp (-(1 / 2 : Real) * x) : Complex) * conj (u x))
            (fun y => (Real.exp ((1 / 2 : Real) * y) : Complex) * u y),
    show (∫ p in suzukiFiniteSquare a, constantTerm p) =
      (∫ x in Set.Icc (-a) a, conj (u x)) *
        ∫ y in Set.Icc (-a) a, u y by
        simpa only [constantTerm] using
          setIntegral_suzukiFiniteSquare_separable a
            (fun x => conj (u x)) u]
  have hderivZero :
      (∫ x in Set.Icc (-a) a, u x) = 0 := by
    simpa [u] using setIntegral_exp_mul_deriv_eq ha hsupport 0
  have hconjZero :
      (∫ x in Set.Icc (-a) a, conj (u x)) = 0 := by
    rw [integral_conj, hderivZero, map_zero]
  have hweightedPlus :=
    setIntegral_exp_mul_deriv_eq ha hsupport (1 / 2 : Real)
  have hweightedMinus :=
    setIntegral_exp_mul_deriv_eq ha hsupport (-(1 / 2 : Real))
  rw [setIntegral_conj_exp_mul_deriv_eq_conj,
    setIntegral_conj_exp_mul_deriv_eq_conj,
    hweightedPlus, hweightedMinus,
    hderivZero, hconjZero]
  simp only [map_mul, map_neg, Complex.conj_ofReal]
  norm_num
  ring

/-- The complete pole component of the residual is exactly the pole
exponential component of the Suzuki derivative-kernel pairing. -/
theorem guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase_eq_kernelPairing
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    guinandWeilBurnolLiteraturePoleSide (suzukiProjectBase v) =
      suzukiFiniteKernelPairing suzukiPoleScrewKernel a
        (SchwartzMap.derivCLM Complex Complex v) := by
  rw [guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase,
    suzukiFourierSource_autocorrelation_I_div_two hsupport,
    suzukiFourierSource_autocorrelation_neg_I_div_two hsupport]
  unfold suzukiFiniteKernelPairing
  rw [suzukiFiniteKernelPairingComplex_pole_eq_weightedProducts ha hsupport]

private theorem support_deriv_subset_Icc
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    Function.support (SchwartzMap.derivCLM Complex Complex v) ⊆
      Set.Icc (-a) a := by
  have hvTSupport : tsupport v ⊆ Set.Icc (-a) a :=
    closure_minimal hsupport isClosed_Icc
  intro x hx
  exact hvTSupport
    (SchwartzMap.tsupport_derivCLM_subset Complex v (subset_closure hx))

private theorem setIntegral_Iic_left_endpoint_eq_zero
    {a : Real} {f : Real → Complex}
    (hsupport : Function.support f ⊆ Set.Icc (-a) a) :
    (∫ x in Set.Iic (-a), f x) = 0 := by
  apply setIntegral_eq_zero_of_ae_eq_zero
  filter_upwards [(volume : Measure Real).ae_ne (-a)] with x hx
  intro hxmem
  have hxlt : x < -a := lt_of_le_of_ne hxmem hx
  by_contra hne
  exact (not_lt_of_ge (hsupport hne).1) hxlt

private theorem integrable_affine_mul_deriv_of_support_subset_Icc
    {a b : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    Integrable (fun x : Real =>
      ((b - x : Real) : Complex) *
        SchwartzMap.derivCLM Complex Complex v x) := by
  have hderivSupport := support_deriv_subset_Icc hsupport
  have hsub : Function.support (fun x : Real =>
      ((b - x : Real) : Complex) *
        SchwartzMap.derivCLM Complex Complex v x) ⊆ Set.Icc (-a) a := by
    intro x hx
    exact hderivSupport (fun hzero => hx (by simp [hzero]))
  apply (integrableOn_iff_integrable_of_support_subset hsub).mp
  exact (by fun_prop : Continuous (fun x : Real =>
      ((b - x : Real) : Complex) *
        SchwartzMap.derivCLM Complex Complex v x)).continuousOn
    |>.integrableOn_compact isCompact_Icc

/-- The one-sided affine ramp is a first antiderivative of the compactly
supported source derivative. -/
private theorem setIntegral_Iic_affine_mul_deriv_eq_source
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (b : Real) :
    (∫ x in Set.Iic b,
        ((b - x : Real) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x) =
      ∫ x in Set.Iic b, v x := by
  have hleft :=
    (schwartz_eq_zero_at_endpoints_of_support_subset_Icc ha hsupport).1
  have hderivSupport := support_deriv_subset_Icc hsupport
  have hweightedSupport : Function.support (fun x : Real =>
      ((b - x : Real) : Complex) *
        SchwartzMap.derivCLM Complex Complex v x) ⊆ Set.Icc (-a) a := by
    intro x hx
    exact hderivSupport (fun hzero => hx (by simp [hzero]))
  have hweighted :=
    integrable_affine_mul_deriv_of_support_subset_Icc
      (b := b) hsupport
  have hbaseWeighted :
      (∫ x in Set.Iic (-a),
          ((b - x : Real) : Complex) *
            SchwartzMap.derivCLM Complex Complex v x) = 0 :=
    setIntegral_Iic_left_endpoint_eq_zero hweightedSupport
  have hbaseSource : (∫ x in Set.Iic (-a), v x) = 0 :=
    setIntegral_Iic_left_endpoint_eq_zero hsupport
  have hweightedInterval := intervalIntegral.integral_Iic_sub_Iic
    (a := -a) (b := b) (μ := volume) hweighted.integrableOn
    (hweighted.integrableOn : IntegrableOn
      (fun x : Real => ((b - x : Real) : Complex) *
        SchwartzMap.derivCLM Complex Complex v x) (Set.Iic b))
  have hvIntegrable : Integrable (fun x : Real => v x) := v.integrable
  have hsourceInterval := intervalIntegral.integral_Iic_sub_Iic
    (a := -a) (b := b) (μ := volume)
    hvIntegrable.integrableOn hvIntegrable.integrableOn
  rw [hbaseWeighted, sub_zero] at hweightedInterval
  rw [hbaseSource, sub_zero] at hsourceInterval
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := -a) (b := b)
    (u := fun x : Real => ((b - x : Real) : Complex))
    (v := fun x : Real => v x)
    (u' := fun _ : Real => (-1 : Complex))
    (v' := fun x : Real => SchwartzMap.derivCLM Complex Complex v x)
    (fun x _ => by
      simpa using
        (((hasDerivAt_const x b).sub (hasDerivAt_id x)).ofReal_comp))
    (fun x _ => by
      simpa only [SchwartzMap.derivCLM_apply] using v.hasDerivAt x)
    ((by fun_prop : Continuous (fun _ : Real => (-1 : Complex))).intervalIntegrable _ _)
    ((SchwartzMap.derivCLM Complex Complex v).continuous.intervalIntegrable _ _)
  rw [hweightedInterval, hsourceInterval]
  rw [hibp]
  simp [hleft]

private theorem integral_max_sub_mul_deriv_eq_Iic_source
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (b : Real) :
    (∫ x : Real,
        ((max (b - x) 0 : Real) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x) =
      ∫ x in Set.Iic b, v x := by
  calc
    (∫ x : Real,
        ((max (b - x) 0 : Real) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x) =
        ∫ x in Set.Iic b,
          ((max (b - x) 0 : Real) : Complex) *
            SchwartzMap.derivCLM Complex Complex v x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hxb : b < x := lt_of_not_ge hx
      rw [max_eq_right (by linarith : b - x ≤ 0)]
      simp
    _ = ∫ x in Set.Iic b,
        ((b - x : Real) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x hx
      change ((max (b - x) 0 : Real) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x =
        ((b - x : Real) : Complex) *
          SchwartzMap.derivCLM Complex Complex v x
      rw [max_eq_left (sub_nonneg.mpr hx)]
    _ = ∫ x in Set.Iic b, v x :=
      setIntegral_Iic_affine_mul_deriv_eq_source ha hsupport b

private theorem setIntegral_Ioi_conj_deriv_eq_neg_conj
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (b : Real) :
    (∫ x in Set.Ioi b,
        conj (SchwartzMap.derivCLM Complex Complex v x)) =
      -conj (v b) := by
  let f : Real → Complex := fun x => conj (v x)
  have hfSupport : Function.support f ⊆ Set.Icc (-a) a := by
    intro x hx
    exact hsupport (fun hzero => hx (by simp [f, hzero]))
  have hfCompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfSupport
  have hfContDiff : ContDiff Real 1 f := by
    dsimp only [f]
    change ContDiff Real 1 (fun x : Real => Complex.conjCLE (v x))
    exact Complex.conjCLE.contDiff.comp (v.smooth 1)
  have hconjDeriv (x : Real) :
      HasDerivAt f
        (conj (SchwartzMap.derivCLM Complex Complex v x)) x := by
    dsimp only [f]
    change HasDerivAt (fun y : Real => Complex.conjCLE (v y))
      (Complex.conjCLE (deriv (fun y : Real => v y) x)) x
    exact Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x (v.hasDerivAt x)
  have hfundamental :=
    HasCompactSupport.integral_Ioi_deriv_eq hfContDiff hfCompact b
  calc
    (∫ x in Set.Ioi b,
        conj (SchwartzMap.derivCLM Complex Complex v x)) =
        ∫ x in Set.Ioi b, deriv f x := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      exact (hconjDeriv x).deriv.symm
    _ = -f b := hfundamental
    _ = -conj (v b) := rfl

private theorem integral_Iic_source_mul_conj_deriv_eq_neg_autocorrelation
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (L : Real) :
    (∫ x : Real,
        (∫ y in Set.Iic (x - L), v y) *
          conj (SchwartzMap.derivCLM Complex Complex v x)) =
      -autocorrelation v (-L) := by
  let u : Real → Complex := fun x =>
    SchwartzMap.derivCLM Complex Complex v x
  let F : Real → Real → Complex := fun x y =>
    Set.indicator (Set.Iic (x - L))
      (fun y => conj (u x) * v y) y
  have huIntegrable : Integrable u :=
    (SchwartzMap.derivCLM Complex Complex v).integrable
  have hconjIntegrable : Integrable (fun x : Real => conj (u x)) := by
    have hcomp :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp huIntegrable
    change Integrable (fun x : Real => Complex.conjCLE (u x))
    exact hcomp
  have hvIntegrable : Integrable (fun y : Real => v y) := v.integrable
  have hseparable : Integrable (fun p : Real × Real =>
      conj (u p.1) * v p.2) :=
    hconjIntegrable.mul_prod hvIntegrable
  have hregion : MeasurableSet
      {p : Real × Real | p.2 ≤ p.1 - L} := by
    exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  have hF : Integrable (Function.uncurry F) := by
    have hindicator := hseparable.indicator hregion
    apply hindicator.congr
    filter_upwards with p
    rfl
  have hswap := MeasureTheory.integral_integral_swap hF
  have hleftFiber (x : Real) :
      (∫ y in Set.Iic (x - L), v y) * conj (u x) =
        ∫ y : Real, F x y := by
    change _ = ∫ y : Real,
      Set.indicator (Set.Iic (x - L))
        (fun y => conj (u x) * v y) y
    rw [integral_indicator measurableSet_Iic, integral_const_mul]
    ring
  have hrightFiber (y : Real) :
      (∫ x : Real, F x y) =
        v y * ∫ x in Set.Ici (y + L), conj (u x) := by
    have hfiber (x : Real) : F x y =
        Set.indicator (Set.Ici (y + L))
          (fun x => conj (u x) * v y) x := by
      simp only [F, Set.indicator_apply]
      by_cases hxy : y ≤ x - L
      · have hyx : y + L ≤ x := by linarith
        simp [hxy, hyx]
      · have hyx : ¬ y + L ≤ x := by linarith
        simp [hxy, hyx]
    calc
      (∫ x : Real, F x y) =
          ∫ x : Real,
            Set.indicator (Set.Ici (y + L))
              (fun x => conj (u x) * v y) x := by
        apply integral_congr_ae
        filter_upwards with x
        exact hfiber x
      _ = ∫ x in Set.Ici (y + L), conj (u x) * v y := by
        rw [integral_indicator measurableSet_Ici]
      _ = v y * ∫ x in Set.Ici (y + L), conj (u x) := by
        rw [integral_mul_const]
        ring
  calc
    (∫ x : Real,
        (∫ y in Set.Iic (x - L), v y) *
          conj (SchwartzMap.derivCLM Complex Complex v x)) =
        ∫ x : Real, ∫ y : Real, F x y := by
      apply integral_congr_ae
      filter_upwards with x
      exact hleftFiber x
    _ = ∫ y : Real, ∫ x : Real, F x y := hswap
    _ = ∫ y : Real,
        v y * ∫ x in Set.Ici (y + L), conj (u x) := by
      apply integral_congr_ae
      filter_upwards with y
      exact hrightFiber y
    _ = ∫ y : Real, v y * (-conj (v (y + L))) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_Ici_eq_integral_Ioi]
      rw [show (∫ x in Set.Ioi (y + L), conj (u x)) =
          -conj (v (y + L)) by
        simpa only [u] using
          setIntegral_Ioi_conj_deriv_eq_neg_conj hsupport (y + L)]
    _ = -(∫ y : Real, v y * conj (v (y + L))) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = -autocorrelation v (-L) := by
      apply congrArg Neg.neg
      rw [autocorrelation_apply, MeasureTheory.convolution_def]
      apply integral_congr_ae
      filter_upwards with y
      simp only [star_apply]
      congr 2
      ring

/-- The right shifted ramp whose reflected partner gives
`max (|t| - L) 0`. -/
def suzukiRightRampKernel (L t : Real) : Real :=
  max (t - L) 0

theorem suzukiFiniteKernelPairingComplex_rightRamp_eq_autocorrelation
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (L : Real) :
    suzukiFiniteKernelPairingComplex (suzukiRightRampKernel L) a
        (SchwartzMap.derivCLM Complex Complex v) =
      -autocorrelation v (-L) := by
  let u : Real → Complex := fun x =>
    SchwartzMap.derivCLM Complex Complex v x
  have hsupportU := support_deriv_subset_Icc hsupport
  have hkernel : Continuous (suzukiRightRampKernel L) := by
    unfold suzukiRightRampKernel
    fun_prop
  rw [suzukiFiniteKernelPairingComplex_eq_iterated hkernel
    (SchwartzMap.derivCLM Complex Complex v).continuous]
  have hinner (x : Real) :
      (∫ y in Set.Icc (-a) a,
          (suzukiRightRampKernel L (x - y) : Complex) *
            u y * conj (u x)) =
        (∫ y in Set.Iic (x - L), v y) * conj (u x) := by
    calc
      (∫ y in Set.Icc (-a) a,
          (suzukiRightRampKernel L (x - y) : Complex) *
            u y * conj (u x)) =
          ∫ y : Real,
            (suzukiRightRampKernel L (x - y) : Complex) *
              u y * conj (u x) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have huy : u y = 0 := by
          by_contra hne
          exact hy (hsupportU hne)
        simp [huy]
      _ = (∫ y : Real,
          ((max ((x - L) - y) 0 : Real) : Complex) * u y) *
            conj (u x) := by
        rw [← integral_mul_const]
        apply integral_congr_ae
        filter_upwards with y
        unfold suzukiRightRampKernel
        congr 3
        ring
      _ = (∫ y in Set.Iic (x - L), v y) * conj (u x) := by
        rw [show (∫ y : Real,
            ((max ((x - L) - y) 0 : Real) : Complex) * u y) =
              ∫ y in Set.Iic (x - L), v y by
          simpa only [u] using
            integral_max_sub_mul_deriv_eq_Iic_source
              ha hsupport (x - L)]
  calc
    (∫ x in Set.Icc (-a) a,
        ∫ y in Set.Icc (-a) a,
          (suzukiRightRampKernel L (x - y) : Complex) *
            u y * conj (u x)) =
        ∫ x in Set.Icc (-a) a,
          (∫ y in Set.Iic (x - L), v y) * conj (u x) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x _
      exact hinner x
    _ = ∫ x : Real,
        (∫ y in Set.Iic (x - L), v y) * conj (u x) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hux : u x = 0 := by
        by_contra hne
        exact hx (hsupportU hne)
      simp [hux]
    _ = -autocorrelation v (-L) := by
      simpa only [u] using
        integral_Iic_source_mul_conj_deriv_eq_neg_autocorrelation
          hsupport L

/-- Reflecting a real translation kernel conjugates the finite complex
pairing.  The square cutoff is invariant under exchanging its coordinates. -/
theorem suzukiFiniteKernelPairingComplex_reflect
    (kernel : Real → Real) (a : Real) (u : Real → Complex) :
    suzukiFiniteKernelPairingComplex (fun t => kernel (-t)) a u =
      conj (suzukiFiniteKernelPairingComplex kernel a u) := by
  rw [suzukiFiniteKernelPairingComplex, suzukiFiniteSquare,
    MeasureTheory.Measure.volume_eq_prod]
  calc
    (∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
        suzukiKernelPairingIntegrand (fun t => kernel (-t)) u p) =
        ∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          conj (suzukiKernelPairingIntegrand kernel u p.swap) := by
      apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
      intro p _
      unfold suzukiKernelPairingIntegrand
      simp [Complex.conj_ofReal]
      ring
    _ = ∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          conj (suzukiKernelPairingIntegrand kernel u p) := by
      exact MeasureTheory.setIntegral_prod_swap
        (Set.Icc (-a) a) (Set.Icc (-a) a)
        (fun p => conj (suzukiKernelPairingIntegrand kernel u p))
    _ = conj (∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          suzukiKernelPairingIntegrand kernel u p) := by
      exact integral_conj

/-- The reflected shifted ramp contributes the positive autocorrelation
sample. -/
private theorem conj_autocorrelation_neg
    (v : SchwartzLineTestFunction) (L : Real) :
    conj (autocorrelation v (-L)) = autocorrelation v L := by
  rw [autocorrelation_apply, autocorrelation_apply,
    MeasureTheory.convolution_def, MeasureTheory.convolution_def,
    ← integral_conj]
  calc
    (∫ x : Real, conj (v x * star v (-L - x))) =
        ∫ x : Real,
          (fun y : Real => v y * conj (v (y - L))) (x + L) := by
      apply integral_congr_ae
      filter_upwards with x
      have hneg : -(-L - x) = x + L := by ring
      have hsub : x + L - L = x := by ring
      simp [star_apply, hneg, hsub]
      ring
    _ = ∫ y : Real, v y * conj (v (y - L)) := by
      exact integral_add_right_eq_self
        (fun y : Real => v y * conj (v (y - L))) L
    _ = ∫ x : Real, v x * star v (L - x) := by
      apply integral_congr_ae
      filter_upwards with x
      have hneg : -(L - x) = x - L := by ring
      simp [star_apply, hneg]

theorem suzukiFiniteKernelPairingComplex_leftRamp_eq_autocorrelation
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (L : Real) :
    suzukiFiniteKernelPairingComplex
        (fun t => suzukiRightRampKernel L (-t)) a
        (SchwartzMap.derivCLM Complex Complex v) =
      -autocorrelation v L := by
  rw [suzukiFiniteKernelPairingComplex_reflect,
    suzukiFiniteKernelPairingComplex_rightRamp_eq_autocorrelation
      ha hsupport L, map_neg]
  rw [conj_autocorrelation_neg]

theorem suzukiFiniteKernelPairingComplex_add
    {kernel₁ kernel₂ : Real → Real} {a : Real} {u : Real → Complex}
    (hkernel₁ : Continuous kernel₁) (hkernel₂ : Continuous kernel₂)
    (hu : Continuous u) :
    suzukiFiniteKernelPairingComplex (fun t => kernel₁ t + kernel₂ t) a u =
      suzukiFiniteKernelPairingComplex kernel₁ a u +
        suzukiFiniteKernelPairingComplex kernel₂ a u := by
  have h₁ := integrableOn_suzukiKernelPairingIntegrand
    (a := a) hkernel₁ hu
  have h₂ := integrableOn_suzukiKernelPairingIntegrand
    (a := a) hkernel₂ hu
  rw [suzukiFiniteKernelPairingComplex,
    suzukiFiniteKernelPairingComplex,
    suzukiFiniteKernelPairingComplex,
    ← integral_add h₁ h₂]
  apply setIntegral_congr_fun (isCompact_suzukiFiniteSquare a).measurableSet
  intro p _
  unfold suzukiKernelPairingIntegrand
  push_cast
  ring

theorem suzukiFiniteKernelPairingComplex_const_mul
    (c : Real) (kernel : Real → Real) (a : Real) (u : Real → Complex) :
    suzukiFiniteKernelPairingComplex (fun t => c * kernel t) a u =
      (c : Complex) * suzukiFiniteKernelPairingComplex kernel a u := by
  rw [suzukiFiniteKernelPairingComplex,
    suzukiFiniteKernelPairingComplex, ← integral_const_mul]
  apply setIntegral_congr_fun (isCompact_suzukiFiniteSquare a).measurableSet
  intro p _
  unfold suzukiKernelPairingIntegrand
  push_cast
  ring

theorem suzukiFiniteKernelPairingComplex_finsetSum
    {ι : Type*} (s : Finset ι) (kernel : ι → Real → Real)
    (a : Real) (u : Real → Complex)
    (hkernel : ∀ i ∈ s, Continuous (kernel i)) (hu : Continuous u) :
    suzukiFiniteKernelPairingComplex
        (fun t => ∑ i ∈ s, kernel i t) a u =
      ∑ i ∈ s, suzukiFiniteKernelPairingComplex (kernel i) a u := by
  rw [suzukiFiniteKernelPairingComplex]
  calc
    (∫ p in suzukiFiniteSquare a,
        suzukiKernelPairingIntegrand (fun t => ∑ i ∈ s, kernel i t) u p) =
        ∫ p in suzukiFiniteSquare a,
          ∑ i ∈ s, suzukiKernelPairingIntegrand (kernel i) u p := by
      apply setIntegral_congr_fun
        (isCompact_suzukiFiniteSquare a).measurableSet
      intro p _
      unfold suzukiKernelPairingIntegrand
      push_cast
      simp only [Finset.sum_mul]
    _ = ∑ i ∈ s,
          ∫ p in suzukiFiniteSquare a,
            suzukiKernelPairingIntegrand (kernel i) u p := by
      exact integral_finsetSum s (fun i hi =>
        integrableOn_suzukiKernelPairingIntegrand (hkernel i hi) hu)
    _ = ∑ i ∈ s,
          suzukiFiniteKernelPairingComplex (kernel i) a u := by
      rfl

/-- Suzuki's prime hinge at logarithmic displacement `L`. -/
def suzukiPrimeHingeKernel (L t : Real) : Real :=
  max (|t| - L) 0

private theorem suzukiPrimeHingeKernel_eq_ramps
    {L : Real} (hL : 0 ≤ L) :
    suzukiPrimeHingeKernel L =
      fun t => suzukiRightRampKernel L t +
        suzukiRightRampKernel L (-t) := by
  funext t
  unfold suzukiPrimeHingeKernel suzukiRightRampKernel
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    rw [max_eq_right (by linarith : -t - L ≤ 0)]
    simp
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg ht']
    rw [max_eq_right (by linarith : t - L ≤ 0)]
    simp

/-- The complete even prime hinge contributes the two symmetric
autocorrelation samples appearing in Suzuki's prime residual. -/
theorem suzukiFiniteKernelPairingComplex_primeHinge_eq_autocorrelation
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a)
    {L : Real} (hL : 0 ≤ L) :
    suzukiFiniteKernelPairingComplex (suzukiPrimeHingeKernel L) a
        (SchwartzMap.derivCLM Complex Complex v) =
      -(autocorrelation v L + autocorrelation v (-L)) := by
  rw [suzukiPrimeHingeKernel_eq_ramps hL]
  rw [suzukiFiniteKernelPairingComplex_add]
  · rw [suzukiFiniteKernelPairingComplex_rightRamp_eq_autocorrelation
      ha hsupport L,
      suzukiFiniteKernelPairingComplex_leftRamp_eq_autocorrelation
        ha hsupport L]
    ring
  · unfold suzukiRightRampKernel
    fun_prop
  · unfold suzukiRightRampKernel
    fun_prop
  · exact (SchwartzMap.derivCLM Complex Complex v).continuous

/-- On the finite square, Suzuki's moving prime cutoff is the fixed cutoff
at the maximum displacement `2a`. -/
theorem suzukiFiniteKernelPairingComplex_primeScrewTerm_eq_finiteSum
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFiniteKernelPairingComplex suzukiPrimeScrewTerm a
        (SchwartzMap.derivCLM Complex Complex v) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (-(ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) : Real) *
          (autocorrelation v (Real.log (n : Real)) +
            autocorrelation v (-Real.log (n : Real))) := by
  let cutoff := Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊
  let u : Real → Complex := fun x =>
    SchwartzMap.derivCLM Complex Complex v x
  have hpair :
      suzukiFiniteKernelPairingComplex suzukiPrimeScrewTerm a u =
        suzukiFiniteKernelPairingComplex
          (fun t => ∑ n ∈ cutoff, suzukiPrimeScrewSummand n t) a u := by
    rw [suzukiFiniteKernelPairingComplex,
      suzukiFiniteKernelPairingComplex]
    apply setIntegral_congr_fun
      (isCompact_suzukiFiniteSquare a).measurableSet
    intro p hp
    have hp₁ := hp.1
    have hp₂ := hp.2
    have hdiff : |p.1 - p.2| ≤ 2 * a := by
      rw [abs_le]
      constructor <;> linarith [hp₁.1, hp₁.2, hp₂.1, hp₂.2]
    unfold suzukiKernelPairingIntegrand
    rw [suzukiPrimeScrewTerm_eq_fixed_sum hdiff]
  rw [show SchwartzMap.derivCLM Complex Complex v = u by rfl, hpair]
  rw [suzukiFiniteKernelPairingComplex_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnReal : (1 : Real) ≤ (n : Real) := by
      exact_mod_cast (show 1 ≤ n by omega)
    have hlog : 0 ≤ Real.log (n : Real) := Real.log_nonneg hnReal
    unfold suzukiPrimeScrewSummand
    change suzukiFiniteKernelPairingComplex
        (fun t =>
          (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
            suzukiPrimeHingeKernel (Real.log (n : Real)) t) a u = _
    rw [suzukiFiniteKernelPairingComplex_const_mul,
      suzukiFiniteKernelPairingComplex_primeHinge_eq_autocorrelation
        ha hsupport hlog]
    push_cast
    ring
  · intro n _
    unfold suzukiPrimeScrewSummand
    fun_prop
  · exact (SchwartzMap.derivCLM Complex Complex v).continuous

/-- Compact support turns the normalized prime `tsum` into exactly the same
finite cutoff used by the screw-kernel pairing. -/
theorem guinandWeilLiteraturePrimeSide_suzukiProjectBase_eq_kernelPairing
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    guinandWeilLiteraturePrimeSide
        (fourierAutocorrelation (suzukiProjectBase v)) =
      (suzukiFiniteKernelPairingComplex suzukiPrimeScrewTerm a
        (SchwartzMap.derivCLM Complex Complex v)).re := by
  rw [guinandWeilLiteraturePrimeSide_suzukiProjectBase]
  rw [tsum_eq_sum (s := Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) (fun n hn => by
    by_cases hnTwo : 2 ≤ n
    · have hfloor : ⌊Real.exp (2 * a)⌋₊ < n := by
        exact Nat.lt_of_not_ge (fun hle => hn (Finset.mem_Icc.2 ⟨hnTwo, hle⟩))
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hnTwo
      have hexp : Real.exp (2 * a) < (n : Real) :=
        (Nat.floor_lt' hnpos.ne').1 hfloor
      have hlog : 2 * a < Real.log (n : Real) :=
        (Real.lt_log_iff_exp_lt (by exact_mod_cast hnpos)).2 hexp
      have hlogpos : 0 < Real.log (n : Real) :=
        Real.log_pos (by exact_mod_cast hnTwo)
      have hzeroPos : autocorrelation v (Real.log (n : Real)) = 0 :=
        autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
          hsupport (by simpa [abs_of_pos hlogpos] using hlog)
      have hzeroNeg : autocorrelation v (-Real.log (n : Real)) = 0 :=
        autocorrelation_apply_eq_zero_of_support_subset_Icc_of_two_mul_lt_abs
          hsupport (by simpa [abs_of_pos hlogpos] using hlog)
      rw [hzeroPos, hzeroNeg]
      simp
    · have hnlt : n < 2 := Nat.lt_of_not_ge hnTwo
      interval_cases n <;> simp [ArithmeticFunction.vonMangoldt]
    )]
  rw [suzukiFiniteKernelPairingComplex_primeScrewTerm_eq_finiteSum
    ha hsupport]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, zero_mul, sub_zero]

/-- The constant left after subtracting the quarter-line digamma base point. -/
def suzukiGammaBaseCoefficient : Real :=
  (Complex.digamma (1 / 4 : Complex)).re - Real.log Real.pi

/-- The `|x|` part of Suzuki's Archimedean screw kernel. -/
def suzukiGammaBaseKernel (x : Real) : Real :=
  -|x| / 2 * suzukiGammaBaseCoefficient

/-- The complete Archimedean physical kernel: the base-point absolute-value
term plus the cancellation-safe Lerch series contribution. -/
def suzukiGammaScrewKernel (x : Real) : Real :=
  suzukiGammaBaseKernel x - (1 / 4) * suzukiLerchDifference x

theorem continuous_suzukiGammaBaseKernel :
    Continuous suzukiGammaBaseKernel := by
  unfold suzukiGammaBaseKernel
  fun_prop

theorem continuous_suzukiGammaScrewKernel :
    Continuous suzukiGammaScrewKernel := by
  unfold suzukiGammaScrewKernel
  exact continuous_suzukiGammaBaseKernel.sub
    (continuous_const.mul continuous_suzukiLerchDifference)

/-- The absolute-value kernel is the zero-displacement prime hinge, so its
derivative pairing is twice the negative source autocorrelation mass. -/
theorem suzukiFiniteKernelPairingComplex_abs_eq_autocorrelation_zero
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFiniteKernelPairingComplex (fun x : Real => |x|) a
        (SchwartzMap.derivCLM Complex Complex v) =
      -2 * autocorrelation v 0 := by
  rw [show (fun x : Real => |x|) = suzukiPrimeHingeKernel 0 by
    funext x
    simp [suzukiPrimeHingeKernel]]
  rw [suzukiFiniteKernelPairingComplex_primeHinge_eq_autocorrelation
    ha hsupport (L := 0) (by norm_num)]
  ring

/-- The Gamma base-point kernel pairing is the base coefficient times the
zero-displacement source autocorrelation. -/
theorem suzukiFiniteKernelPairingComplex_gammaBaseKernel_eq
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    suzukiFiniteKernelPairingComplex suzukiGammaBaseKernel a
        (SchwartzMap.derivCLM Complex Complex v) =
      (suzukiGammaBaseCoefficient : Complex) * autocorrelation v 0 := by
  have hkernel : suzukiGammaBaseKernel = fun x : Real =>
      (-suzukiGammaBaseCoefficient / 2) * |x| := by
    funext x
    unfold suzukiGammaBaseKernel
    ring
  rw [hkernel, suzukiFiniteKernelPairingComplex_const_mul,
    suzukiFiniteKernelPairingComplex_abs_eq_autocorrelation_zero
      ha hsupport]
  push_cast
  ring

/-- The source coordinate change contributes exactly `2*pi` to the total
Fourier energy, so the project's outer normalization recovers the original
zero-displacement autocorrelation mass. -/
theorem one_div_twoPi_integral_fourierAutocorrelation_suzukiProjectBase_re
    (v : SchwartzLineTestFunction) :
    (1 / (2 * Real.pi)) *
        ∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re =
      (autocorrelation v 0).re := by
  have henergy :=
    integral_cos_two_pi_mul_fourierEnergyDensity
      (suzukiProjectBase v) 0
  simp only [mul_zero, Real.cos_zero, one_mul] at henergy
  have hrewrite :
      (∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re) =
        ∫ t : Real, fourierEnergyDensity (suzukiProjectBase v) t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [fourierAutocorrelation_apply, Complex.mul_conj]
    simp [fourierEnergyDensity]
  rw [hrewrite, henergy, autocorrelation_suzukiProjectBase,
    suzukiProjectBase_apply]
  simp only [mul_zero]
  unfold suzukiTwoPi
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  field_simp [Real.pi_ne_zero]

/-- The constant part of the quarter-line Gamma expansion is exactly the
finite-square pairing for Suzuki's `|x|` Archimedean base kernel. -/
theorem one_div_twoPi_integral_gammaBase_eq_pairing
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    (1 / (2 * Real.pi)) *
        ∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re *
            suzukiGammaBaseCoefficient =
      (suzukiFiniteKernelPairingComplex suzukiGammaBaseKernel a
        (SchwartzMap.derivCLM Complex Complex v)).re := by
  calc
    (1 / (2 * Real.pi)) *
          ∫ t : Real,
            (fourierAutocorrelation (suzukiProjectBase v) t).re *
              suzukiGammaBaseCoefficient =
        suzukiGammaBaseCoefficient *
          ((1 / (2 * Real.pi)) *
            ∫ t : Real,
              (fourierAutocorrelation (suzukiProjectBase v) t).re) := by
      rw [integral_mul_const]
      ring
    _ = suzukiGammaBaseCoefficient * (autocorrelation v 0).re := by
      rw [one_div_twoPi_integral_fourierAutocorrelation_suzukiProjectBase_re]
    _ = (suzukiFiniteKernelPairingComplex suzukiGammaBaseKernel a
          (SchwartzMap.derivCLM Complex Complex v)).re := by
      rw [suzukiFiniteKernelPairingComplex_gammaBaseKernel_eq ha hsupport]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]

/-- The elementary exponential kernel underlying one quarter-line Gamma
summand.  It is kept separate from the `1 / (4*d^2)` coefficient so its
Fourier transform can be reused without redoing the improper integral. -/
def suzukiGammaCauchyKernel (d x : Real) : Complex :=
  Real.exp (-2 * d * |x|)

private def suzukiGammaCauchyFourierIntegrand
    (d t x : Real) : Complex :=
  Complex.exp (((-2 * Real.pi * x * t : Real) : Complex) * Complex.I) *
    suzukiGammaCauchyKernel d x

private def suzukiGammaCauchyRightExponent
    (d t : Real) : Complex :=
  -(2 * d : Real) -
    ((2 * Real.pi * t : Real) : Complex) * Complex.I

private def suzukiGammaCauchyLeftExponent
    (d t : Real) : Complex :=
  (2 * d : Real) -
    ((2 * Real.pi * t : Real) : Complex) * Complex.I

private theorem suzukiGammaCauchyFourierIntegrand_eq_right
    {d : Real} (t x : Real) (hx : x ∈ Set.Ioi 0) :
    suzukiGammaCauchyFourierIntegrand d t x =
      Complex.exp (suzukiGammaCauchyRightExponent d t * x) := by
  rw [suzukiGammaCauchyFourierIntegrand, suzukiGammaCauchyKernel,
    abs_of_pos hx]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [suzukiGammaCauchyRightExponent]
  push_cast
  ring

private theorem suzukiGammaCauchyFourierIntegrand_eq_left
    {d : Real} (t x : Real) (hx : x ∈ Set.Iic 0) :
    suzukiGammaCauchyFourierIntegrand d t x =
      Complex.exp (suzukiGammaCauchyLeftExponent d t * x) := by
  rw [suzukiGammaCauchyFourierIntegrand, suzukiGammaCauchyKernel,
    abs_of_nonpos hx]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp only [suzukiGammaCauchyLeftExponent]
  push_cast
  ring

private theorem suzukiGammaCauchyRightExponent_re_neg
    {d : Real} (hd : 0 < d) (t : Real) :
    (suzukiGammaCauchyRightExponent d t).re < 0 := by
  simp [suzukiGammaCauchyRightExponent, hd]

private theorem suzukiGammaCauchyLeftExponent_re_pos
    {d : Real} (hd : 0 < d) (t : Real) :
    0 < (suzukiGammaCauchyLeftExponent d t).re := by
  simp [suzukiGammaCauchyLeftExponent, hd]

/-- The positive exponential kernel is integrable for every positive decay
parameter. -/
theorem integrable_suzukiGammaCauchyKernel
    {d : Real} (hd : 0 < d) :
    Integrable (suzukiGammaCauchyKernel d) := by
  have hright : IntegrableOn (suzukiGammaCauchyKernel d) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Ioi
        (a := (-(2 * d : Real) : Complex)) (by simp [hd]) 0) ?_
        measurableSet_Ioi
    intro x hx
    rw [suzukiGammaCauchyKernel, abs_of_pos hx, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hleft : IntegrableOn (suzukiGammaCauchyKernel d) (Set.Iic 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Iic
        (a := ((2 * d : Real) : Complex)) (by simp [hd]) 0) ?_
        measurableSet_Iic
    intro x hx
    rw [suzukiGammaCauchyKernel, abs_of_nonpos hx, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hunion := hleft.union hright
  simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hunion

/-- Exact Fourier transform of `exp (-2*d*|x|)` in Mathlib's convention. -/
theorem fourier_suzukiGammaCauchyKernel
    {d : Real} (hd : 0 < d) (t : Real) :
    (𝓕 (suzukiGammaCauchyKernel d)) t =
      (((4 * d) / (4 * d ^ 2 + (2 * Real.pi * t) ^ 2) : Real) :
        Complex) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ x : Real, suzukiGammaCauchyFourierIntegrand d t x) = _
  have hright :
      IntegrableOn (suzukiGammaCauchyFourierIntegrand d t) (Set.Ioi 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Ioi
        (suzukiGammaCauchyRightExponent_re_neg hd t) 0) ?_
        measurableSet_Ioi
    intro x hx
    exact (suzukiGammaCauchyFourierIntegrand_eq_right t x hx).symm
  have hleft :
      IntegrableOn (suzukiGammaCauchyFourierIntegrand d t) (Set.Iic 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_exp_mul_complex_Iic
        (suzukiGammaCauchyLeftExponent_re_pos hd t) 0) ?_
        measurableSet_Iic
    intro x hx
    exact (suzukiGammaCauchyFourierIntegrand_eq_left t x hx).symm
  rw [← intervalIntegral.integral_Iic_add_Ioi hleft hright]
  have hleftIntegral :
      (∫ x : Real in Set.Iic 0, suzukiGammaCauchyFourierIntegrand d t x) =
        1 / suzukiGammaCauchyLeftExponent d t := by
    rw [setIntegral_congr_fun measurableSet_Iic
      (suzukiGammaCauchyFourierIntegrand_eq_left t)]
    simpa using integral_exp_mul_complex_Iic
      (suzukiGammaCauchyLeftExponent_re_pos hd t) 0
  have hrightIntegral :
      (∫ x : Real in Set.Ioi 0, suzukiGammaCauchyFourierIntegrand d t x) =
        -1 / suzukiGammaCauchyRightExponent d t := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      (suzukiGammaCauchyFourierIntegrand_eq_right t)]
    simpa using integral_exp_mul_complex_Ioi
      (suzukiGammaCauchyRightExponent_re_neg hd t) 0
  rw [hleftIntegral, hrightIntegral]
  have hleft_ne : suzukiGammaCauchyLeftExponent d t ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp [suzukiGammaCauchyLeftExponent, hd.ne'] at hreal
  have hright_ne : suzukiGammaCauchyRightExponent d t ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp [suzukiGammaCauchyRightExponent, hd.ne'] at hreal
  have hden : 4 * d ^ 2 + (2 * Real.pi * t) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hd, sq_nonneg (2 * Real.pi * t)]
  have hdenComplex :
      (4 * (d : Complex) ^ 2 +
        ((2 * Real.pi * t : Real) : Complex) ^ 2) ≠ 0 := by
    exact_mod_cast hden
  have hdenSimpleComplex :
      (d : Complex) ^ 2 +
          (Real.pi : Complex) ^ 2 * (t : Complex) ^ 2 ≠ 0 := by
    have hdenSimpleReal : d ^ 2 + Real.pi ^ 2 * t ^ 2 ≠ 0 := by
      positivity
    exact_mod_cast hdenSimpleReal
  have hleftDen_ne :
      ((2 * d : Real) : Complex) -
          ((2 * Real.pi * t : Real) : Complex) * Complex.I ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp [hd.ne'] at hreal
  have hrightDen_ne :
      (-((2 * d : Real) : Complex) -
          ((2 * Real.pi * t : Real) : Complex) * Complex.I) ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    simp [hd.ne'] at hreal
  push_cast
  simp only [suzukiGammaCauchyLeftExponent,
    suzukiGammaCauchyRightExponent]
  field_simp [hleft_ne, hright_ne, hleftDen_ne, hrightDen_ne,
    hdenComplex]
  ring_nf
  rw [Complex.I_sq]
  push_cast
  ring_nf at hdenComplex
  field_simp [hdenComplex, hdenSimpleComplex]
  ring

/-- The positive exponential piece of the `n`th Suzuki Gamma/Lerch screw
summand.  The complementary constant disappears after pairing with a
derivative of mean zero. -/
def suzukiGammaExponentialKernel (n : Nat) (x : Real) : Real :=
  let d : Real := (n : Real) + 1 / 4
  (1 / (4 * d ^ 2)) * Real.exp (-2 * d * |x|)

/-- The `n`th cancellation-safe Lerch contribution to Suzuki's screw
function, including its global `-1/4` coefficient. -/
def suzukiGammaLerchKernelSummand (n : Nat) (x : Real) : Real :=
  let d : Real := (n : Real) + 1 / 4
  (-1 / 4) *
    ((1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |x|))) / d ^ 2)

/-- The Fourier-facing exponential kernel is the Lerch screw summand plus a
constant.  That constant is the precise term later removed by the zero mean
of the source derivative. -/
theorem suzukiGammaExponentialKernel_eq_lerch_add_const
    (n : Nat) (x : Real) :
    suzukiGammaExponentialKernel n x =
      suzukiGammaLerchKernelSummand n x +
        1 / (4 * ((n : Real) + 1 / 4) ^ 2) := by
  dsimp only [suzukiGammaExponentialKernel,
    suzukiGammaLerchKernelSummand]
  have hd : ((n : Real) + 1 / 4) ≠ 0 := by positivity
  have hexponent :
      -2 * ((n : Real) + 1 / 4) * |x| =
        -((2 * (n : Real) + 1 / 2) * |x|) := by
    ring
  rw [hexponent]
  field_simp [hd]
  ring

/-- Summing the cancellation-safe kernel summands recovers exactly the
Lerch part of Suzuki's displayed screw function. -/
theorem tsum_suzukiGammaLerchKernelSummand (x : Real) :
    (∑' n : Nat, suzukiGammaLerchKernelSummand n x) =
      -(1 / 4) * suzukiLerchDifference x := by
  unfold suzukiGammaLerchKernelSummand suzukiLerchDifference
  rw [tsum_mul_left]
  ring

theorem continuous_suzukiGammaExponentialKernel (n : Nat) :
    Continuous (suzukiGammaExponentialKernel n) := by
  unfold suzukiGammaExponentialKernel
  fun_prop

theorem continuous_suzukiGammaLerchKernelSummand (n : Nat) :
    Continuous (suzukiGammaLerchKernelSummand n) := by
  unfold suzukiGammaLerchKernelSummand
  fun_prop

private theorem summable_suzukiGammaInverseSquareQuarter :
    Summable (fun n : Nat =>
      1 / (4 * ((n : Real) + 1 / 4) ^ 2)) := by
  have hbase :
      Summable (fun n : Nat => 1 / ((n : Real) + 1 / 4) ^ 2) := by
    have h :=
      (Real.summable_one_div_nat_add_rpow (1 / 4) 2).2 (by norm_num)
    apply h.congr
    intro n
    rw [abs_of_pos (by
      have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
      linarith), Real.rpow_two]
  have h := hbase.mul_left (1 / 4 : Real)
  apply h.congr
  intro n
  field_simp [show ((n : Real) + 1 / 4) ≠ 0 by positivity]

private theorem norm_suzukiGammaLerchKernelSummand_le
    (n : Nat) (x : Real) :
    ‖suzukiGammaLerchKernelSummand n x‖ ≤
      1 / (4 * ((n : Real) + 1 / 4) ^ 2) := by
  have hcoefficient : 0 ≤ 2 * (n : Real) + 1 / 2 := by positivity
  have hexponent :
      -((2 * (n : Real) + 1 / 2) * |x|) ≤ 0 := by
    exact neg_nonpos.mpr (mul_nonneg hcoefficient (abs_nonneg x))
  have hexp_le_one :
      Real.exp (-((2 * (n : Real) + 1 / 2) * |x|)) ≤ 1 :=
    (Real.exp_le_one_iff).2 hexponent
  have hnum_nonneg :
      0 ≤ 1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |x|)) :=
    sub_nonneg.mpr hexp_le_one
  have hnum_le_one :
      1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |x|)) ≤ 1 := by
    linarith [Real.exp_pos (-((2 * (n : Real) + 1 / 2) * |x|))]
  have hden : 0 < ((n : Real) + 1 / 4) ^ 2 := by positivity
  have hquarter : |(-1 / 4 : Real)| = 1 / 4 := by norm_num
  unfold suzukiGammaLerchKernelSummand
  rw [Real.norm_eq_abs, abs_mul, hquarter,
    abs_div, abs_of_nonneg hnum_nonneg, abs_of_pos hden]
  calc
    (1 / 4) *
          ((1 - Real.exp (-((2 * (n : Real) + 1 / 2) * |x|))) /
            ((n : Real) + 1 / 4) ^ 2) ≤
        (1 / 4) * (1 / ((n : Real) + 1 / 4) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact (div_le_div_iff_of_pos_right hden).2 hnum_le_one
      · norm_num
    _ = 1 / (4 * ((n : Real) + 1 / 4) ^ 2) := by
      field_simp [show ((n : Real) + 1 / 4) ≠ 0 by positivity]

theorem suzukiGammaExponentialKernel_neg (n : Nat) (x : Real) :
    suzukiGammaExponentialKernel n (-x) =
      suzukiGammaExponentialKernel n x := by
  simp [suzukiGammaExponentialKernel]

theorem suzukiGammaExponentialKernel_nonneg (n : Nat) (x : Real) :
    0 ≤ suzukiGammaExponentialKernel n x := by
  unfold suzukiGammaExponentialKernel
  positivity

theorem suzukiGammaExponentialKernel_le_basePoint
    (n : Nat) (x : Real) :
    suzukiGammaExponentialKernel n x ≤
      1 / (4 * ((n : Real) + 1 / 4) ^ 2) := by
  unfold suzukiGammaExponentialKernel
  have hexponent :
      -2 * ((n : Real) + 1 / 4) * |x| ≤ 0 := by
    nlinarith [abs_nonneg x]
  have hexp :
      Real.exp (-2 * ((n : Real) + 1 / 4) * |x|) ≤ 1 :=
    (Real.exp_le_one_iff).2 hexponent
  have hcoefficient :
      0 ≤ 1 / (4 * ((n : Real) + 1 / 4) ^ 2) := by
    positivity
  nlinarith

private theorem coe_suzukiGammaExponentialKernel_eq_cauchy
    (n : Nat) :
    (fun x : Real => (suzukiGammaExponentialKernel n x : Complex)) =
      fun x : Real =>
        ((1 / (4 * ((n : Real) + 1 / 4) ^ 2) : Real) : Complex) *
          suzukiGammaCauchyKernel ((n : Real) + 1 / 4) x := by
  funext x
  simp only [suzukiGammaExponentialKernel, suzukiGammaCauchyKernel]
  push_cast
  ring

theorem integrable_coe_suzukiGammaExponentialKernel (n : Nat) :
    Integrable (fun x : Real =>
      (suzukiGammaExponentialKernel n x : Complex)) := by
  rw [coe_suzukiGammaExponentialKernel_eq_cauchy]
  exact (integrable_suzukiGammaCauchyKernel (d := (n : Real) + 1 / 4)
    (by positivity)).const_mul _

/-- A physical exponential Gamma summand against the derivative
autocorrelation is exactly its compact finite-square kernel pairing.  The
proof extends the square integral to the full plane using source support,
then uses Fubini and translation invariance to recover the autocorrelation.
-/
theorem integral_suzukiGammaExponentialKernel_mul_autocorrelation_eq_pairing
    {a : Real} {v : SchwartzLineTestFunction}
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (n : Nat) :
    (∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation (SchwartzMap.derivCLM Complex Complex v) x) =
      suzukiFiniteKernelPairingComplex
        (suzukiGammaExponentialKernel n) a
          (SchwartzMap.derivCLM Complex Complex v) := by
  let u : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v
  let F : Real → Real → Complex := fun x y =>
    (suzukiGammaExponentialKernel n (x - y) : Complex) *
      u y * conj (u x)
  let G : Real → Real → Complex := fun y s =>
    (suzukiGammaExponentialKernel n s : Complex) *
      u y * conj (u (s + y))
  have hu : Integrable u :=
    (SchwartzMap.derivCLM Complex Complex v).integrable
  have hconj : Integrable (fun x : Real => conj (u x)) := by
    have hcomp :=
      Complex.conjCLE.toContinuousLinearMap.integrable_comp hu
    change Integrable (fun x : Real => Complex.conjCLE (u x))
    exact hcomp
  have hseparable : Integrable (fun p : Real × Real =>
      u p.2 * conj (u p.1)) (volume.prod volume) := by
    have hprod := hconj.mul_prod hu
    apply hprod.congr
    filter_upwards with p
    ring
  have hFraw : Integrable (fun p : Real × Real =>
      (suzukiGammaExponentialKernel n (p.1 - p.2) : Complex) *
        (u p.2 * conj (u p.1))) (volume.prod volume) := by
    apply hseparable.bdd_mul
    · change AEStronglyMeasurable (fun p : Real × Real =>
        (suzukiGammaExponentialKernel n (p.1 - p.2) : Complex))
      exact (Complex.continuous_ofReal.comp
        ((continuous_suzukiGammaExponentialKernel n).comp
          (by fun_prop : Continuous (fun p : Real × Real => p.1 - p.2))))
            |>.aestronglyMeasurable
    · filter_upwards with p
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suzukiGammaExponentialKernel_nonneg n _)]
      exact suzukiGammaExponentialKernel_le_basePoint n _
  have hF : Integrable (fun p : Real × Real => F p.1 p.2)
      (volume.prod volume) := by
    simpa only [F, mul_assoc] using hFraw
  have hcoupled : Integrable (fun p : Real × Real =>
      u p.1 * conj (u (p.2 + p.1))) (volume.prod volume) := by
    let H : Real × Real → Complex := fun p => u p.1 * conj (u p.2)
    have hH : Integrable H := hu.mul_prod hconj
    have hcomp :=
      (measurePreserving_prod_add_right
        (volume : Measure Real) (volume : Measure Real)).integrable_comp_of_integrable hH
    change Integrable (fun p : Real × Real =>
      u p.1 * conj (u (p.2 + p.1))) (volume.prod volume) at hcomp
    exact hcomp
  have hGraw : Integrable (fun p : Real × Real =>
      (suzukiGammaExponentialKernel n p.2 : Complex) *
        (u p.1 * conj (u (p.2 + p.1)))) (volume.prod volume) := by
    apply hcoupled.bdd_mul
    · change AEStronglyMeasurable (fun p : Real × Real =>
        (suzukiGammaExponentialKernel n p.2 : Complex))
      exact (Complex.continuous_ofReal.comp
        ((continuous_suzukiGammaExponentialKernel n).comp
          (by fun_prop : Continuous (fun p : Real × Real => p.2))))
            |>.aestronglyMeasurable
    · filter_upwards with p
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (suzukiGammaExponentialKernel_nonneg n _)]
      exact suzukiGammaExponentialKernel_le_basePoint n _
  have hG : Integrable (fun p : Real × Real => G p.1 p.2)
      (volume.prod volume) := by
    simpa only [G, mul_assoc] using hGraw
  have hsupportU : Function.support u ⊆ Set.Icc (-a) a := by
    simpa only [u] using support_deriv_subset_Icc hsupport
  have hrestrict :
      (∫ p in suzukiFiniteSquare a, F p.1 p.2) =
        ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro p hp
    by_cases hx : p.1 ∈ Set.Icc (-a) a
    · have hy : p.2 ∉ Set.Icc (-a) a := fun hy => hp ⟨hx, hy⟩
      have huy : u p.2 = 0 := by
        by_contra hne
        exact hy (hsupportU hne)
      simp [F, huy]
    · have hux : u p.1 = 0 := by
        by_contra hne
        exact hx (hsupportU hne)
      simp [F, hux]
  have hfiber (y : Real) :
      (∫ x : Real, F x y) = ∫ s : Real, G y s := by
    have htranslate := integral_sub_right_eq_self
      (fun s : Real => G y s) y (μ := volume)
    simpa only [F, G, sub_add_cancel] using htranslate
  have hphysicalNeg :
      (∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume)) =
        ∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation u (-s) := by
    rw [MeasureTheory.integral_prod_symm _ hG]
    apply integral_congr_ae
    filter_upwards with s
    simp only [G]
    rw [show (fun x : Real =>
        (suzukiGammaExponentialKernel n s : Complex) *
            u x * conj (u (s + x))) =
          fun x : Real =>
            (suzukiGammaExponentialKernel n s : Complex) *
              (u x * conj (u (s + x))) by
        funext x
        ring]
    rw [integral_const_mul]
    apply congrArg (fun z : Complex =>
      (suzukiGammaExponentialKernel n s : Complex) * z)
    rw [autocorrelation_apply, MeasureTheory.convolution_def]
    apply integral_congr_ae
    filter_upwards with y
    simp only [star_apply]
    congr 2
    ring
  have hreflect := integral_neg_eq_self
    (f := fun x : Real =>
      (suzukiGammaExponentialKernel n x : Complex) *
        autocorrelation u x) volume
  have hphysical :
      (∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation u (-s)) =
        ∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation u s := by
    simpa only [suzukiGammaExponentialKernel_neg, neg_neg] using hreflect
  calc
    (∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation
            (SchwartzMap.derivCLM Complex Complex v) x) =
        ∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation u s := by rfl
    _ = ∫ s : Real,
          (suzukiGammaExponentialKernel n s : Complex) *
            autocorrelation u (-s) := hphysical.symm
    _ = ∫ p : Real × Real, G p.1 p.2 ∂(volume.prod volume) :=
      hphysicalNeg.symm
    _ = ∫ y : Real, ∫ s : Real, G y s :=
      MeasureTheory.integral_prod (fun p : Real × Real => G p.1 p.2) hG
    _ = ∫ y : Real, ∫ x : Real, F x y := by
      apply integral_congr_ae
      filter_upwards with y
      exact hfiber y |>.symm
    _ = ∫ x : Real, ∫ y : Real, F x y :=
      (MeasureTheory.integral_integral_swap hF).symm
    _ = ∫ p : Real × Real, F p.1 p.2 ∂(volume.prod volume) :=
      MeasureTheory.integral_integral hF
    _ = ∫ p in suzukiFiniteSquare a, F p.1 p.2 := hrestrict.symm
    _ = suzukiFiniteKernelPairingComplex
        (suzukiGammaExponentialKernel n) a
          (SchwartzMap.derivCLM Complex Complex v) := by
      rfl

private theorem suzukiFiniteKernelPairingComplex_const_eq_zero_of_zeroMean
    {a : Real} {u : Real → Complex}
    (hzero : (∫ x in Set.Icc (-a) a, u x) = 0) (c : Real) :
    suzukiFiniteKernelPairingComplex (fun _ => c) a u = 0 := by
  rw [suzukiFiniteKernelPairingComplex]
  calc
    (∫ p in suzukiFiniteSquare a,
        suzukiKernelPairingIntegrand (fun _ => c) u p) =
        ∫ p in Set.Icc (-a) a ×ˢ Set.Icc (-a) a,
          conj (u p.1) * ((c : Complex) * u p.2) := by
      apply setIntegral_congr_fun
        (isCompact_suzukiFiniteSquare a).measurableSet
      intro p _
      unfold suzukiKernelPairingIntegrand
      ring
    _ = (∫ x in Set.Icc (-a) a, conj (u x)) *
          ∫ y in Set.Icc (-a) a, (c : Complex) * u y := by
      exact MeasureTheory.setIntegral_prod_mul
        (fun x : Real => conj (u x))
        (fun y : Real => (c : Complex) * u y)
        (Set.Icc (-a) a) (Set.Icc (-a) a)
    _ = 0 := by
      rw [integral_conj, hzero, map_zero, zero_mul]

/-- The explicit base-point constant between the physical exponential
kernel and the cancellation-safe Lerch summand is invisible to the compact
pairing because the supported source derivative has zero interval mean. -/
theorem suzukiFiniteKernelPairingComplex_gammaExponential_eq_lerch
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (n : Nat) :
    suzukiFiniteKernelPairingComplex
        (suzukiGammaExponentialKernel n) a
          (SchwartzMap.derivCLM Complex Complex v) =
      suzukiFiniteKernelPairingComplex
        (suzukiGammaLerchKernelSummand n) a
          (SchwartzMap.derivCLM Complex Complex v) := by
  let u : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v
  have hzero : (∫ x in Set.Icc (-a) a, u x) = 0 := by
    have hbase := setIntegral_exp_mul_deriv_eq ha hsupport 0
    norm_num at hbase
    have hderiv :
        deriv (v : Real → Complex) = (u : Real → Complex) := by
      funext x
      exact (SchwartzMap.derivCLM_apply Complex v x).symm
    rw [← hderiv]
    exact hbase
  have hconst :
      suzukiFiniteKernelPairingComplex
          (fun _ : Real => 1 / (4 * ((n : Real) + 1 / 4) ^ 2)) a u = 0 :=
    suzukiFiniteKernelPairingComplex_const_eq_zero_of_zeroMean hzero _
  have hkernel :
      suzukiGammaExponentialKernel n = fun x =>
        suzukiGammaLerchKernelSummand n x +
          1 / (4 * ((n : Real) + 1 / 4) ^ 2) := by
    funext x
    exact suzukiGammaExponentialKernel_eq_lerch_add_const n x
  rw [show SchwartzMap.derivCLM Complex Complex v = u by rfl, hkernel]
  rw [suzukiFiniteKernelPairingComplex_add]
  · rw [hconst, add_zero]
  · unfold suzukiGammaLerchKernelSummand
    fun_prop
  · fun_prop
  · exact u.continuous

/-- The exact Fourier multiplier carried by one positive exponential
Gamma/Lerch kernel piece. -/
theorem fourier_suzukiGammaExponentialKernel
    (n : Nat) (t : Real) :
    (𝓕 (fun x : Real =>
      (suzukiGammaExponentialKernel n x : Complex))) t =
      ((1 / (((n : Real) + 1 / 4) *
        (4 * ((n : Real) + 1 / 4) ^ 2 +
          (2 * Real.pi * t) ^ 2)) : Real) : Complex) := by
  rw [coe_suzukiGammaExponentialKernel_eq_cauchy]
  let c : Complex :=
    ((1 / (4 * ((n : Real) + 1 / 4) ^ 2) : Real) : Complex)
  let d : Real := (n : Real) + 1 / 4
  have hlinear :
      (𝓕 (c • suzukiGammaCauchyKernel d)) t =
        c * (𝓕 (suzukiGammaCauchyKernel d)) t := by
    rw [Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  change (𝓕 (c • suzukiGammaCauchyKernel d)) t = _
  rw [hlinear,
    fourier_suzukiGammaCauchyKernel (d := d) (by simp [d]; positivity)]
  dsimp only [c, d]
  have hd : ((n : Real) + 1 / 4) ≠ 0 := by positivity
  have hden :
      4 * ((n : Real) + 1 / 4) ^ 2 +
          (2 * Real.pi * t) ^ 2 ≠ 0 := by
    positivity
  push_cast
  field_simp [hd, hden]

/-- Fourier self-adjointness turns one rational Gamma multiplier against the
Fourier energy of `v'` into the corresponding physical exponential
autocorrelation integral. -/
theorem integral_suzukiGammaMultiplier_mul_fourierAutocorrelation_deriv
    (n : Nat) (v : SchwartzLineTestFunction) :
    (∫ t : Real,
        ((1 / (((n : Real) + 1 / 4) *
          (4 * ((n : Real) + 1 / 4) ^ 2 +
            (2 * Real.pi * t) ^ 2)) : Real) : Complex) *
          fourierAutocorrelation
            (SchwartzMap.derivCLM Complex Complex v) t) =
      ∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation (SchwartzMap.derivCLM Complex Complex v) x := by
  let u : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v
  have hself :=
    VectorFourier.integral_fourierIntegral_smul_eq_flip
      (e := Real.fourierChar) (μ := volume) (ν := volume) (L := innerₗ Real)
        Real.continuous_fourierChar continuous_inner
        (integrable_coe_suzukiGammaExponentialKernel n)
        (fourierAutocorrelation u).integrable
  rw [flip_innerₗ] at hself
  change
    (∫ t : Real,
        (𝓕 (fun x : Real =>
          (suzukiGammaExponentialKernel n x : Complex))) t •
            fourierAutocorrelation u t) =
      ∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) •
          (𝓕 (fourierAutocorrelation u : Real → Complex)) x at hself
  have hraw :
      (∫ t : Real,
          ((1 / (((n : Real) + 1 / 4) *
            (4 * ((n : Real) + 1 / 4) ^ 2 +
              (2 * Real.pi * t) ^ 2)) : Real) : Complex) *
            fourierAutocorrelation u t) =
        ∫ x : Real,
          (suzukiGammaExponentialKernel n x : Complex) *
            autocorrelation u (-x) := by
    simpa only [smul_eq_mul, fourier_suzukiGammaExponentialKernel,
      ← SchwartzMap.fourier_coe,
      fourier_fourierAutocorrelation_apply] using hself
  have hreflect := integral_neg_eq_self
    (f := fun x : Real =>
      (suzukiGammaExponentialKernel n x : Complex) *
        autocorrelation u x) volume
  have hphysical :
      (∫ x : Real,
          (suzukiGammaExponentialKernel n x : Complex) *
            autocorrelation u (-x)) =
        ∫ x : Real,
          (suzukiGammaExponentialKernel n x : Complex) *
            autocorrelation u x := by
    simpa only [suzukiGammaExponentialKernel_neg, neg_neg] using hreflect
  exact hraw.trans hphysical

/-- Differentiating the source multiplies its Mathlib-frequency Fourier
energy by `(2*pi*t)^2`. -/
theorem fourierAutocorrelation_derivCLM_apply
    (v : SchwartzLineTestFunction) (t : Real) :
    fourierAutocorrelation (SchwartzMap.derivCLM Complex Complex v) t =
      ((2 * Real.pi * t) ^ 2 : Real) * fourierAutocorrelation v t := by
  let u : SchwartzLineTestFunction :=
    SchwartzMap.derivCLM Complex Complex v
  have hderiv :
      deriv (v : Real → Complex) = (u : Real → Complex) := by
    funext x
    exact (SchwartzMap.derivCLM_apply Complex v x).symm
  have hfourierFunction :=
    congrFun (Real.fourier_deriv v.integrable v.differentiable u.integrable) t
  rw [hderiv] at hfourierFunction
  have hfourier :
      (𝓕 u) t =
        ((2 * Real.pi * t : Real) : Complex) * Complex.I * (𝓕 v) t := by
    rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
    simp only [smul_eq_mul] at hfourierFunction
    rw [hfourierFunction]
    push_cast
    ring
  rw [fourierAutocorrelation_apply, fourierAutocorrelation_apply, hfourier]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Suzuki frequency `-2*pi*t` is exactly Mathlib frequency `t`. -/
private theorem suzukiFourierSource_neg_twoPi_mul_eq_fourier
    (f : SchwartzLineTestFunction) (t : Real) :
    suzukiFourierSource f ((-2 * Real.pi * t : Real) : Complex) =
      (𝓕 f) t := by
  rw [SchwartzMap.fourier_coe,
    Real.fourier_real_eq_integral_exp_smul]
  unfold suzukiFourierSource
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with x
  apply congrArg (fun z : Complex => Complex.exp z * f x)
  push_cast
  ring

private theorem fourierAutocorrelation_suzukiProjectBase_neg_twoPi_mul
    (v : SchwartzLineTestFunction) (t : Real) :
    fourierAutocorrelation (suzukiProjectBase v) (-2 * Real.pi * t) =
      fourierAutocorrelation v t := by
  rw [fourierAutocorrelation_suzukiProjectBase_apply,
    suzukiFourierSource_neg_twoPi_mul_eq_fourier]
  rfl

/-- The nonnegative reciprocal term obtained from the real part of Gauss's
digamma series on the quarter line.  Its exact `1/4` and `t/2`
normalization is the spectral counterpart of Suzuki's Lerch kernel. -/
def suzukiGammaSpectralSummand (n : Nat) (t : Real) : Real :=
  (t / 2) ^ 2 /
    (((n : Real) + 1 / 4) *
      (((n : Real) + 1 / 4) ^ 2 + (t / 2) ^ 2))

/-- One quarter-line rational Gamma summand, including the outer project
`1/(2*pi)` normalization, is exactly the physical exponential
autocorrelation integral of the source derivative. -/
theorem one_div_twoPi_integral_suzukiGammaSpectralSummand_eq_exponential
    (n : Nat) (v : SchwartzLineTestFunction) :
    ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ t : Real,
          fourierAutocorrelation (suzukiProjectBase v) t *
            (suzukiGammaSpectralSummand n t : Complex) =
      ∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation (SchwartzMap.derivCLM Complex Complex v) x := by
  let spectralIntegrand : Real → Complex := fun t =>
    fourierAutocorrelation (suzukiProjectBase v) t *
      (suzukiGammaSpectralSummand n t : Complex)
  have hscale := Measure.integral_comp_mul_left
    (g := spectralIntegrand) (-2 * Real.pi)
  have hscaleNormalized :
      (∫ t : Real, spectralIntegrand (-2 * Real.pi * t)) =
        (1 / (2 * Real.pi) : Real) •
          ∫ t : Real, spectralIntegrand t := by
    simpa [abs_inv, abs_mul, abs_of_pos Real.pi_pos] using hscale
  calc
    ((1 / (2 * Real.pi) : Real) : Complex) *
          ∫ t : Real,
            fourierAutocorrelation (suzukiProjectBase v) t *
              (suzukiGammaSpectralSummand n t : Complex) =
        ∫ t : Real, spectralIntegrand (-2 * Real.pi * t) := by
          simpa only [spectralIntegrand, Complex.real_smul] using
            hscaleNormalized.symm
    _ = ∫ t : Real,
        ((1 / (((n : Real) + 1 / 4) *
          (4 * ((n : Real) + 1 / 4) ^ 2 +
            (2 * Real.pi * t) ^ 2)) : Real) : Complex) *
          fourierAutocorrelation
            (SchwartzMap.derivCLM Complex Complex v) t := by
      apply integral_congr_ae
      filter_upwards with t
      unfold spectralIntegrand
      rw [fourierAutocorrelation_suzukiProjectBase_neg_twoPi_mul,
        fourierAutocorrelation_derivCLM_apply]
      unfold suzukiGammaSpectralSummand
      have hd : ((n : Real) + 1 / 4) ≠ 0 := by positivity
      have hdenSmall :
          ((n : Real) + 1 / 4) ^ 2 +
              ((-2 * Real.pi * t) / 2) ^ 2 ≠ 0 := by
        positivity
      have hdenLarge :
          4 * ((n : Real) + 1 / 4) ^ 2 +
              (2 * Real.pi * t) ^ 2 ≠ 0 := by
        positivity
      push_cast
      field_simp [hd, hdenSmall, hdenLarge]
      ring
    _ = ∫ x : Real,
        (suzukiGammaExponentialKernel n x : Complex) *
          autocorrelation (SchwartzMap.derivCLM Complex Complex v) x :=
      integral_suzukiGammaMultiplier_mul_fourierAutocorrelation_deriv n v

/-- One quarter-line rational Gamma summand is exactly the compact
finite-square pairing for the corresponding cancellation-safe Lerch kernel.
This is the termwise spectral-to-Suzuki bridge; it uses no series/integral
interchange. -/
theorem one_div_twoPi_integral_suzukiGammaSpectralSummand_eq_lerchPairing
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (n : Nat) :
    ((1 / (2 * Real.pi) : Real) : Complex) *
        ∫ t : Real,
          fourierAutocorrelation (suzukiProjectBase v) t *
            (suzukiGammaSpectralSummand n t : Complex) =
      suzukiFiniteKernelPairingComplex
        (suzukiGammaLerchKernelSummand n) a
          (SchwartzMap.derivCLM Complex Complex v) := by
  calc
    ((1 / (2 * Real.pi) : Real) : Complex) *
          ∫ t : Real,
            fourierAutocorrelation (suzukiProjectBase v) t *
              (suzukiGammaSpectralSummand n t : Complex) =
        ∫ x : Real,
          (suzukiGammaExponentialKernel n x : Complex) *
            autocorrelation
              (SchwartzMap.derivCLM Complex Complex v) x :=
      one_div_twoPi_integral_suzukiGammaSpectralSummand_eq_exponential n v
    _ = suzukiFiniteKernelPairingComplex
        (suzukiGammaExponentialKernel n) a
          (SchwartzMap.derivCLM Complex Complex v) :=
      integral_suzukiGammaExponentialKernel_mul_autocorrelation_eq_pairing
        hsupport n
    _ = suzukiFiniteKernelPairingComplex
        (suzukiGammaLerchKernelSummand n) a
          (SchwartzMap.derivCLM Complex Complex v) :=
      suzukiFiniteKernelPairingComplex_gammaExponential_eq_lerch
        ha hsupport n

/-- The inverse-square kernel bound gives the convergent physical pairing
series, with sum equal to the pairing of the pointwise kernel series. -/
theorem hasSum_suzukiFiniteKernelPairingComplex_gammaLerch
    (a : Real) {u : Real → Complex} (hu : Continuous u) :
    HasSum (fun n : Nat =>
        suzukiFiniteKernelPairingComplex
          (suzukiGammaLerchKernelSummand n) a u)
      (suzukiFiniteKernelPairingComplex
        (fun x => ∑' n : Nat, suzukiGammaLerchKernelSummand n x) a u) := by
  let F : Nat → (Real × Real) → Complex := fun n p =>
    suzukiKernelPairingIntegrand
      (suzukiGammaLerchKernelSummand n) u p
  let bound : Nat → (Real × Real) → Real := fun n p =>
    (1 / (4 * ((n : Real) + 1 / 4) ^ 2)) *
      (‖u p.2‖ * ‖u p.1‖)
  let μ : Measure (Real × Real) :=
    (volume : Measure (Real × Real)).restrict (suzukiFiniteSquare a)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) μ := by
    intro n
    exact (continuous_suzukiKernelPairingIntegrand
      (continuous_suzukiGammaLerchKernelSummand n) hu).aestronglyMeasurable
  have h_bound : ∀ n, ∀ᵐ p ∂μ, ‖F n p‖ ≤ bound n p := by
    intro n
    filter_upwards with p
    dsimp only [F, bound]
    unfold suzukiKernelPairingIntegrand
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_conj]
    calc
      ‖suzukiGammaLerchKernelSummand n (p.1 - p.2)‖ *
            ‖u p.2‖ * ‖u p.1‖ ≤
          (1 / (4 * ((n : Real) + 1 / 4) ^ 2)) *
            ‖u p.2‖ * ‖u p.1‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right
            (norm_suzukiGammaLerchKernelSummand_le n (p.1 - p.2))
            (norm_nonneg _)
        · exact norm_nonneg _
      _ = (1 / (4 * ((n : Real) + 1 / 4) ^ 2)) *
          (‖u p.2‖ * ‖u p.1‖) := by ring
  have hbound_summable : ∀ᵐ p ∂μ, Summable (fun n => bound n p) := by
    filter_upwards with p
    exact summable_suzukiGammaInverseSquareQuarter.mul_right
      (‖u p.2‖ * ‖u p.1‖)
  have hbase_continuous :
      Continuous (fun p : Real × Real => ‖u p.2‖ * ‖u p.1‖) := by
    fun_prop
  have hbase_integrable :
      Integrable (fun p : Real × Real => ‖u p.2‖ * ‖u p.1‖) μ := by
    exact hbase_continuous.continuousOn.integrableOn_compact
      (isCompact_suzukiFiniteSquare a)
  have hbound_integrable : Integrable (fun p => ∑' n, bound n p) μ := by
    have hscaled := hbase_integrable.const_mul
      (∑' n : Nat, 1 / (4 * ((n : Real) + 1 / 4) ^ 2))
    simpa only [bound, tsum_mul_right] using hscaled
  have h_lim : ∀ᵐ p ∂μ,
      HasSum (fun n => F n p)
        (suzukiKernelPairingIntegrand
          (fun x => ∑' n : Nat, suzukiGammaLerchKernelSummand n x) u p) := by
    filter_upwards with p
    have hkernelComplex :
        Summable (fun n : Nat =>
          (suzukiGammaLerchKernelSummand n (p.1 - p.2) : Complex)) :=
      summable_suzukiGammaInverseSquareQuarter.of_norm_bounded
        (fun n => by
          simpa only [Complex.norm_real] using
            norm_suzukiGammaLerchKernelSummand_le n (p.1 - p.2))
    have hprod :=
      (hkernelComplex.hasSum.mul_right (u p.2)).mul_right (conj (u p.1))
    simpa only [F, suzukiKernelPairingIntegrand, Complex.ofReal_tsum] using hprod
  have hinterchange := hasSum_integral_of_dominated_convergence
    (μ := μ) bound hF_meas h_bound hbound_summable hbound_integrable h_lim
  simpa only [F, μ, suzukiFiniteKernelPairingComplex] using
    hinterchange

/-- The inverse-square kernel bound justifies exchanging the Lerch series
with the compact finite-square pairing. -/
theorem tsum_suzukiFiniteKernelPairingComplex_gammaLerch
    (a : Real) {u : Real → Complex} (hu : Continuous u) :
    (∑' n : Nat,
        suzukiFiniteKernelPairingComplex
          (suzukiGammaLerchKernelSummand n) a u) =
      suzukiFiniteKernelPairingComplex
        (fun x => ∑' n : Nat, suzukiGammaLerchKernelSummand n x) a u :=
  (hasSum_suzukiFiniteKernelPairingComplex_gammaLerch a hu).tsum_eq

theorem tsum_suzukiFiniteKernelPairingComplex_gammaLerch_eq_difference
    (a : Real) {u : Real → Complex} (hu : Continuous u) :
    (∑' n : Nat,
        suzukiFiniteKernelPairingComplex
          (suzukiGammaLerchKernelSummand n) a u) =
      suzukiFiniteKernelPairingComplex
        (fun x => -(1 / 4) * suzukiLerchDifference x) a u := by
  rw [tsum_suzukiFiniteKernelPairingComplex_gammaLerch a hu]
  congr 1
  funext x
  exact tsum_suzukiGammaLerchKernelSummand x

/-- Real-part form of the termwise Gamma bridge, matching the real spectral
integrals used by the completed-zeta Gamma side. -/
theorem one_div_twoPi_integral_suzukiGammaSpectralSummand_re_eq_lerchPairing
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) (n : Nat) :
    (1 / (2 * Real.pi)) *
        ∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re *
            suzukiGammaSpectralSummand n t =
      (suzukiFiniteKernelPairingComplex
        (suzukiGammaLerchKernelSummand n) a
          (SchwartzMap.derivCLM Complex Complex v)).re := by
  have hintegral :
      (∫ t : Real,
          fourierAutocorrelation (suzukiProjectBase v) t *
            (suzukiGammaSpectralSummand n t : Complex)) =
        ((∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re *
            suzukiGammaSpectralSummand n t : Real) : Complex) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    rw [fourierAutocorrelation_apply, Complex.mul_conj]
    simp
  have hreal := congrArg Complex.re
    (one_div_twoPi_integral_suzukiGammaSpectralSummand_eq_lerchPairing
      ha hsupport n)
  rw [hintegral] at hreal
  simpa [Complex.mul_re] using hreal

/-- Subtracting the quarter-line base point cancels the constant part of
Gauss's digamma series term by term. -/
theorem digamma_quarterLine_sub_eq_tsum (t : Real) :
    Complex.digamma
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) -
        Complex.digamma (1 / 4 : Complex) =
      ∑' n : Nat,
        (ComplexCompactExhaustion.gaussDigammaSeriesTerm
            ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n -
          ComplexCompactExhaustion.gaussDigammaSeriesTerm
            (1 / 4 : Complex) n) := by
  let z : Complex :=
    (1 / 4 : Complex) + (t / 2 : Real) * Complex.I
  let z₀ : Complex := (1 / 4 : Complex)
  have hz : 0 < z.re := by
    simp [z]
  have hz₀ : 0 < z₀.re := by
    simp [z₀]
  have hsum :=
    ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz
  have hsum₀ :=
    ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz₀
  have hseries :=
    ComplexCompactExhaustion.gaussDigammaSeriesSum_eq_digamma_add_eulerMascheroni
      hz
  have hseries₀ :=
    ComplexCompactExhaustion.gaussDigammaSeriesSum_eq_digamma_add_eulerMascheroni
      hz₀
  change Complex.digamma z - Complex.digamma z₀ = _
  have hdigamma :
      Complex.digamma z - Complex.digamma z₀ =
        ComplexCompactExhaustion.gaussDigammaSeriesSum z -
          ComplexCompactExhaustion.gaussDigammaSeriesSum z₀ := by
    rw [hseries, hseries₀]
    ring
  rw [hdigamma]
  unfold ComplexCompactExhaustion.gaussDigammaSeriesSum
  rw [hsum.tsum_sub hsum₀]

private theorem re_inv_real_sub_inv_real_add_mul_I
    {d y : Real} (hd : 0 < d) :
    (((d : Complex)⁻¹ -
        ((d : Complex) + (y : Complex) * Complex.I)⁻¹).re) =
      y ^ 2 / (d * (d ^ 2 + y ^ 2)) := by
  have hdne : d ≠ 0 := hd.ne'
  have hden : d ^ 2 + y ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_pos hd, sq_nonneg y]
  rw [Complex.sub_re, Complex.inv_re, Complex.inv_re]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    mul_one, zero_add]
  field_simp [hdne, hden]
  ring

private theorem re_gaussDigammaSeriesTerm_quarterLine_sub
    (n : Nat) (t : Real) :
    (ComplexCompactExhaustion.gaussDigammaSeriesTerm
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n -
        ComplexCompactExhaustion.gaussDigammaSeriesTerm
          (1 / 4 : Complex) n).re =
      suzukiGammaSpectralSummand n t := by
  let d : Real := (n : Real) + 1 / 4
  let y : Real := t / 2
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hcancel :
      ComplexCompactExhaustion.gaussDigammaSeriesTerm
            ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n -
          ComplexCompactExhaustion.gaussDigammaSeriesTerm
            (1 / 4 : Complex) n =
        (d : Complex)⁻¹ -
          ((d : Complex) + (y : Complex) * Complex.I)⁻¹ := by
    dsimp only [d, y]
    unfold ComplexCompactExhaustion.gaussDigammaSeriesTerm
    push_cast
    ring
  rw [hcancel]
  simpa only [suzukiGammaSpectralSummand, d, y] using
    re_inv_real_sub_inv_real_add_mul_I hd

theorem suzukiGammaSpectralSummand_nonneg (n : Nat) (t : Real) :
    0 ≤ suzukiGammaSpectralSummand n t := by
  unfold suzukiGammaSpectralSummand
  positivity

theorem continuous_suzukiGammaSpectralSummand (n : Nat) :
    Continuous (suzukiGammaSpectralSummand n) := by
  unfold suzukiGammaSpectralSummand
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro t
  positivity

private theorem summable_suzukiGammaInverseCube :
    Summable (fun n : Nat => 1 / ((n : Real) + 1 / 4) ^ 3) := by
  have h :=
    (Real.summable_one_div_nat_add_rpow (1 / 4) 3).2 (by norm_num)
  apply h.congr
  intro n
  rw [abs_of_pos (by
    have hn : (0 : Real) ≤ n := Nat.cast_nonneg n
    linarith)]
  exact congrArg (fun x : Real => 1 / x)
    (Real.rpow_natCast ((n : Real) + 1 / 4) 3)

private theorem summable_suzukiGammaInverseCubeQuarter :
    Summable (fun n : Nat =>
      1 / (4 * ((n : Real) + 1 / 4) ^ 3)) := by
  have h := summable_suzukiGammaInverseCube.mul_left (1 / 4 : Real)
  apply h.congr
  intro n
  field_simp [show ((n : Real) + 1 / 4) ≠ 0 by positivity]

/-- The rational Gamma summand has an inverse-cube majorant, with all
dependence on the spectral variable isolated in the quadratic factor. -/
theorem suzukiGammaSpectralSummand_le_inverseCube_mul_sq
    (n : Nat) (t : Real) :
    suzukiGammaSpectralSummand n t ≤
      t ^ 2 / (4 * ((n : Real) + 1 / 4) ^ 3) := by
  let d : Real := (n : Real) + 1 / 4
  let y : Real := t / 2
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hden : d ^ 3 ≤ d * (d ^ 2 + y ^ 2) := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_left hy (by positivity : 0 < d ^ 3) hden
  have hrewrite : y ^ 2 / d ^ 3 = t ^ 2 / (4 * d ^ 3) := by
    dsimp only [y]
    field_simp [hd.ne']
    ring
  unfold suzukiGammaSpectralSummand
  change y ^ 2 / (d * (d ^ 2 + y ^ 2)) ≤
    t ^ 2 / (4 * d ^ 3)
  rw [← hrewrite]
  exact hdiv

/-- A quadratic spectral moment of the Fourier autocorrelation is integrable,
as a direct specialization of Schwartz weighted integrability. -/
theorem integrable_sq_mul_fourierAutocorrelation_re
    (g : SchwartzLineTestFunction) :
    Integrable (fun t : Real =>
      t ^ 2 * (fourierAutocorrelation g t).re) := by
  have hweighted :=
    (fourierAutocorrelation g).integrable_pow_mul
      (volume : Measure Real) 2
  convert hweighted using 1
  ext t
  rw [fourierAutocorrelation_apply, Complex.mul_conj]
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
  rw [sq_abs, abs_of_nonneg (Complex.normSq_nonneg _)]

/-- The exact rational series on the quarter line is absolutely summable.
This is the convergence input needed by the later Gamma/Lerch integral
interchange. -/
theorem summable_suzukiGammaSpectralSummand (t : Real) :
    Summable (fun n : Nat => suzukiGammaSpectralSummand n t) := by
  have hz :
      0 < (((1 / 4 : Complex) +
        (t / 2 : Real) * Complex.I)).re := by simp
  have hz₀ : 0 < ((1 / 4 : Complex)).re := by simp
  have hsum :=
    (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz).sub
      (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz₀)
  rcases hsum with ⟨s, hs⟩
  have hre : Summable (fun n : Nat =>
      (ComplexCompactExhaustion.gaussDigammaSeriesTerm
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n -
        ComplexCompactExhaustion.gaussDigammaSeriesTerm
          (1 / 4 : Complex) n).re) :=
    ⟨s.re, Complex.hasSum_re hs⟩
  exact hre.congr (fun n => re_gaussDigammaSeriesTerm_quarterLine_sub n t)

/-- The inverse-cube estimate justifies exchanging the rational Gamma series
with the formula-side spectral integral. -/
theorem integral_tsum_suzukiGammaSpectralSummand
    (v : SchwartzLineTestFunction) :
    (∫ t : Real,
        (fourierAutocorrelation (suzukiProjectBase v) t).re *
          ∑' n : Nat, suzukiGammaSpectralSummand n t) =
      ∑' n : Nat,
        ∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re *
            suzukiGammaSpectralSummand n t := by
  let g : SchwartzLineTestFunction := suzukiProjectBase v
  let F : Nat → Real → Real := fun n t =>
    (fourierAutocorrelation g t).re *
      suzukiGammaSpectralSummand n t
  let bound : Nat → Real → Real := fun n t =>
    (1 / (4 * ((n : Real) + 1 / 4) ^ 3)) *
      (t ^ 2 * (fourierAutocorrelation g t).re)
  have hF_meas : ∀ n, AEStronglyMeasurable (F n) (volume : Measure Real) := by
    intro n
    exact ((Complex.continuous_re.comp
      (fourierAutocorrelation g).continuous).mul
      (continuous_suzukiGammaSpectralSummand n)).aestronglyMeasurable
  have h_bound : ∀ n, ∀ᵐ t ∂(volume : Measure Real),
      ‖F n t‖ ≤ bound n t := by
    intro n
    filter_upwards with t
    have henergy :
        0 ≤ (fourierAutocorrelation g t).re :=
      fourierAutocorrelation_re_nonneg g t
    have hsummand :=
      suzukiGammaSpectralSummand_nonneg n t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg henergy hsummand)]
    calc
      (fourierAutocorrelation g t).re *
            suzukiGammaSpectralSummand n t ≤
          (fourierAutocorrelation g t).re *
            (t ^ 2 / (4 * ((n : Real) + 1 / 4) ^ 3)) :=
        mul_le_mul_of_nonneg_left
          (suzukiGammaSpectralSummand_le_inverseCube_mul_sq n t) henergy
      _ = bound n t := by
        dsimp only [bound]
        ring
  have hbound_summable : ∀ᵐ t ∂(volume : Measure Real),
      Summable (fun n => bound n t) := by
    filter_upwards with t
    exact summable_suzukiGammaInverseCubeQuarter.mul_right
      (t ^ 2 * (fourierAutocorrelation g t).re)
  have hbound_integrable :
      Integrable (fun t => ∑' n, bound n t) (volume : Measure Real) := by
    have hscaled :=
      (integrable_sq_mul_fourierAutocorrelation_re g).const_mul
        (∑' n : Nat, 1 / (4 * ((n : Real) + 1 / 4) ^ 3))
    simpa only [bound, tsum_mul_right] using hscaled
  have h_lim : ∀ᵐ t ∂(volume : Measure Real),
      HasSum (fun n => F n t)
        ((fourierAutocorrelation g t).re *
          ∑' n : Nat, suzukiGammaSpectralSummand n t) := by
    filter_upwards with t
    exact (summable_suzukiGammaSpectralSummand t).hasSum.mul_left
      (fourierAutocorrelation g t).re
  have hinterchange := hasSum_integral_of_dominated_convergence
    (μ := (volume : Measure Real)) bound hF_meas h_bound hbound_summable
      hbound_integrable h_lim
  simpa only [F, g] using hinterchange.tsum_eq.symm

theorem integrable_fourierAutocorrelation_re_mul_suzukiGammaSpectralSeries
    (v : SchwartzLineTestFunction) :
    Integrable (fun t : Real =>
      (fourierAutocorrelation (suzukiProjectBase v) t).re *
        ∑' n : Nat, suzukiGammaSpectralSummand n t) := by
  let g : SchwartzLineTestFunction := suzukiProjectBase v
  let C : Real :=
    ∑' n : Nat, 1 / (4 * ((n : Real) + 1 / 4) ^ 3)
  have hseries_meas :
      Measurable (fun t : Real =>
        ∑' n : Nat, suzukiGammaSpectralSummand n t) :=
    Measurable.tsum (fun n =>
      (continuous_suzukiGammaSpectralSummand n).measurable)
  have henergy_meas :
      Measurable (fun t : Real => (fourierAutocorrelation g t).re) :=
    (Complex.continuous_re.comp
      (fourierAutocorrelation g).continuous).measurable
  have hmajorant :=
    (integrable_sq_mul_fourierAutocorrelation_re g).const_mul C
  apply hmajorant.mono_nonneg
    (henergy_meas.mul hseries_meas).aestronglyMeasurable
  · filter_upwards with t
    exact mul_nonneg (fourierAutocorrelation_re_nonneg g t)
      (tsum_nonneg (fun n => suzukiGammaSpectralSummand_nonneg n t))
  · filter_upwards with t
    have hmajorSummable :
        Summable (fun n : Nat =>
          t ^ 2 / (4 * ((n : Real) + 1 / 4) ^ 3)) := by
      have h := summable_suzukiGammaInverseCubeQuarter.mul_right (t ^ 2)
      apply h.congr
      intro n
      ring
    have hsum_le :=
      (summable_suzukiGammaSpectralSummand t).tsum_le_tsum
        (fun n => suzukiGammaSpectralSummand_le_inverseCube_mul_sq n t)
        hmajorSummable
    have hsum_major :
        (∑' n : Nat, t ^ 2 / (4 * ((n : Real) + 1 / 4) ^ 3)) =
          C * t ^ 2 := by
      calc
        (∑' n : Nat, t ^ 2 / (4 * ((n : Real) + 1 / 4) ^ 3)) =
            ∑' n : Nat,
              (1 / (4 * ((n : Real) + 1 / 4) ^ 3)) * t ^ 2 := by
          apply tsum_congr
          intro n
          ring
        _ = C * t ^ 2 := by
          exact tsum_mul_right
    calc
      (fourierAutocorrelation g t).re *
            (∑' n : Nat, suzukiGammaSpectralSummand n t) ≤
          (fourierAutocorrelation g t).re *
            (∑' n : Nat,
              t ^ 2 / (4 * ((n : Real) + 1 / 4) ^ 3)) :=
        mul_le_mul_of_nonneg_left hsum_le
          (fourierAutocorrelation_re_nonneg g t)
      _ = C * (t ^ 2 * (fourierAutocorrelation g t).re) := by
        rw [hsum_major]
        ring

/-- Exact real quarter-line digamma expansion in the spectral variables
that occur in the project Gamma side.  This is a sign-free identity; no
positivity or interchange of the series with the formula integral is used. -/
theorem digamma_quarterLine_re_eq_suzukiGammaSpectralSeries (t : Real) :
    (Complex.digamma
        ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I)).re =
      (Complex.digamma (1 / 4 : Complex)).re +
        ∑' n : Nat, suzukiGammaSpectralSummand n t := by
  have hcomplex := digamma_quarterLine_sub_eq_tsum t
  have hz :
      0 < (((1 / 4 : Complex) +
        (t / 2 : Real) * Complex.I)).re := by simp
  have hz₀ : 0 < ((1 / 4 : Complex)).re := by simp
  have hsum :=
    (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz).sub
      (ComplexCompactExhaustion.summable_gaussDigammaSeriesTerm hz₀)
  have hre := congrArg Complex.re hcomplex
  rw [Complex.sub_re, Complex.re_tsum hsum] at hre
  rw [show (∑' n : Nat,
      (ComplexCompactExhaustion.gaussDigammaSeriesTerm
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I) n -
        ComplexCompactExhaustion.gaussDigammaSeriesTerm
          (1 / 4 : Complex) n).re) =
      ∑' n : Nat, suzukiGammaSpectralSummand n t by
        apply tsum_congr
        intro n
        exact re_gaussDigammaSeriesTerm_quarterLine_sub n t] at hre
  linarith

/-- The Archimedean spectral weight is the base-point constant plus the
summable rational series that the Suzuki Lerch kernel must reproduce. -/
theorem neg_log_pi_add_digamma_quarterLine_re_eq_suzukiGammaSeries
    (t : Real) :
    -Real.log Real.pi +
        (Complex.digamma
          ((1 / 4 : Complex) + (t / 2 : Real) * Complex.I)).re =
      ((Complex.digamma (1 / 4 : Complex)).re - Real.log Real.pi) +
        ∑' n : Nat, suzukiGammaSpectralSummand n t := by
  rw [digamma_quarterLine_re_eq_suzukiGammaSpectralSeries]
  ring

/-- The complete project Gamma side on the scaled Suzuki base, rewritten as
one integral of the exact base-point constant plus the summable rational
quarter-line series.  The series remains inside the integral here; exchanging
it with the integral is the next X14 obligation. -/
theorem guinandWeilLiteratureGammaSide_suzukiProjectBase_eq_seriesIntegral
    (v : SchwartzLineTestFunction) :
    guinandWeilLiteratureGammaSide
        (fourierAutocorrelation (suzukiProjectBase v)) =
      (1 / (2 * Real.pi)) *
        ∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re *
            (((Complex.digamma (1 / 4 : Complex)).re -
                Real.log Real.pi) +
              ∑' n : Nat, suzukiGammaSpectralSummand n t) := by
  rw [guinandWeilLiteratureGammaSide_eq_digammaIntegral]
  have hintegral :
      (∫ t : Real,
          ((fourierAutocorrelation (suzukiProjectBase v) t) *
            (-(Real.log Real.pi : Complex) / 2 +
              Complex.digamma
                ((1 / 4 : Complex) +
                  (t / 2 : Real) * Complex.I) / 2)).re) =
        (1 / 2 : Real) *
          ∫ t : Real,
            (fourierAutocorrelation (suzukiProjectBase v) t).re *
              (((Complex.digamma (1 / 4 : Complex)).re -
                  Real.log Real.pi) +
                ∑' n : Nat, suzukiGammaSpectralSummand n t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    have hreal :
        fourierAutocorrelation (suzukiProjectBase v) t =
          ((fourierAutocorrelation (suzukiProjectBase v) t).re : Complex) := by
      rw [fourierAutocorrelation_apply, Complex.mul_conj]
      simp
    rw [hreal]
    norm_num [Complex.mul_re, Complex.div_re]
    rw [show
      (1 / 4 : Complex) + (t : Complex) / 2 * Complex.I =
        (1 / 4 : Complex) + (t / 2 : Real) * Complex.I by
          push_cast
          ring]
    rw [digamma_quarterLine_re_eq_suzukiGammaSpectralSeries]
    ring
  rw [hintegral]
  field_simp [Real.pi_ne_zero]

/-- The full completed-zeta Gamma side is exactly the compact pairing of the
Archimedean absolute-value and Lerch screw kernel. -/
theorem guinandWeilLiteratureGammaSide_suzukiProjectBase_eq_kernelPairing
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    guinandWeilLiteratureGammaSide
        (fourierAutocorrelation (suzukiProjectBase v)) =
      suzukiFiniteKernelPairing suzukiGammaScrewKernel a
        (SchwartzMap.derivCLM Complex Complex v) := by
  let u : Real → Complex :=
    SchwartzMap.derivCLM Complex Complex v
  have hu : Continuous u :=
    (SchwartzMap.derivCLM Complex Complex v).continuous
  have hbase_integrable :
      Integrable (fun t : Real =>
        (fourierAutocorrelation (suzukiProjectBase v) t).re *
          suzukiGammaBaseCoefficient) := by
    exact ((fourierAutocorrelation
      (suzukiProjectBase v)).integrable.re).mul_const _
  have hseries_integrable :=
    integrable_fourierAutocorrelation_re_mul_suzukiGammaSpectralSeries v
  have hphysical :=
    hasSum_suzukiFiniteKernelPairingComplex_gammaLerch a hu
  have hseries :
      (1 / (2 * Real.pi)) *
          ∫ t : Real,
            (fourierAutocorrelation (suzukiProjectBase v) t).re *
              (∑' n : Nat, suzukiGammaSpectralSummand n t) =
        (suzukiFiniteKernelPairingComplex
          (fun x => -(1 / 4) * suzukiLerchDifference x) a u).re := by
    calc
      (1 / (2 * Real.pi)) *
            ∫ t : Real,
              (fourierAutocorrelation (suzukiProjectBase v) t).re *
                (∑' n : Nat, suzukiGammaSpectralSummand n t) =
          (1 / (2 * Real.pi)) *
            (∑' n : Nat,
              ∫ t : Real,
                (fourierAutocorrelation (suzukiProjectBase v) t).re *
                  suzukiGammaSpectralSummand n t) := by
        rw [integral_tsum_suzukiGammaSpectralSummand v]
      _ = ∑' n : Nat,
          (1 / (2 * Real.pi)) *
            ∫ t : Real,
              (fourierAutocorrelation (suzukiProjectBase v) t).re *
                suzukiGammaSpectralSummand n t := by
        rw [tsum_mul_left]
      _ = ∑' n : Nat,
          (suzukiFiniteKernelPairingComplex
            (suzukiGammaLerchKernelSummand n) a u).re := by
        apply tsum_congr
        intro n
        exact one_div_twoPi_integral_suzukiGammaSpectralSummand_re_eq_lerchPairing
          ha hsupport n
      _ = (∑' n : Nat,
          suzukiFiniteKernelPairingComplex
            (suzukiGammaLerchKernelSummand n) a u).re :=
        (Complex.re_tsum hphysical.summable).symm
      _ = (suzukiFiniteKernelPairingComplex
          (fun x => -(1 / 4) * suzukiLerchDifference x) a u).re := by
        exact congrArg Complex.re
          (tsum_suzukiFiniteKernelPairingComplex_gammaLerch_eq_difference
            a hu)
  have hkernel :
      suzukiGammaScrewKernel = fun x =>
        suzukiGammaBaseKernel x +
          (-(1 / 4)) * suzukiLerchDifference x := by
    funext x
    unfold suzukiGammaScrewKernel
    ring
  have hpair :
      suzukiFiniteKernelPairingComplex suzukiGammaScrewKernel a u =
        suzukiFiniteKernelPairingComplex suzukiGammaBaseKernel a u +
          suzukiFiniteKernelPairingComplex
            (fun x => -(1 / 4) * suzukiLerchDifference x) a u := by
    rw [hkernel]
    exact suzukiFiniteKernelPairingComplex_add
      continuous_suzukiGammaBaseKernel
      (continuous_const.mul continuous_suzukiLerchDifference) hu
  rw [guinandWeilLiteratureGammaSide_suzukiProjectBase_eq_seriesIntegral]
  change
    (1 / (2 * Real.pi)) *
        ∫ t : Real,
          (fourierAutocorrelation (suzukiProjectBase v) t).re *
            (suzukiGammaBaseCoefficient +
              ∑' n : Nat, suzukiGammaSpectralSummand n t) = _
  calc
    (1 / (2 * Real.pi)) *
          ∫ t : Real,
            (fourierAutocorrelation (suzukiProjectBase v) t).re *
              (suzukiGammaBaseCoefficient +
                ∑' n : Nat, suzukiGammaSpectralSummand n t) =
        (1 / (2 * Real.pi)) *
          ((∫ t : Real,
              (fourierAutocorrelation (suzukiProjectBase v) t).re *
                suzukiGammaBaseCoefficient) +
            ∫ t : Real,
              (fourierAutocorrelation (suzukiProjectBase v) t).re *
                (∑' n : Nat, suzukiGammaSpectralSummand n t)) := by
      congr 1
      rw [← integral_add hbase_integrable hseries_integrable]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = (1 / (2 * Real.pi)) *
          (∫ t : Real,
            (fourierAutocorrelation (suzukiProjectBase v) t).re *
              suzukiGammaBaseCoefficient) +
        (1 / (2 * Real.pi)) *
          (∫ t : Real,
            (fourierAutocorrelation (suzukiProjectBase v) t).re *
              (∑' n : Nat, suzukiGammaSpectralSummand n t)) := by
      ring
    _ = (suzukiFiniteKernelPairingComplex
          suzukiGammaBaseKernel a u).re +
        (suzukiFiniteKernelPairingComplex
          (fun x => -(1 / 4) * suzukiLerchDifference x) a u).re := by
      rw [one_div_twoPi_integral_gammaBase_eq_pairing ha hsupport,
        hseries]
    _ = (suzukiFiniteKernelPairingComplex suzukiGammaScrewKernel a u).re := by
      rw [hpair, Complex.add_re]
    _ = suzukiFiniteKernelPairing suzukiGammaScrewKernel a u := by
      rfl

/-- The displayed Suzuki screw function is the sum of the three physical
kernels matching the literature-normalized prime, pole, and Gamma sides. -/
theorem suzukiScrewFunction_eq_componentKernels :
    suzukiScrewFunction = fun t =>
      suzukiPrimeScrewTerm t + suzukiPoleScrewKernel t +
        suzukiGammaScrewKernel t := by
  funext t
  unfold suzukiScrewFunction suzukiPoleScrewKernel
    suzukiGammaScrewKernel suzukiGammaBaseKernel
    suzukiGammaBaseCoefficient
  rw [suzukiLerchDifference_eq_sourceFormula]
  ring

/-- X14 endpoint: every compactly supported source test satisfies the exact
Suzuki scalar-kernel identity, with no sign or positivity assertion. -/
theorem suzukiScalarKernelIdentityAt_of_support
    {a : Real} {v : SchwartzLineTestFunction} (ha : 0 < a)
    (hsupport : Function.support v ⊆ Set.Icc (-a) a) :
    SuzukiScalarKernelIdentityAt a v := by
  let u : Real → Complex :=
    SchwartzMap.derivCLM Complex Complex v
  have hu : Continuous u :=
    (SchwartzMap.derivCLM Complex Complex v).continuous
  have hpole : Continuous suzukiPoleScrewKernel := by
    unfold suzukiPoleScrewKernel
    fun_prop
  have hprimePole : Continuous (fun t =>
      suzukiPrimeScrewTerm t + suzukiPoleScrewKernel t) :=
    continuous_suzukiPrimeScrewTerm.add hpole
  have hpair :
      suzukiFiniteKernelPairingComplex suzukiScrewFunction a u =
        suzukiFiniteKernelPairingComplex suzukiPrimeScrewTerm a u +
          suzukiFiniteKernelPairingComplex suzukiPoleScrewKernel a u +
            suzukiFiniteKernelPairingComplex suzukiGammaScrewKernel a u := by
    rw [suzukiScrewFunction_eq_componentKernels]
    rw [suzukiFiniteKernelPairingComplex_add
      hprimePole continuous_suzukiGammaScrewKernel hu]
    rw [suzukiFiniteKernelPairingComplex_add
      continuous_suzukiPrimeScrewTerm hpole hu]
  unfold SuzukiScalarKernelIdentityAt
  unfold guinandWeilBurnolLiteratureResidualSide
  rw [guinandWeilLiteraturePrimeSide_suzukiProjectBase_eq_kernelPairing
      ha hsupport,
    guinandWeilBurnolLiteraturePoleSide_suzukiProjectBase_eq_kernelPairing
      ha hsupport,
    guinandWeilLiteratureGammaSide_suzukiProjectBase_eq_kernelPairing
      ha hsupport]
  unfold suzukiFiniteKernelPairing
  rw [hpair, Complex.add_re, Complex.add_re]

end

end M100
end Experiments
end RiemannHypothesisProject
