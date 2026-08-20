import RiemannHypothesisProject.Experiments.M100.SuzukiEquation25RegularKernelReduction

/-!
# Finite Gamma cancellation for Suzuki's equation (2.5)

This module isolates the termwise Fourier cancellation behind the remaining
regular-kernel identity.  For each quarter-line Gamma mode, the multiplier of
the Lerch pairing on `v'` plus the multiplier of the corresponding raw
exponential `r1''` summand is the constant `1 / (n + 1/4)`.

The infinite renormalized limit is not taken here.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open SchwartzLineTestFunction
open scoped BigOperators FourierTransform

/-- The Fourier multiplier of the normalized physical exponential kernel in
the `n`th quarter-line Gamma mode. -/
def suzukiEquation25GammaRationalMultiplier (n : Nat) (xi : Real) : Real :=
  1 / (((n : Real) + 1 / 4) *
    (4 * ((n : Real) + 1 / 4) ^ 2 + (2 * Real.pi * xi) ^ 2))

/-- The raw exponential summand occurring before subtraction of the
reciprocal singular kernel in `r1''`. -/
def suzukiEquation25RawGammaExponentialKernel
    (n : Nat) (x : Real) : Real :=
  Real.exp (-(2 * (n : Real) + 1 / 2) * |x|)

theorem fourier_suzukiGammaExponentialKernel_eq_equation25Multiplier
    (n : Nat) (xi : Real) :
    (𝓕 (fun x : Real =>
      (suzukiGammaExponentialKernel n x : Complex))) xi =
      (suzukiEquation25GammaRationalMultiplier n xi : Complex) := by
  simpa only [suzukiEquation25GammaRationalMultiplier] using
    fourier_suzukiGammaExponentialKernel n xi

theorem suzukiEquation25RawGammaExponentialKernel_eq_scaled
    (n : Nat) (x : Real) :
    suzukiEquation25RawGammaExponentialKernel n x =
      4 * ((n : Real) + 1 / 4) ^ 2 *
        suzukiGammaExponentialKernel n x := by
  unfold suzukiEquation25RawGammaExponentialKernel
    suzukiGammaExponentialKernel
  have hd : ((n : Real) + 1 / 4) ≠ 0 := by positivity
  have hexponent :
      -(2 * (n : Real) + 1 / 2) * |x| =
        -2 * ((n : Real) + 1 / 4) * |x| := by ring
  rw [hexponent]
  field_simp [hd]

/-- The derivative multiplier and the raw exponential multiplier cancel to
the cusp mass of one quarter-line Gamma mode. -/
theorem suzukiEquation25GammaRationalMultiplier_cancellation
    (n : Nat) (xi : Real) :
    (2 * Real.pi * xi) ^ 2 *
          suzukiEquation25GammaRationalMultiplier n xi +
        4 * ((n : Real) + 1 / 4) ^ 2 *
          suzukiEquation25GammaRationalMultiplier n xi =
      1 / ((n : Real) + 1 / 4) := by
  unfold suzukiEquation25GammaRationalMultiplier
  have hd : ((n : Real) + 1 / 4) ≠ 0 := by positivity
  have hden :
      4 * ((n : Real) + 1 / 4) ^ 2 +
          (2 * Real.pi * xi) ^ 2 ≠ 0 := by positivity
  field_simp [hd, hden]
  ring

/-- The pointwise cancellation acts on the actual Fourier autocorrelation:
the derivative supplies the quadratic frequency factor. -/
theorem suzukiEquation25GammaFourierMode_cancellation
    (n : Nat) (xi : Real) (v : SchwartzLineTestFunction) :
    (suzukiEquation25GammaRationalMultiplier n xi : Complex) *
          fourierAutocorrelation
            (SchwartzMap.derivCLM Complex Complex v) xi +
        (4 * ((n : Real) + 1 / 4) ^ 2 *
          suzukiEquation25GammaRationalMultiplier n xi : Real) *
            fourierAutocorrelation v xi =
      (1 / ((n : Real) + 1 / 4) : Real) *
        fourierAutocorrelation v xi := by
  rw [fourierAutocorrelation_derivCLM_apply]
  push_cast
  have hcancel :=
    suzukiEquation25GammaRationalMultiplier_cancellation n xi
  have hcancelComplex :=
    congrArg (fun x : Real => (x : Complex)) hcancel
  push_cast at hcancelComplex
  linear_combination hcancelComplex * fourierAutocorrelation v xi

/-- The finite sum of the cancelled multipliers is exactly the shifted
harmonic cusp coefficient. -/
def suzukiEquation25ShiftedHarmonicPartial (N : Nat) : Real :=
  ∑ n ∈ Finset.range N, 1 / ((n : Real) + 1 / 4)

def suzukiEquation25CancelledGammaMultiplierPartial
    (N : Nat) (xi : Real) : Real :=
  ∑ n ∈ Finset.range N,
    ((2 * Real.pi * xi) ^ 2 *
        suzukiEquation25GammaRationalMultiplier n xi +
      4 * ((n : Real) + 1 / 4) ^ 2 *
        suzukiEquation25GammaRationalMultiplier n xi)

theorem suzukiEquation25CancelledGammaMultiplierPartial_eq
    (N : Nat) (xi : Real) :
    suzukiEquation25CancelledGammaMultiplierPartial N xi =
      suzukiEquation25ShiftedHarmonicPartial N := by
  unfold suzukiEquation25CancelledGammaMultiplierPartial
    suzukiEquation25ShiftedHarmonicPartial
  apply Finset.sum_congr rfl
  intro n _hn
  exact suzukiEquation25GammaRationalMultiplier_cancellation n xi

/-- After multiplication by the Fourier autocorrelation of the smooth core,
the same cancellation is the constant shifted-harmonic mass multiplier. -/
theorem suzukiEquation25CancelledGammaMultiplierPartial_mul_fourierAutocorrelation
    (N : Nat) (xi : Real) (v : SchwartzLineTestFunction) :
    (suzukiEquation25CancelledGammaMultiplierPartial N xi : Complex) *
        fourierAutocorrelation v xi =
      (suzukiEquation25ShiftedHarmonicPartial N : Complex) *
        fourierAutocorrelation v xi := by
  rw [suzukiEquation25CancelledGammaMultiplierPartial_eq]

end

end M100
end Experiments
end RiemannHypothesisProject
