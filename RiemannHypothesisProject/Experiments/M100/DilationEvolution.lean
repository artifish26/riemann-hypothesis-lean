import RiemannHypothesisProject.WeilPositivity.BurnolFormulaBridge
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# M100-X11 Burnol dilation and residual evolution

This experimental module fixes the `L2`-normalized additive dilation

`D_a g(x) = exp(a / 2) * g(exp(a) * x)`.

The action shrinks an already compact support as `a` increases, but its
invertibility also shows that no finite parameter can turn noncompact support
into Burnol compact support.  The results below are sign-free; no monotonicity
or positivity assertion is made.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open MeasureTheory
open SchwartzLineTestFunction
open scoped ComplexConjugate FourierTransform

noncomputable section

/-- Multiplication by `exp a` as a continuous real-linear equivalence. -/
def burnolExpScaleEquiv (a : Real) : Real ≃L[Real] Real :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (Real.exp a) (Real.exp_ne_zero a))

@[simp]
theorem burnolExpScaleEquiv_apply (a x : Real) :
    burnolExpScaleEquiv a x = Real.exp a * x := by
  rfl

/-- The `L2`-normalized additive dilation used in X11. -/
def burnolDilation (a : Real)
    (g : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  (Real.exp (a / 2) : Complex) •
    SchwartzMap.compCLMOfContinuousLinearEquiv Complex
      (burnolExpScaleEquiv a) g

@[simp]
theorem burnolDilation_apply (a x : Real) (g : SchwartzLineTestFunction) :
    burnolDilation a g x =
      (Real.exp (a / 2) : Complex) * g (Real.exp a * x) := by
  rfl

@[simp]
theorem burnolDilation_zero (g : SchwartzLineTestFunction) :
    burnolDilation 0 g = g := by
  ext x
  simp [burnolDilation_apply]

/-- The normalized dilations form an additive semigroup action. -/
theorem burnolDilation_add (a b : Real) (g : SchwartzLineTestFunction) :
    burnolDilation (a + b) g = burnolDilation a (burnolDilation b g) := by
  ext x
  simp only [burnolDilation_apply]
  have hscale : (Real.exp ((a + b) / 2) : Complex) =
      (Real.exp (a / 2) : Complex) * (Real.exp (b / 2) : Complex) := by
    norm_cast
    rw [show (a + b) / 2 = a / 2 + b / 2 by ring, Real.exp_add]
  have harg : Real.exp (a + b) * x =
      Real.exp b * (Real.exp a * x) := by
    rw [Real.exp_add]
    ring
  rw [hscale, harg]
  ring

/-- Fourier scaling for the `L2`-normalized dilation. -/
theorem fourier_burnolDilation_apply
    (a t : Real) (g : SchwartzLineTestFunction) :
    (𝓕 (burnolDilation a g)) t =
      (Real.exp (-a / 2) : Complex) *
        (𝓕 g) (Real.exp (-a) * t) := by
  let s : Real := Real.exp a
  have hs : 0 < s := Real.exp_pos a
  have hs0 : s ≠ 0 := hs.ne'
  have hscale := Measure.integral_comp_mul_left
    (g := fun y : Real =>
      Complex.exp (((-2 * Real.pi * y * (Real.exp (-a) * t) : Real) :
        Complex) * Complex.I) * g y) s
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, burnolDilation_apply]
  calc
    _ =
        (Real.exp (a / 2) : Complex) *
          ∫ x : Real,
            Complex.exp (((-2 * Real.pi * x * t : Real) : Complex) *
              Complex.I) * g (s * x) := by
          rw [← MeasureTheory.integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          simp only [s]
          ring
    _ = (Real.exp (a / 2) : Complex) *
          ((s⁻¹ : Real) •
            ∫ y : Real,
              Complex.exp (((-2 * Real.pi * y * (Real.exp (-a) * t) : Real) :
                Complex) * Complex.I) * g y) := by
          congr 1
          rw [← abs_of_pos (inv_pos.mpr hs)]
          rw [← hscale]
          apply integral_congr_ae
          filter_upwards with x
          apply congrArg (fun z : Complex => z * g (s * x))
          apply congrArg Complex.exp
          push_cast
          simp only [s]
          rw [Complex.exp_neg]
          field_simp [Complex.exp_ne_zero]
          rw [Complex.ofReal_exp]
    _ = (Real.exp (-a / 2) : Complex) *
          ∫ y : Real,
            Complex.exp (((-2 * Real.pi * y * (Real.exp (-a) * t) : Real) :
              Complex) * Complex.I) * g y := by
          simp only [s, Complex.real_smul]
          rw [← mul_assoc]
          congr 1
          norm_cast
          rw [show -a / 2 = a / 2 - a by ring, Real.exp_sub]
          simp only [div_eq_mul_inv]

/-- The Fourier energy density rescales without changing total `L2` mass. -/
theorem fourierEnergyDensity_burnolDilation
    (a t : Real) (g : SchwartzLineTestFunction) :
    fourierEnergyDensity (burnolDilation a g) t =
      Real.exp (-a) *
        fourierEnergyDensity g (Real.exp (-a) * t) := by
  rw [fourierEnergyDensity, fourier_burnolDilation_apply,
    fourierEnergyDensity, Complex.normSq_mul]
  rw [Complex.normSq_ofReal]
  have hexp : Real.exp (-a / 2) * Real.exp (-a / 2) = Real.exp (-a) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- The formula-facing Fourier autocorrelation has the inverse dilation law. -/
theorem fourierAutocorrelation_burnolDilation_apply
    (a t : Real) (g : SchwartzLineTestFunction) :
    fourierAutocorrelation (burnolDilation a g) t =
      (Real.exp (-a) : Complex) *
        fourierAutocorrelation g (Real.exp (-a) * t) := by
  rw [fourierAutocorrelation_apply, fourier_burnolDilation_apply,
    fourierAutocorrelation_apply]
  simp only [map_mul, Complex.conj_ofReal]
  have hexp : (Real.exp (-a / 2) : Complex) *
      (Real.exp (-a / 2) : Complex) = (Real.exp (-a) : Complex) := by
    norm_cast
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

/-- Physical autocorrelation is transported by the direct spatial scale; the
`L2` normalization cancels the Jacobian. -/
theorem autocorrelation_burnolDilation
    (a : Real) (g : SchwartzLineTestFunction) :
    autocorrelation (burnolDilation a g) =
      (Real.exp (-a / 2) : Complex) •
        burnolDilation a (autocorrelation g) := by
  apply (FourierTransform.fourierCLE Complex SchwartzLineTestFunction).injective
  ext t
  change fourierAutocorrelation (burnolDilation a g) t = _
  rw [map_smul]
  change
    fourierAutocorrelation (burnolDilation a g) t =
      (Real.exp (-a / 2) : Complex) *
        (𝓕 (burnolDilation a (autocorrelation g))) t
  rw [fourierAutocorrelation_burnolDilation_apply,
    fourier_burnolDilation_apply]
  change
    (Real.exp (-a) : Complex) *
        fourierAutocorrelation g (Real.exp (-a) * t) =
      (Real.exp (-a / 2) : Complex) *
        ((Real.exp (-a / 2) : Complex) *
          fourierAutocorrelation g (Real.exp (-a) * t))
  have hexp : (Real.exp (-a / 2) : Complex) *
      (Real.exp (-a / 2) : Complex) = (Real.exp (-a) : Complex) := by
    norm_cast
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

theorem autocorrelation_burnolDilation_apply
    (a x : Real) (g : SchwartzLineTestFunction) :
    autocorrelation (burnolDilation a g) x =
      autocorrelation g (Real.exp a * x) := by
  rw [autocorrelation_burnolDilation, smul_apply, burnolDilation_apply]
  have hexp : (Real.exp (-a / 2) : Complex) *
      (Real.exp (a / 2) : Complex) = 1 := by
    norm_cast
    rw [← Real.exp_add]
    rw [show -a / 2 + a / 2 = 0 by ring, Real.exp_zero]
  simp only [smul_eq_mul]
  rw [← mul_assoc, hexp, one_mul]

/-- The entire Fourier-Laplace source has the same inverse scaling law. This
makes the direct pole evaluations move from `±i/2` to `±i*exp(-a)/2`. -/
theorem burnolFourierLaplaceSource_burnolDilation
    (a : Real) (g : SchwartzLineTestFunction) (z : Complex) :
    burnolFourierLaplaceSource (burnolDilation a g) z =
      (Real.exp (-a) : Complex) *
        burnolFourierLaplaceSource g ((Real.exp (-a) : Complex) * z) := by
  let s : Real := Real.exp a
  have hs : 0 < s := Real.exp_pos a
  have hscale := Measure.integral_comp_mul_left
    (g := fun y : Real =>
      Complex.exp (((-2 * Real.pi * y : Real) : Complex) * Complex.I *
        ((Real.exp (-a) : Complex) * z)) * autocorrelation g y) s
  unfold burnolFourierLaplaceSource
  simp_rw [autocorrelation_burnolDilation_apply]
  calc
    (∫ x : Real,
        Complex.exp (((-2 * Real.pi * x : Real) : Complex) * Complex.I * z) *
          autocorrelation g (Real.exp a * x)) =
        ∫ x : Real,
          (Complex.exp (((-2 * Real.pi * (s * x) : Real) : Complex) *
              Complex.I * ((Real.exp (-a) : Complex) * z)) *
            autocorrelation g (s * x)) := by
          apply integral_congr_ae
          filter_upwards with x
          congr 2
          simp only [s]
          push_cast
          rw [Complex.exp_neg]
          field_simp [Complex.exp_ne_zero]
    _ = (s⁻¹ : Real) •
          ∫ y : Real,
            Complex.exp (((-2 * Real.pi * y : Real) : Complex) * Complex.I *
              ((Real.exp (-a) : Complex) * z)) * autocorrelation g y := by
          rw [← abs_of_pos (inv_pos.mpr hs)]
          exact hscale
    _ = (Real.exp (-a) : Complex) *
          ∫ y : Real,
            Complex.exp (((-2 * Real.pi * y : Real) : Complex) * Complex.I *
              ((Real.exp (-a) : Complex) * z)) * autocorrelation g y := by
          rw [Real.exp_neg]
          rfl

/-- Applying Fourier transform once more shows that every prime sample moves
from `x` to `exp(a) * x`. -/
theorem fourier_fourierAutocorrelation_burnolDilation_apply
    (a x : Real) (g : SchwartzLineTestFunction) :
    (SchwartzLineTestFunction.fourier
        (fourierAutocorrelation (burnolDilation a g))) x =
      (SchwartzLineTestFunction.fourier (fourierAutocorrelation g))
        (Real.exp a * x) := by
  change
    (𝓕 (fourierAutocorrelation (burnolDilation a g))) x =
      (𝓕 (fourierAutocorrelation g)) (Real.exp a * x)
  rw [fourier_fourierAutocorrelation_apply,
    fourier_fourierAutocorrelation_apply,
    autocorrelation_burnolDilation_apply]
  congr 2
  ring

/-- One explicitly rescaled prime-power contribution along the dilation. -/
def burnolDilationPrimeTerm
    (a : Real) (g : SchwartzLineTestFunction) (n : Nat) : Real :=
  - (1 / (2 * Real.pi)) *
    (ArithmeticFunction.vonMangoldt n / Real.sqrt (n : Real)) *
      (((SchwartzLineTestFunction.fourier (fourierAutocorrelation g))
          (Real.exp a * (Real.log (n : Real) / (2 * Real.pi)))).re +
        ((SchwartzLineTestFunction.fourier (fourierAutocorrelation g))
          (Real.exp a * (-Real.log (n : Real) / (2 * Real.pi)))).re)

/-- The production prime term of the dilated test is exactly the rescaled
prime sample above. -/
theorem guinandWeilLiteraturePrimeTerm_burnolDilation
    (a : Real) (g : SchwartzLineTestFunction) (n : Nat) :
    guinandWeilLiteraturePrimeTerm
        (fourierAutocorrelation (burnolDilation a g)) n =
      burnolDilationPrimeTerm a g n := by
  unfold guinandWeilLiteraturePrimeTerm burnolDilationPrimeTerm
  rw [fourier_fourierAutocorrelation_burnolDilation_apply,
    fourier_fourierAutocorrelation_burnolDilation_apply]

/-- The complete prime side keeps every von-Mangoldt atom visible under the
dilation. -/
theorem guinandWeilLiteraturePrimeSide_burnolDilation
    (a : Real) (g : SchwartzLineTestFunction) :
    guinandWeilLiteraturePrimeSide
        (fourierAutocorrelation (burnolDilation a g)) =
      ∑' n : Nat, burnolDilationPrimeTerm a g n := by
  unfold guinandWeilLiteraturePrimeSide
  apply tsum_congr
  exact guinandWeilLiteraturePrimeTerm_burnolDilation a g

/-- The Archimedean side with the formula test's inverse dilation displayed
inside the production Gamma integral. -/
def burnolDilationGammaSide
    (a : Real) (g : SchwartzLineTestFunction) : Real :=
  (1 / Real.pi) *
    ∫ t : Real,
      (((Real.exp (-a) : Complex) *
          fourierAutocorrelation g (Real.exp (-a) * t)) *
        guinandWeilGammaLogDerivative t).re ∂volume

theorem guinandWeilLiteratureGammaSide_burnolDilation
    (a : Real) (g : SchwartzLineTestFunction) :
    guinandWeilLiteratureGammaSide
        (fourierAutocorrelation (burnolDilation a g)) =
      burnolDilationGammaSide a g := by
  unfold guinandWeilLiteratureGammaSide burnolDilationGammaSide
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [fourierAutocorrelation_burnolDilation_apply]

/-- The actual project-normalized direct residual with every transformed
prime, pole, and Gamma contribution exposed. -/
def burnolDilationResidualExpression
    (a : Real) (g : SchwartzLineTestFunction) : Real :=
  (∑' n : Nat, burnolDilationPrimeTerm a g n) +
    ((Real.exp (-a) : Complex) *
        burnolFourierLaplaceSource g
          ((Real.exp (-a) : Complex) * (Complex.I / 2)) +
      (Real.exp (-a) : Complex) *
        burnolFourierLaplaceSource g
          ((Real.exp (-a) : Complex) * (-Complex.I / 2))).re +
      burnolDilationGammaSide a g

/-- Exact finite-parameter evolution identity for the actual direct residual.
No local-integrand replacement or positivity statement is used. -/
theorem guinandWeilBurnolLiteratureResidualSide_burnolDilation
    (a : Real) (g : SchwartzLineTestFunction) :
    guinandWeilBurnolLiteratureResidualSide (burnolDilation a g) =
      burnolDilationResidualExpression a g := by
  unfold guinandWeilBurnolLiteratureResidualSide
  unfold guinandWeilBurnolLiteraturePoleSide
  unfold burnolDilationResidualExpression
  rw [guinandWeilLiteraturePrimeSide_burnolDilation,
    guinandWeilLiteratureGammaSide_burnolDilation,
    burnolFourierLaplaceSource_burnolDilation,
    burnolFourierLaplaceSource_burnolDilation]

/-- The exact two-parameter residual difference, before any derivative or
monotonicity proposal. -/
theorem guinandWeilBurnolLiteratureResidualSide_burnolDilation_sub
    (a b : Real) (g : SchwartzLineTestFunction) :
    guinandWeilBurnolLiteratureResidualSide (burnolDilation b g) -
        guinandWeilBurnolLiteratureResidualSide (burnolDilation a g) =
      burnolDilationResidualExpression b g -
        burnolDilationResidualExpression a g := by
  rw [guinandWeilBurnolLiteratureResidualSide_burnolDilation,
    guinandWeilBurnolLiteratureResidualSide_burnolDilation]

/-- Exact membership in the support of a finite dilation. -/
theorem mem_support_burnolDilation_iff
    (a x : Real) (g : SchwartzLineTestFunction) :
    x ∈ Function.support (burnolDilation a g) ↔
      Real.exp a * x ∈ Function.support g := by
  simp only [Function.mem_support, burnolDilation_apply]
  rw [mul_ne_zero_iff_left]
  exact_mod_cast Real.exp_ne_zero (a / 2)

/-- Dilation transports an interval support to the inversely scaled interval. -/
theorem support_burnolDilation_subset_Icc
    {a r : Real} {g : SchwartzLineTestFunction}
    (hsupport : Function.support g ⊆ Set.Icc (-r) r) :
    Function.support (burnolDilation a g) ⊆
      Set.Icc (-r / Real.exp a) (r / Real.exp a) := by
  intro x hx
  have hscaled := hsupport ((mem_support_burnolDilation_iff a x g).mp hx)
  constructor
  · apply (div_le_iff₀ (Real.exp_pos a)).2
    simpa [mul_comm] using hscaled.1
  · apply (le_div_iff₀ (Real.exp_pos a)).2
    simpa [mul_comm] using hscaled.2

/-- A finite dilation has compact interval support only if the original test
already had compact interval support. -/
theorem support_subset_Icc_of_burnolDilation_support_subset_Icc
    {a r : Real} {g : SchwartzLineTestFunction}
    (hsupport : Function.support (burnolDilation a g) ⊆ Set.Icc (-r) r) :
    Function.support g ⊆
      Set.Icc (-r * Real.exp a) (r * Real.exp a) := by
  intro x hx
  have hxscaled : x / Real.exp a ∈
      Function.support (burnolDilation a g) := by
    rw [mem_support_burnolDilation_iff]
    field_simp [Real.exp_ne_zero a]
    exact hx
  have hmem := hsupport hxscaled
  constructor
  · exact (le_div_iff₀ (Real.exp_pos a)).1 hmem.1
  · exact (div_le_iff₀ (Real.exp_pos a)).1 hmem.2

/-- No finite invertible dilation can move a genuinely noncompactly supported
Schwartz test into any Burnol support interval. -/
theorem no_finite_burnolDilation_compact_support
    {g : SchwartzLineTestFunction}
    (hnoncompact : ¬ ∃ r : Real,
      Function.support g ⊆ Set.Icc (-r) r) :
    ∀ a r : Real,
      ¬ Function.support (burnolDilation a g) ⊆ Set.Icc (-r) r := by
  intro a r hsupport
  apply hnoncompact
  refine ⟨r * Real.exp a, ?_⟩
  simpa [neg_mul] using
    support_subset_Icc_of_burnolDilation_support_subset_Icc hsupport

end

end M100
end Experiments
end RiemannHypothesisProject
