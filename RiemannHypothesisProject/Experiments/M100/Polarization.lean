import RiemannHypothesisProject.WeilPositivity.SchwartzFourierAutocorrelation

/-!
# M100-X01 polarization of the checked Schwartz Weil form

This experimental module polarizes the genuine M80 autocorrelation form. It
defines the two-input cross-correlation, freezes its Fourier normalization,
and proves the exact two-block expansion. No positivity hypothesis or
criterion-determining density statement appears here.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open scoped ComplexConjugate FourierTransform
open SchwartzLineTestFunction

noncomputable section

/-- The ordered two-input convolution `g * h★`. -/
def schwartzCrossCorrelation
    (g h : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  SchwartzMap.convolution (ContinuousLinearMap.mul Complex Complex) g (star h)

theorem schwartzCrossCorrelation_self (g : SchwartzLineTestFunction) :
    schwartzCrossCorrelation g g = autocorrelation g :=
  rfl

theorem schwartzCrossCorrelation_add_left
    (g₁ g₂ h : SchwartzLineTestFunction) :
    schwartzCrossCorrelation (g₁ + g₂) h =
      schwartzCrossCorrelation g₁ h + schwartzCrossCorrelation g₂ h := by
  simp [schwartzCrossCorrelation]

theorem schwartzCrossCorrelation_add_right
    (g h₁ h₂ : SchwartzLineTestFunction) :
    schwartzCrossCorrelation g (h₁ + h₂) =
      schwartzCrossCorrelation g h₁ + schwartzCrossCorrelation g h₂ := by
  simp [schwartzCrossCorrelation]

/-- Expanding the autocorrelation of a sum retains both ordered cross terms. -/
theorem autocorrelation_add_eq_crossCorrelation_sum
    (g h : SchwartzLineTestFunction) :
    autocorrelation (g + h) =
      autocorrelation g + schwartzCrossCorrelation g h +
        schwartzCrossCorrelation h g + autocorrelation h := by
  simp [autocorrelation, schwartzCrossCorrelation]
  abel

/-- The Fourier transform of the ordered cross-correlation. -/
def fourierSchwartzCrossCorrelation
    (g h : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  𝓕 (schwartzCrossCorrelation g h)

/-- Fourier normalization of `g * h★` in Mathlib's
`exp (-2*pi*i*x*xi)` convention. -/
theorem fourierSchwartzCrossCorrelation_apply
    (g h : SchwartzLineTestFunction) (t : Real) :
    fourierSchwartzCrossCorrelation g h t =
      (𝓕 g) t * conj ((𝓕 h) t) := by
  rw [fourierSchwartzCrossCorrelation, schwartzCrossCorrelation]
  change
    (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.mul Complex Complex)
      g (star h))) t = _
  rw [SchwartzMap.fourier_convolution,
    SchwartzMap.pairing_apply_apply, fourier_star_apply]
  rfl

theorem fourierSchwartzCrossCorrelation_eq_pointwiseProduct
    (g h : SchwartzLineTestFunction) :
    fourierSchwartzCrossCorrelation g h =
      pointwiseProduct (𝓕 g) (conjugate (𝓕 h)) := by
  ext t
  rw [fourierSchwartzCrossCorrelation_apply]
  simp

/-- The Fourier cross-correlation is jointly continuous in both base tests. -/
theorem continuous_fourierSchwartzCrossCorrelation :
    Continuous (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
      fourierSchwartzCrossCorrelation p.1 p.2) := by
  have hleft : Continuous
      (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        (𝓕 p.1 : SchwartzLineTestFunction)) :=
    (SchwartzMap.fourierTransformCLM Complex).continuous.comp continuous_fst
  have hright : Continuous
      (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        conjugate (𝓕 p.2 : SchwartzLineTestFunction)) :=
    conjugate.continuous.comp
      ((SchwartzMap.fourierTransformCLM Complex).continuous.comp continuous_snd)
  have hproduct := continuous_pointwiseProduct.comp (hleft.prodMk hright)
  apply hproduct.congr
  intro p
  exact (fourierSchwartzCrossCorrelation_eq_pointwiseProduct p.1 p.2).symm

/-- The ordered cross-correlation itself is jointly continuous. -/
theorem continuous_schwartzCrossCorrelation :
    Continuous (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
      schwartzCrossCorrelation p.1 p.2) := by
  have hinverse : Continuous
      (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        (𝓕⁻ (fourierSchwartzCrossCorrelation p.1 p.2) :
          SchwartzLineTestFunction)) :=
    (FourierTransform.fourierInvCLM Complex SchwartzLineTestFunction).continuous.comp
      continuous_fourierSchwartzCrossCorrelation
  apply hinverse.congr
  intro p
  simp [fourierSchwartzCrossCorrelation]

/-- The real symmetric polarization of `Q(g) = W(g * g★)`. -/
def schwartzWeilPolarizedForm
    (data : SchwartzWeilQuadraticFormData)
    (g h : SchwartzLineTestFunction) : Real :=
  (1 / 2 : Real) * data.formulaFunctional
    (schwartzCrossCorrelation g h + schwartzCrossCorrelation h g)

theorem schwartzWeilPolarizedForm_symm
    (data : SchwartzWeilQuadraticFormData)
    (g h : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data g h =
      schwartzWeilPolarizedForm data h g := by
  unfold schwartzWeilPolarizedForm
  rw [add_comm]

theorem schwartzWeilPolarizedForm_add_left
    (data : SchwartzWeilQuadraticFormData)
    (g₁ g₂ h : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data (g₁ + g₂) h =
      schwartzWeilPolarizedForm data g₁ h +
        schwartzWeilPolarizedForm data g₂ h := by
  simp only [schwartzWeilPolarizedForm, schwartzCrossCorrelation_add_left,
    schwartzCrossCorrelation_add_right, map_add]
  ring

theorem schwartzWeilPolarizedForm_add_right
    (data : SchwartzWeilQuadraticFormData)
    (g h₁ h₂ : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data g (h₁ + h₂) =
      schwartzWeilPolarizedForm data g h₁ +
        schwartzWeilPolarizedForm data g h₂ := by
  rw [schwartzWeilPolarizedForm_symm]
  rw [schwartzWeilPolarizedForm_add_left]
  rw [schwartzWeilPolarizedForm_symm data h₁ g,
    schwartzWeilPolarizedForm_symm data h₂ g]

/-- The polarized diagonal is exactly the checked M80 quadratic form. -/
theorem schwartzWeilPolarizedForm_self
    (data : SchwartzWeilQuadraticFormData)
    (g : SchwartzLineTestFunction) :
    schwartzWeilPolarizedForm data g g = data.quadraticForm g := by
  simp only [schwartzWeilPolarizedForm, schwartzCrossCorrelation_self,
    SchwartzWeilQuadraticFormData.quadraticForm,
    SchwartzWeilQuadraticFormData.formulaTest, map_add]
  ring

/-- Exact two-block expansion with the complete symmetric cross term. -/
theorem quadraticForm_add_eq_polarized
    (data : SchwartzWeilQuadraticFormData)
    (g h : SchwartzLineTestFunction) :
    data.quadraticForm (g + h) =
      data.quadraticForm g + 2 * schwartzWeilPolarizedForm data g h +
        data.quadraticForm h := by
  simp only [SchwartzWeilQuadraticFormData.quadraticForm,
    SchwartzWeilQuadraticFormData.formulaTest,
    autocorrelation_add_eq_crossCorrelation_sum, map_add,
    schwartzWeilPolarizedForm]
  ring

/-- Standard real polarization identity, derived from the actual
autocorrelation expansion rather than postulated for an unrelated form. -/
theorem two_mul_polarizedForm_eq_quadraticForm_add_sub
    (data : SchwartzWeilQuadraticFormData)
    (g h : SchwartzLineTestFunction) :
    2 * schwartzWeilPolarizedForm data g h =
      data.quadraticForm (g + h) - data.quadraticForm g -
        data.quadraticForm h := by
  rw [quadraticForm_add_eq_polarized]
  ring

/-- Continuity of the formula functional makes the polarized form jointly
continuous; no positivity input is used. -/
theorem continuous_schwartzWeilPolarizedForm
    (data : SchwartzWeilQuadraticFormData)
    (hcontinuous : Continuous data.formulaFunctional) :
    Continuous
      (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        schwartzWeilPolarizedForm data p.1 p.2) := by
  change Continuous
    (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
      (1 / 2 : Real) * data.formulaFunctional
        (schwartzCrossCorrelation p.1 p.2 +
          schwartzCrossCorrelation p.2 p.1))
  have hswap : Continuous
      (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        (p.2, p.1)) :=
    continuous_snd.prodMk continuous_fst
  have hreverse := continuous_schwartzCrossCorrelation.comp hswap
  change Continuous
    (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
      schwartzCrossCorrelation p.2 p.1) at hreverse
  have hsum : Continuous
      (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        schwartzCrossCorrelation p.1 p.2 +
          schwartzCrossCorrelation p.2 p.1) :=
    continuous_schwartzCrossCorrelation.add hreverse
  have hformula : Continuous
      (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        data.formulaFunctional
          (schwartzCrossCorrelation p.1 p.2 +
            schwartzCrossCorrelation p.2 p.1)) :=
    hcontinuous.comp hsum
  have hconstant : Continuous
      (fun _p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
        (1 / 2 : Real)) :=
    continuous_const
  exact hconstant.mul hformula

end

end M100
end Experiments
end RiemannHypothesisProject
