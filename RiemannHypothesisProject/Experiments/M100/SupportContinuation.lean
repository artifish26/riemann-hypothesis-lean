import Mathlib.LinearAlgebra.Matrix.PosDef
import RiemannHypothesisProject.Experiments.M100.PolynomialGaussianMomentMatrix
import RiemannHypothesisProject.Experiments.M100.TwoBlockPSD
import RiemannHypothesisProject.WeilPositivity.BurnolLocalSupport

/-!
# M100-X08 translated Burnol blocks and finite-union continuation

This experimental module separates the translation step, which preserves the
Burnol spectral form, from the finite-union step, which requires positivity of
the complete block Gram matrix.

No theorem below promotes translated local positivity to arbitrary unions or
to a criterion-determining class.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open MeasureTheory
open scoped BigOperators ComplexConjugate FourierTransform Matrix
open SchwartzLineTestFunction

noncomputable section

/-- Physical translation of a Schwartz base test: `x ↦ g (x - a)`. -/
def schwartzTranslate
    (a : Real) (g : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  g.compSubConstCLM Complex a

@[simp]
theorem schwartzTranslate_apply
    (a x : Real) (g : SchwartzLineTestFunction) :
    schwartzTranslate a g x = g (x - a) :=
  rfl

/-- Fourier translation law in Mathlib's `exp (-2*pi*i*x*t)` convention. -/
theorem fourier_schwartzTranslate_apply
    (a t : Real) (g : SchwartzLineTestFunction) :
    (𝓕 (schwartzTranslate a g)) t =
      Real.fourierChar ((-a) * t) • (𝓕 g) t := by
  change 𝓕 ((g : Real → Complex) ∘ fun x => x + (-a)) t = _
  have h := congrFun
    (Fourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (g : Real → Complex) (-a)) t
  exact h

/-- Translation changes the Fourier transform only by a unit phase, so its
pointwise energy density is unchanged. -/
theorem fourierEnergyDensity_schwartzTranslate
    (a t : Real) (g : SchwartzLineTestFunction) :
    fourierEnergyDensity (schwartzTranslate a g) t =
      fourierEnergyDensity g t := by
  rw [fourierEnergyDensity, fourier_schwartzTranslate_apply]
  simp [Complex.normSq_apply, Complex.norm_mul]

/-- The Burnol spectral quadratic form is exactly translation invariant. -/
theorem burnolLocalSpectralQuadraticForm_schwartzTranslate
    (a : Real) (g : SchwartzLineTestFunction) :
    burnolLocalSpectralQuadraticForm (schwartzTranslate a g) =
      burnolLocalSpectralQuadraticForm g := by
  unfold burnolLocalSpectralQuadraticForm
  apply integral_congr_ae
  filter_upwards with t
  rw [fourierEnergyDensity_schwartzTranslate]

/-- Translating a test supported around `a` by `-a` recenters its support. -/
theorem support_schwartzTranslate_neg_subset_Icc
    {a r : Real} {g : SchwartzLineTestFunction}
    (hsupport : Function.support g ⊆ Set.Icc (a - r) (a + r)) :
    Function.support (schwartzTranslate (-a) g) ⊆ Set.Icc (-r) r := by
  intro x hx
  have hg : g (x + a) ≠ 0 := by
    simpa [schwartzTranslate_apply] using hx
  have hmem := hsupport hg
  constructor <;> linarith [hmem.1, hmem.2]

/-- Burnol fixed-support positivity holds with the same radius around every
translation center. This is still a one-block theorem: it says nothing about
cross terms between tests supported in different translated intervals. -/
theorem exists_burnolTranslatedFixedSupport_spectral_nonneg_of_binet
    (hBinet : ComplexCompactExhaustion.BennettGammaBinetDigammaFormula) :
    ∃ epsilon > 0, ∃ A : Real, 0 ≤ A ∧
      ∀ (a : Real) (g : SchwartzLineTestFunction),
        Function.support g ⊆
            Set.Icc (a - epsilon / (8 * Real.pi))
              (a + epsilon / (8 * Real.pi)) →
        0 ≤ burnolLocalSpectralQuadraticForm g := by
  obtain ⟨epsilon, hepsilon, A, hA, hfixed⟩ :=
    exists_burnolFixedSupport_spectral_nonneg_of_binet hBinet
  refine ⟨epsilon, hepsilon, A, hA, ?_⟩
  intro a g hsupport
  have hcentered := hfixed (schwartzTranslate (-a) g)
    (support_schwartzTranslate_neg_subset_Icc hsupport)
  rwa [burnolLocalSpectralQuadraticForm_schwartzTranslate] at hcentered

/-- Gram matrix of an arbitrary finite family for the checked polarized Weil
form. Unlike a one-block diagonal statement, this records every cross term. -/
def schwartzWeilFiniteBlockGram
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (g : Fin N → SchwartzLineTestFunction) : Matrix (Fin N) (Fin N) Real :=
  fun i j ↦ schwartzWeilPolarizedForm data (g i) (g j)

/-- The finite block Gram matrix is Hermitian by symmetry of polarization. -/
theorem schwartzWeilFiniteBlockGram_isHermitian
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (g : Fin N → SchwartzLineTestFunction) :
    (schwartzWeilFiniteBlockGram data N g).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [schwartzWeilFiniteBlockGram, star_trivial]
  exact schwartzWeilPolarizedForm_symm data _ _

/-- The matrix quadratic expression is exactly the Weil quadratic form of the
corresponding finite linear combination. -/
theorem schwartzWeilFiniteBlockGram_dotProduct_mulVec
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (g : Fin N → SchwartzLineTestFunction) (c : Fin N → Real) :
    star c ⊹ᵥ (schwartzWeilFiniteBlockGram data N g *ᵥ c) =
      data.quadraticForm (∑ i : Fin N, c i • g i) := by
  rw [← schwartzWeilPolarizedForm_self]
  rw [schwartzWeilPolarizedForm_finset_sum_left]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  rw [schwartzWeilPolarizedForm_real_smul_left]
  rw [schwartzWeilPolarizedForm_finset_sum_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [schwartzWeilPolarizedForm_real_smul_right]
  simp only [schwartzWeilFiniteBlockGram]
  ring

/-- Exact arbitrary-finite-block criterion: positivity of all combinations is
equivalent to positive semidefiniteness of the complete Gram matrix. -/
theorem schwartzWeilFiniteBlockGram_posSemidef_iff
    (data : SchwartzWeilQuadraticFormData) (N : Nat)
    (g : Fin N → SchwartzLineTestFunction) :
    (schwartzWeilFiniteBlockGram data N g).PosSemidef ↔
      ∀ c : Fin N → Real,
        0 ≤ data.quadraticForm (∑ i : Fin N, c i • g i) := by
  constructor
  · intro hPSD c
    have h := hPSD.dotProduct_mulVec_nonneg c
    rwa [schwartzWeilFiniteBlockGram_dotProduct_mulVec] at h
  · intro hnonnegative
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (schwartzWeilFiniteBlockGram_isHermitian data N g)
    intro c
    rw [schwartzWeilFiniteBlockGram_dotProduct_mulVec]
    exact hnonnegative c

/-- A three-block scalar model whose every two-by-two principal block passes
the Schur test, but whose all-ones direction is negative. This rules out the
purely algebraic inference from pairwise PSD to arbitrary finite-block PSD. -/
def syntheticThreeBlockQuadratic (a b c : Real) : Real :=
  a ^ 2 + b ^ 2 + c ^ 2 -
    (3 / 2 : Real) * (a * b + a * c + b * c)

theorem pairwise_schur_does_not_force_threeBlock_nonnegative :
    (∀ a b : Real, 0 ≤ twoBlockQuadratic 1 1 (-3 / 4) a b) ∧
      syntheticThreeBlockQuadratic 1 1 1 < 0 := by
  constructor
  · exact twoBlockQuadratic_nonnegative_of_schur
      (by norm_num) (by norm_num) (by norm_num)
  · norm_num [syntheticThreeBlockQuadratic]

end


end M100
end Experiments
end RiemannHypothesisProject
