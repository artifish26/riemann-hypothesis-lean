import RiemannHypothesisProject.GuinandWeilConcrete.EvenHermiteDensity
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFormulaIdentity

/-!
# Polynomial-Gaussian formula density bridge

The contour theorem proves the multiplicity-correct Guinand-Weil formula on
the exact real-even polynomial-Gaussian source.  This module feeds that theorem
into the Hermite density route without pretending that off-axis evaluation is
continuous on ordinary Schwartz space.

A downstream residual functional is therefore supplied as a continuous real
linear extension whose values on the exact source are the checked literature
residual.  The formula then identifies its values with the actual
multiplicity-weighted zero sums along every canonical dense approximation.
Residual positivity, when proved on the source, consequently extends to the
whole real-even Schwartz sector by continuity.
-/

namespace RiemannHypothesisProject

open Filter Topology
open ComplexCompactExhaustion
open scoped Topology

noncomputable section

/-- Every real-even Schwartz test has a dense polynomial-Gaussian
approximation on which the unconditional multiplicity-correct literature
formula holds term by term. -/
theorem exists_evenPolynomialGaussianLiteratureFormulaApproximation
    (f : guinandWeilRealEvenSchwartzSubmodule) :
    ∃ p : Nat → Polynomial Real,
      Tendsto
        (fun N =>
          guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap (p N))
        atTop (𝓝 f) ∧
      ∀ N : Nat,
        GuinandWeilPiMultiplicityPolynomialGaussianLiteratureFormula
          (guinandWeilPiEvenPolynomial (p N)) := by
  rcases exists_evenPolynomialGaussianSource_approximation f with ⟨p, hp⟩
  refine ⟨p, ?_, fun N =>
    guinandWeilPiEvenPolynomialGaussianLiteratureFormula (p N)⟩
  rw [tendsto_subtype_rng]
  simpa [guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap] using hp

/-- A continuous residual extension with the checked source normalization is
the limit of the actual multiplicity-weighted zero sums along a dense
polynomial-Gaussian approximation. -/
theorem exists_evenPolynomialGaussianZeroSide_tendsto_continuousResidual
    (residual :
      guinandWeilRealEvenSchwartzSubmodule →L[Real] Real)
    (residual_eq_literature :
      ∀ p : Polynomial Real,
        residual
            (guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap p) =
          guinandWeilPiPolynomialGaussianLiteratureResidualSide
            (guinandWeilPiEvenPolynomial p))
    (f : guinandWeilRealEvenSchwartzSubmodule) :
    ∃ p : Nat → Polynomial Real,
      Tendsto
        (fun N =>
          guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap (p N))
        atTop (𝓝 f) ∧
      Tendsto
        (fun N =>
          guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
            (guinandWeilPiEvenPolynomial (p N)))
        atTop (𝓝 (residual f)) := by
  rcases exists_evenPolynomialGaussianLiteratureFormulaApproximation f with
    ⟨p, hp, hformula⟩
  refine ⟨p, hp, ?_⟩
  have hresidual :
      Tendsto
        (fun N =>
          residual
            (guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap (p N)))
        atTop (𝓝 (residual f)) :=
    residual.continuous.tendsto f |>.comp hp
  apply hresidual.congr'
  exact Eventually.of_forall fun N => by
    change
      residual
          (guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap (p N)) =
        guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
          (guinandWeilPiEvenPolynomial (p N))
    rw [residual_eq_literature]
    exact (hformula N).symm

/-- Nonnegativity of the actual multiplicity-weighted zero side on the exact
source promotes to nonnegativity of every continuously extended residual on
the real-even Schwartz sector. -/
theorem continuousResidual_nonneg_of_evenPolynomialGaussianZeroSide_nonneg
    (residual :
      guinandWeilRealEvenSchwartzSubmodule →L[Real] Real)
    (residual_eq_literature :
      ∀ p : Polynomial Real,
        residual
            (guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap p) =
          guinandWeilPiPolynomialGaussianLiteratureResidualSide
            (guinandWeilPiEvenPolynomial p))
    (zeroSide_nonneg :
      ∀ p : Polynomial Real,
        0 ≤
          guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
            (guinandWeilPiEvenPolynomial p))
    (f : guinandWeilRealEvenSchwartzSubmodule) :
    0 ≤ residual f := by
  rcases
      exists_evenPolynomialGaussianZeroSide_tendsto_continuousResidual
        residual residual_eq_literature f with
    ⟨p, _hp, hzero⟩
  exact isClosed_Ici.mem_of_tendsto hzero
    (Eventually.of_forall fun N => zeroSide_nonneg (p N))

end

end RiemannHypothesisProject
