import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianFormulaIdentity
import RiemannHypothesisProject.WeilPositivity.PolynomialGaussianAutocorrelation
import RiemannHypothesisProject.WeilPositivity.ZetaZeroPairing

/-!
# The zeta formula on polynomial-Gaussian autocorrelations

This module identifies the unconditional multiplicity-correct Guinand-Weil
formula with the actual M70 Hermitian pairing.  Nontrivial zeroes are regrouped
through an explicit positive/conjugate-ordinate equivalence; no unordered
conditional rearrangement or zero-location hypothesis is used.
-/

namespace RiemannHypothesisProject

open scoped ComplexConjugate

namespace ComplexCompactExhaustion

noncomputable section

/-- Include a positive-ordinate zero in the nontrivial-zero subtype. -/
def positiveOrdinateToNontrivialZetaZero
    (rho : PositiveOrdinateZetaZeroSubtype) : NontrivialZetaZeroSubtype :=
  ⟨rho.1, not_isTrivialZetaZero_of_im_ne_zero (ne_of_gt rho.2)⟩

/-- Include the conjugate of a positive-ordinate zero in the nontrivial-zero
subtype. -/
def conjugatePositiveOrdinateToNontrivialZetaZero
    (rho : PositiveOrdinateZetaZeroSubtype) : NontrivialZetaZeroSubtype :=
  ⟨⟨conj (rho : Complex),
      zetaZeroConjugationSymmetry (rho : Complex) rho.1.property⟩,
    not_isTrivialZetaZero_of_im_ne_zero (by
      simpa using ne_of_lt (neg_lt_zero.mpr rho.2))⟩

/-- Every nontrivial zeta zero occurs exactly once as a positive-ordinate zero
or as its conjugate. -/
def nontrivialZetaZeroOrdinateEquiv :
    PositiveOrdinateZetaZeroSubtype ⊕ PositiveOrdinateZetaZeroSubtype ≃
      NontrivialZetaZeroSubtype where
  toFun
    | Sum.inl rho => positiveOrdinateToNontrivialZetaZero rho
    | Sum.inr rho => conjugatePositiveOrdinateToNontrivialZetaZero rho
  invFun rho := by
    classical
    if hpos : 0 < (rho : Complex).im then
      exact Sum.inl ⟨rho.1, hpos⟩
    else
      have him_ne := isNontrivialZetaZero_im_ne_zero rho.1 rho.property
      have him_neg : (rho : Complex).im < 0 :=
        lt_of_le_of_ne (le_of_not_gt hpos) him_ne
      exact Sum.inr
        ⟨⟨conj (rho : Complex),
            zetaZeroConjugationSymmetry (rho : Complex) rho.1.property⟩,
          by simpa using neg_pos.mpr him_neg⟩
  left_inv i := by
    classical
    cases i with
    | inl rho =>
        simp [positiveOrdinateToNontrivialZetaZero, rho.2]
    | inr rho =>
        have hnonneg : 0 <= (rho : Complex).im := rho.2.le
        simp [conjugatePositiveOrdinateToNontrivialZetaZero, hnonneg]
  right_inv rho := by
    classical
    by_cases hpos : 0 < (rho : Complex).im
    · simp [hpos, positiveOrdinateToNontrivialZetaZero]
    · simp [hpos, conjugatePositiveOrdinateToNontrivialZetaZero]

/-- Functional reflection becomes complex conjugation in the spectral
Riemann-Weil coordinate. -/
theorem riemannWeilZeroArgument_one_sub_conj (s : Complex) :
    riemannWeilZeroArgument (1 - conj s) =
      conj (riemannWeilZeroArgument s) := by
  unfold riemannWeilZeroArgument
  apply Complex.ext <;>
    simp <;> ring

/-- Conjugating a zero negates the conjugate spectral coordinate. -/
theorem riemannWeilZeroArgument_conj (s : Complex) :
    riemannWeilZeroArgument (conj s) =
      -conj (riemannWeilZeroArgument s) := by
  unfold riemannWeilZeroArgument
  apply Complex.ext <;>
    simp

/-- Reflection across `1/2` negates the spectral coordinate. -/
theorem riemannWeilZeroArgument_one_sub (s : Complex) :
    riemannWeilZeroArgument (1 - s) =
      -riemannWeilZeroArgument s := by
  unfold riemannWeilZeroArgument
  apply Complex.ext <;>
    simp <;> ring

/-- The M70 pairing test induced by the selected half-Gaussian transform. -/
def zetaWeilPolynomialGaussianTransform
    (q : Polynomial Real) (s : Complex) : Complex :=
  zetaWeilHalfGaussianEntire q (riemannWeilZeroArgument s)

/-- One M70 pairing summand is exactly the real conjugate-pair contribution
of the formula's full-scale polynomial-Gaussian zero side. -/
theorem zetaWeilPairingSummand_polynomialGaussian_eq
    (q : Polynomial Real) (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaWeilPairingSummand
        (zetaWeilPolynomialGaussianTransform q)
        (zetaWeilPolynomialGaussianTransform q) rho =
      ((2 * zetaZeroMultiplicityReal rho.1 *
          (guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiEvenPolynomial
              (zetaWeilAutocorrelationPolynomial q))
            (riemannWeilZeroArgument (rho : Complex))).re : Real) : Complex) := by
  let z := riemannWeilZeroArgument (rho : Complex)
  let E := zetaWeilHalfGaussianEntire q z
  let H := guinandWeilPiPolynomialGaussianSource
    (guinandWeilPiEvenPolynomial (zetaWeilAutocorrelationPolynomial q)) z
  have hEconj : zetaWeilHalfGaussianEntire q (conj z) = conj E := by
    exact zetaWeilHalfGaussianEntire_conj q z
  have hEneg : zetaWeilHalfGaussianEntire q (-z) = E := by
    exact zetaWeilHalfGaussianEntire_neg q z
  have hEnegconj : zetaWeilHalfGaussianEntire q (-conj z) = conj E := by
    rw [zetaWeilHalfGaussianEntire_neg]
    exact hEconj
  have hH : E ^ 2 = H := by
    exact zetaWeilHalfGaussianEntire_sq q z
  rw [zetaWeilPairingSummand]
  change (zetaZeroMultiplicity rho.1 : Complex) *
    (E * conj (zetaWeilHalfGaussianEntire q
        (riemannWeilZeroArgument (1 - conj (rho : Complex)))) +
      zetaWeilHalfGaussianEntire q
          (riemannWeilZeroArgument (conj (rho : Complex))) *
        conj (zetaWeilHalfGaussianEntire q
          (riemannWeilZeroArgument (1 - (rho : Complex))))) = _
  rw [riemannWeilZeroArgument_one_sub_conj,
    riemannWeilZeroArgument_conj,
    riemannWeilZeroArgument_one_sub]
  change (zetaZeroMultiplicity rho.1 : Complex) *
    (E * conj (zetaWeilHalfGaussianEntire q (conj z)) +
      zetaWeilHalfGaussianEntire q (-conj z) *
        conj (zetaWeilHalfGaussianEntire q (-z))) = _
  rw [hEconj, hEnegconj, hEneg]
  simp only [starRingEnd_apply, star_star]
  have hstarSq : star E * star E = star (E ^ 2) := by
    simp [pow_two]
  rw [hstarSq, ← pow_two E, hH]
  apply Complex.ext <;> simp [zetaZeroMultiplicityReal] <;> ring

/-- A positive zero and its conjugate contribute twice the real part of the
same real-even source value. -/
theorem nontrivialPolynomialGaussianWeight_positive_add_conjugate
    (q : Polynomial Real) (rho : PositiveOrdinateZetaZeroSubtype) :
    multiplicityPolynomialGaussianNontrivialZetaZeroWeight
        (guinandWeilPiEvenPolynomial
          (zetaWeilAutocorrelationPolynomial q))
        (positiveOrdinateToNontrivialZetaZero rho) +
      multiplicityPolynomialGaussianNontrivialZetaZeroWeight
        (guinandWeilPiEvenPolynomial
          (zetaWeilAutocorrelationPolynomial q))
        (conjugatePositiveOrdinateToNontrivialZetaZero rho) =
      2 * zetaZeroMultiplicityReal rho.1 *
        (guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiEvenPolynomial
            (zetaWeilAutocorrelationPolynomial q))
          (riemannWeilZeroArgument (rho : Complex))).re := by
  rw [multiplicityPolynomialGaussianNontrivialZetaZeroWeight,
    multiplicityPolynomialGaussianNontrivialZetaZeroWeight]
  unfold positiveOrdinateToNontrivialZetaZero
  unfold conjugatePositiveOrdinateToNontrivialZetaZero
  rw [zetaZeroMultiplicityReal, zetaZeroMultiplicityReal,
    zetaZeroMultiplicity_conj]
  rw [riemannWeilZeroArgument_conj]
  rw [guinandWeilPiEvenPolynomialGaussianSource_neg,
    guinandWeilPiEvenPolynomialGaussianSource_conj]
  simp
  ring

/-- The formula's faithful all-zero side is the canonical positive/conjugate
pair sum used by the M70 pairing. -/
theorem guinandWeilPolynomialGaussianZeroSide_eq_positivePairSum
    (q : Polynomial Real) :
    guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
        (guinandWeilPiEvenPolynomial
          (zetaWeilAutocorrelationPolynomial q)) =
      ∑' rho : PositiveOrdinateZetaZeroSubtype,
        2 * zetaZeroMultiplicityReal rho.1 *
          (guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiEvenPolynomial
              (zetaWeilAutocorrelationPolynomial q))
            (riemannWeilZeroArgument (rho : Complex))).re := by
  let p := guinandWeilPiEvenPolynomial
    (zetaWeilAutocorrelationPolynomial q)
  let w := multiplicityPolynomialGaussianNontrivialZetaZeroWeight p
  have hw : Summable w :=
    summable_multiplicityPolynomialGaussianNontrivialZetaZeroWeight_unconditional p
  have hsum : Summable (w ∘ nontrivialZetaZeroOrdinateEquiv) :=
    hw.comp_injective nontrivialZetaZeroOrdinateEquiv.injective
  have hpositive := hsum.comp_injective Sum.inl_injective
  have hconjugate := hsum.comp_injective Sum.inr_injective
  have hpositive' : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      w (positiveOrdinateToNontrivialZetaZero rho)) := by
    simpa [Function.comp_def, nontrivialZetaZeroOrdinateEquiv] using hpositive
  have hconjugate' : Summable (fun rho : PositiveOrdinateZetaZeroSubtype =>
      w (conjugatePositiveOrdinateToNontrivialZetaZero rho)) := by
    simpa [Function.comp_def, nontrivialZetaZeroOrdinateEquiv] using hconjugate
  unfold guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
  simp only [guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroWeight]
  rw [tsum_multiplicityPolynomialGaussianCompletedZetaZeroWeight_eq_nontrivial]
  change (∑' rho : NontrivialZetaZeroSubtype, w rho) = _
  calc
    (∑' rho : NontrivialZetaZeroSubtype, w rho) =
        ∑' i : PositiveOrdinateZetaZeroSubtype ⊕
            PositiveOrdinateZetaZeroSubtype,
          w (nontrivialZetaZeroOrdinateEquiv i) :=
      (nontrivialZetaZeroOrdinateEquiv.tsum_eq w).symm
    _ = (∑' rho : PositiveOrdinateZetaZeroSubtype,
          w (positiveOrdinateToNontrivialZetaZero rho)) +
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          w (conjugatePositiveOrdinateToNontrivialZetaZero rho) := by
      exact hpositive.tsum_sum hconjugate
    _ = ∑' rho : PositiveOrdinateZetaZeroSubtype,
        (w (positiveOrdinateToNontrivialZetaZero rho) +
          w (conjugatePositiveOrdinateToNontrivialZetaZero rho)) := by
      exact (hpositive'.tsum_add hconjugate').symm
    _ = _ := by
      apply tsum_congr
      intro rho
      exact nontrivialPolynomialGaussianWeight_positive_add_conjugate q rho

/-- The actual M70 Hermitian pairing is the complex embedding of the
multiplicity-correct literature zero side. -/
theorem zetaWeilPairing_polynomialGaussian_eq_formulaZeroSide
    (q : Polynomial Real) :
    zetaWeilPairing
        (zetaWeilPolynomialGaussianTransform q)
        (zetaWeilPolynomialGaussianTransform q) =
      (guinandWeilPiMultiplicityPolynomialGaussianLiteratureZeroSide
        (guinandWeilPiEvenPolynomial
          (zetaWeilAutocorrelationPolynomial q)) : Complex) := by
  rw [zetaWeilPairing,
    guinandWeilPolynomialGaussianZeroSide_eq_positivePairSum,
    Complex.ofReal_tsum]
  apply tsum_congr
  intro rho
  exact zetaWeilPairingSummand_polynomialGaussian_eq q rho

/-- M80 endpoint: the unconditional literature formula evaluates the Fourier
transform of a genuine convolution square and its zero side is exactly the M70
Weil pairing. -/
theorem zetaWeilPolynomialGaussian_formula_on_autocorrelation
    (q : Polynomial Real) :
    SchwartzLineTestFunction.fourierAutocorrelation
        (zetaWeilPolynomialGaussianBase q) =
        guinandWeilPiEvenPolynomialGaussianSchwartz
          (zetaWeilAutocorrelationPolynomial q) ∧
      zetaWeilPairing
          (zetaWeilPolynomialGaussianTransform q)
          (zetaWeilPolynomialGaussianTransform q) =
        (guinandWeilPiPolynomialGaussianLiteratureResidualSide
          (guinandWeilPiEvenPolynomial
            (zetaWeilAutocorrelationPolynomial q)) : Complex) := by
  constructor
  · exact fourierAutocorrelation_zetaWeilPolynomialGaussianBase q
  · rw [zetaWeilPairing_polynomialGaussian_eq_formulaZeroSide]
    exact_mod_cast
      guinandWeilPiEvenPolynomialGaussianLiteratureFormula
        (zetaWeilAutocorrelationPolynomial q)

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
