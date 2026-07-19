import RiemannHypothesisProject.LiCriterion.LiRationalBasis
import RiemannHypothesisProject.LiCriterion.ZetaBombieriLagariasCriterion
import RiemannHypothesisProject.WeilPositivity.ZetaZeroPairing

/-!
# Lagarias's Li-basis evaluation of the zeta Weil pairing

This module sums the rational-basis algebra over the actual nontrivial zeta
zeros with analytic multiplicity.  It proves unconditional convergence of
every basis pairing, the full off-diagonal Lagarias identity, the diagonal
`2 * lambda_n` identity, and the resulting M60-backed criterion-determining
statement.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate

noncomputable section

/-- The multiplicity-weighted conjugate-paired integer Li summand. -/
def zetaLiIntegerPairedSummand
    (n : Int) (rho : PositiveOrdinateZetaZeroSubtype) : Complex :=
  (zetaZeroMultiplicity rho.1 : Complex) *
    (liRationalTest n (rho : Complex) +
      liRationalTest n (conj (rho : Complex)))

/-- The full integer-indexed zeta Li coefficient in the canonical
positive/conjugate ordering. -/
def fullZetaLiCoefficientInt (n : Int) : Complex :=
  ∑' rho : PositiveOrdinateZetaZeroSubtype,
    zetaLiIntegerPairedSummand n rho

/-- Nonnegative integer summands agree with the M50 paired summands. -/
theorem zetaLiIntegerPairedSummand_ofNat
    (n : Nat) (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaLiIntegerPairedSummand (n : Int) rho =
      multiplicityWeightedZetaLiPairedSummand n rho := by
  simp [zetaLiIntegerPairedSummand, liRationalTest_ofNat,
    multiplicityWeightedZetaLiPairedSummand, zetaLiPairedSummand]

/-- Nonnegative integer Li summands are summable. -/
theorem summable_zetaLiIntegerPairedSummand_ofNat (n : Nat) :
    Summable (zetaLiIntegerPairedSummand (n : Int)) := by
  exact (summable_multiplicityWeightedZetaLiPairedSummand n).congr
    (zetaLiIntegerPairedSummand_ofNat n)

/-- Negating the Li index is the same as functionally reflecting the positive
zero pair. -/
theorem zetaLiIntegerPairedSummand_neg
    (n : Int) (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaLiIntegerPairedSummand (-n) rho =
      zetaLiIntegerPairedSummand n
        (positiveOrdinateZetaZeroFunctionalReflection rho) := by
  have hrho := positiveOrdinateZetaZero_isNontrivial rho
  have hconj := positiveOrdinateZetaZero_conj_isNontrivial rho
  rw [zetaLiIntegerPairedSummand, zetaLiIntegerPairedSummand]
  rw [zetaZeroMultiplicity_positiveOrdinateFunctionalReflection]
  rw [liRationalTest_neg n (isZetaZero_ne_zero hrho.1) hrho.2.2]
  rw [liRationalTest_neg n (isZetaZero_ne_zero hconj.1) hconj.2.2]
  simp [positiveOrdinateZetaZeroFunctionalReflection_value]
  ring_nf
  exact Or.inl trivial

/-- Every integer-indexed paired Li family is unconditionally summable. -/
theorem summable_zetaLiIntegerPairedSummand (n : Int) :
    Summable (zetaLiIntegerPairedSummand n) := by
  cases n with
  | ofNat n => exact summable_zetaLiIntegerPairedSummand_ofNat n
  | negSucc n =>
      let k : Nat := n + 1
      have hpositive : Summable (zetaLiIntegerPairedSummand (k : Int)) :=
        summable_zetaLiIntegerPairedSummand_ofNat k
      have hreflected : Summable
          (zetaLiIntegerPairedSummand (k : Int) ∘
            positiveOrdinateZetaZeroFunctionalReflectionEquiv) :=
        positiveOrdinateZetaZeroFunctionalReflectionEquiv.summable_iff.mpr
          hpositive
      have hindex : Int.negSucc n = -(k : Int) := by
        omega
      rw [hindex]
      exact hreflected.congr (fun rho => by
        change zetaLiIntegerPairedSummand (k : Int)
            (positiveOrdinateZetaZeroFunctionalReflection rho) =
          zetaLiIntegerPairedSummand (-(k : Int)) rho
        exact (zetaLiIntegerPairedSummand_neg (k : Int) rho).symm)

/-- Functional reflection gives the integer coefficient symmetry
`lambda_{-n} = lambda_n`. -/
theorem fullZetaLiCoefficientInt_neg (n : Int) :
    fullZetaLiCoefficientInt (-n) = fullZetaLiCoefficientInt n := by
  rw [fullZetaLiCoefficientInt, fullZetaLiCoefficientInt]
  calc
    (∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaLiIntegerPairedSummand (-n) rho) =
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          zetaLiIntegerPairedSummand n
            (positiveOrdinateZetaZeroFunctionalReflectionEquiv rho) := by
      apply tsum_congr
      intro rho
      exact zetaLiIntegerPairedSummand_neg n rho
    _ = ∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaLiIntegerPairedSummand n rho :=
      positiveOrdinateZetaZeroFunctionalReflectionEquiv.tsum_eq
        (zetaLiIntegerPairedSummand n)

/-- The integer coefficient at zero vanishes. -/
@[simp]
theorem fullZetaLiCoefficientInt_zero :
    fullZetaLiCoefficientInt 0 = 0 := by
  simp [fullZetaLiCoefficientInt, zetaLiIntegerPairedSummand]

/-- The integer extension agrees exactly with the M50 coefficient at every
natural index. -/
theorem fullZetaLiCoefficientInt_ofNat (n : Nat) :
    fullZetaLiCoefficientInt (n : Int) =
      (fullZetaLiCoefficient n : Complex) := by
  rw [fullZetaLiCoefficientInt]
  calc
    (∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaLiIntegerPairedSummand (n : Int) rho) =
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          multiplicityWeightedZetaLiPairedSummand n rho := by
      apply tsum_congr
      intro rho
      exact zetaLiIntegerPairedSummand_ofNat n rho
    _ = fullZetaLiCoefficientComplex n := rfl
    _ = (fullZetaLiCoefficient n : Complex) :=
      fullZetaLiCoefficientComplex_eq_ofReal n

/-- Each Li-basis pairing summand is the Lagarias three-coefficient
combination before summation. -/
theorem zetaWeilPairingSummand_liRationalTest
    (n m : Int) (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaWeilPairingSummand (liRationalTest n) (liRationalTest m) rho =
      zetaLiIntegerPairedSummand n rho +
        zetaLiIntegerPairedSummand (-m) rho -
          zetaLiIntegerPairedSummand (n - m) rho := by
  have hrho := positiveOrdinateZetaZero_isNontrivial rho
  have hconj := positiveOrdinateZetaZero_conj_isNontrivial rho
  have hsecond :
      conj (liRationalTest m (1 - (rho : Complex))) =
        liRationalTest (-m) (conj (rho : Complex)) := by
    simpa using conj_liRationalTest_one_sub_conj m
      (isZetaZero_ne_zero hconj.1) hconj.2.2
  rw [zetaWeilPairingSummand, zetaLiIntegerPairedSummand,
    zetaLiIntegerPairedSummand, zetaLiIntegerPairedSummand]
  rw [conj_liRationalTest_one_sub_conj m
    (isZetaZero_ne_zero hrho.1) hrho.2.2]
  rw [hsecond]
  rw [liRationalTest_mul_neg n m hrho.2.2]
  rw [liRationalTest_mul_neg n m hconj.2.2]
  ring

/-- Every pairing of two Li rational basis functions converges
unconditionally on the actual multiplicity-aware zeta zero family. -/
theorem summable_zetaWeilPairingSummand_liRationalTest (n m : Int) :
    Summable (zetaWeilPairingSummand
      (liRationalTest n) (liRationalTest m)) := by
  have hn := summable_zetaLiIntegerPairedSummand n
  have hnegm := summable_zetaLiIntegerPairedSummand (-m)
  have hdiff := summable_zetaLiIntegerPairedSummand (n - m)
  have hcombination : Summable (fun rho =>
      zetaLiIntegerPairedSummand n rho +
        zetaLiIntegerPairedSummand (-m) rho -
          zetaLiIntegerPairedSummand (n - m) rho) :=
    (hn.add hnegm).sub hdiff
  exact hcombination.congr (fun rho =>
    (zetaWeilPairingSummand_liRationalTest n m rho).symm)

/-- Lagarias's full Li-basis identity for the actual zeta Weil pairing. -/
theorem zetaWeilPairing_liRationalTest (n m : Int) :
    zetaWeilPairing (liRationalTest n) (liRationalTest m) =
      fullZetaLiCoefficientInt n + fullZetaLiCoefficientInt (-m) -
        fullZetaLiCoefficientInt (n - m) := by
  have hn := summable_zetaLiIntegerPairedSummand n
  have hnegm := summable_zetaLiIntegerPairedSummand (-m)
  have hdiff := summable_zetaLiIntegerPairedSummand (n - m)
  rw [zetaWeilPairing, fullZetaLiCoefficientInt,
    fullZetaLiCoefficientInt, fullZetaLiCoefficientInt]
  calc
    (∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaWeilPairingSummand (liRationalTest n)
          (liRationalTest m) rho) =
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          (zetaLiIntegerPairedSummand n rho +
            zetaLiIntegerPairedSummand (-m) rho -
              zetaLiIntegerPairedSummand (n - m) rho) := by
      apply tsum_congr
      intro rho
      exact zetaWeilPairingSummand_liRationalTest n m rho
    _ = (∑' rho : PositiveOrdinateZetaZeroSubtype,
          zetaLiIntegerPairedSummand n rho) +
        (∑' rho : PositiveOrdinateZetaZeroSubtype,
          zetaLiIntegerPairedSummand (-m) rho) -
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          zetaLiIntegerPairedSummand (n - m) rho := by
      rw [(hn.add hnegm).tsum_sub hdiff, hn.tsum_add hnegm]

/-- Zeta functional symmetry removes the negative coefficient from the
Lagarias identity. -/
theorem zetaWeilPairing_liRationalTest_symmetric (n m : Int) :
    zetaWeilPairing (liRationalTest n) (liRationalTest m) =
      fullZetaLiCoefficientInt n + fullZetaLiCoefficientInt m -
        fullZetaLiCoefficientInt (n - m) := by
  rw [zetaWeilPairing_liRationalTest, fullZetaLiCoefficientInt_neg]

/-- The diagonal Li-basis Weil pairing is twice the integer Li coefficient. -/
theorem zetaWeilPairing_liRationalTest_self (n : Int) :
    zetaWeilPairing (liRationalTest n) (liRationalTest n) =
      2 * fullZetaLiCoefficientInt n := by
  rw [zetaWeilPairing_liRationalTest_symmetric, Int.sub_self,
    fullZetaLiCoefficientInt_zero]
  ring

/-- At natural indices, the diagonal is exactly twice the M50 coefficient. -/
theorem zetaWeilPairing_liRationalTest_self_ofNat (n : Nat) :
    zetaWeilPairing (liRationalTest (n : Int))
        (liRationalTest (n : Int)) =
      ((2 * fullZetaLiCoefficient n : Real) : Complex) := by
  rw [zetaWeilPairing_liRationalTest_self,
    fullZetaLiCoefficientInt_ofNat]
  norm_num

/-- Under RH, the Li rational tests satisfy the explicit square-summability
hypothesis of the zero-pairing theorem. -/
theorem summable_zetaWeilNormSqSummand_liRationalTest_of_RH
    (hRH : RHStatement) (n : Int) :
    Summable (zetaWeilNormSqSummand (liRationalTest n)) := by
  rw [← Complex.summable_ofReal]
  exact (summable_zetaWeilPairingSummand_liRationalTest n n).congr
    (fun rho =>
      zetaWeilPairingSummand_self_eq_ofReal_normSq_of_RH
        hRH (liRationalTest n) rho)

/-- The real diagonal value used by the zeta Li-basis criterion. -/
def zetaLiWeilNormSq (n : Nat) : Real :=
  (zetaWeilPairing (liRationalTest (n : Int))
    (liRationalTest (n : Int))).re

/-- The Li-basis diagonal is twice the full M50 real coefficient. -/
theorem zetaLiWeilNormSq_eq_two_mul_fullZetaLiCoefficient (n : Nat) :
    zetaLiWeilNormSq n = 2 * fullZetaLiCoefficient n := by
  rw [zetaLiWeilNormSq, zetaWeilPairing_liRationalTest_self_ofNat]
  simp

/-- The Li basis is criterion-determining: positivity of all its nonzero
diagonal Weil values is equivalent to project RH. -/
theorem RHStatement_iff_zetaLiWeilNormSq_nonneg :
    RHStatement ↔
      ∀ n : Nat, 0 < n -> 0 <= zetaLiWeilNormSq n := by
  constructor
  · intro hRH n _hn
    rw [zetaLiWeilNormSq_eq_two_mul_fullZetaLiCoefficient]
    exact mul_nonneg (by norm_num)
      (fullZetaLiCoefficient_nonneg_of_RHStatement hRH n)
  · intro hpairing
    apply RHStatement_of_fullZetaLiCoefficient_nonneg
    intro n hn
    have h := hpairing n hn
    rw [zetaLiWeilNormSq_eq_two_mul_fullZetaLiCoefficient] at h
    linarith

/-- Mathlib RH has the same criterion-determining Li-basis formulation. -/
theorem mathlib_RH_iff_zetaLiWeilNormSq_nonneg :
    RiemannHypothesis ↔
      ∀ n : Nat, 0 < n -> 0 <= zetaLiWeilNormSq n := by
  rw [← RHStatement_iff_mathlib]
  exact RHStatement_iff_zetaLiWeilNormSq_nonneg

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
