import RiemannHypothesisProject.LiCriterion.ZetaFunctionalMultiplicityReflection

/-!
# The multiplicity-aware zeta Weil pairing

For functions on the zero set, the source pairing is
`⟨F,G⟩ = Σρ F(ρ) * conj (G (1 - conj ρ))`.  The implementation groups each
positive-ordinate zero with its conjugate and weights the pair by analytic
multiplicity.  Functional reflection supplies Hermitian symmetry.  Under RH,
the diagonal is a convergent sum of squared norms whenever the corresponding
square family is summable.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate

noncomputable section

/-- One positive/conjugate pair in the zeta Weil pairing. -/
def zetaWeilPairingSummand
    (F G : Complex -> Complex)
    (rho : PositiveOrdinateZetaZeroSubtype) : Complex :=
  (zetaZeroMultiplicity rho.1 : Complex) *
    (F (rho : Complex) * conj (G (1 - conj (rho : Complex))) +
      F (conj (rho : Complex)) * conj (G (1 - (rho : Complex))))

/-- The actual analytic-multiplicity zeta Weil pairing, canonically grouped
by conjugate zero pairs. -/
def zetaWeilPairing (F G : Complex -> Complex) : Complex :=
  ∑' rho : PositiveOrdinateZetaZeroSubtype,
    zetaWeilPairingSummand F G rho

/-- Functional reflection converts the conjugate of the reversed pairing
summand into the original summand. -/
theorem conj_zetaWeilPairingSummand_functionalReflection
    (F G : Complex -> Complex)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    conj (zetaWeilPairingSummand G F
      (positiveOrdinateZetaZeroFunctionalReflection rho)) =
      zetaWeilPairingSummand F G rho := by
  rw [zetaWeilPairingSummand, zetaWeilPairingSummand]
  rw [zetaZeroMultiplicity_positiveOrdinateFunctionalReflection]
  simp [positiveOrdinateZetaZeroFunctionalReflection_value]
  ring_nf
  exact Or.inl trivial

/-- The zeta Weil pairing is Hermitian.  The identity itself does not need a
convergence assumption; the functional-reflection equivalence preserves both
summability and the `tsum` convention. -/
theorem zetaWeilPairing_conj_symm (F G : Complex -> Complex) :
    zetaWeilPairing F G = conj (zetaWeilPairing G F) := by
  rw [zetaWeilPairing, zetaWeilPairing, Complex.conj_tsum]
  calc
    (∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaWeilPairingSummand F G rho) =
        ∑' rho : PositiveOrdinateZetaZeroSubtype,
          conj (zetaWeilPairingSummand G F
            (positiveOrdinateZetaZeroFunctionalReflectionEquiv rho)) := by
      apply tsum_congr
      intro rho
      exact (conj_zetaWeilPairingSummand_functionalReflection F G rho).symm
    _ = ∑' rho : PositiveOrdinateZetaZeroSubtype,
        conj (zetaWeilPairingSummand G F rho) :=
      positiveOrdinateZetaZeroFunctionalReflectionEquiv.tsum_eq
        (fun rho => conj (zetaWeilPairingSummand G F rho))

/-- Scalar multiplication in the first argument. -/
theorem zetaWeilPairing_mul_left
    (c : Complex) (F G : Complex -> Complex) :
    zetaWeilPairing (fun s => c * F s) G = c * zetaWeilPairing F G := by
  rw [zetaWeilPairing, zetaWeilPairing, ← tsum_mul_left]
  apply tsum_congr
  intro rho
  simp [zetaWeilPairingSummand]
  ring

/-- Conjugate scalar multiplication in the second argument. -/
theorem zetaWeilPairing_mul_right
    (c : Complex) (F G : Complex -> Complex) :
    zetaWeilPairing F (fun s => c * G s) =
      conj c * zetaWeilPairing F G := by
  rw [zetaWeilPairing, zetaWeilPairing, ← tsum_mul_left]
  apply tsum_congr
  intro rho
  simp [zetaWeilPairingSummand]
  ring

/-- Additivity in the first argument for two explicitly summable pairing
families. -/
theorem zetaWeilPairing_add_left
    (F H G : Complex -> Complex)
    (hF : Summable (zetaWeilPairingSummand F G))
    (hH : Summable (zetaWeilPairingSummand H G)) :
    zetaWeilPairing (fun s => F s + H s) G =
      zetaWeilPairing F G + zetaWeilPairing H G := by
  rw [zetaWeilPairing, zetaWeilPairing, zetaWeilPairing]
  rw [← hF.tsum_add hH]
  apply tsum_congr
  intro rho
  simp [zetaWeilPairingSummand]
  ring

/-- The real square family appearing on the RH diagonal. -/
def zetaWeilNormSqSummand
    (F : Complex -> Complex)
    (rho : PositiveOrdinateZetaZeroSubtype) : Real :=
  zetaZeroMultiplicityReal rho.1 *
    (norm (F (rho : Complex)) ^ 2 +
      norm (F (conj (rho : Complex))) ^ 2)

/-- On the critical line, the Weil functional reflection fixes the point. -/
theorem one_sub_conj_eq_self_of_isCriticalLine
    {s : Complex} (hs : IsCriticalLine s) :
    1 - conj s = s := by
  apply Complex.ext
  · simp [IsCriticalLine] at hs ⊢
    linarith
  · simp

/-- Under RH, each diagonal pairing summand is the corresponding weighted
sum of two squared norms. -/
theorem zetaWeilPairingSummand_self_eq_ofReal_normSq_of_RH
    (hRH : RHStatement) (F : Complex -> Complex)
    (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaWeilPairingSummand F F rho =
      (zetaWeilNormSqSummand F rho : Complex) := by
  have hrho : IsCriticalLine (rho : Complex) :=
    hRH (rho : Complex) (positiveOrdinateZetaZero_isNontrivial rho)
  have hconj : IsCriticalLine (conj (rho : Complex)) := by
    unfold IsCriticalLine at hrho ⊢
    simpa using hrho
  have hone_sub : 1 - (rho : Complex) = conj (rho : Complex) := by
    simpa using one_sub_conj_eq_self_of_isCriticalLine hconj
  rw [zetaWeilPairingSummand, zetaWeilNormSqSummand,
    one_sub_conj_eq_self_of_isCriticalLine hrho,
    hone_sub]
  rw [Complex.mul_conj', Complex.mul_conj']
  simp [zetaZeroMultiplicityReal]

/-- Under RH, square summability of a test gives convergence of its diagonal
Weil pairing. -/
theorem summable_zetaWeilPairingSummand_self_of_RH
    (hRH : RHStatement) (F : Complex -> Complex)
    (hF : Summable (zetaWeilNormSqSummand F)) :
    Summable (zetaWeilPairingSummand F F) := by
  rw [← Complex.summable_ofReal] at hF
  exact hF.congr (fun rho =>
    (zetaWeilPairingSummand_self_eq_ofReal_normSq_of_RH hRH F rho).symm)

/-- Under RH, the diagonal pairing is the real weighted square sum. -/
theorem zetaWeilPairing_self_eq_ofReal_tsum_of_RH
    (hRH : RHStatement) (F : Complex -> Complex) :
    zetaWeilPairing F F =
      ((∑' rho : PositiveOrdinateZetaZeroSubtype,
        zetaWeilNormSqSummand F rho : Real) : Complex) := by
  rw [zetaWeilPairing, Complex.ofReal_tsum]
  apply tsum_congr
  intro rho
  exact zetaWeilPairingSummand_self_eq_ofReal_normSq_of_RH hRH F rho

/-- Every convergent zeta Weil square has nonnegative real part under RH. -/
theorem zetaWeilPairing_self_re_nonneg_of_RH
    (hRH : RHStatement) (F : Complex -> Complex)
    (_hF : Summable (zetaWeilNormSqSummand F)) :
    0 <= (zetaWeilPairing F F).re := by
  rw [zetaWeilPairing_self_eq_ofReal_tsum_of_RH hRH F]
  simp only [Complex.ofReal_re]
  apply tsum_nonneg
  intro rho
  exact mul_nonneg (zetaZeroMultiplicityReal_pos rho.1).le
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
