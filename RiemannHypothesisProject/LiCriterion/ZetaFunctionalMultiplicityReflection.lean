import RiemannHypothesisProject.LiCriterion.ZetaFunctionalReflection
import RiemannHypothesisProject.GuinandWeilConcrete.XiDivisor

/-!
# Multiplicity-preserving functional reflection of zeta zeros

The Weil involution on a zero is `rho ↦ 1 - conj rho`.  This module proves
that it is an involutive equivalence of the positive-ordinate zero family and
that it preserves analytic multiplicity.  The multiplicity proof is reduced
to the checked xi divisor normalization and the nonvanishing derivative of
`z ↦ 1 - z`.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

open ComplexConjugate

noncomputable section

/-- Xi has the same analytic order at functionally reflected points. -/
theorem analyticOrderAt_riemannXi_one_sub (rho : Complex) :
    analyticOrderAt riemannXi (1 - rho) = analyticOrderAt riemannXi rho := by
  let reflect : Complex -> Complex := fun z => 1 - z
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero
    (f := riemannXi) (g := reflect) (z₀ := rho)
    (by fun_prop) (by simp [reflect])
  have hfun : riemannXi ∘ reflect = riemannXi := by
    funext z
    exact riemannXi_one_sub z
  rw [hfun] at hcomp
  simpa [reflect] using hcomp.symm

/-- Functional reflection preserves the analytic multiplicity of every
nontrivial zeta zero. -/
theorem zetaZeroMultiplicity_one_sub
    (rho : ZetaZeroSubtype)
    (hrho : IsNontrivialZetaZero (rho : Complex)) :
    zetaZeroMultiplicity
        ⟨1 - (rho : Complex), (isNontrivialZetaZero_one_sub hrho).1⟩ =
      zetaZeroMultiplicity rho := by
  have hleft :=
    analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
      ⟨1 - (rho : Complex), (isNontrivialZetaZero_one_sub hrho).1⟩
      (isNontrivialZetaZero_one_sub hrho).2.1
  have hright :=
    analyticOrderAt_riemannXi_eq_zetaZeroMultiplicity_of_not_trivial
      rho hrho.2.1
  rw [← ENat.coe_inj]
  rw [← hleft, ← hright]
  exact analyticOrderAt_riemannXi_one_sub (rho : Complex)

/-- The conjugate of a positive-ordinate zeta zero is nontrivial. -/
theorem positiveOrdinateZetaZero_conj_isNontrivial
    (rho : PositiveOrdinateZetaZeroSubtype) :
    IsNontrivialZetaZero (conj (rho : Complex)) := by
  refine ⟨zetaZeroConjugationSymmetry (rho : Complex) rho.1.property, ?_, ?_⟩
  · exact not_isTrivialZetaZero_of_im_ne_zero (by
      simpa using ne_of_gt rho.2)
  · intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt rho.2) him

/-- A positive-ordinate zeta zero is nontrivial. -/
theorem positiveOrdinateZetaZero_isNontrivial
    (rho : PositiveOrdinateZetaZeroSubtype) :
    IsNontrivialZetaZero (rho : Complex) := by
  refine ⟨rho.1.property, ?_, ?_⟩
  · exact not_isTrivialZetaZero_of_im_ne_zero (ne_of_gt rho.2)
  · intro h
    have him := congrArg Complex.im h
    simp at him
    exact (ne_of_gt rho.2) him

/-- Functional reflection restricted to positive-ordinate zeta zeros. -/
def positiveOrdinateZetaZeroFunctionalReflection
    (rho : PositiveOrdinateZetaZeroSubtype) :
    PositiveOrdinateZetaZeroSubtype :=
  ⟨⟨1 - conj (rho : Complex),
      (isNontrivialZetaZero_one_sub
        (positiveOrdinateZetaZero_conj_isNontrivial rho)).1⟩,
    by simpa using rho.2⟩

@[simp]
theorem positiveOrdinateZetaZeroFunctionalReflection_value
    (rho : PositiveOrdinateZetaZeroSubtype) :
    (positiveOrdinateZetaZeroFunctionalReflection rho : Complex) =
      1 - conj (rho : Complex) :=
  rfl

@[simp]
theorem positiveOrdinateZetaZeroFunctionalReflection_involutive
    (rho : PositiveOrdinateZetaZeroSubtype) :
    positiveOrdinateZetaZeroFunctionalReflection
        (positiveOrdinateZetaZeroFunctionalReflection rho) = rho := by
  ext
  simp [positiveOrdinateZetaZeroFunctionalReflection]

/-- The Weil functional reflection as an equivalence of positive-ordinate
zeta zeros. -/
def positiveOrdinateZetaZeroFunctionalReflectionEquiv :
    PositiveOrdinateZetaZeroSubtype ≃ PositiveOrdinateZetaZeroSubtype where
  toFun := positiveOrdinateZetaZeroFunctionalReflection
  invFun := positiveOrdinateZetaZeroFunctionalReflection
  left_inv := positiveOrdinateZetaZeroFunctionalReflection_involutive
  right_inv := positiveOrdinateZetaZeroFunctionalReflection_involutive

/-- The positive-ordinate functional reflection preserves analytic
multiplicity. -/
theorem zetaZeroMultiplicity_positiveOrdinateFunctionalReflection
    (rho : PositiveOrdinateZetaZeroSubtype) :
    zetaZeroMultiplicity
        (positiveOrdinateZetaZeroFunctionalReflection rho).1 =
      zetaZeroMultiplicity rho.1 := by
  let rhoConj : ZetaZeroSubtype :=
    ⟨conj (rho : Complex),
      zetaZeroConjugationSymmetry (rho : Complex) rho.1.property⟩
  calc
    zetaZeroMultiplicity
        (positiveOrdinateZetaZeroFunctionalReflection rho).1 =
        zetaZeroMultiplicity rhoConj := by
      simpa [rhoConj, positiveOrdinateZetaZeroFunctionalReflection] using
        zetaZeroMultiplicity_one_sub rhoConj
          (positiveOrdinateZetaZero_conj_isNontrivial rho)
    _ = zetaZeroMultiplicity rho.1 := by
      simpa [rhoConj] using zetaZeroMultiplicity_conj rho.1

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
