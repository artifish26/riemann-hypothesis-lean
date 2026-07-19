import RiemannHypothesisProject.SchwartzExplicitFormula
import RiemannHypothesisProject.FiniteZeroWindow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Schwartz finite zero windows

This file introduces the first concrete zero-side approximation for the
explicit-formula track.

For a finite zero window `zeroes : Finset ℂ`, we sample a Schwartz test function
at the imaginary parts of the candidate zeroes and form the finite nonnegative
sum

`∑ ρ ∈ zeroes, ‖f ρ.im‖ ^ 2`.

This is not the Riemann-Weil zero side, but it is the first checked bridge from
Schwartz test functions to a zero-indexed side with a summability statement.
-/

namespace RiemannHypothesisProject

/-- Finite-window zero-side sampling energy for Schwartz test functions. -/
noncomputable def schwartzZeroWindowEnergy
    (zeroes : Finset ℂ) (f : SchwartzLineTestFunction) : ℝ :=
  zeroes.sum fun rho => ‖f (Complex.im rho)‖ ^ 2

/-- Finite-window zero-side sampling energy is nonnegative. -/
theorem schwartzZeroWindowEnergy_nonneg
    (zeroes : Finset ℂ) (f : SchwartzLineTestFunction) :
    0 ≤ schwartzZeroWindowEnergy zeroes f := by
  unfold schwartzZeroWindowEnergy
  exact Finset.sum_nonneg fun rho _ => sq_nonneg ‖f (Complex.im rho)‖

/--
The all-complex-number weight associated to a finite zero window.

It is zero outside the finite window and agrees with the sampling energy
integrand inside the window.
-/
noncomputable def schwartzZeroWindowWeight
    (zeroes : Finset ℂ) (f : SchwartzLineTestFunction) (rho : ℂ) : ℝ :=
  if rho ∈ zeroes then ‖f (Complex.im rho)‖ ^ 2 else 0

/-- The finite-window zero weight has finite support. -/
theorem schwartzZeroWindowWeight_hasFiniteSupport
    (zeroes : Finset ℂ) (f : SchwartzLineTestFunction) :
    (schwartzZeroWindowWeight zeroes f).HasFiniteSupport := by
  classical
  unfold Function.HasFiniteSupport
  refine zeroes.finite_toSet.subset ?_
  intro rho hrho_support
  by_contra hrho_not_mem
  have hweight_zero : schwartzZeroWindowWeight zeroes f rho = 0 := by
    have hrho_not_mem_finset : rho ∉ zeroes := by
      simpa using hrho_not_mem
    simp [schwartzZeroWindowWeight, hrho_not_mem_finset]
  exact hrho_support hweight_zero

/-- The finite-window zero weight is summable as a function over all complex numbers. -/
theorem schwartzZeroWindowWeight_summable
    (zeroes : Finset ℂ) (f : SchwartzLineTestFunction) :
    Summable (schwartzZeroWindowWeight zeroes f) :=
  summable_of_hasFiniteSupport
    (schwartzZeroWindowWeight_hasFiniteSupport zeroes f)

/-- The infinite sum of the finite-window zero weight is the finite sampling energy. -/
theorem schwartzZeroWindowWeight_tsum_eq_energy
    (zeroes : Finset ℂ) (f : SchwartzLineTestFunction) :
    (∑' ρ : ℂ, schwartzZeroWindowWeight zeroes f ρ) =
      schwartzZeroWindowEnergy zeroes f := by
  classical
  calc
    (∑' rho : ℂ, schwartzZeroWindowWeight zeroes f rho)
        = zeroes.sum (schwartzZeroWindowWeight zeroes f) := by
          refine tsum_eq_sum (s := zeroes) ?_
          intro rho hrho_not_mem
          have hrho_not_mem_finset : rho ∉ zeroes := by
            simpa using hrho_not_mem
          simp [schwartzZeroWindowWeight, hrho_not_mem_finset]
    _ = schwartzZeroWindowEnergy zeroes f := by
          simp [schwartzZeroWindowWeight, schwartzZeroWindowEnergy]

/--
A finite-zero-window local criterion using Schwartz test functions and the
finite zero-side sampling energy.

The explicit formula is still a finite-window toy identity: the same finite
zero-side is placed on the prime side. The local RH conclusion comes from the
finite zero-window certificate, not from the toy identity.
-/
noncomputable def schwartzZeroWindowLocalCriterion
    {family : ℂ → Prop}
    (certificate : FiniteZeroWindowCertificate family) :
    SchwartzExplicitFormulaLocalCriterion family where
  zeroSide := schwartzZeroWindowEnergy certificate.zeroes
  primeSide := schwartzZeroWindowEnergy certificate.zeroes
  poleSide := fun _ => 0
  gammaSide := fun _ => 0
  explicitFormula := by
    intro f
    simp
  quadraticForm := schwartzZeroWindowEnergy certificate.zeroes
  quadraticForm_eq_zeroSide := by
    intro f
    rfl
  positivity_implies_RHOn := fun _ =>
    RHOn.of_finiteZeroWindowCertificate certificate

/--
The finite-zero-window Schwartz criterion proves RH on the certified family.
-/
theorem RHOn.of_schwartzZeroWindowLocalCriterion
    {family : ℂ → Prop}
    (certificate : FiniteZeroWindowCertificate family) :
    RHOn family :=
  RHOn.of_schwartzExplicitFormulaLocalCriterion
    (schwartzZeroWindowLocalCriterion certificate)
    (schwartzZeroWindowEnergy_nonneg certificate.zeroes)

end RiemannHypothesisProject
