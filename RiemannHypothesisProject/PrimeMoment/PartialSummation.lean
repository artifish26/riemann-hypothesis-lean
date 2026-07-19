import Mathlib.NumberTheory.AbelSummation
import RiemannHypothesisProject.PrimeMoment.PsiNormalization

/-!
# Finite partial summation for the Li prime moments

This module keeps the finite Abel-summation identity separate from the
asymptotic PNT estimate.  In particular, the divergent main term and the
finite-prime sum remain under the same natural cutoff.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open MeasureTheory
open scoped ArithmeticFunction Chebyshev

/-- The logarithmic weight in the `j`th Bombieri--Lagarias prime moment. -/
def liPrimeMomentWeight (j : Nat) (x : Real) : Real :=
  Real.log x ^ j / x

/-- The classical pointwise derivative of `liPrimeMomentWeight`. -/
def liPrimeMomentWeightDeriv (j : Nat) (x : Real) : Real :=
  ((j : Real) * Real.log x ^ (j - 1) - Real.log x ^ j) / x ^ 2

theorem hasDerivAt_liPrimeMomentWeight
    (j : Nat) {x : Real} (hx : x ≠ 0) :
    HasDerivAt (liPrimeMomentWeight j) (liPrimeMomentWeightDeriv j x) x := by
  unfold liPrimeMomentWeight liPrimeMomentWeightDeriv
  have h := ((Real.hasDerivAt_log hx).pow j).div (hasDerivAt_id x) hx
  apply h.congr_deriv
  simp only [id_eq, Pi.pow_apply]
  field_simp [hx]

theorem deriv_liPrimeMomentWeight
    (j : Nat) {x : Real} (hx : x ≠ 0) :
    deriv (liPrimeMomentWeight j) x = liPrimeMomentWeightDeriv j x :=
  (hasDerivAt_liPrimeMomentWeight j hx).deriv

theorem differentiableAt_liPrimeMomentWeight
    (j : Nat) {x : Real} (hx : x ≠ 0) :
    DifferentiableAt Real (liPrimeMomentWeight j) x :=
  (hasDerivAt_liPrimeMomentWeight j hx).differentiableAt

theorem continuousOn_deriv_liPrimeMomentWeight_Icc
    (j N : Nat) :
    ContinuousOn (deriv (liPrimeMomentWeight j))
      (Set.Icc (1 : Real) N) := by
  have hcontinuous : ContinuousOn (liPrimeMomentWeightDeriv j)
      (Set.Icc (1 : Real) N) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hx.1)
    exact (((continuousAt_const.mul
      ((Real.continuousAt_log hx0).pow (j - 1))).sub
        ((Real.continuousAt_log hx0).pow j)).div
          (continuousAt_id.pow 2) (pow_ne_zero 2 hx0)).continuousWithinAt
  refine hcontinuous.congr ?_
  intro x hx
  exact deriv_liPrimeMomentWeight j
    (ne_of_gt (zero_lt_one.trans_le hx.1))

theorem integrableOn_deriv_liPrimeMomentWeight_Icc
    (j N : Nat) :
    IntegrableOn (deriv (liPrimeMomentWeight j))
      (Set.Icc (1 : Real) N) := by
  exact (continuousOn_deriv_liPrimeMomentWeight_Icc j N).integrableOn_Icc

/-- An antiderivative of `x * w_j'(x)` on the positive half-line. -/
def liPrimeMomentMainAntiderivative (j : Nat) (x : Real) : Real :=
  x * liPrimeMomentWeight j x - Real.log x ^ (j + 1) / (j + 1)

theorem hasDerivAt_liPrimeMomentMainAntiderivative
    (j : Nat) {x : Real} (hx : x ≠ 0) :
    HasDerivAt (liPrimeMomentMainAntiderivative j)
      (liPrimeMomentWeightDeriv j x * x) x := by
  unfold liPrimeMomentMainAntiderivative
  have hw := hasDerivAt_liPrimeMomentWeight j hx
  have hlog := ((Real.hasDerivAt_log hx).pow (j + 1)).div_const
    (j + 1 : Real)
  have h := ((hasDerivAt_id x).mul hw).sub hlog
  apply h.congr_deriv
  simp only [id_eq, Nat.cast_add, Nat.cast_one, liPrimeMomentWeight,
    Nat.add_sub_cancel_right]
  field_simp [hx, Nat.cast_add_one_ne_zero]
  ring

/-- Exact evaluation of the main-term integral in the finite Abel identity. -/
theorem integral_deriv_liPrimeMomentWeight_mul_id
    (j N : Nat) (hN : 1 ≤ N) :
    (∫ t in Set.Ioc (1 : Real) N,
      deriv (liPrimeMomentWeight j) t * t) =
        liPrimeMomentMainAntiderivative j N -
          liPrimeMomentMainAntiderivative j 1 := by
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hderiv : ∀ x ∈ Set.uIcc (1 : Real) N,
      HasDerivAt (liPrimeMomentMainAntiderivative j)
        (deriv (liPrimeMomentWeight j) x * x) x := by
    intro x hx
    rw [Set.uIcc_of_le hNreal] at hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hx.1)
    convert hasDerivAt_liPrimeMomentMainAntiderivative j hx0 using 1
    rw [deriv_liPrimeMomentWeight j hx0]
  have hint : IntervalIntegrable
      (fun t => deriv (liPrimeMomentWeight j) t * t) volume 1 N := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNreal]
    exact (integrableOn_deriv_liPrimeMomentWeight_Icc j N).mul_continuousOn
      continuousOn_id isCompact_Icc
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rwa [intervalIntegral.integral_of_le hNreal] at h

/-- Abel summation at a natural cutoff, with the summatory von Mangoldt
function normalized exactly to Mathlib's `Chebyshev.psi`. -/
theorem liPrimeMomentCutoff_eq_endpoint_sub_integral
    (j N : Nat) :
    liPrimeMomentCutoff j N =
      liPrimeMomentWeight j N * Chebyshev.psi (N : Real) -
        ∫ t in Set.Ioc (1 : Real) N,
          deriv (liPrimeMomentWeight j) t * Chebyshev.psi t := by
  have hdiff : ∀ t ∈ Set.Icc (1 : Real) N,
      DifferentiableAt Real (liPrimeMomentWeight j) t := by
    intro t ht
    exact differentiableAt_liPrimeMomentWeight j
      (ne_of_gt (zero_lt_one.trans_le ht.1))
  have hab := sum_mul_eq_sub_integral_mul₀'
    (c := fun n => ArithmeticFunction.vonMangoldt n)
    (f := liPrimeMomentWeight j) (by simp) N hdiff
    (integrableOn_deriv_liPrimeMomentWeight_Icc j N)
  have hcut : liPrimeMomentCutoff j N =
      ∑ k ∈ Finset.Icc 0 N,
        liPrimeMomentWeight j k * ArithmeticFunction.vonMangoldt k := by
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le N), Finset.sum_cons]
    simp only [liPrimeMomentCutoff, liPrimeMomentWeight,
      ArithmeticFunction.map_zero, mul_zero, zero_add]
    rw [← Finset.Icc_add_one_left_eq_Ioc]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hpsi_nat :
      (∑ k ∈ Finset.Icc 0 N, ArithmeticFunction.vonMangoldt k) =
        Chebyshev.psi (N : Real) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [hpsi_nat] at hab
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hab
  exact hcut.trans hab

/-- The PNT remainder used in the convergent part of partial summation. -/
def liPrimeMomentPNTError (x : Real) : Real :=
  Chebyshev.psi x - x

theorem integrableOn_liPrimeMomentPNTError_Icc
    (N : Nat) (hN : 1 ≤ N) :
    IntegrableOn liPrimeMomentPNTError (Set.Icc (1 : Real) N) := by
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hpsi : IntegrableOn Chebyshev.psi (Set.Icc (1 : Real) N) := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hNreal]
    exact Chebyshev.psi_mono.intervalIntegrable
  exact hpsi.sub continuousOn_id.integrableOn_Icc

/-- The finite Abel identity after exact cancellation of the logarithmic main
term.  Only one endpoint error and one weighted error integral remain. -/
theorem liPrimeMomentRemainder_eq_error
    (j N : Nat) (hN : 1 ≤ N) :
    liPrimeMomentRemainder j N =
      liPrimeMomentWeight j 1 +
        liPrimeMomentWeight j N * liPrimeMomentPNTError N -
          ∫ t in Set.Ioc (1 : Real) N,
            deriv (liPrimeMomentWeight j) t * liPrimeMomentPNTError t := by
  have hmain : IntegrableOn
      (fun t => deriv (liPrimeMomentWeight j) t * t)
      (Set.Ioc (1 : Real) N) :=
    ((integrableOn_deriv_liPrimeMomentWeight_Icc j N).mul_continuousOn
      continuousOn_id isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have herr : IntegrableOn
      (fun t => deriv (liPrimeMomentWeight j) t * liPrimeMomentPNTError t)
      (Set.Ioc (1 : Real) N) :=
    ((integrableOn_liPrimeMomentPNTError_Icc N hN).continuousOn_mul
      (continuousOn_deriv_liPrimeMomentWeight_Icc j N)
      isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hsplit :
      (∫ t in Set.Ioc (1 : Real) N,
        deriv (liPrimeMomentWeight j) t * Chebyshev.psi t) =
          (∫ t in Set.Ioc (1 : Real) N,
            deriv (liPrimeMomentWeight j) t * t) +
          ∫ t in Set.Ioc (1 : Real) N,
            deriv (liPrimeMomentWeight j) t * liPrimeMomentPNTError t := by
    rw [← MeasureTheory.integral_add hmain herr]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [liPrimeMomentPNTError]
    ring
  rw [liPrimeMomentRemainder,
    liPrimeMomentCutoff_eq_endpoint_sub_integral, hsplit,
    integral_deriv_liPrimeMomentWeight_mul_id j N hN]
  simp only [liPrimeMomentMainAntiderivative, liPrimeMomentPNTError]
  have hcast : (N : Real) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  rw [show Chebyshev.psi (N : Real) =
      (N : Real) + (Chebyshev.psi (N : Real) - N) by ring]
  simp only [liPrimeMomentWeight, Real.log_one, zero_pow (Nat.succ_ne_zero j),
    zero_div, sub_zero, one_mul]
  field_simp [hcast, Nat.cast_add_one_ne_zero]
  ring

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
