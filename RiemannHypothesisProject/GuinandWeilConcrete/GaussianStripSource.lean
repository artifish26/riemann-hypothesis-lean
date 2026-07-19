import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Gaussian strip source estimates

This module records proof-bearing estimates for the concrete entire Gaussian
source `z |-> exp (-z^2)`.  These are not receiving-surface or normalization
bridges: they are direct analytic facts about an actual strip-admissible source
test.
-/

namespace RiemannHypothesisProject

open Filter
open scoped FourierTransform Pointwise BigOperators ComplexConjugate

noncomputable section

/-- The basic entire Gaussian source used for strip-estimate experiments. -/
def guinandWeilGaussianSource (z : Complex) : Complex :=
  Complex.exp (-(z * z))

/--
The `pi`-normalized Gaussian source.  This is the Fourier self-reciprocal
normalization for mathlib's real-line Fourier transform convention.
-/
def guinandWeilPiGaussianSource (z : Complex) : Complex :=
  Complex.exp (-(Real.pi : Complex) * (z * z))

/-- The Gaussian source is entire. -/
theorem differentiable_guinandWeilGaussianSource :
    Differentiable Complex guinandWeilGaussianSource := by
  unfold guinandWeilGaussianSource
  fun_prop

/-- The `pi`-normalized Gaussian source is entire. -/
theorem differentiable_guinandWeilPiGaussianSource :
    Differentiable Complex guinandWeilPiGaussianSource := by
  unfold guinandWeilPiGaussianSource
  fun_prop

/-- The Gaussian source is entire in the analytic sense. -/
theorem analyticOnNhd_guinandWeilGaussianSource :
    AnalyticOnNhd Complex guinandWeilGaussianSource Set.univ := by
  intro z _hz
  exact differentiable_guinandWeilGaussianSource.analyticAt z

/-- The `pi`-normalized Gaussian source is entire in the analytic sense. -/
theorem analyticOnNhd_guinandWeilPiGaussianSource :
    AnalyticOnNhd Complex guinandWeilPiGaussianSource Set.univ := by
  intro z _hz
  exact differentiable_guinandWeilPiGaussianSource.analyticAt z

/--
The `pi`-normalized Gaussian source is analytic on every horizontal strip.
This is the source-side holomorphy hypothesis used by Guinand-Weil test
classes, stated without packaging it into an endpoint record.
-/
theorem analyticOnNhd_guinandWeilPiGaussianSource_horizontalStrip
    (A : Real) :
    AnalyticOnNhd Complex guinandWeilPiGaussianSource
      {z : Complex | abs z.im <= A} := by
  exact analyticOnNhd_guinandWeilPiGaussianSource.mono (by intro z _hz; simp)

/--
The closed-form Fourier-side horizontal-line extension of the `pi`-normalized
Gaussian source is entire.
-/
theorem analyticOnNhd_fourier_guinandWeilPiGaussianSource_horizontalLineExtension
    (y : Real) :
    AnalyticOnNhd Complex
      (fun z : Complex =>
        Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
          guinandWeilPiGaussianSource (z + (y : Complex)))
      Set.univ := by
  have hd :
      Differentiable Complex
        (fun z : Complex =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource (z + (y : Complex))) := by
    have haffine :
        Differentiable Complex (fun z : Complex => z + (y : Complex)) := by
      fun_prop
    exact
      (differentiable_guinandWeilPiGaussianSource.comp haffine).const_mul
        (Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2))
  intro z _hz
  exact hd.analyticAt z

/--
The closed-form Fourier-side horizontal-line extension is analytic on every
horizontal strip.
-/
theorem analyticOnNhd_fourier_guinandWeilPiGaussianSource_horizontalLineExtension_horizontalStrip
    (A y : Real) :
    AnalyticOnNhd Complex
      (fun z : Complex =>
        Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
          guinandWeilPiGaussianSource (z + (y : Complex)))
      {z : Complex | abs z.im <= A} := by
  exact
    (analyticOnNhd_fourier_guinandWeilPiGaussianSource_horizontalLineExtension y).mono
      (by intro z _hz; simp)

/-- The Gaussian source has no complex zeroes. -/
theorem guinandWeilGaussianSource_ne_zero
    (z : Complex) :
    guinandWeilGaussianSource z ≠ 0 := by
  simp [guinandWeilGaussianSource, Complex.exp_ne_zero]

/-- The `pi`-normalized Gaussian source has no complex zeroes. -/
theorem guinandWeilPiGaussianSource_ne_zero
    (z : Complex) :
    guinandWeilPiGaussianSource z ≠ 0 := by
  simp [guinandWeilPiGaussianSource, Complex.exp_ne_zero]

/-- The norm of the `pi`-normalized Gaussian source is strictly positive. -/
theorem norm_guinandWeilPiGaussianSource_pos
    (z : Complex) :
    0 < norm (guinandWeilPiGaussianSource z) :=
  norm_pos_iff.mpr (guinandWeilPiGaussianSource_ne_zero z)

/--
The `pi`-normalized Gaussian is real-normalized: it commutes with complex
conjugation.
-/
theorem guinandWeilPiGaussianSource_conj
    (z : Complex) :
    guinandWeilPiGaussianSource (conj z) =
      conj (guinandWeilPiGaussianSource z) := by
  unfold guinandWeilPiGaussianSource
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul]

/-- The `pi`-normalized Gaussian is real-valued on the real axis. -/
theorem guinandWeilPiGaussianSource_ofReal_im
    (x : Real) :
    (guinandWeilPiGaussianSource (x : Complex)).im = 0 := by
  have h := guinandWeilPiGaussianSource_conj (x : Complex)
  have hconj :
      conj (guinandWeilPiGaussianSource (x : Complex)) =
        guinandWeilPiGaussianSource (x : Complex) := by
    simpa using h.symm
  exact Complex.conj_eq_iff_im.mp hconj

/-- The `pi`-normalized Gaussian is even. -/
theorem guinandWeilPiGaussianSource_neg
    (z : Complex) :
    guinandWeilPiGaussianSource (-z) = guinandWeilPiGaussianSource z := by
  unfold guinandWeilPiGaussianSource
  congr 1
  ring

/-- The real-line `pi`-normalized Gaussian is even. -/
theorem guinandWeilPiGaussianSource_ofReal_neg
    (x : Real) :
    guinandWeilPiGaussianSource ((-x : Real) : Complex) =
      guinandWeilPiGaussianSource (x : Complex) := by
  simpa using guinandWeilPiGaussianSource_neg (x : Complex)

/-- Derivative of the `pi`-normalized Gaussian source. -/
theorem deriv_guinandWeilPiGaussianSource
    (z : Complex) :
    deriv guinandWeilPiGaussianSource z =
      (-(2 : Complex) * (Real.pi : Complex) * z) *
        guinandWeilPiGaussianSource z := by
  unfold guinandWeilPiGaussianSource
  rw [deriv_cexp]
  · have hderiv :
        deriv (fun w : Complex => -(Real.pi : Complex) * (w * w)) z =
          -(2 : Complex) * (Real.pi : Complex) * z := by
      rw [deriv_const_mul]
      · have hsq : (fun w : Complex => w * w) = fun w : Complex => w ^ 2 := by
          funext w
          ring
        rw [hsq, deriv_pow_field]
        ring
      · fun_prop
    rw [hderiv]
    ring
  · fun_prop

/--
The first derivative of the `pi`-normalized Gaussian is bounded by one
extra shifted-radius power times the source itself.
-/
theorem norm_deriv_guinandWeilPiGaussianSource_le
    (z : Complex) :
    norm (deriv guinandWeilPiGaussianSource z) <=
      (2 * Real.pi) * norm z * norm (guinandWeilPiGaussianSource z) := by
  rw [deriv_guinandWeilPiGaussianSource]
  rw [norm_mul, norm_mul, norm_mul]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_pos.le]

/--
The polynomial factor multiplying the `pi`-Gaussian after taking `m` complex
derivatives.  It is the Hermite-type recurrence
`P_{m+1} = P'_m - 2*pi*X*P_m` in the project's Fourier normalization.
-/
def guinandWeilPiGaussianDerivativeRealPolynomial : Nat -> Polynomial Real
  | 0 => 1
  | m + 1 =>
      (guinandWeilPiGaussianDerivativeRealPolynomial m).derivative -
        Polynomial.C (2 * Real.pi) *
          Polynomial.X * guinandWeilPiGaussianDerivativeRealPolynomial m

def guinandWeilPiGaussianDerivativePolynomial : Nat -> Polynomial Complex
  | 0 => 1
  | m + 1 =>
      (guinandWeilPiGaussianDerivativePolynomial m).derivative -
        Polynomial.C ((2 : Complex) * (Real.pi : Complex)) *
          Polynomial.X * guinandWeilPiGaussianDerivativePolynomial m

/--
The complex Hermite-type derivative factors are the scalar extension of the
real-coefficient factors.
-/
theorem guinandWeilPiGaussianDerivativePolynomial_eq_map_real
    (m : Nat) :
    guinandWeilPiGaussianDerivativePolynomial m =
      (guinandWeilPiGaussianDerivativeRealPolynomial m).map
        (algebraMap Real Complex) := by
  induction m with
  | zero =>
      simp [guinandWeilPiGaussianDerivativePolynomial,
        guinandWeilPiGaussianDerivativeRealPolynomial]
  | succ m ih =>
      simp [guinandWeilPiGaussianDerivativePolynomial,
        guinandWeilPiGaussianDerivativeRealPolynomial, ih,
        Polynomial.derivative_map, mul_assoc]

/--
The real-coefficient Hermite factors respect complex conjugation after
evaluation.
-/
theorem guinandWeilPiGaussianDerivativePolynomial_aeval_conj
    (m : Nat) (z : Complex) :
    (guinandWeilPiGaussianDerivativePolynomial m).aeval (conj z) =
      conj
        ((guinandWeilPiGaussianDerivativePolynomial m).aeval z) := by
  rw [guinandWeilPiGaussianDerivativePolynomial_eq_map_real m]
  simpa using
    (Polynomial.aeval_conj
      (guinandWeilPiGaussianDerivativeRealPolynomial m) z)

/--
Every finite complex derivative of the `pi`-Gaussian is a polynomial factor
times the same Gaussian.
-/
theorem iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial
    (m : Nat) (z : Complex) :
    iteratedDeriv m guinandWeilPiGaussianSource z =
      (guinandWeilPiGaussianDerivativePolynomial m).aeval z *
        guinandWeilPiGaussianSource z := by
  induction m generalizing z with
  | zero =>
      simp [guinandWeilPiGaussianDerivativePolynomial]
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv m guinandWeilPiGaussianSource =
            fun w : Complex =>
              (guinandWeilPiGaussianDerivativePolynomial m).aeval w *
              guinandWeilPiGaussianSource w := by
        funext w
        exact ih w
      rw [hfun]
      change
        deriv
            ((fun w : Complex =>
                (guinandWeilPiGaussianDerivativePolynomial m).aeval w) *
              guinandWeilPiGaussianSource) z =
          (guinandWeilPiGaussianDerivativePolynomial (m + 1)).aeval z *
            guinandWeilPiGaussianSource z
      rw [deriv_mul
        (Polynomial.differentiableAt_aeval
          (guinandWeilPiGaussianDerivativePolynomial m))
        (differentiable_guinandWeilPiGaussianSource.differentiableAt)]
      rw [Polynomial.deriv_aeval, deriv_guinandWeilPiGaussianSource]
      simp [guinandWeilPiGaussianDerivativePolynomial, mul_assoc, mul_left_comm,
        mul_comm, sub_eq_add_neg]
      ring

/--
Every finite complex derivative of the `pi`-normalized Gaussian respects
complex conjugation.
-/
theorem iteratedDeriv_guinandWeilPiGaussianSource_conj
    (m : Nat) (z : Complex) :
    iteratedDeriv m guinandWeilPiGaussianSource (conj z) =
      conj (iteratedDeriv m guinandWeilPiGaussianSource z) := by
  rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial,
    iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial]
  rw [guinandWeilPiGaussianDerivativePolynomial_aeval_conj,
    guinandWeilPiGaussianSource_conj]
  simp [map_mul]

/--
Every finite complex derivative of the `pi`-normalized Gaussian is real-valued
on the real axis.
-/
theorem iteratedDeriv_guinandWeilPiGaussianSource_ofReal_im
    (m : Nat) (x : Real) :
    (iteratedDeriv m guinandWeilPiGaussianSource (x : Complex)).im = 0 := by
  have h := iteratedDeriv_guinandWeilPiGaussianSource_conj m (x : Complex)
  have hconj :
      conj (iteratedDeriv m guinandWeilPiGaussianSource (x : Complex)) =
        iteratedDeriv m guinandWeilPiGaussianSource (x : Complex) := by
    simpa using h.symm
  exact Complex.conj_eq_iff_im.mp hconj

/--
Every finite complex derivative of the `pi`-normalized Gaussian has the parity
forced by the even source.
-/
theorem iteratedDeriv_guinandWeilPiGaussianSource_neg
    (m : Nat) (z : Complex) :
    iteratedDeriv m guinandWeilPiGaussianSource (-z) =
      (-1 : Complex) ^ m *
        iteratedDeriv m guinandWeilPiGaussianSource z := by
  have hfun :
      (fun w : Complex => guinandWeilPiGaussianSource (-w)) =
        guinandWeilPiGaussianSource := by
    funext w
    exact guinandWeilPiGaussianSource_neg w
  calc
    iteratedDeriv m guinandWeilPiGaussianSource (-z)
        = iteratedDeriv m
            (fun w : Complex => guinandWeilPiGaussianSource (-w)) (-z) := by
            rw [hfun]
    _ = (-1 : Complex) ^ m •
          iteratedDeriv m guinandWeilPiGaussianSource (-(-z)) :=
        iteratedDeriv_comp_neg m guinandWeilPiGaussianSource (-z)
    _ = (-1 : Complex) ^ m *
          iteratedDeriv m guinandWeilPiGaussianSource z := by
        simp [smul_eq_mul]

/--
The real-line finite derivatives of the `pi`-normalized Gaussian have the
expected `(-1)^m` parity.
-/
theorem iteratedDeriv_guinandWeilPiGaussianSource_ofReal_neg
    (m : Nat) (x : Real) :
    iteratedDeriv m guinandWeilPiGaussianSource ((-x : Real) : Complex) =
      (-1 : Complex) ^ m *
        iteratedDeriv m guinandWeilPiGaussianSource (x : Complex) := by
  simpa using iteratedDeriv_guinandWeilPiGaussianSource_neg m (x : Complex)

/--
The Hermite-type polynomial factor multiplying the `m`th Gaussian derivative
has the same `(-1)^m` parity.
-/
theorem guinandWeilPiGaussianDerivativePolynomial_aeval_neg
    (m : Nat) (z : Complex) :
    (guinandWeilPiGaussianDerivativePolynomial m).aeval (-z) =
      (-1 : Complex) ^ m *
        (guinandWeilPiGaussianDerivativePolynomial m).aeval z := by
  have h :=
    iteratedDeriv_guinandWeilPiGaussianSource_neg m z
  rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial,
    iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial,
    guinandWeilPiGaussianSource_neg] at h
  have hmul :
      (guinandWeilPiGaussianDerivativePolynomial m).aeval (-z) *
          guinandWeilPiGaussianSource z =
        ((-1 : Complex) ^ m *
            (guinandWeilPiGaussianDerivativePolynomial m).aeval z) *
          guinandWeilPiGaussianSource z := by
    simpa [mul_assoc] using h
  exact mul_right_cancel₀ (guinandWeilPiGaussianSource_ne_zero z) hmul

/--
Every finite complex derivative of the closed-form Fourier-side horizontal-line
extension is the same Hermite-type polynomial factor, evaluated at the shifted
source argument, times the closed-form source.
-/
theorem iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_eq_derivativePolynomial
    (m : Nat) (y : Real) (z : Complex) :
    iteratedDeriv m
        (fun w : Complex =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource (w + (y : Complex)))
        z =
      Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
        ((guinandWeilPiGaussianDerivativePolynomial m).aeval
            (z + (y : Complex)) *
          guinandWeilPiGaussianSource (z + (y : Complex))) := by
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_add_const]
  change
    Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
        iteratedDeriv m guinandWeilPiGaussianSource (z + (y : Complex)) =
      Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
        ((guinandWeilPiGaussianDerivativePolynomial m).aeval
            (z + (y : Complex)) *
          guinandWeilPiGaussianSource (z + (y : Complex)))
  rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial]

/--
Norm form of the all-order derivative formula for the closed-form Fourier-side
horizontal-line extension.
-/
theorem norm_iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource
    (m : Nat) (y : Real) (z : Complex) :
    norm (iteratedDeriv m
        (fun w : Complex =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource (w + (y : Complex)))
        z) =
      norm (Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2)) *
        norm ((guinandWeilPiGaussianDerivativePolynomial m).aeval
          (z + (y : Complex))) *
        norm (guinandWeilPiGaussianSource (z + (y : Complex))) := by
  rw [iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_eq_derivativePolynomial]
  rw [norm_mul, norm_mul]
  ring

/--
Every finite complex derivative of the closed-form Fourier-side
horizontal-line extension respects complex conjugation.
-/
theorem iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_conj
    (m : Nat) (y : Real) (z : Complex) :
    iteratedDeriv m
        (fun w : Complex =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource (w + (y : Complex)))
        (conj z) =
      conj
        (iteratedDeriv m
          (fun w : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (w + (y : Complex)))
          z) := by
  let c : Complex := Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2)
  have hc : conj c = c := by
    dsimp [c]
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hleft :
      iteratedDeriv m
          (fun w : Complex =>
            c * guinandWeilPiGaussianSource (w + (y : Complex)))
          (conj z) =
        c * iteratedDeriv m guinandWeilPiGaussianSource
          (conj z + (y : Complex)) := by
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_add_const]
  have hright :
      iteratedDeriv m
          (fun w : Complex =>
            c * guinandWeilPiGaussianSource (w + (y : Complex)))
          z =
        c * iteratedDeriv m guinandWeilPiGaussianSource
          (z + (y : Complex)) := by
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_add_const]
  have harg :
      conj z + (y : Complex) = conj (z + (y : Complex)) := by
    simp [map_add]
  dsimp [c] at hleft hright ⊢
  rw [hleft, hright, map_mul, hc, harg,
    iteratedDeriv_guinandWeilPiGaussianSource_conj]

/--
Every finite complex derivative of the closed-form Fourier-side
horizontal-line extension is real-valued on the real axis.
-/
theorem iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_ofReal_im
    (m : Nat) (y x : Real) :
    (iteratedDeriv m
        (fun z : Complex =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource (z + (y : Complex)))
        (x : Complex)).im = 0 := by
  have h :=
    iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_conj
      m y (x : Complex)
  have hconj :
      conj
          (iteratedDeriv m
            (fun z : Complex =>
              Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
                guinandWeilPiGaussianSource (z + (y : Complex)))
            (x : Complex)) =
        iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          (x : Complex) := by
    simpa using h.symm
  exact Complex.conj_eq_iff_im.mp hconj

/--
A fixed complex polynomial has polynomial growth in the shifted complex radius.
This is the finite-dimensional algebraic input used to turn the Hermite
derivative identity into strip-decay estimates.
-/
theorem exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow
    (p : Polynomial Complex) :
    ∃ C : Real, 0 < C ∧ ∀ z : Complex,
      norm (p.aeval z) <= C * (norm z + 2) ^ p.natDegree := by
  let C0 : Real :=
    ∑ i ∈ Finset.range (p.natDegree + 1), norm (p.coeff i)
  have hC0_nonneg : 0 <= C0 := by
    exact Finset.sum_nonneg fun i _hi => norm_nonneg (p.coeff i)
  refine ⟨C0 + 1, by linarith, ?_⟩
  intro z
  let R : Real := norm z + 2
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hR_one : 1 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hnorm_le_R : norm z <= R := by
    dsimp [R]
    linarith
  have hsum :
      norm (p.aeval z) <=
        ∑ i ∈ Finset.range (p.natDegree + 1), norm (p.coeff i • z ^ i) := by
    rw [Polynomial.aeval_eq_sum_range]
    exact norm_sum_le _ _
  have hterm :
      (∑ i ∈ Finset.range (p.natDegree + 1), norm (p.coeff i • z ^ i)) <=
        ∑ i ∈ Finset.range (p.natDegree + 1),
          norm (p.coeff i) * R ^ p.natDegree := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i <= p.natDegree :=
      Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpow_norm_le : norm z ^ i <= R ^ i :=
      pow_le_pow_left₀ (norm_nonneg z) hnorm_le_R i
    have hpow_le : norm z ^ i <= R ^ p.natDegree :=
      hpow_norm_le.trans (pow_le_pow_right₀ hR_one hi_le)
    rw [norm_smul, norm_pow]
    exact mul_le_mul_of_nonneg_left hpow_le (norm_nonneg (p.coeff i))
  calc
    norm (p.aeval z)
        <= ∑ i ∈ Finset.range (p.natDegree + 1),
          norm (p.coeff i • z ^ i) := hsum
    _ <= ∑ i ∈ Finset.range (p.natDegree + 1),
          norm (p.coeff i) * R ^ p.natDegree := hterm
    _ = C0 * R ^ p.natDegree := by
      simp [C0, Finset.sum_mul]
    _ <= (C0 + 1) * R ^ p.natDegree := by
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hR_nonneg _)

/--
Shifting a complex argument by a real constant changes the shifted radius by
only a fixed multiplicative factor depending on the shift.
-/
theorem norm_add_two_le_abs_real_add_two_mul_norm_add_real_add_two
    (z : Complex) (y : Real) :
    norm z + 2 <= (abs y + 2) * (norm (z + (y : Complex)) + 2) := by
  have hz_le : norm z <= norm (z + (y : Complex)) + abs y := by
    have h := norm_add_le (z + (y : Complex)) (-(y : Complex))
    have hz : z + (y : Complex) + -(y : Complex) = z := by
      ring
    simpa [hz, Complex.norm_real, Real.norm_eq_abs] using h
  have hy_nonneg : 0 <= abs y := abs_nonneg y
  have hw_nonneg : 0 <= norm (z + (y : Complex)) :=
    norm_nonneg (z + (y : Complex))
  have hprod_nonneg : 0 <= abs y * norm (z + (y : Complex)) :=
    mul_nonneg hy_nonneg hw_nonneg
  nlinarith

/--
On the real line, the `pi`-normalized Gaussian is fixed by mathlib's Fourier
transform convention.
-/
theorem fourier_guinandWeilPiGaussianSource_real :
    (𝓕 fun x : Real => guinandWeilPiGaussianSource (x : Complex)) =
      fun t : Real => guinandWeilPiGaussianSource (t : Complex) := by
  simpa [guinandWeilPiGaussianSource, pow_two] using
    fourier_gaussian_pi (b := (1 : Complex))
      (by norm_num : 0 < (1 : Complex).re)

/--
The Fourier transform of the real-line `pi`-normalized Gaussian source is even.
-/
theorem fourier_guinandWeilPiGaussianSource_real_even
    (t : Real) :
    ((𝓕 fun x : Real => guinandWeilPiGaussianSource (x : Complex)) (-t)) =
      ((𝓕 fun x : Real => guinandWeilPiGaussianSource (x : Complex)) t) := by
  have hF := congrFun fourier_guinandWeilPiGaussianSource_real
  rw [hF (-t), hF t]
  exact guinandWeilPiGaussianSource_ofReal_neg t

/--
Fourier transform of the `pi`-normalized Gaussian source restricted to a
horizontal line.  This records the Fourier convention explicitly for the
source value `z = x + i y`.
-/
theorem fourier_guinandWeilPiGaussianSource_horizontalLine
    (y : Real) :
    (𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) =
      fun t : Real =>
        Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
          guinandWeilPiGaussianSource ((t + y : Real) : Complex) := by
  let c : Complex := -Complex.I * (y : Complex)
  let C : Complex := Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2)
  have hpoint (x : Real) :
      guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I) =
        C *
          Complex.exp
            (-(Real.pi : Complex) * (1 : Complex) * (x : Complex) ^ 2 +
              2 * (Real.pi : Complex) * c * (x : Complex)) := by
    dsimp [C, c, guinandWeilPiGaussianSource]
    rw [← Complex.exp_add]
    congr 1
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfun :
      (fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) =
        C •
          (fun x : Real =>
            Complex.exp
              (-(Real.pi : Complex) * (1 : Complex) * (x : Complex) ^ 2 +
                2 * (Real.pi : Complex) * c * (x : Complex))) := by
    funext x
    simpa [Pi.smul_apply] using hpoint x
  have hbase :=
    fourier_gaussian_pi' (b := (1 : Complex)) (c := c)
      (by norm_num : 0 < (1 : Complex).re)
  calc
    (𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I))
        = 𝓕
          (C •
            (fun x : Real =>
              Complex.exp
                (-(Real.pi : Complex) * (1 : Complex) * (x : Complex) ^ 2 +
                  2 * (Real.pi : Complex) * c * (x : Complex)))) := by
          rw [hfun]
    _ =
        C •
          (𝓕 fun x : Real =>
            Complex.exp
              (-(Real.pi : Complex) * (1 : Complex) * (x : Complex) ^ 2 +
                2 * (Real.pi : Complex) * c * (x : Complex))) := by
          ext t
          simp only [Pi.smul_apply]
          rw [Real.fourier_real_eq, Real.fourier_real_eq]
          rw [← MeasureTheory.integral_smul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards with v
          simp [Circle.smul_def, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    _ =
        C •
          (fun t : Real =>
            1 / (1 : Complex) ^ (1 / 2 : Complex) *
              Complex.exp
                (-(Real.pi : Complex) / (1 : Complex) *
                  ((t : Complex) + Complex.I * c) ^ 2)) := by
          rw [hbase]
    _ =
        fun t : Real =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource ((t + y : Real) : Complex) := by
          funext t
          dsimp [C, c, guinandWeilPiGaussianSource]
          ring_nf
          simp [Complex.I_sq, Complex.I_pow_four]
          congr 1
          ring

/--
The Fourier transform of each horizontal-line `pi`-Gaussian source is exactly
the positive real Gaussian in the frequency variable.
-/
theorem fourier_guinandWeilPiGaussianSource_horizontalLine_eq_realGaussian
    (t y : Real) :
    ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) =
      (Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2)) : Complex) := by
  rw [congrFun (fourier_guinandWeilPiGaussianSource_horizontalLine y) t]
  dsimp [guinandWeilPiGaussianSource]
  rw [← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  norm_num [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- Real part of the horizontal-line Fourier transform of the Gaussian source. -/
theorem fourier_guinandWeilPiGaussianSource_horizontalLine_re
    (t y : Real) :
    (((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t).re) =
      Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2)) := by
  rw [fourier_guinandWeilPiGaussianSource_horizontalLine_eq_realGaussian]
  rw [Complex.ofReal_re]

/-- Imaginary part of the horizontal-line Fourier transform of the Gaussian source. -/
theorem fourier_guinandWeilPiGaussianSource_horizontalLine_im
    (t y : Real) :
    (((𝓕 fun x : Real =>
      guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t).im) = 0 := by
  rw [fourier_guinandWeilPiGaussianSource_horizontalLine_eq_realGaussian]
  rw [Complex.ofReal_im]

/-- Strict positivity of the real Fourier-side horizontal-line Gaussian. -/
theorem fourier_guinandWeilPiGaussianSource_horizontalLine_re_pos
    (t y : Real) :
    0 <
      (((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t).re) := by
  rw [fourier_guinandWeilPiGaussianSource_horizontalLine_re]
  exact Real.exp_pos _

/--
The Fourier transform of each horizontal-line `pi`-Gaussian source is
nonvanishing on the real frequency axis.
-/
theorem fourier_guinandWeilPiGaussianSource_horizontalLine_ne_zero
    (t y : Real) :
    ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) ≠ 0 := by
  rw [congrFun (fourier_guinandWeilPiGaussianSource_horizontalLine y) t]
  exact
    mul_ne_zero
      (Complex.exp_ne_zero ((Real.pi : Complex) * (y : Complex) ^ 2))
      (guinandWeilPiGaussianSource_ne_zero ((t + y : Real) : Complex))

/--
The Fourier-side horizontal-line `pi`-Gaussian has strictly positive norm on
the real frequency axis.
-/
theorem norm_fourier_guinandWeilPiGaussianSource_horizontalLine_pos
    (t y : Real) :
    0 <
      norm ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) :=
  norm_pos_iff.mpr
    (fourier_guinandWeilPiGaussianSource_horizontalLine_ne_zero t y)

/--
The `pi`-normalized Gaussian source is integrable on every horizontal line.
This is a direct admissibility fact for the concrete source test.
-/
theorem integrable_guinandWeilPiGaussianSource_horizontalLine
    (y : Real) :
    MeasureTheory.Integrable fun x : Real =>
      guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I) := by
  simpa [guinandWeilPiGaussianSource, pow_two] using
    GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I
      (b := (Real.pi : Complex))
      (by simpa using Real.pi_pos) y

/--
The horizontal-line integral of the `pi`-normalized Gaussian source is the
same as on the real axis.
-/
theorem integral_guinandWeilPiGaussianSource_horizontalLine
    (y : Real) :
    ∫ x : Real,
      guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I) = 1 := by
  have hpi_ne : (Real.pi : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simpa [guinandWeilPiGaussianSource, pow_two, div_self hpi_ne] using
    GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I
      (b := (Real.pi : Complex))
      (by simpa using Real.pi_pos) y

/--
The Fourier transform of the `pi`-normalized Gaussian source restricted to a
horizontal line is integrable on the real frequency line.
-/
theorem integrable_fourier_guinandWeilPiGaussianSource_horizontalLine
    (y : Real) :
    MeasureTheory.Integrable fun t : Real =>
      (𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t := by
  have hreal :
      MeasureTheory.Integrable fun t : Real =>
        guinandWeilPiGaussianSource ((t : Real) : Complex) := by
    simpa [guinandWeilPiGaussianSource, pow_two] using
      GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I
        (b := (Real.pi : Complex))
        (by simpa using Real.pi_pos) (0 : Real)
  have hshift :
      MeasureTheory.Integrable fun t : Real =>
        guinandWeilPiGaussianSource ((t + y : Real) : Complex) := by
    exact
      (MeasureTheory.measurePreserving_add_right
          (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Real)
          y).integrable_comp_of_integrable hreal
  rw [fourier_guinandWeilPiGaussianSource_horizontalLine y]
  exact hshift.const_mul _

/--
The integral of the Fourier transform of the shifted horizontal-line Gaussian
is the explicit Fourier-normalization factor.
-/
theorem integral_fourier_guinandWeilPiGaussianSource_horizontalLine
    (y : Real) :
    ∫ t : Real,
      (𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t =
        Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) := by
  have hshift_integral_real :
      (∫ t : Real,
        guinandWeilPiGaussianSource ((t + y : Real) : Complex)) = 1 := by
    have htranslate :=
      (MeasureTheory.measurePreserving_add_right
          (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Real)
          y).integral_comp
        (MeasurableEquiv.addRight y).measurableEmbedding
        (fun u : Real => guinandWeilPiGaussianSource ((u : Real) : Complex))
    calc
      (∫ t : Real,
        guinandWeilPiGaussianSource ((t + y : Real) : Complex))
          = ∫ u : Real, guinandWeilPiGaussianSource ((u : Real) : Complex) := by
            simpa using htranslate
      _ = 1 := by
        simpa using integral_guinandWeilPiGaussianSource_horizontalLine (0 : Real)
  have hshift_integral :
      (∫ t : Real,
        guinandWeilPiGaussianSource ((t : Complex) + (y : Complex))) = 1 := by
    simpa [Complex.ofReal_add] using hshift_integral_real
  rw [fourier_guinandWeilPiGaussianSource_horizontalLine y]
  rw [MeasureTheory.integral_const_mul]
  simp [hshift_integral]

/-- Exact norm of the `pi`-normalized complex Gaussian. -/
theorem norm_guinandWeilPiGaussianSource
    (z : Complex) :
    norm (guinandWeilPiGaussianSource z) =
      Real.exp (Real.pi * (z.im ^ 2 - z.re ^ 2)) := by
  unfold guinandWeilPiGaussianSource
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, pow_two]
  ring

/--
Exact norm of the Fourier transform of the `pi`-normalized Gaussian source
restricted to a horizontal line.
-/
theorem norm_fourier_guinandWeilPiGaussianSource_horizontalLine
    (t y : Real) :
    norm ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) =
      Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2)) := by
  rw [congrFun (fourier_guinandWeilPiGaussianSource_horizontalLine y) t]
  rw [norm_mul, Complex.norm_exp, norm_guinandWeilPiGaussianSource]
  rw [← Real.exp_add]
  congr 1
  have hy_re : ((Real.pi : Complex) * (y : Complex) ^ 2).re =
      Real.pi * y ^ 2 := by
    rw [Complex.re_ofReal_mul]
    have hpow_re : ((y : Complex) ^ 2).re = y ^ 2 := by
      rw [← Complex.ofReal_pow y 2]
      exact Complex.ofReal_re (y ^ 2)
    rw [hpow_re]
  rw [hy_re]
  simp
  ring_nf

/--
Bounded horizontal-line Fourier norm majorant for the `pi`-normalized Gaussian
source, uniform over `abs y <= A`.
-/
theorem norm_fourier_guinandWeilPiGaussianSource_le_horizontalStripMajorant
    {A : Real} (hA : 0 <= A) (t y : Real) (hy : abs y <= A) :
    norm ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) <=
      Real.exp (Real.pi * (A ^ 2 - (t + y) ^ 2)) := by
  rw [norm_fourier_guinandWeilPiGaussianSource_horizontalLine]
  apply Real.exp_le_exp.mpr
  have hy_sq : y ^ 2 <= A ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hA] using hy)
  nlinarith [Real.pi_pos]

/--
On any bounded horizontal strip, the `pi`-normalized Gaussian is bounded by a
real-axis Gaussian with the explicit strip-loss factor `exp (pi * A^2)`.
-/
theorem norm_guinandWeilPiGaussianSource_le_horizontalStrip
    {A : Real} (hA : 0 <= A) {z : Complex}
    (hz : abs z.im <= A) :
    norm (guinandWeilPiGaussianSource z) <=
      Real.exp (Real.pi * (A ^ 2 - z.re ^ 2)) := by
  rw [norm_guinandWeilPiGaussianSource]
  apply Real.exp_le_exp.mpr
  have him_sq : z.im ^ 2 <= A ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hA] using hz)
  nlinarith [Real.pi_pos]

/-- Exact norm of the `pi`-normalized Gaussian source on a horizontal line. -/
theorem norm_guinandWeilPiGaussianSource_horizontalLine
    (x y : Real) :
    norm (guinandWeilPiGaussianSource
      ((x : Complex) + (y : Complex) * Complex.I)) =
      Real.exp (Real.pi * (y ^ 2 - x ^ 2)) := by
  simp [norm_guinandWeilPiGaussianSource]

/--
Every horizontal line of the `pi`-normalized Gaussian has finite polynomial
moments.  This is the `L^1` form of the horizontal-strip source admissibility
condition for a concrete Gaussian test.
-/
theorem integrable_abs_rpow_mul_norm_guinandWeilPiGaussianSource_horizontalLine
    {s y : Real} (hs : -1 < s) :
    MeasureTheory.Integrable fun x : Real =>
      |x| ^ s *
        norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) := by
  have hbase :
      MeasureTheory.Integrable fun x : Real =>
        |x| ^ s * Real.exp (-Real.pi * x ^ 2) := by
    rw [← MeasureTheory.integrableOn_univ,
      ← @Set.Iio_union_Ici _ _ (0 : Real),
      MeasureTheory.integrableOn_union,
      integrableOn_Ici_iff_integrableOn_Ioi]
    refine ⟨?_, ?_⟩
    · rw [← (MeasureTheory.Measure.measurePreserving_neg
          (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Real)).integrableOn_comp_preimage
        (Homeomorph.neg Real).measurableEmbedding]
      simp only [Function.comp_def, neg_sq, Set.neg_preimage, Set.neg_Iio, neg_zero,
        abs_neg]
      exact
        (integrableOn_rpow_mul_exp_neg_mul_sq
          (b := Real.pi) Real.pi_pos hs).congr_fun
          (fun x hx => by
            rw [abs_of_pos hx])
          measurableSet_Ioi
    · exact
        (integrableOn_rpow_mul_exp_neg_mul_sq
          (b := Real.pi) Real.pi_pos hs).congr_fun
          (fun x hx => by
            rw [abs_of_pos hx])
          measurableSet_Ioi
  have hscaled :
      MeasureTheory.Integrable fun x : Real =>
        Real.exp (Real.pi * y ^ 2) *
          (|x| ^ s * Real.exp (-Real.pi * x ^ 2)) :=
    hbase.const_mul _
  refine hscaled.congr (Eventually.of_forall fun x => ?_)
  simp only
  calc
    Real.exp (Real.pi * y ^ 2) *
        (|x| ^ s * Real.exp (-Real.pi * x ^ 2))
        = |x| ^ s *
            (Real.exp (Real.pi * y ^ 2) *
              Real.exp (-Real.pi * x ^ 2)) := by
          ring
    _ = |x| ^ s *
          Real.exp (Real.pi * y ^ 2 + -Real.pi * x ^ 2) := by
          rw [Real.exp_add]
    _ = |x| ^ s *
        norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) := by
          rw [norm_guinandWeilPiGaussianSource_horizontalLine]
          congr 1
          ring_nf

/--
The horizontal-strip Gaussian majorant has finite polynomial moments.  This is
the reusable integrable majorant behind the concrete Gaussian strip source.
-/
theorem integrable_abs_rpow_mul_guinandWeilPiGaussianHorizontalStripMajorant
    {s A : Real} (hs : -1 < s) :
    MeasureTheory.Integrable fun x : Real =>
      |x| ^ s * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
  simpa [norm_guinandWeilPiGaussianSource_horizontalLine] using
    (integrable_abs_rpow_mul_norm_guinandWeilPiGaussianSource_horizontalLine
      (s := s) (y := A) hs)

/--
The standard `(abs x + 1)^k` polynomial weights are integrable against the
horizontal-strip Gaussian majorant.
-/
theorem integrable_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant
    (k : Nat) (A : Real) :
    MeasureTheory.Integrable fun x : Real =>
      (|x| + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
  have hk :
      MeasureTheory.Integrable fun x : Real =>
        |x| ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_abs_rpow_mul_guinandWeilPiGaussianHorizontalStripMajorant
        (s := (k : Real)) (A := A)
        (lt_of_lt_of_le (by norm_num : (-1 : Real) < 0) (Nat.cast_nonneg k)))
  have h0 :
      MeasureTheory.Integrable fun x : Real =>
        Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    simpa using
      (integrable_abs_rpow_mul_guinandWeilPiGaussianHorizontalStripMajorant
        (s := (0 : Real)) (A := A) (by norm_num : -1 < (0 : Real)))
  have hsum :
      MeasureTheory.Integrable fun x : Real =>
        (|x| ^ k + 1) * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    have h0' :
        MeasureTheory.Integrable fun x : Real =>
          1 * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
      simpa using h0
    refine (hk.add h0').congr (Eventually.of_forall fun x => ?_)
    simp [Pi.add_apply]
    ring_nf
  have hmajorant :
      MeasureTheory.Integrable fun x : Real =>
        (2 : Real) ^ k *
          ((|x| ^ k + 1) * Real.exp (Real.pi * (A ^ 2 - x ^ 2))) :=
    hsum.const_mul _
  refine hmajorant.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  have htarget_nonneg :
      0 <= (|x| + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    exact mul_nonneg
      (pow_nonneg (by positivity : 0 <= |x| + (1 : Real)) k)
      (Real.exp_pos _).le
  have hpoly :
      (|x| + 1) ^ k <= (2 : Real) ^ k * (|x| ^ k + 1) := by
    by_cases hx : |x| <= (1 : Real)
    · have hbase : |x| + 1 <= (2 : Real) := by
        linarith
      have hpow : (|x| + 1) ^ k <= (2 : Real) ^ k :=
        pow_le_pow_left₀ (by positivity : 0 <= |x| + (1 : Real)) hbase k
      have hone : (1 : Real) <= |x| ^ k + 1 := by
        have hnonneg : 0 <= |x| ^ k := pow_nonneg (abs_nonneg x) k
        linarith
      exact hpow.trans
        (le_mul_of_one_le_right (pow_nonneg (by norm_num : (0 : Real) <= 2) k) hone)
    · have hxge : (1 : Real) <= |x| := by
        linarith
      have hbase : |x| + 1 <= (2 : Real) * |x| := by
        linarith
      have hpow : (|x| + 1) ^ k <= ((2 : Real) * |x|) ^ k :=
        pow_le_pow_left₀ (by positivity : 0 <= |x| + (1 : Real)) hbase k
      have hpow' : (|x| + 1) ^ k <= (2 : Real) ^ k * |x| ^ k := by
        simpa [mul_pow] using hpow
      have hadd : |x| ^ k <= |x| ^ k + 1 := by
        linarith
      exact hpow'.trans
        (mul_le_mul_of_nonneg_left hadd
          (pow_nonneg (by norm_num : (0 : Real) <= 2) k))
  rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
  calc
    (|x| + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2))
        <= ((2 : Real) ^ k * (|x| ^ k + 1)) *
            Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
          exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = (2 : Real) ^ k *
        ((|x| ^ k + 1) * Real.exp (Real.pi * (A ^ 2 - x ^ 2))) := by
          ring

/--
Every horizontal line of the `pi`-normalized Gaussian has finite standard
polynomial moments.
-/
theorem integrable_abs_add_one_pow_mul_norm_guinandWeilPiGaussianSource_horizontalLine
    (k : Nat) (y : Real) :
    MeasureTheory.Integrable fun x : Real =>
      (|x| + 1) ^ k *
        norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) := by
  simpa [norm_guinandWeilPiGaussianSource_horizontalLine] using
    (integrable_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant
      k y)

/--
Every finite complex derivative of the `pi`-normalized Gaussian has finite
standard polynomial moments on each horizontal line.
-/
theorem integrable_abs_add_one_pow_mul_norm_iteratedDeriv_guinandWeilPiGaussianSource_horizontalLine
    (m k : Nat) (y : Real) :
    MeasureTheory.Integrable fun x : Real =>
      (|x| + 1) ^ k *
        norm (iteratedDeriv m guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) := by
  let P : Polynomial Complex := guinandWeilPiGaussianDerivativePolynomial m
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow P with
    ⟨B, hB_pos, hB⟩
  let scale : Real := B * (|y| + 3) ^ P.natDegree
  have hscale_nonneg : 0 <= scale := by
    exact mul_nonneg hB_pos.le
      (pow_nonneg (by linarith [abs_nonneg y] : 0 <= |y| + 3) P.natDegree)
  have hbase :
      MeasureTheory.Integrable fun x : Real =>
        (|x| + 1) ^ (k + P.natDegree) *
          norm (guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) :=
    integrable_abs_add_one_pow_mul_norm_guinandWeilPiGaussianSource_horizontalLine
      (k + P.natDegree) y
  have hscaled :
      MeasureTheory.Integrable fun x : Real =>
        scale *
          ((|x| + 1) ^ (k + P.natDegree) *
            norm (guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I))) :=
    hbase.const_mul scale
  have htarget_eq :
      (fun x : Real =>
        (|x| + 1) ^ k *
          norm (iteratedDeriv m guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I))) =
        fun x : Real =>
          (|x| + 1) ^ k *
            norm ((P.aeval ((x : Complex) + (y : Complex) * Complex.I)) *
              guinandWeilPiGaussianSource
                ((x : Complex) + (y : Complex) * Complex.I)) := by
    funext x
    rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial]
  refine hscaled.mono' ?_ (Eventually.of_forall fun x => ?_)
  · rw [htarget_eq]
    have hline :
        Continuous fun x : Real =>
          ((x : Complex) + (y : Complex) * Complex.I) := by
      fun_prop
    have hpoly :
        Continuous fun x : Real =>
          P.aeval ((x : Complex) + (y : Complex) * Complex.I) :=
      P.continuous_aeval.comp hline
    have hsource :
        Continuous fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I) :=
      differentiable_guinandWeilPiGaussianSource.continuous.comp hline
    exact
      (((continuous_abs.add continuous_const).pow k).mul
        ((hpoly.mul hsource).norm)).aestronglyMeasurable
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have htarget_nonneg :
      0 <= (|x| + 1) ^ k *
        norm (iteratedDeriv m guinandWeilPiGaussianSource z) := by
    exact mul_nonneg
      (pow_nonneg (by positivity : 0 <= |x| + (1 : Real)) k)
      (norm_nonneg _)
  have hz_norm_le : norm z <= |x| + |y| := by
    calc
      norm z <= norm (x : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |x| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (|y| + 3) * (|x| + 1) := by
    have hx_nonneg : 0 <= |x| := abs_nonneg x
    have hy_nonneg : 0 <= |y| := abs_nonneg y
    nlinarith
  have hshift_pow :
      (norm z + 2) ^ P.natDegree <=
        ((|y| + 3) * (|x| + 1)) ^ P.natDegree := by
    exact pow_le_pow_left₀
      (by linarith [norm_nonneg z] : 0 <= norm z + 2)
      hshift_le P.natDegree
  have hshift_pow' :
      (norm z + 2) ^ P.natDegree <=
        (|y| + 3) ^ P.natDegree * (|x| + 1) ^ P.natDegree := by
    simpa [mul_pow] using hshift_pow
  have hiter :
      norm (iteratedDeriv m guinandWeilPiGaussianSource z) <=
        scale * (|x| + 1) ^ P.natDegree *
          norm (guinandWeilPiGaussianSource z) := by
    rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial]
    rw [norm_mul]
    calc
      norm ((guinandWeilPiGaussianDerivativePolynomial m).aeval z) *
          norm (guinandWeilPiGaussianSource z)
          <= (B * (norm z + 2) ^ P.natDegree) *
              norm (guinandWeilPiGaussianSource z) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [P] using hB z) (norm_nonneg _)
      _ <= (B * ((|y| + 3) ^ P.natDegree *
              (|x| + 1) ^ P.natDegree)) *
            norm (guinandWeilPiGaussianSource z) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hshift_pow' hB_pos.le)
              (norm_nonneg _)
      _ = scale * (|x| + 1) ^ P.natDegree *
            norm (guinandWeilPiGaussianSource z) := by
            simp [scale, mul_assoc, mul_left_comm, mul_comm]
  rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
  calc
    (|x| + 1) ^ k *
        norm (iteratedDeriv m guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I))
        = (|x| + 1) ^ k *
          norm (iteratedDeriv m guinandWeilPiGaussianSource z) := by
            rfl
    _ <= (|x| + 1) ^ k *
          (scale * (|x| + 1) ^ P.natDegree *
            norm (guinandWeilPiGaussianSource z)) := by
          exact mul_le_mul_of_nonneg_left hiter
            (pow_nonneg (by positivity : 0 <= |x| + (1 : Real)) k)
    _ = scale *
          ((|x| + 1) ^ (k + P.natDegree) *
            norm (guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I))) := by
          rw [pow_add]
          simp [z]
          ring

/--
Every finite complex derivative of the `pi`-normalized Gaussian admits a
single integrable polynomially weighted majorant on each bounded horizontal
strip.
-/
theorem exists_integrable_majorant_abs_add_one_pow_mul_norm_iteratedDeriv_guinandWeilPiGaussianSource_horizontalStrip
    (m k : Nat) {A : Real} (hA : 0 <= A) :
    ∃ M : Real -> Real,
      MeasureTheory.Integrable M ∧
        ∀ x y : Real, abs y <= A ->
          (|x| + 1) ^ k *
            norm (iteratedDeriv m guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) <=
          M x := by
  let P : Polynomial Complex := guinandWeilPiGaussianDerivativePolynomial m
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow P with
    ⟨B, hB_pos, hB⟩
  let scale : Real := B * (A + 3) ^ P.natDegree
  refine
    ⟨fun x : Real =>
      scale *
        ((|x| + 1) ^ (k + P.natDegree) *
          Real.exp (Real.pi * (A ^ 2 - x ^ 2))), ?_, ?_⟩
  · exact
      (integrable_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant
        (k + P.natDegree) A).const_mul scale
  intro x y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have hscale_nonneg : 0 <= scale := by
    exact mul_nonneg hB_pos.le
      (pow_nonneg (by linarith : 0 <= A + 3) P.natDegree)
  have hx_weight_nonneg : 0 <= (|x| + 1) ^ k := by
    exact pow_nonneg (by positivity : 0 <= |x| + (1 : Real)) k
  have hz_norm_le : norm z <= |x| + |y| := by
    calc
      norm z <= norm (x : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |x| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (A + 3) * (|x| + 1) := by
    have hx_nonneg : 0 <= |x| := abs_nonneg x
    nlinarith
  have hshift_pow :
      (norm z + 2) ^ P.natDegree <=
        ((A + 3) * (|x| + 1)) ^ P.natDegree := by
    exact pow_le_pow_left₀
      (by linarith [norm_nonneg z] : 0 <= norm z + 2)
      hshift_le P.natDegree
  have hshift_pow' :
      (norm z + 2) ^ P.natDegree <=
        (A + 3) ^ P.natDegree * (|x| + 1) ^ P.natDegree := by
    simpa [mul_pow] using hshift_pow
  have hsource :
      norm (guinandWeilPiGaussianSource z) <=
        Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    have hz_im : abs z.im <= A := by
      simpa [z] using hy
    simpa [z] using
      (norm_guinandWeilPiGaussianSource_le_horizontalStrip
        (A := A) hA (z := z) hz_im)
  have hiter :
      norm (iteratedDeriv m guinandWeilPiGaussianSource z) <=
        scale * (|x| + 1) ^ P.natDegree *
          Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial]
    rw [norm_mul]
    calc
      norm ((guinandWeilPiGaussianDerivativePolynomial m).aeval z) *
          norm (guinandWeilPiGaussianSource z)
          <= (B * (norm z + 2) ^ P.natDegree) *
              norm (guinandWeilPiGaussianSource z) := by
            exact mul_le_mul_of_nonneg_right
              (by simpa [P] using hB z) (norm_nonneg _)
      _ <= (B * ((A + 3) ^ P.natDegree *
              (|x| + 1) ^ P.natDegree)) *
            norm (guinandWeilPiGaussianSource z) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hshift_pow' hB_pos.le)
              (norm_nonneg _)
      _ = scale * (|x| + 1) ^ P.natDegree *
            norm (guinandWeilPiGaussianSource z) := by
            simp [scale, mul_assoc, mul_left_comm, mul_comm]
      _ <= scale * (|x| + 1) ^ P.natDegree *
            Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hsource
              (mul_nonneg hscale_nonneg
                (pow_nonneg
                  (by positivity : 0 <= |x| + (1 : Real)) P.natDegree))
  calc
    (|x| + 1) ^ k *
        norm (iteratedDeriv m guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I))
        = (|x| + 1) ^ k *
          norm (iteratedDeriv m guinandWeilPiGaussianSource z) := by
            rfl
    _ <= (|x| + 1) ^ k *
          (scale * (|x| + 1) ^ P.natDegree *
            Real.exp (Real.pi * (A ^ 2 - x ^ 2))) := by
          exact mul_le_mul_of_nonneg_left hiter hx_weight_nonneg
    _ = scale *
          ((|x| + 1) ^ (k + P.natDegree) *
            Real.exp (Real.pi * (A ^ 2 - x ^ 2))) := by
          rw [pow_add]
          ring

/--
Every Fourier-side horizontal line of the `pi`-normalized Gaussian has finite
standard polynomial moments in the real frequency variable.
-/
theorem integrable_abs_add_one_pow_mul_norm_fourier_guinandWeilPiGaussianSource_horizontalLine
    (k : Nat) (y : Real) :
    MeasureTheory.Integrable fun t : Real =>
      (|t| + 1) ^ k *
        norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) := by
  have hshifted_base :
      MeasureTheory.Integrable fun u : Real =>
        (|u| + 1) ^ k * Real.exp (Real.pi * (y ^ 2 - u ^ 2)) :=
    integrable_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant
      k y
  have hshifted :
      MeasureTheory.Integrable fun t : Real =>
        (|t + y| + 1) ^ k *
          Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2)) :=
    (MeasureTheory.measurePreserving_add_right
      (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Real)
      y).integrable_comp_of_integrable hshifted_base
  have hscaled :
      MeasureTheory.Integrable fun t : Real =>
        (|y| + 2) ^ k *
          ((|t + y| + 1) ^ k *
            Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2))) :=
    hshifted.const_mul _
  have hexp :
      MeasureTheory.Integrable fun t : Real =>
        (|t| + 1) ^ k *
          Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2)) := by
    refine hscaled.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
    have htarget_nonneg :
        0 <= (|t| + 1) ^ k *
          Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2)) := by
      exact mul_nonneg
        (pow_nonneg (by positivity : 0 <= |t| + (1 : Real)) k)
        (Real.exp_pos _).le
    have ht_abs : |t| <= |t + y| + |y| := by
      have h := abs_add_le (t + y) (-y)
      simpa [add_assoc, add_left_comm, add_comm] using h
    have hshift_le : |t| + 1 <= (|y| + 2) * (|t + y| + 1) := by
      have hty_nonneg : 0 <= |t + y| := abs_nonneg (t + y)
      have hy_nonneg : 0 <= |y| := abs_nonneg y
      nlinarith
    have hpow :
        (|t| + 1) ^ k <= ((|y| + 2) * (|t + y| + 1)) ^ k :=
      pow_le_pow_left₀ (by positivity : 0 <= |t| + (1 : Real)) hshift_le k
    have hpow' :
        (|t| + 1) ^ k <= (|y| + 2) ^ k * (|t + y| + 1) ^ k := by
      simpa [mul_pow] using hpow
    rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
    calc
      (|t| + 1) ^ k * Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2))
          <= ((|y| + 2) ^ k * (|t + y| + 1) ^ k) *
              Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2)) := by
            exact mul_le_mul_of_nonneg_right hpow' (Real.exp_pos _).le
      _ = (|y| + 2) ^ k *
            ((|t + y| + 1) ^ k *
              Real.exp (Real.pi * (y ^ 2 - (t + y) ^ 2))) := by
            ring
  refine hexp.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [norm_fourier_guinandWeilPiGaussianSource_horizontalLine]

/--
Every finite complex derivative of the closed-form Fourier-side
horizontal-line extension has finite standard polynomial moments on the real
frequency axis.
-/
theorem integrable_abs_add_one_pow_mul_norm_iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_horizontalLine
    (m k : Nat) (y : Real) :
    MeasureTheory.Integrable fun t : Real =>
      (|t| + 1) ^ k *
        norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          (t : Complex)) := by
  let c : Complex := Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2)
  let P : Polynomial Complex := guinandWeilPiGaussianDerivativePolynomial m
  have hbase :
      MeasureTheory.Integrable fun u : Real =>
        (|u| + 1) ^ k *
          norm (iteratedDeriv m guinandWeilPiGaussianSource (u : Complex)) := by
    simpa using
      (integrable_abs_add_one_pow_mul_norm_iteratedDeriv_guinandWeilPiGaussianSource_horizontalLine
        m k 0)
  have hshifted :
      MeasureTheory.Integrable fun t : Real =>
        (|t + y| + 1) ^ k *
          norm (iteratedDeriv m guinandWeilPiGaussianSource
            ((t + y : Real) : Complex)) := by
    simpa [Function.comp_def] using
      ((MeasureTheory.measurePreserving_add_right
        (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Real)
        y).integrable_comp_of_integrable hbase)
  let scale : Real := norm c * (|y| + 2) ^ k
  have hscaled :
      MeasureTheory.Integrable fun t : Real =>
        scale *
          ((|t + y| + 1) ^ k *
            norm (iteratedDeriv m guinandWeilPiGaussianSource
              ((t + y : Real) : Complex))) :=
    hshifted.const_mul scale
  refine hscaled.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have htarget_eq :
        (fun t : Real =>
          (|t| + 1) ^ k *
            norm (iteratedDeriv m
              (fun z : Complex =>
                c * guinandWeilPiGaussianSource (z + (y : Complex)))
              (t : Complex))) =
          fun t : Real =>
            (|t| + 1) ^ k *
              norm (c *
                (P.aeval ((t + y : Real) : Complex) *
                  guinandWeilPiGaussianSource ((t + y : Real) : Complex))) := by
      funext t
      have hderiv_eval :
          iteratedDeriv m
              (fun z : Complex =>
                c * guinandWeilPiGaussianSource (z + (y : Complex)))
              (t : Complex) =
            c * iteratedDeriv m guinandWeilPiGaussianSource
              ((t + y : Real) : Complex) := by
        dsimp [c]
        rw [iteratedDeriv_const_mul_field]
        rw [iteratedDeriv_comp_add_const]
        simp [Complex.ofReal_add]
      rw [hderiv_eval]
      simp [P, iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial,
        Complex.ofReal_add]
    dsimp [c] at htarget_eq
    rw [htarget_eq]
    have hline :
        Continuous fun t : Real => ((t + y : Real) : Complex) := by
      fun_prop
    have hpoly :
        Continuous fun t : Real =>
          P.aeval ((t + y : Real) : Complex) :=
      P.continuous_aeval.comp hline
    have hsource :
        Continuous fun t : Real =>
          guinandWeilPiGaussianSource ((t + y : Real) : Complex) :=
      differentiable_guinandWeilPiGaussianSource.continuous.comp hline
    exact
      (((continuous_abs.add continuous_const).pow k).mul
        ((continuous_const.mul (hpoly.mul hsource)).norm)).aestronglyMeasurable
  let z : Complex := ((t + y : Real) : Complex)
  have htarget_nonneg :
      0 <= (|t| + 1) ^ k *
        norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          (t : Complex)) := by
    exact mul_nonneg
      (pow_nonneg (by positivity : 0 <= |t| + (1 : Real)) k)
      (norm_nonneg _)
  have ht_abs : |t| <= |t + y| + |y| := by
    have h := abs_add_le (t + y) (-y)
    simpa [add_assoc, add_left_comm, add_comm] using h
  have hshift_le : |t| + 1 <= (|y| + 2) * (|t + y| + 1) := by
    have hty_nonneg : 0 <= |t + y| := abs_nonneg (t + y)
    have hy_nonneg : 0 <= |y| := abs_nonneg y
    nlinarith
  have hpow :
      (|t| + 1) ^ k <= ((|y| + 2) * (|t + y| + 1)) ^ k :=
    pow_le_pow_left₀ (by positivity : 0 <= |t| + (1 : Real)) hshift_le k
  have hpow' :
      (|t| + 1) ^ k <= (|y| + 2) ^ k * (|t + y| + 1) ^ k := by
    simpa [mul_pow] using hpow
  have hderiv_eval :
      iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          (t : Complex) =
        c * iteratedDeriv m guinandWeilPiGaussianSource z := by
    dsimp [c, z]
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_add_const]
    simp [Complex.ofReal_add]
  rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
  calc
    (|t| + 1) ^ k *
        norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          (t : Complex))
        = (|t| + 1) ^ k *
          (norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource z)) := by
            rw [hderiv_eval, norm_mul]
    _ <= ((|y| + 2) ^ k * (|t + y| + 1) ^ k) *
          (norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource z)) := by
          exact mul_le_mul_of_nonneg_right hpow'
            (mul_nonneg (norm_nonneg c) (norm_nonneg _))
    _ = scale *
          ((|t + y| + 1) ^ k *
            norm (iteratedDeriv m guinandWeilPiGaussianSource
              ((t + y : Real) : Complex))) := by
          simp [scale, z]
          ring

/--
Every finite complex derivative of the closed-form Fourier-side
horizontal-line extension admits a single integrable polynomially weighted
majorant on each bounded horizontal strip.
-/
theorem exists_integrable_majorant_abs_add_one_pow_mul_norm_iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_horizontalStrip
    (m k : Nat) {A : Real} (hA : 0 <= A) (y : Real) :
    ∃ M : Real -> Real,
      MeasureTheory.Integrable M ∧
        ∀ t v : Real, abs v <= A ->
          (|t| + 1) ^ k *
            norm (iteratedDeriv m
              (fun z : Complex =>
                Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
                  guinandWeilPiGaussianSource (z + (y : Complex)))
              ((t : Complex) + (v : Complex) * Complex.I)) <=
          M t := by
  let c : Complex := Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2)
  rcases
    exists_integrable_majorant_abs_add_one_pow_mul_norm_iteratedDeriv_guinandWeilPiGaussianSource_horizontalStrip
      m k hA with ⟨M0, hM0_int, hM0⟩
  let scale : Real := norm c * (|y| + 2) ^ k
  refine ⟨fun t : Real => scale * M0 (t + y), ?_, ?_⟩
  · have hshifted :
        MeasureTheory.Integrable fun t : Real => M0 (t + y) := by
      simpa [Function.comp_def] using
        ((MeasureTheory.measurePreserving_add_right
          (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure Real)
          y).integrable_comp_of_integrable hM0_int)
    exact hshifted.const_mul scale
  intro t v hv
  let z : Complex := (t : Complex) + (v : Complex) * Complex.I
  let w : Complex := z + (y : Complex)
  have hw_coord :
      w = ((t + y : Real) : Complex) + (v : Complex) * Complex.I := by
    dsimp [w, z]
    rw [Complex.ofReal_add]
    ring
  have hsource :
      (|t + y| + 1) ^ k *
        norm (iteratedDeriv m guinandWeilPiGaussianSource w) <=
      M0 (t + y) := by
    simpa [hw_coord] using hM0 (t + y) v hv
  have hscale_nonneg : 0 <= scale := by
    exact mul_nonneg (norm_nonneg c)
      (pow_nonneg (by linarith [abs_nonneg y] : 0 <= |y| + 2) k)
  have ht_abs : |t| <= |t + y| + |y| := by
    have h := abs_add_le (t + y) (-y)
    simpa [add_assoc, add_left_comm, add_comm] using h
  have hshift_le : |t| + 1 <= (|y| + 2) * (|t + y| + 1) := by
    have hty_nonneg : 0 <= |t + y| := abs_nonneg (t + y)
    have hy_nonneg : 0 <= |y| := abs_nonneg y
    nlinarith
  have hshift_pow :
      (|t| + 1) ^ k <= ((|y| + 2) * (|t + y| + 1)) ^ k :=
    pow_le_pow_left₀ (by positivity : 0 <= |t| + (1 : Real)) hshift_le k
  have hshift_pow' :
      (|t| + 1) ^ k <= (|y| + 2) ^ k * (|t + y| + 1) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hderiv_eval :
      iteratedDeriv m
          (fun z : Complex =>
            c * guinandWeilPiGaussianSource (z + (y : Complex))) z =
        c * iteratedDeriv m guinandWeilPiGaussianSource w := by
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_add_const]
  calc
    (|t| + 1) ^ k *
        norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          ((t : Complex) + (v : Complex) * Complex.I))
        = (|t| + 1) ^ k *
          (norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource w)) := by
            dsimp [c, z, w] at hderiv_eval ⊢
            rw [hderiv_eval, norm_mul]
    _ <= ((|y| + 2) ^ k * (|t + y| + 1) ^ k) *
          (norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource w)) := by
          exact mul_le_mul_of_nonneg_right hshift_pow'
            (mul_nonneg (norm_nonneg c) (norm_nonneg _))
    _ = scale *
          ((|t + y| + 1) ^ k *
            norm (iteratedDeriv m guinandWeilPiGaussianSource w)) := by
          simp [scale]
          ring
    _ <= scale * M0 (t + y) := by
      exact mul_le_mul_of_nonneg_left hsource hscale_nonneg

/--
Uniform pointwise polynomial majorant for the `pi`-normalized Gaussian source
on a horizontal strip.
-/
theorem abs_rpow_mul_norm_guinandWeilPiGaussianSource_le_horizontalStripMajorant
    (s A x y : Real) (hA : 0 <= A) (hy : abs y <= A) :
    |x| ^ s *
        norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) <=
      |x| ^ s * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
  have hnorm :
      norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) <=
        Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    simpa using
      (norm_guinandWeilPiGaussianSource_le_horizontalStrip
        (A := A) hA
        (z := (x : Complex) + (y : Complex) * Complex.I)
        (by simpa using hy))
  exact mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg (abs_nonneg x) s)

/--
The horizontal-strip majorant for the `pi`-normalized Gaussian has rapid
polynomial decay in the real direction, for every fixed strip width.
-/
theorem tendsto_abs_rpow_mul_guinandWeilPiGaussianHorizontalStripMajorant_cocompact
    (s A : Real) :
    Tendsto
      (fun x : Real =>
        |x| ^ s * Real.exp (Real.pi * (A ^ 2 - x ^ 2)))
      (cocompact Real) (nhds 0) := by
  have hbase :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := Real.pi) Real.pi_pos s
  have hscaled :
      Tendsto
        (fun x : Real =>
          Real.exp (Real.pi * A ^ 2) *
            (|x| ^ s * Real.exp (-Real.pi * x ^ 2)))
        (cocompact Real) (nhds 0) := by
    simpa using hbase.const_mul (Real.exp (Real.pi * A ^ 2))
  exact hscaled.congr' (Eventually.of_forall fun x => by
    calc
      Real.exp (Real.pi * A ^ 2) *
          (|x| ^ s * Real.exp (-Real.pi * x ^ 2))
          = |x| ^ s *
              (Real.exp (Real.pi * A ^ 2) *
                Real.exp (-Real.pi * x ^ 2)) := by
            ring
      _ = |x| ^ s *
            Real.exp (Real.pi * A ^ 2 + -Real.pi * x ^ 2) := by
            rw [Real.exp_add]
      _ = |x| ^ s * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
            congr 1
            congr 1
            ring)

/--
Uniform epsilon-form horizontal-strip decay for the `pi`-normalized Gaussian
source, on every fixed strip width.
-/
theorem eventually_forall_abs_rpow_mul_norm_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (s A : Real) (hA : 0 <= A) {epsilon : Real}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        |x| ^ s *
            norm (guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) <=
          epsilon := by
  have hmajor_tendsto :=
    tendsto_abs_rpow_mul_guinandWeilPiGaussianHorizontalStripMajorant_cocompact
      s A
  have hmajor_small :
      ∀ᶠ x : Real in cocompact Real,
        |x| ^ s * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) <=
          epsilon := by
    have hball :
        Metric.ball (0 : Real) epsilon ∈ nhds (0 : Real) :=
      Metric.ball_mem_nhds (0 : Real) hepsilon
    filter_upwards [hmajor_tendsto.eventually hball] with x hx
    have hx_abs :
        abs (|x| ^ s * Real.exp (Real.pi * (A ^ 2 - x ^ 2))) <
          epsilon := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    exact le_of_lt (lt_of_abs_lt hx_abs)
  filter_upwards [hmajor_small] with x hx y hy
  exact
    (abs_rpow_mul_norm_guinandWeilPiGaussianSource_le_horizontalStripMajorant
      s A x y hA hy).trans hx

/--
Uniform epsilon-form shifted-radius decay for the `pi`-normalized Gaussian
source, on every fixed horizontal strip.
-/
theorem eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        norm (guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) *
          (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  have hscale_pos : 0 < (A + 3) ^ k :=
    pow_pos (by linarith : 0 < A + 3) k
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ y : Real, abs y <= A ->
          |x| ^ (k : Real) *
              norm (guinandWeilPiGaussianSource
                ((x : Complex) + (y : Complex) * Complex.I)) <=
            epsilon / (A + 3) ^ k :=
    eventually_forall_abs_rpow_mul_norm_guinandWeilPiGaussianSource_le_of_horizontalStrip
      (k : Real) A hA (div_pos hepsilon hscale_pos)
  have hlarge : ∀ᶠ x : Real in cocompact Real, 1 <= |x| := by
    have h :=
      (tendsto_norm_cocompact_atTop (E := Real)).eventually
        (eventually_ge_atTop (1 : Real))
    simpa [Real.norm_eq_abs] using h
  filter_upwards [hsmall, hlarge] with x hxsmall hxlarge y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have hnorm_z_le : norm z <= |x| + |y| := by
    calc
      norm z <= norm (x : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |x| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (A + 3) * |x| := by
    calc
      norm z + 2 <= |x| + |y| + 2 := by
        linarith
      _ <= |x| + A + 2 := by
        linarith
      _ <= (A + 3) * |x| := by
        have hx_minus_nonneg : 0 <= |x| - 1 := by
          linarith
        have hA_mul : 0 <= A * (|x| - 1) :=
          mul_nonneg hA hx_minus_nonneg
        have htwo_mul : 0 <= (2 : Real) * (|x| - 1) :=
          mul_nonneg (by norm_num) hx_minus_nonneg
        nlinarith
  have hshift_nonneg : 0 <= norm z + 2 := by
    have hz_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hshift_pow :
      (norm z + 2) ^ k <= ((A + 3) * |x|) ^ k :=
    pow_le_pow_left₀ hshift_nonneg hshift_le k
  have hshift_pow_scaled :
      (norm z + 2) ^ k <= (A + 3) ^ k * |x| ^ k := by
    simpa [mul_pow] using hshift_pow
  have hxsmall_nat :
      |x| ^ k *
          norm (guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) <=
        epsilon / (A + 3) ^ k := by
    simpa [Real.rpow_natCast] using hxsmall y hy
  calc
    norm (guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (guinandWeilPiGaussianSource z) * (norm z + 2) ^ k := by
          rfl
    _ <= norm (guinandWeilPiGaussianSource z) *
          ((A + 3) ^ k * |x| ^ k) := by
      exact mul_le_mul_of_nonneg_left hshift_pow_scaled
        (norm_nonneg (guinandWeilPiGaussianSource z))
    _ = (A + 3) ^ k *
        (|x| ^ k *
          norm (guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I))) := by
      simp [z, mul_assoc, mul_left_comm, mul_comm]
    _ <= (A + 3) ^ k * (epsilon / (A + 3) ^ k) := by
      exact mul_le_mul_of_nonneg_left hxsmall_nat
        (pow_nonneg (by linarith : 0 <= A + 3) k)
    _ = epsilon := by
      field_simp [ne_of_gt hscale_pos]

/--
The one-dimensional majorant controlling the `pi`-normalized Gaussian on a
fixed horizontal strip has rapid decay.
-/
theorem tendsto_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant_cocompact
    (k : Nat) (A : Real) :
    Tendsto
      (fun x : Real =>
        (|x| + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2)))
      (cocompact Real) (nhds 0) := by
  have hbase :=
    tendsto_abs_rpow_mul_guinandWeilPiGaussianHorizontalStripMajorant_cocompact
      (k : Real) A
  have hscaled :
      Tendsto
        (fun x : Real =>
          (2 : Real) ^ k *
            (|x| ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2))))
        (cocompact Real) (nhds 0) := by
    simpa [Real.rpow_natCast, mul_assoc] using
      hbase.const_mul ((2 : Real) ^ k)
  have hnonneg :
      ∀ᶠ x : Real in cocompact Real,
        0 <= (|x| + 1) ^ k *
          Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    exact Eventually.of_forall fun x =>
      mul_nonneg
        (pow_nonneg (by positivity : 0 <= |x| + (1 : Real)) k)
        (Real.exp_pos _).le
  have hupper :
      ∀ᶠ x : Real in cocompact Real,
        (|x| + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) <=
          (2 : Real) ^ k *
            (|x| ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2))) := by
    have hlarge : ∀ᶠ x : Real in cocompact Real, 1 <= |x| := by
      have h :=
        (tendsto_norm_cocompact_atTop (E := Real)).eventually
          (eventually_ge_atTop (1 : Real))
      simpa [Real.norm_eq_abs] using h
    filter_upwards [hlarge] with x hxlarge
    have hbase_le : |x| + 1 <= (2 : Real) * |x| := by
      linarith
    have hpow_le : (|x| + 1) ^ k <= ((2 : Real) * |x|) ^ k := by
      exact pow_le_pow_left₀
        (by positivity : 0 <= |x| + (1 : Real)) hbase_le k
    have hpow_le' : (|x| + 1) ^ k <= (2 : Real) ^ k * |x| ^ k := by
      simpa [mul_pow] using hpow_le
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_right hpow_le' (Real.exp_pos _).le
  exact squeeze_zero' hnonneg hupper hscaled

/--
The `pi`-normalized Gaussian horizontal-strip majorant has a global finite
bound for every fixed strip width.
-/
theorem exists_bound_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant
    (k : Nat) (A : Real) :
    ∃ C : Real, ∀ x : Real,
      (|x| + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2)) <= C := by
  let majorant : Real -> Real :=
    fun x => (|x| + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - x ^ 2))
  have hcont : Continuous majorant := by
    dsimp [majorant]
    fun_prop
  have htendsto : Tendsto majorant (cocompact Real) (nhds 0) := by
    simpa [majorant] using
      tendsto_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant_cocompact
        k A
  have hmajorant_one_pos : 0 < majorant 1 := by
    dsimp [majorant]
    positivity
  have heventual :
      ∀ᶠ x in cocompact Real, majorant x <= majorant 1 := by
    have hball :
        Metric.ball (0 : Real) (majorant 1) ∈ nhds (0 : Real) :=
      Metric.ball_mem_nhds (0 : Real) hmajorant_one_pos
    filter_upwards [htendsto.eventually hball] with x hx
    have hx_abs : abs (majorant x) < majorant 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    exact le_of_lt (lt_of_abs_lt hx_abs)
  rcases hcont.exists_forall_ge' (1 : Real) heventual with ⟨xmax, hmax⟩
  exact ⟨majorant xmax, hmax⟩

/--
Global Fourier-side shifted-radius envelope for horizontal lines of the
`pi`-normalized Gaussian source, uniform over every bounded horizontal strip.
-/
theorem exists_bound_norm_fourier_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
    (k : Nat) {A : Real} (hA : 0 <= A) :
    ∃ C : Real, ∀ t y : Real, abs y <= A ->
      norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
        (abs t + 2) ^ k <= C := by
  rcases
    exists_bound_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant
      k A with ⟨C, hC⟩
  refine ⟨(A + 3) ^ k * C, ?_⟩
  intro t y hy
  let u : Real := t + y
  have hnorm :
      norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) <=
        Real.exp (Real.pi * (A ^ 2 - u ^ 2)) := by
    simpa [u] using
      norm_fourier_guinandWeilPiGaussianSource_le_horizontalStripMajorant
        hA t y hy
  have hshift_le : abs t + 2 <= (A + 3) * (abs u + 1) := by
    have ht_abs : abs t <= abs u + abs y := by
      have h := abs_add_le u (-y)
      simpa [u, add_assoc, add_left_comm, add_comm] using h
    calc
      abs t + 2 <= abs u + abs y + 2 := by
        linarith
      _ <= abs u + A + 2 := by
        linarith
      _ <= (A + 3) * (abs u + 1) := by
        have hu_nonneg : 0 <= abs u := abs_nonneg u
        nlinarith
  have hshift_pow :
      (abs t + 2) ^ k <= ((A + 3) * (abs u + 1)) ^ k := by
    exact pow_le_pow_left₀
      (by
        have ht_nonneg : 0 <= abs t := abs_nonneg t
        linarith)
      hshift_le k
  have hshift_pow' :
      (abs t + 2) ^ k <= (A + 3) ^ k * (abs u + 1) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hmul :
      norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
        (abs t + 2) ^ k <=
        Real.exp (Real.pi * (A ^ 2 - u ^ 2)) *
          ((A + 3) ^ k * (abs u + 1) ^ k) := by
    exact mul_le_mul hnorm hshift_pow'
      (pow_nonneg
        (by
          have ht_nonneg : 0 <= abs t := abs_nonneg t
          linarith : 0 <= abs t + (2 : Real))
        k)
      (Real.exp_pos _).le
  calc
    norm ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) *
      (abs t + 2) ^ k
        <= Real.exp (Real.pi * (A ^ 2 - u ^ 2)) *
          ((A + 3) ^ k * (abs u + 1) ^ k) := hmul
    _ = (A + 3) ^ k *
          ((abs u + 1) ^ k *
            Real.exp (Real.pi * (A ^ 2 - u ^ 2))) := by
      ring
    _ <= (A + 3) ^ k * C := by
      exact mul_le_mul_of_nonneg_left (hC u)
        (pow_nonneg (by linarith : 0 <= A + 3) k)

/--
Global Fourier-side shifted-radius envelope for horizontal lines of the
`pi`-normalized Gaussian source, using the actual complex radius
`‖t + i y‖ + 2` on bounded horizontal strips.
-/
theorem exists_bound_norm_fourier_mul_complexShiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
    (k : Nat) {A : Real} (hA : 0 <= A) :
    ∃ C : Real, ∀ t y : Real, abs y <= A ->
      norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
        (norm ((t : Complex) + (y : Complex) * Complex.I) + 2) ^ k <= C := by
  rcases
    exists_bound_norm_fourier_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
      k hA with ⟨C, hC⟩
  refine ⟨(A + 2) ^ k * C, ?_⟩
  intro t y hy
  let z : Complex := (t : Complex) + (y : Complex) * Complex.I
  have hnorm_z_le : norm z <= |t| + |y| := by
    calc
      norm z <= norm (t : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |t| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (A + 2) * (abs t + 2) := by
    calc
      norm z + 2 <= |t| + |y| + 2 := by
        linarith
      _ <= |t| + A + 2 := by
        linarith
      _ <= (A + 2) * (abs t + 2) := by
        have ht_nonneg : 0 <= abs t := abs_nonneg t
        nlinarith
  have hshift_pow :
      (norm z + 2) ^ k <= ((A + 2) * (abs t + 2)) ^ k := by
    exact pow_le_pow_left₀
      (by
        have hz_nonneg : 0 <= norm z := norm_nonneg z
        linarith)
      hshift_le k
  have hshift_pow' :
      (norm z + 2) ^ k <= (A + 2) ^ k * (abs t + 2) ^ k := by
    simpa [mul_pow] using hshift_pow
  calc
    norm ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) *
      (norm ((t : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm ((𝓕 fun x : Real =>
            guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (norm z + 2) ^ k := by
            rfl
    _ <= norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
        ((A + 2) ^ k * (abs t + 2) ^ k) := by
          exact mul_le_mul_of_nonneg_left hshift_pow'
            (norm_nonneg _)
    _ = (A + 2) ^ k *
        (norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (abs t + 2) ^ k) := by
          ring
    _ <= (A + 2) ^ k * C := by
      exact mul_le_mul_of_nonneg_left (hC t y hy)
        (pow_nonneg (by linarith : 0 <= A + 2) k)

/--
For each fixed horizontal line, the Fourier-side shifted-radius Gaussian
envelope tends to zero in the real frequency direction.
-/
theorem tendsto_norm_fourier_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalLine_cocompact
    (k : Nat) (y : Real) :
    Tendsto
      (fun t : Real =>
        norm ((𝓕 fun x : Real =>
            guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (abs t + 2) ^ k)
      (cocompact Real) (nhds 0) := by
  let A : Real := abs y
  let majorant : Real -> Real :=
    fun u => (abs u + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - u ^ 2))
  have hmajorant_tendsto :
      Tendsto majorant (cocompact Real) (nhds 0) := by
    simpa [majorant] using
      tendsto_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant_cocompact
        k A
  have htranslate :
      Tendsto (fun t : Real => t + y) (cocompact Real) (cocompact Real) := by
    simpa [Metric.cobounded_eq_cocompact] using
      (tendsto_add_const_cobounded (R := Real) y)
  have hscaled :
      Tendsto
        (fun t : Real => (A + 3) ^ k * majorant (t + y))
        (cocompact Real) (nhds 0) := by
    simpa using
      (hmajorant_tendsto.comp htranslate).const_mul ((A + 3) ^ k)
  have hnonneg :
      ∀ᶠ t : Real in cocompact Real,
        0 <=
          norm ((𝓕 fun x : Real =>
              guinandWeilPiGaussianSource
                ((x : Complex) + (y : Complex) * Complex.I)) t) *
            (abs t + 2) ^ k := by
    exact Eventually.of_forall fun t =>
      mul_nonneg
        (norm_nonneg _)
        (pow_nonneg
          (by
            have ht_nonneg : 0 <= abs t := abs_nonneg t
            linarith : 0 <= abs t + (2 : Real))
          k)
  have hupper :
      ∀ᶠ t : Real in cocompact Real,
        norm ((𝓕 fun x : Real =>
            guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (abs t + 2) ^ k <=
        (A + 3) ^ k * majorant (t + y) := by
    exact Eventually.of_forall fun t => by
      let u : Real := t + y
      have hA : 0 <= A := by
        exact abs_nonneg y
      have hnorm :
          norm ((𝓕 fun x : Real =>
              guinandWeilPiGaussianSource
                ((x : Complex) + (y : Complex) * Complex.I)) t) <=
            Real.exp (Real.pi * (A ^ 2 - u ^ 2)) := by
        simpa [A, u] using
          norm_fourier_guinandWeilPiGaussianSource_le_horizontalStripMajorant
            (A := A) hA t y (by simp [A])
      have hshift_le : abs t + 2 <= (A + 3) * (abs u + 1) := by
        have ht_abs : abs t <= abs u + abs y := by
          have h := abs_add_le u (-y)
          simpa [u, add_assoc, add_left_comm, add_comm] using h
        calc
          abs t + 2 <= abs u + abs y + 2 := by
            linarith
          _ <= abs u + A + 2 := by
            simp [A]
          _ <= (A + 3) * (abs u + 1) := by
            have hu_nonneg : 0 <= abs u := abs_nonneg u
            nlinarith
      have hshift_pow :
          (abs t + 2) ^ k <= ((A + 3) * (abs u + 1)) ^ k := by
        exact pow_le_pow_left₀
          (by
            have ht_nonneg : 0 <= abs t := abs_nonneg t
            linarith : 0 <= abs t + (2 : Real))
          hshift_le k
      have hshift_pow' :
          (abs t + 2) ^ k <= (A + 3) ^ k * (abs u + 1) ^ k := by
        simpa [mul_pow] using hshift_pow
      calc
        norm ((𝓕 fun x : Real =>
            guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (abs t + 2) ^ k
            <= Real.exp (Real.pi * (A ^ 2 - u ^ 2)) *
                ((A + 3) ^ k * (abs u + 1) ^ k) := by
              exact mul_le_mul hnorm hshift_pow'
                (pow_nonneg
                  (by
                    have ht_nonneg : 0 <= abs t := abs_nonneg t
                    linarith : 0 <= abs t + (2 : Real))
                  k)
                (Real.exp_pos _).le
        _ = (A + 3) ^ k *
              ((abs u + 1) ^ k *
                Real.exp (Real.pi * (A ^ 2 - u ^ 2))) := by
          ring
        _ = (A + 3) ^ k * majorant (t + y) := by
          simp [majorant, u]
  exact squeeze_zero' hnonneg hupper hscaled

/--
Uniform epsilon-form Fourier-side shifted-radius decay for the
`pi`-normalized Gaussian source on every bounded horizontal strip.
-/
theorem eventually_forall_norm_fourier_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ t : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        norm ((𝓕 fun x : Real =>
            guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (abs t + 2) ^ k <=
        epsilon := by
  classical
  let majorant : Real -> Real :=
    fun u => (abs u + 1) ^ k * Real.exp (Real.pi * (A ^ 2 - u ^ 2))
  have hscale_pos : 0 < (A + 3) ^ k :=
    pow_pos (by linarith : 0 < A + 3) k
  have hmajorant_tendsto :
      Tendsto majorant (cocompact Real) (nhds 0) := by
    simpa [majorant] using
      tendsto_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant_cocompact
        k A
  have hmajorant_small :
      ∀ᶠ u : Real in cocompact Real,
        majorant u <= epsilon / (A + 3) ^ k := by
    have hball :
        Metric.ball (0 : Real) (epsilon / (A + 3) ^ k) ∈
          nhds (0 : Real) :=
      Metric.ball_mem_nhds (0 : Real) (div_pos hepsilon hscale_pos)
    filter_upwards [hmajorant_tendsto.eventually hball] with u hu
    have hu_abs : abs (majorant u) < epsilon / (A + 3) ^ k := by
      simpa [Metric.mem_ball, Real.dist_eq] using hu
    exact le_of_lt (lt_of_abs_lt hu_abs)
  have hshifted_majorant_small :
      ∀ᶠ t : Real in cocompact Real,
        ∀ y : Real, abs y <= A ->
          majorant (t + y) <= epsilon / (A + 3) ^ k := by
    let S : Set Real :=
      {u : Real | majorant u <= epsilon / (A + 3) ^ k}
    let Y : Set Real := {y : Real | abs y <= A}
    have hS_mem : S ∈ cocompact Real := by
      simpa [S] using hmajorant_small
    have hS_bounded_compl : Bornology.IsBounded Sᶜ := by
      rw [Bornology.isBounded_def]
      simpa [Metric.cobounded_eq_cocompact] using hS_mem
    have hY_subset_closedBall : Y ⊆ Metric.closedBall (0 : Real) A := by
      intro y hy
      have hy' : abs y <= A := by
        simpa [Y] using hy
      simpa [Metric.mem_closedBall, Real.dist_eq] using hy'
    have hY_bounded : Bornology.IsBounded Y :=
      Metric.isBounded_closedBall.subset hY_subset_closedBall
    let T : Set Real :=
      {t : Real | ∀ y : Real, y ∈ Y -> t + y ∈ S}
    have hT_compl_subset : Tᶜ ⊆ Sᶜ - Y := by
      intro t ht
      have hnot : ¬ ∀ y : Real, y ∈ Y -> t + y ∈ S := by
        simpa [T] using ht
      push Not at hnot
      rcases hnot with ⟨y, hyY, hyS⟩
      rw [Set.mem_sub]
      refine ⟨t + y, ?_, y, hyY, ?_⟩
      · simpa using hyS
      · ring
    have hT_compl_bounded : Bornology.IsBounded Tᶜ :=
      (isBounded_sub hS_bounded_compl hY_bounded).subset hT_compl_subset
    have hT_mem_cobounded : T ∈ Bornology.cobounded Real := by
      simpa [Bornology.isBounded_def] using hT_compl_bounded
    have hT_mem : T ∈ cocompact Real := by
      simpa [Metric.cobounded_eq_cocompact] using hT_mem_cobounded
    filter_upwards [hT_mem] with t ht y hy
    exact ht y (by simpa [Y] using hy)
  filter_upwards [hshifted_majorant_small] with t ht y hy
  let u : Real := t + y
  have hmajorant_u :
      majorant u <= epsilon / (A + 3) ^ k := by
    simpa [u] using ht y hy
  have hnorm :
      norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) <=
        Real.exp (Real.pi * (A ^ 2 - u ^ 2)) := by
    simpa [u] using
      norm_fourier_guinandWeilPiGaussianSource_le_horizontalStripMajorant
        hA t y hy
  have hshift_le : abs t + 2 <= (A + 3) * (abs u + 1) := by
    have ht_abs : abs t <= abs u + abs y := by
      have h := abs_add_le u (-y)
      simpa [u, add_assoc, add_left_comm, add_comm] using h
    calc
      abs t + 2 <= abs u + abs y + 2 := by
        linarith
      _ <= abs u + A + 2 := by
        linarith
      _ <= (A + 3) * (abs u + 1) := by
        have hu_nonneg : 0 <= abs u := abs_nonneg u
        nlinarith
  have hshift_pow :
      (abs t + 2) ^ k <= ((A + 3) * (abs u + 1)) ^ k := by
    exact pow_le_pow_left₀
      (by
        have ht_nonneg : 0 <= abs t := abs_nonneg t
        linarith : 0 <= abs t + (2 : Real))
      hshift_le k
  have hshift_pow' :
      (abs t + 2) ^ k <= (A + 3) ^ k * (abs u + 1) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hbound :
      norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
        (abs t + 2) ^ k <=
        (A + 3) ^ k * majorant u := by
    calc
      norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
        (abs t + 2) ^ k
          <= Real.exp (Real.pi * (A ^ 2 - u ^ 2)) *
              ((A + 3) ^ k * (abs u + 1) ^ k) := by
            exact mul_le_mul hnorm hshift_pow'
              (pow_nonneg
                (by
                  have ht_nonneg : 0 <= abs t := abs_nonneg t
                  linarith : 0 <= abs t + (2 : Real))
                k)
              (Real.exp_pos _).le
      _ = (A + 3) ^ k *
            ((abs u + 1) ^ k *
              Real.exp (Real.pi * (A ^ 2 - u ^ 2))) := by
        ring
      _ = (A + 3) ^ k * majorant u := by
        simp [majorant]
  calc
    norm ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) *
      (abs t + 2) ^ k
        <= (A + 3) ^ k * majorant u := hbound
    _ <= (A + 3) ^ k * (epsilon / (A + 3) ^ k) := by
      exact mul_le_mul_of_nonneg_left hmajorant_u
        (pow_nonneg (by linarith : 0 <= A + 3) k)
    _ = epsilon := by
      field_simp [ne_of_gt hscale_pos]

/--
Uniform epsilon-form Fourier-side shifted-radius decay for the
`pi`-normalized Gaussian source on every bounded horizontal strip, using the
actual complex radius `‖t + i y‖ + 2`.
-/
theorem eventually_forall_norm_fourier_mul_complexShiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ t : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        norm ((𝓕 fun x : Real =>
            guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (norm ((t : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  have hscale_pos : 0 < (A + 2) ^ k :=
    pow_pos (by linarith : 0 < A + 2) k
  have hsmall :
      ∀ᶠ t : Real in cocompact Real,
        ∀ y : Real, abs y <= A ->
          norm ((𝓕 fun x : Real =>
              guinandWeilPiGaussianSource
                ((x : Complex) + (y : Complex) * Complex.I)) t) *
            (abs t + 2) ^ k <=
          epsilon / (A + 2) ^ k :=
    eventually_forall_norm_fourier_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
      k hA (div_pos hepsilon hscale_pos)
  filter_upwards [hsmall] with t ht y hy
  let z : Complex := (t : Complex) + (y : Complex) * Complex.I
  have hnorm_z_le : norm z <= |t| + |y| := by
    calc
      norm z <= norm (t : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |t| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (A + 2) * (abs t + 2) := by
    calc
      norm z + 2 <= |t| + |y| + 2 := by
        linarith
      _ <= |t| + A + 2 := by
        linarith
      _ <= (A + 2) * (abs t + 2) := by
        have ht_nonneg : 0 <= abs t := abs_nonneg t
        nlinarith
  have hshift_pow :
      (norm z + 2) ^ k <= ((A + 2) * (abs t + 2)) ^ k := by
    exact pow_le_pow_left₀
      (by
        have hz_nonneg : 0 <= norm z := norm_nonneg z
        linarith)
      hshift_le k
  have hshift_pow' :
      (norm z + 2) ^ k <= (A + 2) ^ k * (abs t + 2) ^ k := by
    simpa [mul_pow] using hshift_pow
  calc
    norm ((𝓕 fun x : Real =>
        guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) t) *
      (norm ((t : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm ((𝓕 fun x : Real =>
            guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (norm z + 2) ^ k := by
            rfl
    _ <= norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
        ((A + 2) ^ k * (abs t + 2) ^ k) := by
          exact mul_le_mul_of_nonneg_left hshift_pow'
            (norm_nonneg _)
    _ = (A + 2) ^ k *
        (norm ((𝓕 fun x : Real =>
          guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) t) *
          (abs t + 2) ^ k) := by
          ring
    _ <= (A + 2) ^ k * (epsilon / (A + 2) ^ k) := by
      exact mul_le_mul_of_nonneg_left (ht y hy)
        (pow_nonneg (by linarith : 0 <= A + 2) k)
    _ = epsilon := by
      field_simp [ne_of_gt hscale_pos]

/--
Global shifted-radius horizontal-strip envelope for the `pi`-normalized
Gaussian source on every fixed horizontal strip.
-/
theorem exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
    (k : Nat) {A : Real} (hA : 0 <= A) :
    ∃ C : Real, ∀ x y : Real, abs y <= A ->
      norm (guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <= C := by
  rcases
    exists_bound_abs_add_one_pow_mul_guinandWeilPiGaussianHorizontalStripMajorant
      k A with ⟨C, hC⟩
  refine ⟨(A + 3) ^ k * C, ?_⟩
  intro x y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have hnorm_source :
      norm (guinandWeilPiGaussianSource z) <=
        Real.exp (Real.pi * (A ^ 2 - x ^ 2)) := by
    simpa [z] using
      (norm_guinandWeilPiGaussianSource_le_horizontalStrip
        (A := A) hA (z := z) (by simpa [z] using hy))
  have hnorm_z_le : norm z <= |x| + |y| := by
    calc
      norm z <= norm (x : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |x| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (A + 3) * (|x| + 1) := by
    calc
      norm z + 2 <= |x| + |y| + 2 := by
        linarith
      _ <= |x| + A + 2 := by
        linarith
      _ <= (A + 3) * (|x| + 1) := by
        have hx_nonneg : 0 <= |x| := abs_nonneg x
        nlinarith
  have hshift_pow :
      (norm z + 2) ^ k <= ((A + 3) * (|x| + 1)) ^ k := by
    exact pow_le_pow_left₀
      (by
        have hz_nonneg : 0 <= norm z := norm_nonneg z
        linarith)
      hshift_le k
  have hshift_pow' :
      (norm z + 2) ^ k <= (A + 3) ^ k * (|x| + 1) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hmul :
      norm (guinandWeilPiGaussianSource z) * (norm z + 2) ^ k <=
        Real.exp (Real.pi * (A ^ 2 - x ^ 2)) *
          ((A + 3) ^ k * (|x| + 1) ^ k) := by
    exact mul_le_mul hnorm_source hshift_pow'
      (pow_nonneg
        (by
          have hz_nonneg : 0 <= norm z := norm_nonneg z
          linarith : 0 <= norm z + (2 : Real))
        k)
      (Real.exp_pos _).le
  calc
    norm (guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (guinandWeilPiGaussianSource z) * (norm z + 2) ^ k := by
          rfl
    _ <= Real.exp (Real.pi * (A ^ 2 - x ^ 2)) *
          ((A + 3) ^ k * (|x| + 1) ^ k) := hmul
    _ = (A + 3) ^ k *
          ((|x| + 1) ^ k *
            Real.exp (Real.pi * (A ^ 2 - x ^ 2))) := by
      ring
    _ <= (A + 3) ^ k * C := by
      exact mul_le_mul_of_nonneg_left (hC x)
        (pow_nonneg (by linarith : 0 <= A + 3) k)

/--
Global first-derivative shifted-radius horizontal-strip envelope for the
`pi`-normalized Gaussian source.
-/
theorem exists_bound_norm_deriv_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
    (k : Nat) {A : Real} (hA : 0 <= A) :
    ∃ C : Real, ∀ x y : Real, abs y <= A ->
      norm (deriv guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <= C := by
  rcases
    exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
      (k + 1) hA with ⟨C, hC⟩
  refine ⟨(2 * Real.pi) * C, ?_⟩
  intro x y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  let R : Real := norm z + 2
  have htwo_pi_nonneg : 0 <= 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hz_le_R : norm z <= R := by
    dsimp [R]
    linarith
  have hderiv_base :
      norm (deriv guinandWeilPiGaussianSource z) <=
        (2 * Real.pi) * norm z * norm (guinandWeilPiGaussianSource z) :=
    norm_deriv_guinandWeilPiGaussianSource_le z
  have hderiv_R :
      norm (deriv guinandWeilPiGaussianSource z) <=
        (2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * R := by
    calc
      norm (deriv guinandWeilPiGaussianSource z)
          <= (2 * Real.pi) * norm z * norm (guinandWeilPiGaussianSource z) :=
            hderiv_base
      _ = (2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * norm z := by
        ring
      _ <= (2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * R := by
        exact mul_le_mul_of_nonneg_left hz_le_R
          (mul_nonneg htwo_pi_nonneg (norm_nonneg _))
  calc
    norm (deriv guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
      (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (deriv guinandWeilPiGaussianSource z) * R ^ k := by
          rfl
    _ <= ((2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * R) *
        R ^ k := by
          exact mul_le_mul_of_nonneg_right hderiv_R
            (pow_nonneg hR_nonneg k)
    _ = (2 * Real.pi) *
        (norm (guinandWeilPiGaussianSource z) * R ^ (k + 1)) := by
          rw [pow_succ']
          ring
    _ <= (2 * Real.pi) * C := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [z, R] using hC x y hy) htwo_pi_nonneg

/--
Uniform epsilon-form first-derivative shifted-radius decay for the
`pi`-normalized Gaussian source on every bounded horizontal strip.
-/
theorem eventually_forall_norm_deriv_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        norm (deriv guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) *
          (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  have htwo_pi_pos : 0 < 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have htwo_pi_nonneg : 0 <= 2 * Real.pi := htwo_pi_pos.le
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ y : Real, abs y <= A ->
          norm (guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) *
            (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ (k + 1) <=
          epsilon / (2 * Real.pi) :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
      (k + 1) hA (div_pos hepsilon htwo_pi_pos)
  filter_upwards [hsmall] with x hx y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  let R : Real := norm z + 2
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hz_le_R : norm z <= R := by
    dsimp [R]
    linarith
  have hderiv_base :
      norm (deriv guinandWeilPiGaussianSource z) <=
        (2 * Real.pi) * norm z * norm (guinandWeilPiGaussianSource z) :=
    norm_deriv_guinandWeilPiGaussianSource_le z
  have hderiv_R :
      norm (deriv guinandWeilPiGaussianSource z) <=
        (2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * R := by
    calc
      norm (deriv guinandWeilPiGaussianSource z)
          <= (2 * Real.pi) * norm z * norm (guinandWeilPiGaussianSource z) :=
            hderiv_base
      _ = (2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * norm z := by
        ring
      _ <= (2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * R := by
        exact mul_le_mul_of_nonneg_left hz_le_R
          (mul_nonneg htwo_pi_nonneg (norm_nonneg _))
  calc
    norm (deriv guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
      (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (deriv guinandWeilPiGaussianSource z) * R ^ k := by
          rfl
    _ <= ((2 * Real.pi) * norm (guinandWeilPiGaussianSource z) * R) *
        R ^ k := by
          exact mul_le_mul_of_nonneg_right hderiv_R
            (pow_nonneg hR_nonneg k)
    _ = (2 * Real.pi) *
        (norm (guinandWeilPiGaussianSource z) * R ^ (k + 1)) := by
          rw [pow_succ']
          ring
    _ <= (2 * Real.pi) * (epsilon / (2 * Real.pi)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [z, R] using hx y hy) htwo_pi_nonneg
    _ = epsilon := by
      field_simp [ne_of_gt htwo_pi_pos]

/--
Global finite-order derivative shifted-radius horizontal-strip envelope for the
`pi`-normalized Gaussian source.  The derivative order is arbitrary but fixed.
-/
theorem exists_bound_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
    (m k : Nat) {A : Real} (hA : 0 <= A) :
    ∃ C : Real, ∀ x y : Real, abs y <= A ->
      norm (iteratedDeriv m guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <= C := by
  let P : Polynomial Complex := guinandWeilPiGaussianDerivativePolynomial m
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow P with
    ⟨B, hB_pos, hB⟩
  rcases
    exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
      (P.natDegree + k) hA with ⟨C, hC⟩
  refine ⟨B * C, ?_⟩
  intro x y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  let R : Real := norm z + 2
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hiter :
      norm (iteratedDeriv m guinandWeilPiGaussianSource z) <=
        B * R ^ P.natDegree * norm (guinandWeilPiGaussianSource z) := by
    rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [P, R] using hB z) (norm_nonneg _)
  calc
    norm (iteratedDeriv m guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
      (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (iteratedDeriv m guinandWeilPiGaussianSource z) * R ^ k := by
          rfl
    _ <= (B * R ^ P.natDegree * norm (guinandWeilPiGaussianSource z)) *
        R ^ k := by
          exact mul_le_mul_of_nonneg_right hiter (pow_nonneg hR_nonneg k)
    _ = B * (norm (guinandWeilPiGaussianSource z) *
        R ^ (P.natDegree + k)) := by
          rw [pow_add]
          ring
    _ <= B * C := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [P, z, R] using hC x y hy) hB_pos.le

/--
Uniform epsilon-form finite-order derivative shifted-radius decay for the
`pi`-normalized Gaussian source on every bounded horizontal strip.  This is
the all-finite-order version of the concrete Gaussian strip source estimate.
-/
theorem eventually_forall_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (m k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        norm (iteratedDeriv m guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) *
          (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  let P : Polynomial Complex := guinandWeilPiGaussianDerivativePolynomial m
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow P with
    ⟨B, hB_pos, hB⟩
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ y : Real, abs y <= A ->
          norm (guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) *
            (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^
              (P.natDegree + k) <=
          epsilon / B :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
      (P.natDegree + k) hA (div_pos hepsilon hB_pos)
  filter_upwards [hsmall] with x hx y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  let R : Real := norm z + 2
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hiter :
      norm (iteratedDeriv m guinandWeilPiGaussianSource z) <=
        B * R ^ P.natDegree * norm (guinandWeilPiGaussianSource z) := by
    rw [iteratedDeriv_guinandWeilPiGaussianSource_eq_derivativePolynomial]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [P, R] using hB z) (norm_nonneg _)
  calc
    norm (iteratedDeriv m guinandWeilPiGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
      (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (iteratedDeriv m guinandWeilPiGaussianSource z) * R ^ k := by
          rfl
    _ <= (B * R ^ P.natDegree * norm (guinandWeilPiGaussianSource z)) *
        R ^ k := by
          exact mul_le_mul_of_nonneg_right hiter (pow_nonneg hR_nonneg k)
    _ = B * (norm (guinandWeilPiGaussianSource z) *
        R ^ (P.natDegree + k)) := by
          rw [pow_add]
          ring
    _ <= B * (epsilon / B) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [P, z, R] using hx y hy) hB_pos.le
    _ = epsilon := by
      field_simp [ne_of_gt hB_pos]

/--
Uniform epsilon-form real-coordinate polynomial decay for every finite complex
derivative of the `pi`-normalized Gaussian on each bounded horizontal strip.
This is the classical Guinand-Weil strip-decay shape with weight
`(abs x + 1)^k`.
-/
theorem eventually_forall_abs_add_one_pow_mul_norm_iteratedDeriv_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (m k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        (|x| + 1) ^ k *
          norm (iteratedDeriv m guinandWeilPiGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) <=
        epsilon := by
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ y : Real, abs y <= A ->
          norm (iteratedDeriv m guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) *
            (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
          epsilon :=
    eventually_forall_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
      m k hA hepsilon
  filter_upwards [hsmall] with x hx y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have hx_le_norm : |x| <= norm z := by
    simpa [z] using (Complex.abs_re_le_norm z)
  have hbase :
      |x| + 1 <= norm z + 2 := by
    linarith
  have hpow :
      (|x| + 1) ^ k <= (norm z + 2) ^ k := by
    exact pow_le_pow_left₀
      (by positivity : 0 <= |x| + (1 : Real)) hbase k
  calc
    (|x| + 1) ^ k *
        norm (iteratedDeriv m guinandWeilPiGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I))
        = (|x| + 1) ^ k *
          norm (iteratedDeriv m guinandWeilPiGaussianSource z) := by
            rfl
    _ = norm (iteratedDeriv m guinandWeilPiGaussianSource z) *
          (|x| + 1) ^ k := by
            ring
    _ <= norm (iteratedDeriv m guinandWeilPiGaussianSource z) *
          (norm z + 2) ^ k := by
            exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ <= epsilon := by
      simpa [z] using hx y hy

/--
Global finite-order derivative shifted-radius horizontal-strip envelope for the
closed-form Fourier-side horizontal-line extension of the `pi`-Gaussian.
-/
theorem exists_bound_norm_iteratedDeriv_fourierLineExtension_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
    (m k : Nat) {A : Real} (hA : 0 <= A) (y : Real) :
    ∃ C : Real, ∀ x v : Real, abs v <= A ->
      norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          ((x : Complex) + (v : Complex) * Complex.I)) *
        (norm ((x : Complex) + (v : Complex) * Complex.I) + 2) ^ k <= C := by
  let c : Complex := Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2)
  let scale : Real := norm c * (abs y + 2) ^ k
  have hscale_nonneg : 0 <= scale := by
    exact mul_nonneg (norm_nonneg c)
      (pow_nonneg (by linarith [abs_nonneg y] : 0 <= abs y + 2) k)
  rcases
    exists_bound_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
      m k hA with ⟨C, hC⟩
  refine ⟨scale * C, ?_⟩
  intro x v hv
  let z : Complex := (x : Complex) + (v : Complex) * Complex.I
  let w : Complex := z + (y : Complex)
  have hw_coord :
      w = ((x + y : Real) : Complex) + (v : Complex) * Complex.I := by
    dsimp [w, z]
    rw [Complex.ofReal_add]
    ring
  have hsource :
      norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
        (norm w + 2) ^ k <= C := by
    simpa [hw_coord] using hC (x + y) v hv
  have hshift_pow :
      (norm z + 2) ^ k <= (abs y + 2) ^ k * (norm w + 2) ^ k := by
    have hshift := norm_add_two_le_abs_real_add_two_mul_norm_add_real_add_two z y
    have hpow :
        (norm z + 2) ^ k <=
          ((abs y + 2) * (norm w + 2)) ^ k := by
      exact pow_le_pow_left₀
        (by linarith [norm_nonneg z] : 0 <= norm z + 2) hshift k
    simpa [w, mul_pow] using hpow
  have hderiv_eval :
      iteratedDeriv m
          (fun z : Complex =>
            c * guinandWeilPiGaussianSource (z + (y : Complex))) z =
        c * iteratedDeriv m guinandWeilPiGaussianSource w := by
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_add_const]
  calc
    norm (iteratedDeriv m
        (fun z : Complex =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource (z + (y : Complex)))
        ((x : Complex) + (v : Complex) * Complex.I)) *
      (norm ((x : Complex) + (v : Complex) * Complex.I) + 2) ^ k
        = norm (c * iteratedDeriv m guinandWeilPiGaussianSource w) *
          (norm z + 2) ^ k := by
            dsimp [c, z, w] at hderiv_eval ⊢
            rw [hderiv_eval]
    _ = norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
          (norm z + 2) ^ k := by
            rw [norm_mul]
    _ <= norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
          ((abs y + 2) ^ k * (norm w + 2) ^ k) := by
            exact mul_le_mul_of_nonneg_left hshift_pow
              (mul_nonneg (norm_nonneg c) (norm_nonneg _))
    _ = scale *
          (norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
            (norm w + 2) ^ k) := by
            simp [scale]
            ring
    _ <= scale * C := by
      exact mul_le_mul_of_nonneg_left hsource hscale_nonneg

/--
Uniform epsilon-form finite-order derivative shifted-radius decay for the
closed-form Fourier-side horizontal-line extension of the `pi`-Gaussian.
-/
theorem eventually_forall_norm_iteratedDeriv_fourierLineExtension_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (m k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) (y : Real) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ v : Real, abs v <= A ->
        norm (iteratedDeriv m
            (fun z : Complex =>
              Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
                guinandWeilPiGaussianSource (z + (y : Complex)))
            ((x : Complex) + (v : Complex) * Complex.I)) *
          (norm ((x : Complex) + (v : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  let c : Complex := Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2)
  let scale : Real := norm c * (abs y + 2) ^ k
  have hc_pos : 0 < norm c := by
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hfactor_pos : 0 < (abs y + 2) ^ k := by
    exact pow_pos (by linarith [abs_nonneg y] : 0 < abs y + 2) k
  have hscale_pos : 0 < scale := by
    exact mul_pos hc_pos hfactor_pos
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ v : Real, abs v <= A ->
          norm (iteratedDeriv m guinandWeilPiGaussianSource
              ((x : Complex) + (v : Complex) * Complex.I)) *
            (norm ((x : Complex) + (v : Complex) * Complex.I) + 2) ^ k <=
          epsilon / scale :=
    eventually_forall_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
      m k hA (div_pos hepsilon hscale_pos)
  have htranslate :
      Tendsto (fun x : Real => x + y) (cocompact Real) (cocompact Real) := by
    simpa [Metric.cobounded_eq_cocompact] using
      (tendsto_add_const_cobounded (R := Real) y)
  have hsmall_shifted :
      ∀ᶠ x : Real in cocompact Real,
        ∀ v : Real, abs v <= A ->
          norm (iteratedDeriv m guinandWeilPiGaussianSource
              (((x + y : Real) : Complex) + (v : Complex) * Complex.I)) *
            (norm (((x + y : Real) : Complex) + (v : Complex) * Complex.I) + 2) ^ k <=
          epsilon / scale := by
    exact htranslate.eventually hsmall
  filter_upwards [hsmall_shifted] with x hx v hv
  let z : Complex := (x : Complex) + (v : Complex) * Complex.I
  let w : Complex := z + (y : Complex)
  have hw_coord :
      w = ((x + y : Real) : Complex) + (v : Complex) * Complex.I := by
    dsimp [w, z]
    rw [Complex.ofReal_add]
    ring
  have hsource :
      norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
        (norm w + 2) ^ k <= epsilon / scale := by
    simpa [hw_coord] using hx v hv
  have hshift_pow :
      (norm z + 2) ^ k <= (abs y + 2) ^ k * (norm w + 2) ^ k := by
    have hshift := norm_add_two_le_abs_real_add_two_mul_norm_add_real_add_two z y
    have hpow :
        (norm z + 2) ^ k <=
          ((abs y + 2) * (norm w + 2)) ^ k := by
      exact pow_le_pow_left₀
        (by linarith [norm_nonneg z] : 0 <= norm z + 2) hshift k
    simpa [w, mul_pow] using hpow
  have hderiv_eval :
      iteratedDeriv m
          (fun z : Complex =>
            c * guinandWeilPiGaussianSource (z + (y : Complex))) z =
        c * iteratedDeriv m guinandWeilPiGaussianSource w := by
    rw [iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_add_const]
  calc
    norm (iteratedDeriv m
        (fun z : Complex =>
          Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
            guinandWeilPiGaussianSource (z + (y : Complex)))
        ((x : Complex) + (v : Complex) * Complex.I)) *
      (norm ((x : Complex) + (v : Complex) * Complex.I) + 2) ^ k
        = norm (c * iteratedDeriv m guinandWeilPiGaussianSource w) *
          (norm z + 2) ^ k := by
            dsimp [c, z, w] at hderiv_eval ⊢
            rw [hderiv_eval]
    _ = norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
          (norm z + 2) ^ k := by
            rw [norm_mul]
    _ <= norm c * norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
          ((abs y + 2) ^ k * (norm w + 2) ^ k) := by
            exact mul_le_mul_of_nonneg_left hshift_pow
              (mul_nonneg (norm_nonneg c) (norm_nonneg _))
    _ = scale *
          (norm (iteratedDeriv m guinandWeilPiGaussianSource w) *
            (norm w + 2) ^ k) := by
            simp [scale]
            ring
    _ <= scale * (epsilon / scale) := by
      exact mul_le_mul_of_nonneg_left hsource hscale_pos.le
    _ = epsilon := by
      field_simp [ne_of_gt hscale_pos]

/--
Uniform epsilon-form real-coordinate polynomial decay for every finite complex
derivative of the closed-form Fourier-side horizontal-line extension on each
bounded horizontal strip.
-/
theorem eventually_forall_abs_add_one_pow_mul_norm_iteratedDeriv_fourierLineExtension_guinandWeilPiGaussianSource_le_of_horizontalStrip
    (m k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) (y : Real) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ v : Real, abs v <= A ->
        (|x| + 1) ^ k *
          norm (iteratedDeriv m
            (fun z : Complex =>
              Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
                guinandWeilPiGaussianSource (z + (y : Complex)))
            ((x : Complex) + (v : Complex) * Complex.I)) <=
        epsilon := by
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ v : Real, abs v <= A ->
          norm (iteratedDeriv m
              (fun z : Complex =>
                Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
                  guinandWeilPiGaussianSource (z + (y : Complex)))
              ((x : Complex) + (v : Complex) * Complex.I)) *
            (norm ((x : Complex) + (v : Complex) * Complex.I) + 2) ^ k <=
          epsilon :=
    eventually_forall_norm_iteratedDeriv_fourierLineExtension_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
      m k hA hepsilon y
  filter_upwards [hsmall] with x hx v hv
  let z : Complex := (x : Complex) + (v : Complex) * Complex.I
  have hx_le_norm : |x| <= norm z := by
    simpa [z] using (Complex.abs_re_le_norm z)
  have hbase :
      |x| + 1 <= norm z + 2 := by
    linarith
  have hpow :
      (|x| + 1) ^ k <= (norm z + 2) ^ k := by
    exact pow_le_pow_left₀
      (by positivity : 0 <= |x| + (1 : Real)) hbase k
  calc
    (|x| + 1) ^ k *
        norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          ((x : Complex) + (v : Complex) * Complex.I))
        = (|x| + 1) ^ k *
          norm (iteratedDeriv m
            (fun z : Complex =>
              Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
                guinandWeilPiGaussianSource (z + (y : Complex)))
            z) := by
            rfl
    _ = norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          z) *
        (|x| + 1) ^ k := by
          ring
    _ <= norm (iteratedDeriv m
          (fun z : Complex =>
            Complex.exp ((Real.pi : Complex) * (y : Complex) ^ 2) *
              guinandWeilPiGaussianSource (z + (y : Complex)))
          z) *
        (norm z + 2) ^ k := by
          exact mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ <= epsilon := by
      simpa [z] using hx v hv

/-- Exact norm of the complex Gaussian in real/imaginary coordinates. -/
theorem norm_guinandWeilGaussianSource
    (z : Complex) :
    norm (guinandWeilGaussianSource z) =
      Real.exp (z.im ^ 2 - z.re ^ 2) := by
  unfold guinandWeilGaussianSource
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, pow_two]

/--
On the critical horizontal strip, the Gaussian norm is bounded by the real-axis
Gaussian with the explicit strip-loss factor `exp (1 / 4)`.
-/
theorem norm_guinandWeilGaussianSource_le_criticalStrip
    {z : Complex}
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (guinandWeilGaussianSource z) <=
      Real.exp ((1 / 4 : Real) - z.re ^ 2) := by
  rw [norm_guinandWeilGaussianSource]
  apply Real.exp_le_exp.mpr
  have him_sq : z.im ^ 2 <= (1 / 2 : Real) ^ 2 := by
    nlinarith
  nlinarith

/-- Exact norm of the Gaussian source on a fixed horizontal line. -/
theorem norm_guinandWeilGaussianSource_horizontalLine
    (x y : Real) :
    norm (guinandWeilGaussianSource ((x : Complex) + (y : Complex) * Complex.I)) =
      Real.exp (y ^ 2 - x ^ 2) := by
  simp [norm_guinandWeilGaussianSource]

/--
Uniform pointwise polynomial majorant for the Gaussian source on the critical
horizontal strip.
-/
theorem abs_rpow_mul_norm_guinandWeilGaussianSource_le_criticalStripMajorant
    (s x y : Real)
    (hy : |y| <= (1 / 2 : Real)) :
    |x| ^ s *
        norm (guinandWeilGaussianSource ((x : Complex) + (y : Complex) * Complex.I)) <=
      |x| ^ s * Real.exp ((1 / 4 : Real) - x ^ 2) := by
  have hy' := abs_le.mp hy
  have hnorm :
      norm (guinandWeilGaussianSource ((x : Complex) + (y : Complex) * Complex.I)) <=
        Real.exp ((1 / 4 : Real) - x ^ 2) := by
    have hlow :
        -(1 / 2 : Real) <= ((x : Complex) + (y : Complex) * Complex.I).im := by
      simpa using hy'.1
    have hhigh :
        ((x : Complex) + (y : Complex) * Complex.I).im <= (1 / 2 : Real) := by
      simpa using hy'.2
    simpa using
      (norm_guinandWeilGaussianSource_le_criticalStrip
        (z := (x : Complex) + (y : Complex) * Complex.I) hlow hhigh)
  exact mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg (abs_nonneg x) s)

/-- The real-axis Gaussian source has rapid polynomial decay. -/
theorem tendsto_abs_rpow_mul_norm_guinandWeilGaussianSource_real_cocompact
    (s : Real) :
    Tendsto
      (fun x : Real =>
        |x| ^ s * norm (guinandWeilGaussianSource (x : Complex)))
      (cocompact Real) (nhds 0) := by
  simpa [norm_guinandWeilGaussianSource, mul_comm] using
    (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 : Real)) (by norm_num) s)

/-- The uniform critical-strip Gaussian majorant has rapid polynomial decay. -/
theorem tendsto_abs_rpow_mul_guinandWeilGaussianCriticalStripMajorant_cocompact
    (s : Real) :
    Tendsto
      (fun x : Real => |x| ^ s * Real.exp ((1 / 4 : Real) - x ^ 2))
      (cocompact Real) (nhds 0) := by
  have hbase :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 : Real)) (by norm_num) s
  have hscaled :
      Tendsto
        (fun x : Real => Real.exp (1 / 4 : Real) *
          (|x| ^ s * Real.exp (-(1 : Real) * x ^ 2)))
        (cocompact Real) (nhds 0) := by
    simpa using hbase.const_mul (Real.exp (1 / 4 : Real))
  simpa [Real.exp_add, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    using hscaled

/--
Uniform epsilon-form horizontal-strip decay for the Gaussian source on the
critical strip.
-/
theorem eventually_forall_abs_rpow_mul_norm_guinandWeilGaussianSource_le_of_criticalStrip
    (s : Real) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= (1 / 2 : Real) ->
        |x| ^ s *
            norm (guinandWeilGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) <=
          epsilon := by
  have hmajor_tendsto :=
    tendsto_abs_rpow_mul_guinandWeilGaussianCriticalStripMajorant_cocompact s
  have hmajor_small :
      ∀ᶠ x : Real in cocompact Real,
        |x| ^ s * Real.exp ((1 / 4 : Real) - x ^ 2) <= epsilon := by
    have hball :
        Metric.ball (0 : Real) epsilon ∈ nhds (0 : Real) :=
      Metric.ball_mem_nhds (0 : Real) hepsilon
    filter_upwards [hmajor_tendsto.eventually hball] with x hx
    have hx_abs :
        abs (|x| ^ s * Real.exp ((1 / 4 : Real) - x ^ 2)) < epsilon := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    exact le_of_lt (lt_of_abs_lt hx_abs)
  filter_upwards [hmajor_small] with x hx y hy
  exact
    (abs_rpow_mul_norm_guinandWeilGaussianSource_le_criticalStripMajorant
      s x y hy).trans hx

/--
Uniform epsilon-form shifted-radius horizontal-strip decay for the Gaussian
source on the critical strip.
-/
theorem eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilGaussianSource_le_of_criticalStrip
    (k : Nat) {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= (1 / 2 : Real) ->
        norm (guinandWeilGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) *
          (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  have hscale_pos : 0 < (4 : Real) ^ k :=
    pow_pos (by norm_num) k
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ y : Real, abs y <= (1 / 2 : Real) ->
          |x| ^ (k : Real) *
              norm (guinandWeilGaussianSource
                ((x : Complex) + (y : Complex) * Complex.I)) <=
            epsilon / (4 : Real) ^ k :=
    eventually_forall_abs_rpow_mul_norm_guinandWeilGaussianSource_le_of_criticalStrip
      (k : Real) (div_pos hepsilon hscale_pos)
  have hlarge : ∀ᶠ x : Real in cocompact Real, 1 <= |x| := by
    have h :=
      (tendsto_norm_cocompact_atTop (E := Real)).eventually
        (eventually_ge_atTop (1 : Real))
    simpa [Real.norm_eq_abs] using h
  filter_upwards [hsmall, hlarge] with x hxsmall hxlarge y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have hnorm_z_le : norm z <= |x| + |y| := by
    calc
      norm z <= norm (x : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |x| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (4 : Real) * |x| := by
    have hy_half : |y| <= (1 / 2 : Real) := hy
    calc
      norm z + 2 <= |x| + |y| + 2 := by
        linarith
      _ <= |x| + (1 / 2 : Real) + 2 := by
        linarith
      _ <= (4 : Real) * |x| := by
        nlinarith
  have hshift_nonneg : 0 <= norm z + 2 := by
    have hz_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hshift_pow :
      (norm z + 2) ^ k <= ((4 : Real) * |x|) ^ k :=
    pow_le_pow_left₀ hshift_nonneg hshift_le k
  have hshift_pow_scaled :
      (norm z + 2) ^ k <= (4 : Real) ^ k * |x| ^ k := by
    simpa [mul_pow] using hshift_pow
  have hxsmall_nat :
      |x| ^ k *
          norm (guinandWeilGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I)) <=
        epsilon / (4 : Real) ^ k := by
    simpa [Real.rpow_natCast] using hxsmall y hy
  calc
    norm (guinandWeilGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (guinandWeilGaussianSource z) * (norm z + 2) ^ k := by
          rfl
    _ <= norm (guinandWeilGaussianSource z) * ((4 : Real) ^ k * |x| ^ k) := by
      exact mul_le_mul_of_nonneg_left hshift_pow_scaled
        (norm_nonneg (guinandWeilGaussianSource z))
    _ = (4 : Real) ^ k *
        (|x| ^ k *
          norm (guinandWeilGaussianSource
            ((x : Complex) + (y : Complex) * Complex.I))) := by
      simp [z, mul_assoc, mul_left_comm, mul_comm]
    _ <= (4 : Real) ^ k * (epsilon / (4 : Real) ^ k) := by
      exact mul_le_mul_of_nonneg_left hxsmall_nat
        (pow_nonneg (by norm_num : (0 : Real) <= 4) k)
    _ = epsilon := by
      field_simp [ne_of_gt hscale_pos]

/--
The one-dimensional majorant controlling the Gaussian source on the critical
strip has rapid decay.
-/
theorem tendsto_abs_add_one_pow_mul_guinandWeilGaussianCriticalStripMajorant_cocompact
    (k : Nat) :
    Tendsto
      (fun x : Real =>
        (|x| + 1) ^ k * Real.exp ((1 / 4 : Real) - x ^ 2))
      (cocompact Real) (nhds 0) := by
  have hbase :=
    tendsto_abs_rpow_mul_guinandWeilGaussianCriticalStripMajorant_cocompact
      (k : Real)
  have hscaled :
      Tendsto
        (fun x : Real =>
          (2 : Real) ^ k *
            (|x| ^ k * Real.exp ((1 / 4 : Real) - x ^ 2)))
        (cocompact Real) (nhds 0) := by
    simpa [Real.rpow_natCast, mul_assoc, mul_left_comm, mul_comm] using
      hbase.const_mul ((2 : Real) ^ k)
  have hnonneg :
      ∀ᶠ x : Real in cocompact Real,
        0 <= (|x| + 1) ^ k * Real.exp ((1 / 4 : Real) - x ^ 2) :=
    Eventually.of_forall fun x =>
      mul_nonneg
        (pow_nonneg (by positivity : 0 <= |x| + (1 : Real)) k)
        (Real.exp_pos _).le
  have hupper :
      ∀ᶠ x : Real in cocompact Real,
        (|x| + 1) ^ k * Real.exp ((1 / 4 : Real) - x ^ 2) <=
          (2 : Real) ^ k *
            (|x| ^ k * Real.exp ((1 / 4 : Real) - x ^ 2)) := by
    have hlarge : ∀ᶠ x : Real in cocompact Real, 1 <= |x| := by
      have h :=
        (tendsto_norm_cocompact_atTop (E := Real)).eventually
          (eventually_ge_atTop (1 : Real))
      simpa [Real.norm_eq_abs] using h
    filter_upwards [hlarge] with x hxlarge
    have hbase_le : |x| + 1 <= (2 : Real) * |x| := by
      linarith
    have hpow_le : (|x| + 1) ^ k <= ((2 : Real) * |x|) ^ k := by
      exact pow_le_pow_left₀
        (by positivity : 0 <= |x| + (1 : Real)) hbase_le k
    have hpow_le' : (|x| + 1) ^ k <= (2 : Real) ^ k * |x| ^ k := by
      simpa [mul_pow] using hpow_le
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_right hpow_le' (Real.exp_pos _).le
  exact squeeze_zero' hnonneg hupper hscaled

/-- The Gaussian critical-strip majorant has a global finite bound. -/
theorem exists_bound_abs_add_one_pow_mul_guinandWeilGaussianCriticalStripMajorant
    (k : Nat) :
    ∃ C : Real, ∀ x : Real,
      (|x| + 1) ^ k * Real.exp ((1 / 4 : Real) - x ^ 2) <= C := by
  let majorant : Real -> Real :=
    fun x => (|x| + 1) ^ k * Real.exp ((1 / 4 : Real) - x ^ 2)
  have hcont : Continuous majorant := by
    dsimp [majorant]
    fun_prop
  have htendsto : Tendsto majorant (cocompact Real) (nhds 0) := by
    simpa [majorant] using
      tendsto_abs_add_one_pow_mul_guinandWeilGaussianCriticalStripMajorant_cocompact
        k
  have hmajorant_one_pos : 0 < majorant 1 := by
    dsimp [majorant]
    positivity
  have heventual :
      ∀ᶠ x in cocompact Real, majorant x <= majorant 1 := by
    have hball :
        Metric.ball (0 : Real) (majorant 1) ∈ nhds (0 : Real) :=
      Metric.ball_mem_nhds (0 : Real) hmajorant_one_pos
    filter_upwards [htendsto.eventually hball] with x hx
    have hx_abs : abs (majorant x) < majorant 1 := by
      simpa [Metric.mem_ball, Real.dist_eq] using hx
    exact le_of_lt (lt_of_abs_lt hx_abs)
  rcases hcont.exists_forall_ge' (1 : Real) heventual with ⟨xmax, hmax⟩
  exact ⟨majorant xmax, hmax⟩

/--
Global shifted-radius horizontal-strip envelope for the concrete Gaussian
source on the critical strip.
-/
theorem exists_bound_norm_mul_shiftedRadius_pow_guinandWeilGaussianSource_criticalStrip
    (k : Nat) :
    ∃ C : Real, ∀ x y : Real, abs y <= (1 / 2 : Real) ->
      norm (guinandWeilGaussianSource
          ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <= C := by
  rcases
    exists_bound_abs_add_one_pow_mul_guinandWeilGaussianCriticalStripMajorant k
      with ⟨C, hC⟩
  refine ⟨(4 : Real) ^ k * C, ?_⟩
  intro x y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  have hy' := abs_le.mp hy
  have hlow : -(1 / 2 : Real) <= z.im := by
    simpa [z] using hy'.1
  have hhigh : z.im <= (1 / 2 : Real) := by
    simpa [z] using hy'.2
  have hnorm_source :
      norm (guinandWeilGaussianSource z) <=
        Real.exp ((1 / 4 : Real) - x ^ 2) := by
    simpa [z] using
      (norm_guinandWeilGaussianSource_le_criticalStrip
        (z := z) hlow hhigh)
  have hnorm_z_le : norm z <= |x| + |y| := by
    calc
      norm z <= norm (x : Complex) + norm ((y : Complex) * Complex.I) := by
        exact norm_add_le _ _
      _ = |x| + |y| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hshift_le : norm z + 2 <= (4 : Real) * (|x| + 1) := by
    calc
      norm z + 2 <= |x| + |y| + 2 := by
        linarith
      _ <= |x| + (1 / 2 : Real) + 2 := by
        linarith
      _ <= (4 : Real) * (|x| + 1) := by
        have hx_nonneg : 0 <= |x| := abs_nonneg x
        nlinarith
  have hshift_pow :
      (norm z + 2) ^ k <= ((4 : Real) * (|x| + 1)) ^ k := by
    exact pow_le_pow_left₀
      (by
        have hz_nonneg : 0 <= norm z := norm_nonneg z
        linarith)
      hshift_le k
  have hshift_pow' :
      (norm z + 2) ^ k <= (4 : Real) ^ k * (|x| + 1) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hmul :
      norm (guinandWeilGaussianSource z) * (norm z + 2) ^ k <=
        Real.exp ((1 / 4 : Real) - x ^ 2) *
          ((4 : Real) ^ k * (|x| + 1) ^ k) := by
    exact mul_le_mul hnorm_source hshift_pow'
      (pow_nonneg
        (by
          have hz_nonneg : 0 <= norm z := norm_nonneg z
          linarith : 0 <= norm z + (2 : Real))
        k)
      (Real.exp_pos _).le
  calc
    norm (guinandWeilGaussianSource
        ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (guinandWeilGaussianSource z) * (norm z + 2) ^ k := by
          rfl
    _ <= Real.exp ((1 / 4 : Real) - x ^ 2) *
          ((4 : Real) ^ k * (|x| + 1) ^ k) := hmul
    _ = (4 : Real) ^ k *
          ((|x| + 1) ^ k * Real.exp ((1 / 4 : Real) - x ^ 2)) := by
      ring
    _ <= (4 : Real) ^ k * C := by
      exact mul_le_mul_of_nonneg_left (hC x)
        (pow_nonneg (by norm_num : (0 : Real) <= 4) k)

/-- On every fixed horizontal line, the Gaussian source has rapid polynomial decay. -/
theorem tendsto_abs_rpow_mul_norm_guinandWeilGaussianSource_horizontalLine_cocompact
    (s y : Real) :
    Tendsto
      (fun x : Real =>
        |x| ^ s *
          norm (guinandWeilGaussianSource ((x : Complex) + (y : Complex) * Complex.I)))
      (cocompact Real) (nhds 0) := by
  have hbase :=
    tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 : Real)) (by norm_num) s
  have hscaled :
      Tendsto
        (fun x : Real =>
          Real.exp (y ^ 2) * (|x| ^ s * Real.exp (-(1 : Real) * x ^ 2)))
        (cocompact Real) (nhds 0) :=
    by
      simpa using hbase.const_mul (Real.exp (y ^ 2))
  simpa [norm_guinandWeilGaussianSource, Real.exp_add, sub_eq_add_neg,
    mul_assoc, mul_left_comm, mul_comm] using hscaled

end

end RiemannHypothesisProject
