import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.MeanInequalities
import RiemannHypothesisProject.GuinandWeilConcrete.OscillatorHermiteSource

/-!
# Hermite coefficients and oscillator transfer on Schwartz space

This module begins the topological Hermite-density argument.  It bundles the
`pi`-normalized harmonic oscillator on project Schwartz space, proves its
bilinear self-adjointness by Schwartz integration by parts, and transfers
powers of the Hermite eigenvalue from a spectral coefficient onto oscillator
powers of the test function.
-/

namespace RiemannHypothesisProject

open MeasureTheory
open scoped Laplacian

noncomputable section

theorem guinandWeilPiOscillatorScale_pos :
    0 < guinandWeilPiOscillatorScale := by
  simp [guinandWeilPiOscillatorScale, Real.pi_pos]

theorem guinandWeilPiOscillatorScale_ne_zero :
    guinandWeilPiOscillatorScale ≠ 0 :=
  guinandWeilPiOscillatorScale_pos.ne'

/-- The quadratic potential appearing in the `pi`-normalized oscillator. -/
def guinandWeilPiOscillatorPotential (x : Real) : Complex :=
  ((guinandWeilPiOscillatorScale * x) ^ 2 : Real)

theorem guinandWeilPiOscillatorPotential_hasTemperateGrowth :
    guinandWeilPiOscillatorPotential.HasTemperateGrowth := by
  unfold guinandWeilPiOscillatorPotential
  fun_prop

/-- The linear coordinate multiplier `2*pi*x`. -/
def guinandWeilPiOscillatorCoordinate (x : Real) : Complex :=
  guinandWeilPiOscillatorScale * x

theorem guinandWeilPiOscillatorCoordinate_hasTemperateGrowth :
    guinandWeilPiOscillatorCoordinate.HasTemperateGrowth := by
  unfold guinandWeilPiOscillatorCoordinate
  fun_prop

/-- Multiplication by the quadratic oscillator potential on Schwartz space. -/
noncomputable def guinandWeilPiOscillatorPotentialCLM :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  SchwartzMap.smulLeftCLM Complex guinandWeilPiOscillatorPotential

/-- Multiplication by `2*pi*x` on project Schwartz space. -/
noncomputable def guinandWeilPiOscillatorCoordinateCLM :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  SchwartzMap.smulLeftCLM Complex guinandWeilPiOscillatorCoordinate

/-- The annihilation operator `d/dx + 2*pi*x`. -/
noncomputable def guinandWeilPiHermiteAnnihilationCLM :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  SchwartzMap.derivCLM Complex Complex + guinandWeilPiOscillatorCoordinateCLM

/-- The creation operator `-d/dx + 2*pi*x`. -/
noncomputable def guinandWeilPiHermiteCreationCLM :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  -(SchwartzMap.derivCLM Complex Complex) + guinandWeilPiOscillatorCoordinateCLM

/-- The harmonic oscillator `-Delta + (2*pi*x)^2` on project Schwartz space. -/
noncomputable def guinandWeilPiHarmonicOscillatorSchwartzCLM :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  -(LineDeriv.laplacianCLM Complex Real SchwartzLineTestFunction) +
    guinandWeilPiOscillatorPotentialCLM

@[simp]
theorem guinandWeilPiOscillatorPotentialCLM_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiOscillatorPotentialCLM f x =
      guinandWeilPiOscillatorPotential x * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    guinandWeilPiOscillatorPotential_hasTemperateGrowth f x

@[simp]
theorem guinandWeilPiOscillatorCoordinateCLM_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiOscillatorCoordinateCLM f x =
      guinandWeilPiOscillatorCoordinate x * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    guinandWeilPiOscillatorCoordinate_hasTemperateGrowth f x

@[simp]
theorem guinandWeilPiHermiteAnnihilationCLM_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiHermiteAnnihilationCLM f x =
      deriv (fun t : Real => f t) x +
        guinandWeilPiOscillatorCoordinate x * f x := by
  simp [guinandWeilPiHermiteAnnihilationCLM,
    SchwartzMap.derivCLM_apply]

@[simp]
theorem guinandWeilPiHermiteCreationCLM_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiHermiteCreationCLM f x =
      -deriv (fun t : Real => f t) x +
        guinandWeilPiOscillatorCoordinate x * f x := by
  simp [guinandWeilPiHermiteCreationCLM,
    SchwartzMap.derivCLM_apply]

/-- Annihilation removes the Gaussian derivative contribution for any real polynomial. -/
theorem guinandWeilPiHermiteAnnihilation_polynomialGaussianSource_real
    (p : Polynomial Real) (x : Real) :
    deriv
          (fun t : Real =>
            guinandWeilPiPolynomialGaussianSource
              (p.map (algebraMap Real Complex)) (t : Complex)) x +
        guinandWeilPiOscillatorCoordinate x *
          guinandWeilPiPolynomialGaussianSource
            (p.map (algebraMap Real Complex)) (x : Complex) =
      guinandWeilPiPolynomialGaussianSource
        (p.derivative.map (algebraMap Real Complex)) (x : Complex) := by
  rw [deriv_guinandWeilPiPolynomialGaussianSource_real,
    guinandWeilPiPolynomialGaussianDerivativeStep_map_real]
  simp [guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiRealPolynomialGaussianDerivativeStep,
    guinandWeilPiOscillatorCoordinate, Polynomial.aeval_def]
  ring

/-- Creation applies the polynomial raising operator for any real polynomial. -/
theorem guinandWeilPiHermiteCreation_polynomialGaussianSource_real
    (p : Polynomial Real) (x : Real) :
    -deriv
          (fun t : Real =>
            guinandWeilPiPolynomialGaussianSource
              (p.map (algebraMap Real Complex)) (t : Complex)) x +
        guinandWeilPiOscillatorCoordinate x *
          guinandWeilPiPolynomialGaussianSource
            (p.map (algebraMap Real Complex)) (x : Complex) =
      guinandWeilPiPolynomialGaussianSource
        ((-guinandWeilPiRealPolynomialGaussianDerivativeStep p +
            Polynomial.C guinandWeilPiOscillatorScale * Polynomial.X * p).map
          (algebraMap Real Complex)) (x : Complex) := by
  rw [deriv_guinandWeilPiPolynomialGaussianSource_real,
    guinandWeilPiPolynomialGaussianDerivativeStep_map_real]
  simp [guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiRealPolynomialGaussianDerivativeStep,
    guinandWeilPiOscillatorCoordinate, Polynomial.aeval_def]
  ring

/-- Creation sends the `n`th oscillator Hermite test to the next test. -/
theorem guinandWeilPiHermiteCreationCLM_hermite
    (n : Nat) :
    guinandWeilPiHermiteCreationCLM
        (guinandWeilPiOscillatorHermiteSchwartz n) =
      guinandWeilPiOscillatorHermiteSchwartz (n + 1) := by
  ext x
  rw [guinandWeilPiHermiteCreationCLM_apply]
  have hfun :
      (fun t : Real => guinandWeilPiOscillatorHermiteSchwartz n t) =
        fun t : Real =>
          guinandWeilPiPolynomialGaussianSource
            ((guinandWeilPiOscillatorHermiteRealPolynomial n).map
              (algebraMap Real Complex)) (t : Complex) := by
    funext t
    rw [guinandWeilPiOscillatorHermiteSchwartz_apply]
    simp [guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def]
  have hsource := congrFun hfun x
  rw [hfun, hsource,
    guinandWeilPiHermiteCreation_polynomialGaussianSource_real]
  have hpoly :
      -guinandWeilPiRealPolynomialGaussianDerivativeStep
          (guinandWeilPiOscillatorHermiteRealPolynomial n) +
          Polynomial.C guinandWeilPiOscillatorScale * Polynomial.X *
            guinandWeilPiOscillatorHermiteRealPolynomial n =
        guinandWeilPiOscillatorHermiteRealPolynomial (n + 1) := by
    have hrec :
        guinandWeilPiOscillatorHermiteRealPolynomial (n + 1) =
          Polynomial.C (2 * guinandWeilPiOscillatorScale) * Polynomial.X *
              guinandWeilPiOscillatorHermiteRealPolynomial n -
            (guinandWeilPiOscillatorHermiteRealPolynomial n).derivative :=
      rfl
    rw [hrec]
    apply Polynomial.funext
    intro y
    simp [guinandWeilPiRealPolynomialGaussianDerivativeStep]
    ring
  rw [hpoly, guinandWeilPiOscillatorHermiteSchwartz_apply]
  simp [guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def]

/-- Annihilation lowers the successor Hermite test with factor `4*pi*(n+1)`. -/
theorem guinandWeilPiHermiteAnnihilationCLM_hermite_succ
    (n : Nat) :
    guinandWeilPiHermiteAnnihilationCLM
        (guinandWeilPiOscillatorHermiteSchwartz (n + 1)) =
      (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) •
        guinandWeilPiOscillatorHermiteSchwartz n := by
  ext x
  rw [guinandWeilPiHermiteAnnihilationCLM_apply]
  have hfun :
      (fun t : Real => guinandWeilPiOscillatorHermiteSchwartz (n + 1) t) =
        fun t : Real =>
          guinandWeilPiPolynomialGaussianSource
            ((guinandWeilPiOscillatorHermiteRealPolynomial (n + 1)).map
              (algebraMap Real Complex)) (t : Complex) := by
    funext t
    rw [guinandWeilPiOscillatorHermiteSchwartz_apply]
    simp [guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def]
  have hsource := congrFun hfun x
  rw [hfun, hsource,
    guinandWeilPiHermiteAnnihilation_polynomialGaussianSource_real,
    derivative_guinandWeilPiOscillatorHermiteRealPolynomial_succ]
  change
    guinandWeilPiPolynomialGaussianSource
        ((Polynomial.C
            (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) *
          guinandWeilPiOscillatorHermiteRealPolynomial n).map
            (algebraMap Real Complex)) (x : Complex) =
      ((2 * guinandWeilPiOscillatorScale *
          ((n + 1 : Nat) : Real) : Real) : Complex) *
        guinandWeilPiOscillatorHermiteSchwartz n x
  rw [guinandWeilPiOscillatorHermiteSchwartz_apply]
  simp [guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def]
  ring

/-- Annihilation kills the Gaussian ground state. -/
theorem guinandWeilPiHermiteAnnihilationCLM_hermite_zero :
    guinandWeilPiHermiteAnnihilationCLM
        (guinandWeilPiOscillatorHermiteSchwartz 0) = 0 := by
  ext x
  rw [guinandWeilPiHermiteAnnihilationCLM_apply]
  simpa [guinandWeilPiOscillatorHermiteSchwartz_apply,
    guinandWeilPiOscillatorHermiteRealPolynomial,
    guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def] using
    guinandWeilPiHermiteAnnihilation_polynomialGaussianSource_real
      (1 : Polynomial Real) x

@[simp]
theorem guinandWeilPiHarmonicOscillatorSchwartzCLM_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiHarmonicOscillatorSchwartzCLM f x =
      -iteratedDeriv 2 (fun t : Real => f t) x +
        guinandWeilPiOscillatorPotential x * f x := by
  simp [guinandWeilPiHarmonicOscillatorSchwartzCLM,
    SchwartzMap.laplacianCLM_eq, SchwartzMap.laplacian_apply,
    InnerProductSpace.laplacian_eq_iteratedDeriv_real]

/-- The bundled oscillator retains the checked Hermite eigenvalue equation. -/
theorem guinandWeilPiHarmonicOscillatorSchwartzCLM_hermite
    (n : Nat) :
    guinandWeilPiHarmonicOscillatorSchwartzCLM
        (guinandWeilPiOscillatorHermiteSchwartz n) =
      (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) •
        guinandWeilPiOscillatorHermiteSchwartz n := by
  ext x
  rw [guinandWeilPiHarmonicOscillatorSchwartzCLM_apply]
  simpa [guinandWeilPiOscillatorPotential, Complex.real_smul] using
    guinandWeilPiOscillatorHermiteSchwartz_eigen n x

/-- Bilinear Schwartz pairing used for the Hermite coefficient argument. -/
noncomputable def guinandWeilPiSchwartzBilinearPairing
    (f g : SchwartzLineTestFunction) : Complex :=
  ∫ x : Real, f x * g x

theorem guinandWeilPiSchwartzBilinearPairing_smul_left
    (c : Complex) (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing (c • f) g =
      c * guinandWeilPiSchwartzBilinearPairing f g := by
  unfold guinandWeilPiSchwartzBilinearPairing
  change (∫ x : Real, (c * f x) * g x) = _
  simp_rw [mul_assoc]
  rw [integral_const_mul]

theorem guinandWeilPiSchwartzBilinearPairing_smul_right
    (c : Complex) (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing f (c • g) =
      c * guinandWeilPiSchwartzBilinearPairing f g := by
  unfold guinandWeilPiSchwartzBilinearPairing
  change (∫ x : Real, f x * (c * g x)) = _
  have hpoint :
      (fun x : Real => f x * (c * g x)) =
        fun x : Real => c * (f x * g x) := by
    funext x
    ring
  rw [hpoint, integral_const_mul]

theorem guinandWeilPiSchwartzBilinearPairing_real_smul_left
    (c : Real) (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing (c • f) g =
      (c : Complex) * guinandWeilPiSchwartzBilinearPairing f g := by
  simpa [Complex.real_smul] using
    guinandWeilPiSchwartzBilinearPairing_smul_left (c : Complex) f g

theorem guinandWeilPiSchwartzBilinearPairing_real_smul_right
    (c : Real) (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing f (c • g) =
      (c : Complex) * guinandWeilPiSchwartzBilinearPairing f g := by
  simpa [Complex.real_smul] using
    guinandWeilPiSchwartzBilinearPairing_smul_right (c : Complex) f g

/-- The linear coordinate multiplier is symmetric for the bilinear pairing. -/
theorem guinandWeilPiSchwartzBilinearPairing_coordinate_right_eq_left
    (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing f
        (guinandWeilPiOscillatorCoordinateCLM g) =
      guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorCoordinateCLM f) g := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp
  ring

/-- Creation and annihilation are adjoint for the bilinear Schwartz pairing. -/
theorem guinandWeilPiSchwartzBilinearPairing_annihilation_right_eq_creation_left
    (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing f
        (guinandWeilPiHermiteAnnihilationCLM g) =
      guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiHermiteCreationCLM f) g := by
  have hderiv := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul f g
  have hcoord :=
    guinandWeilPiSchwartzBilinearPairing_coordinate_right_eq_left f g
  unfold guinandWeilPiSchwartzBilinearPairing
  change
    (∫ x : Real,
      f x *
        (deriv (fun t : Real => g t) x +
          guinandWeilPiOscillatorCoordinateCLM g x)) =
      ∫ x : Real,
        (-deriv (fun t : Real => f t) x +
          guinandWeilPiOscillatorCoordinateCLM f x) * g x
  have hfderiv : Integrable (fun x : Real =>
      f x * deriv (fun t : Real => g t) x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (SchwartzMap.derivCLM Complex Complex g)).integrable
  have hfcoord : Integrable (fun x : Real =>
      f x * guinandWeilPiOscillatorCoordinateCLM g x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (guinandWeilPiOscillatorCoordinateCLM g)).integrable
  have hderivg : Integrable (fun x : Real =>
      deriv (fun t : Real => f t) x * g x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex)
      (SchwartzMap.derivCLM Complex Complex f) g).integrable
  have hcoordg : Integrable (fun x : Real =>
      guinandWeilPiOscillatorCoordinateCLM f x * g x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex)
      (guinandWeilPiOscillatorCoordinateCLM f) g).integrable
  simp_rw [mul_add, add_mul, neg_mul]
  change
    (∫ x : Real,
      f x * deriv (fun t : Real => g t) x +
        f x * guinandWeilPiOscillatorCoordinateCLM g x) =
      ∫ x : Real,
        (-(fun y : Real =>
          deriv (fun t : Real => f t) y * g y)) x +
          guinandWeilPiOscillatorCoordinateCLM f x * g x
  have hnegderiv :
      (∫ x : Real,
        (-(fun y : Real =>
          deriv (fun t : Real => f t) y * g y)) x) =
        -(∫ x : Real, deriv (fun t : Real => f t) x * g x) := by
    simpa using
      (integral_neg' (μ := volume)
        (fun x : Real => deriv (fun t : Real => f t) x * g x))
  rw [integral_add hfderiv hfcoord, integral_add hderivg.neg hcoordg,
    hnegderiv, hderiv]
  simpa [guinandWeilPiSchwartzBilinearPairing] using hcoord

/-- The squared bilinear norm obeys the standard Hermite recurrence. -/
theorem guinandWeilPiSchwartzBilinearPairing_hermite_succ_self
    (n : Nat) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorHermiteSchwartz (n + 1))
        (guinandWeilPiOscillatorHermiteSchwartz (n + 1)) =
      ((2 * guinandWeilPiOscillatorScale *
          ((n + 1 : Nat) : Real) : Real) : Complex) *
        guinandWeilPiSchwartzBilinearPairing
          (guinandWeilPiOscillatorHermiteSchwartz n)
          (guinandWeilPiOscillatorHermiteSchwartz n) := by
  calc
    _ = guinandWeilPiSchwartzBilinearPairing
          (guinandWeilPiHermiteCreationCLM
            (guinandWeilPiOscillatorHermiteSchwartz n))
          (guinandWeilPiOscillatorHermiteSchwartz (n + 1)) := by
            rw [guinandWeilPiHermiteCreationCLM_hermite]
    _ = guinandWeilPiSchwartzBilinearPairing
          (guinandWeilPiOscillatorHermiteSchwartz n)
          (guinandWeilPiHermiteAnnihilationCLM
            (guinandWeilPiOscillatorHermiteSchwartz (n + 1))) :=
        (guinandWeilPiSchwartzBilinearPairing_annihilation_right_eq_creation_left
          (guinandWeilPiOscillatorHermiteSchwartz n)
          (guinandWeilPiOscillatorHermiteSchwartz (n + 1))).symm
    _ = guinandWeilPiSchwartzBilinearPairing
          (guinandWeilPiOscillatorHermiteSchwartz n)
          ((2 * guinandWeilPiOscillatorScale *
              ((n + 1 : Nat) : Real)) •
            guinandWeilPiOscillatorHermiteSchwartz n) := by
          rw [guinandWeilPiHermiteAnnihilationCLM_hermite_succ]
    _ = _ :=
      guinandWeilPiSchwartzBilinearPairing_real_smul_right
        (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real))
        (guinandWeilPiOscillatorHermiteSchwartz n)
        (guinandWeilPiOscillatorHermiteSchwartz n)

/-- Closed factorial form of the unnormalized Hermite squared norm. -/
theorem guinandWeilPiSchwartzBilinearPairing_hermite_self
    (n : Nat) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorHermiteSchwartz n)
        (guinandWeilPiOscillatorHermiteSchwartz n) =
      ((((2 * guinandWeilPiOscillatorScale) ^ n * n.factorial : Real)) :
          Complex) *
        guinandWeilPiSchwartzBilinearPairing
          (guinandWeilPiOscillatorHermiteSchwartz 0)
          (guinandWeilPiOscillatorHermiteSchwartz 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [guinandWeilPiSchwartzBilinearPairing_hermite_succ_self, ih]
      push_cast
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      ring

/-- The ground-state squared norm is the elementary Gaussian integral `sqrt (1/2)`. -/
theorem guinandWeilPiSchwartzBilinearPairing_hermite_zero_self :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorHermiteSchwartz 0)
        (guinandWeilPiOscillatorHermiteSchwartz 0) =
      (Real.sqrt (1 / 2 : Real) : Complex) := by
  unfold guinandWeilPiSchwartzBilinearPairing
  calc
    _ = ∫ x : Real,
        (Real.exp (-(2 * Real.pi) * x ^ 2) : Complex) := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [guinandWeilPiOscillatorHermiteSchwartz_apply]
          simp [guinandWeilPiOscillatorHermiteRealPolynomial,
            guinandWeilPiGaussianSource, ← Complex.exp_add]
          congr 1
          ring
    _ = ((∫ x : Real, Real.exp (-(2 * Real.pi) * x ^ 2)) : Real) := by
          exact integral_ofReal
    _ = (Real.sqrt (1 / 2 : Real) : Complex) := by
          rw [integral_gaussian]
          congr 2
          field_simp [Real.pi_ne_zero]

/-- The explicit positive squared norm of the unnormalized `n`th Hermite test. -/
noncomputable def guinandWeilPiHermiteNormSq (n : Nat) : Real :=
  (2 * guinandWeilPiOscillatorScale) ^ n * n.factorial *
    Real.sqrt (1 / 2 : Real)

theorem guinandWeilPiHermiteNormSq_succ (n : Nat) :
    guinandWeilPiHermiteNormSq (n + 1) =
      (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) *
        guinandWeilPiHermiteNormSq n := by
  simp [guinandWeilPiHermiteNormSq, pow_succ, Nat.factorial_succ]
  ring

theorem guinandWeilPiHermiteNormSq_pos (n : Nat) :
    0 < guinandWeilPiHermiteNormSq n := by
  unfold guinandWeilPiHermiteNormSq
  exact mul_pos
    (mul_pos
      (pow_pos (mul_pos (by norm_num) guinandWeilPiOscillatorScale_pos) n)
      (by positivity))
    (Real.sqrt_pos.2 (by norm_num))

theorem sqrt_guinandWeilPiHermiteNormSq_succ (n : Nat) :
    Real.sqrt (guinandWeilPiHermiteNormSq (n + 1)) =
      Real.sqrt
          (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) *
        Real.sqrt (guinandWeilPiHermiteNormSq n) := by
  have hfactor_nonneg :
      0 ≤ 2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real) :=
    (mul_pos (mul_pos (by norm_num) guinandWeilPiOscillatorScale_pos)
      (by positivity)).le
  rw [guinandWeilPiHermiteNormSq_succ, Real.sqrt_mul hfactor_nonneg]

/-- Explicit factorial formula for every Hermite squared norm. -/
theorem guinandWeilPiSchwartzBilinearPairing_hermite_self_explicit
    (n : Nat) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorHermiteSchwartz n)
        (guinandWeilPiOscillatorHermiteSchwartz n) =
      (guinandWeilPiHermiteNormSq n : Complex) := by
  rw [guinandWeilPiSchwartzBilinearPairing_hermite_self,
    guinandWeilPiSchwartzBilinearPairing_hermite_zero_self]
  simp [guinandWeilPiHermiteNormSq]

/-- The normalized oscillator Hermite project test. -/
noncomputable def guinandWeilPiNormalizedHermiteSchwartz
    (n : Nat) : SchwartzLineTestFunction :=
  (Real.sqrt (guinandWeilPiHermiteNormSq n))⁻¹ •
    guinandWeilPiOscillatorHermiteSchwartz n

/-- Square-root weight for the normalized Hermite ladder. -/
noncomputable def guinandWeilPiHermiteLadderWeight (n : Nat) : Real :=
  Real.sqrt (2 * guinandWeilPiOscillatorScale * (n : Real))

/-- Creation raises a normalized Hermite test with the square-root ladder
weight. -/
theorem guinandWeilPiHermiteCreationCLM_normalizedHermite
    (n : Nat) :
    guinandWeilPiHermiteCreationCLM
        (guinandWeilPiNormalizedHermiteSchwartz n) =
      Real.sqrt
          (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) •
        guinandWeilPiNormalizedHermiteSchwartz (n + 1) := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  rw [ContinuousLinearMap.map_smul_of_tower,
    guinandWeilPiHermiteCreationCLM_hermite, smul_smul]
  congr 1
  rw [sqrt_guinandWeilPiHermiteNormSq_succ]
  have hfactor :
      Real.sqrt
          (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) ≠ 0 :=
    (Real.sqrt_pos.2
      (mul_pos (mul_pos (by norm_num) guinandWeilPiOscillatorScale_pos)
        (by positivity))).ne'
  have hnorm : Real.sqrt (guinandWeilPiHermiteNormSq n) ≠ 0 :=
    (Real.sqrt_pos.2 (guinandWeilPiHermiteNormSq_pos n)).ne'
  field_simp [hfactor, hnorm]

/-- Annihilation lowers a normalized successor Hermite test with the same
square-root ladder weight. -/
theorem guinandWeilPiHermiteAnnihilationCLM_normalizedHermite_succ
    (n : Nat) :
    guinandWeilPiHermiteAnnihilationCLM
        (guinandWeilPiNormalizedHermiteSchwartz (n + 1)) =
      Real.sqrt
          (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) •
        guinandWeilPiNormalizedHermiteSchwartz n := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  rw [ContinuousLinearMap.map_smul_of_tower,
    guinandWeilPiHermiteAnnihilationCLM_hermite_succ, smul_smul, smul_smul]
  congr 1
  rw [sqrt_guinandWeilPiHermiteNormSq_succ]
  have hfactor_pos :
      0 < 2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real) :=
    mul_pos (mul_pos (by norm_num) guinandWeilPiOscillatorScale_pos)
      (by positivity)
  have hfactor :
      Real.sqrt
          (2 * guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) ≠ 0 :=
    (Real.sqrt_pos.2 hfactor_pos).ne'
  have hnorm : Real.sqrt (guinandWeilPiHermiteNormSq n) ≠ 0 :=
    (Real.sqrt_pos.2 (guinandWeilPiHermiteNormSq_pos n)).ne'
  field_simp [hfactor, hnorm]
  nlinarith [Real.sq_sqrt hfactor_pos.le]

/-- Annihilation kills the normalized ground state. -/
theorem guinandWeilPiHermiteAnnihilationCLM_normalizedHermite_zero :
    guinandWeilPiHermiteAnnihilationCLM
        (guinandWeilPiNormalizedHermiteSchwartz 0) = 0 := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  rw [ContinuousLinearMap.map_smul_of_tower,
    guinandWeilPiHermiteAnnihilationCLM_hermite_zero, smul_zero]

/-- Uniform normalized creation formula in ladder-weight notation. -/
theorem guinandWeilPiHermiteCreationCLM_normalizedHermite_ladder
    (n : Nat) :
    guinandWeilPiHermiteCreationCLM
        (guinandWeilPiNormalizedHermiteSchwartz n) =
      guinandWeilPiHermiteLadderWeight (n + 1) •
        guinandWeilPiNormalizedHermiteSchwartz (n + 1) := by
  simpa [guinandWeilPiHermiteLadderWeight] using
    guinandWeilPiHermiteCreationCLM_normalizedHermite n

/-- Uniform normalized annihilation formula, including the zero mode. -/
theorem guinandWeilPiHermiteAnnihilationCLM_normalizedHermite_ladder
    (n : Nat) :
    guinandWeilPiHermiteAnnihilationCLM
        (guinandWeilPiNormalizedHermiteSchwartz n) =
      guinandWeilPiHermiteLadderWeight n •
        guinandWeilPiNormalizedHermiteSchwartz (n - 1) := by
  cases n with
  | zero =>
      rw [guinandWeilPiHermiteAnnihilationCLM_normalizedHermite_zero]
      simp [guinandWeilPiHermiteLadderWeight]
  | succ n =>
      simpa [guinandWeilPiHermiteLadderWeight, Nat.succ_eq_add_one] using
        guinandWeilPiHermiteAnnihilationCLM_normalizedHermite_succ n

/-- The coordinate multiplier is the half-sum of annihilation and creation. -/
theorem guinandWeilPiOscillatorCoordinateCLM_eq_half_ladder_sum
    (f : SchwartzLineTestFunction) :
    guinandWeilPiOscillatorCoordinateCLM f =
      (1 / 2 : Real) •
        (guinandWeilPiHermiteAnnihilationCLM f +
          guinandWeilPiHermiteCreationCLM f) := by
  ext x
  simp [guinandWeilPiHermiteAnnihilationCLM_apply,
    guinandWeilPiHermiteCreationCLM_apply]
  ring

/-- Differentiation is the half-difference of annihilation and creation. -/
theorem guinandWeilPiDerivCLM_eq_half_ladder_diff
    (f : SchwartzLineTestFunction) :
    SchwartzMap.derivCLM Complex Complex f =
      (1 / 2 : Real) •
        (guinandWeilPiHermiteAnnihilationCLM f -
          guinandWeilPiHermiteCreationCLM f) := by
  ext x
  simp [guinandWeilPiHermiteAnnihilationCLM_apply,
    guinandWeilPiHermiteCreationCLM_apply,
    SchwartzMap.derivCLM_apply]
  ring

/-- Coordinate multiplication has the standard normalized Hermite
three-term expansion. -/
theorem guinandWeilPiOscillatorCoordinateCLM_normalizedHermite
    (n : Nat) :
    guinandWeilPiOscillatorCoordinateCLM
        (guinandWeilPiNormalizedHermiteSchwartz n) =
      (1 / 2 : Real) •
        (guinandWeilPiHermiteLadderWeight n •
            guinandWeilPiNormalizedHermiteSchwartz (n - 1) +
          guinandWeilPiHermiteLadderWeight (n + 1) •
            guinandWeilPiNormalizedHermiteSchwartz (n + 1)) := by
  rw [guinandWeilPiOscillatorCoordinateCLM_eq_half_ladder_sum,
    guinandWeilPiHermiteAnnihilationCLM_normalizedHermite_ladder,
    guinandWeilPiHermiteCreationCLM_normalizedHermite_ladder]

/-- Differentiation has the standard normalized Hermite three-term
expansion. -/
theorem guinandWeilPiDerivCLM_normalizedHermite
    (n : Nat) :
    SchwartzMap.derivCLM Complex Complex
        (guinandWeilPiNormalizedHermiteSchwartz n) =
      (1 / 2 : Real) •
        (guinandWeilPiHermiteLadderWeight n •
            guinandWeilPiNormalizedHermiteSchwartz (n - 1) -
          guinandWeilPiHermiteLadderWeight (n + 1) •
            guinandWeilPiNormalizedHermiteSchwartz (n + 1)) := by
  rw [guinandWeilPiDerivCLM_eq_half_ladder_diff,
    guinandWeilPiHermiteAnnihilationCLM_normalizedHermite_ladder,
    guinandWeilPiHermiteCreationCLM_normalizedHermite_ladder]

/-- Even normalized Hermite tests remain in the formula-compatible even sector. -/
theorem guinandWeilPiNormalizedHermiteSchwartz_even
    (n : Nat) (x : Real) :
    guinandWeilPiNormalizedHermiteSchwartz (2 * n) (-x) =
      guinandWeilPiNormalizedHermiteSchwartz (2 * n) x := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  change
    (Real.sqrt (guinandWeilPiHermiteNormSq (2 * n)))⁻¹ •
        guinandWeilPiOscillatorHermiteSchwartz (2 * n) (-x) =
      (Real.sqrt (guinandWeilPiHermiteNormSq (2 * n)))⁻¹ •
        guinandWeilPiOscillatorHermiteSchwartz (2 * n) x
  exact congrArg
    (fun z : Complex =>
      (Real.sqrt (guinandWeilPiHermiteNormSq (2 * n)))⁻¹ • z)
    (guinandWeilPiOscillatorHermiteSchwartz_even n x)

/-- Every unnormalized oscillator Hermite test is real-valued on the real axis. -/
theorem guinandWeilPiOscillatorHermiteSchwartz_im
    (n : Nat) (x : Real) :
    (guinandWeilPiOscillatorHermiteSchwartz n x).im = 0 := by
  have hsource :
      guinandWeilPiOscillatorHermiteSchwartz n x =
        guinandWeilPiPolynomialGaussianSource
          ((guinandWeilPiOscillatorHermiteRealPolynomial n).map
            (algebraMap Real Complex)) (x : Complex) := by
    rw [guinandWeilPiOscillatorHermiteSchwartz_apply]
    simp [guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def]
  rw [hsource]
  exact guinandWeilPiPolynomialGaussianSource_map_real_ofReal_im
    (guinandWeilPiOscillatorHermiteRealPolynomial n) x

/-- Normalization preserves real-valuedness. -/
theorem guinandWeilPiNormalizedHermiteSchwartz_im
    (n : Nat) (x : Real) :
    (guinandWeilPiNormalizedHermiteSchwartz n x).im = 0 := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  change
    ((Real.sqrt (guinandWeilPiHermiteNormSq n))⁻¹ •
      guinandWeilPiOscillatorHermiteSchwartz n x).im = 0
  rw [Complex.smul_im, guinandWeilPiOscillatorHermiteSchwartz_im]
  simp

/-- Every normalized Hermite test has bilinear squared norm one. -/
theorem guinandWeilPiSchwartzBilinearPairing_normalizedHermite_self
    (n : Nat) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiNormalizedHermiteSchwartz n)
        (guinandWeilPiNormalizedHermiteSchwartz n) = 1 := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  rw [guinandWeilPiSchwartzBilinearPairing_real_smul_left,
    guinandWeilPiSchwartzBilinearPairing_real_smul_right,
    guinandWeilPiSchwartzBilinearPairing_hermite_self_explicit]
  have hpos := guinandWeilPiHermiteNormSq_pos n
  have hsqrt : Real.sqrt (guinandWeilPiHermiteNormSq n) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hsquare :
      Real.sqrt (guinandWeilPiHermiteNormSq n) ^ 2 =
        guinandWeilPiHermiteNormSq n :=
    Real.sq_sqrt hpos.le
  have hsqrtC :
      ((Real.sqrt (guinandWeilPiHermiteNormSq n) : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrt
  rw [← hsquare]
  rw [Real.sqrt_sq (Real.sqrt_nonneg _)]
  push_cast
  field_simp [hsqrtC]

/-- The normalized Hermite test has actual `L2` norm one. -/
theorem integral_norm_sq_guinandWeilPiNormalizedHermiteSchwartz
    (n : Nat) :
    ∫ x : Real, ‖guinandWeilPiNormalizedHermiteSchwartz n x‖ ^ 2 = 1 := by
  let φ := guinandWeilPiNormalizedHermiteSchwartz n
  have hprod : Integrable (fun x : Real => φ x * φ x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) φ φ).integrable
  calc
    _ = ∫ x : Real, (φ x * φ x).re := by
          apply integral_congr_ae
          filter_upwards [] with x
          have him : (φ x).im = 0 :=
            guinandWeilPiNormalizedHermiteSchwartz_im n x
          rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, him]
          ring
    _ = (∫ x : Real, φ x * φ x).re := integral_re hprod
    _ = 1 := by
      change
        (guinandWeilPiSchwartzBilinearPairing φ φ).re = 1
      rw [show φ = guinandWeilPiNormalizedHermiteSchwartz n by rfl,
        guinandWeilPiSchwartzBilinearPairing_normalizedHermite_self]
      simp

/-- The integral expression used in the coefficient estimates is the norm of
the canonical `L2` image of a Schwartz test. -/
theorem guinandWeilPiSchwartz_l2_eq_norm_toLp
    (f : SchwartzLineTestFunction) :
    (∫ x : Real, ‖f x‖ ^ (2 : Real)) ^ (1 / (2 : Real)) =
      ‖f.toLp (2 : ENNReal) volume‖ := by
  rw [SchwartzMap.norm_toLp' (p := (2 : ENNReal)) (by norm_num) (by simp)]
  norm_num

/-- The canonical `L2` image of a normalized Hermite test has norm one. -/
theorem norm_toLp_guinandWeilPiNormalizedHermiteSchwartz
    (n : Nat) :
    ‖(guinandWeilPiNormalizedHermiteSchwartz n).toLp
        (2 : ENNReal) volume‖ = 1 := by
  rw [← guinandWeilPiSchwartz_l2_eq_norm_toLp]
  rw [show
      (∫ x : Real,
          ‖guinandWeilPiNormalizedHermiteSchwartz n x‖ ^ (2 : Real)) = 1 by
    simpa [Real.rpow_two] using
      integral_norm_sq_guinandWeilPiNormalizedHermiteSchwartz n]
  norm_num

/-- The quadratic potential is symmetric for the bilinear Schwartz pairing. -/
theorem guinandWeilPiSchwartzBilinearPairing_potential_right_eq_left
    (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing f
        (guinandWeilPiOscillatorPotentialCLM g) =
      guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorPotentialCLM f) g := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp
  ring

/-- The `pi`-normalized harmonic oscillator is symmetric on Schwartz space. -/
theorem guinandWeilPiSchwartzBilinearPairing_oscillator_right_eq_left
    (f g : SchwartzLineTestFunction) :
    guinandWeilPiSchwartzBilinearPairing f
        (guinandWeilPiHarmonicOscillatorSchwartzCLM g) =
      guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiHarmonicOscillatorSchwartzCLM f) g := by
  have hlap :=
    SchwartzMap.integral_mul_laplacian_right_eq_left (μ := volume) f g
  have hpot :=
    guinandWeilPiSchwartzBilinearPairing_potential_right_eq_left f g
  unfold guinandWeilPiSchwartzBilinearPairing
  simp only [guinandWeilPiHarmonicOscillatorSchwartzCLM,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply]
  rw [SchwartzMap.laplacianCLM_eq, SchwartzMap.laplacianCLM_eq]
  change
    (∫ x : Real,
      f x *
        (-(Δ g) x + guinandWeilPiOscillatorPotentialCLM g x)) =
      ∫ x : Real,
        (-(Δ f) x + guinandWeilPiOscillatorPotentialCLM f x) * g x
  have hflap : Integrable (fun x : Real => f x * (Δ g) x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f (Δ g)).integrable
  have hfpot :
      Integrable (fun x : Real =>
        f x * guinandWeilPiOscillatorPotentialCLM g x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) f
      (guinandWeilPiOscillatorPotentialCLM g)).integrable
  have hlapg : Integrable (fun x : Real => (Δ f) x * g x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex) (Δ f) g).integrable
  have hpotg :
      Integrable (fun x : Real =>
        guinandWeilPiOscillatorPotentialCLM f x * g x) :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex)
      (guinandWeilPiOscillatorPotentialCLM f) g).integrable
  simp_rw [mul_add, mul_neg, add_mul, neg_mul]
  change
    (∫ x : Real,
      (-(fun y : Real => f y * (Δ g) y)) x +
        f x * guinandWeilPiOscillatorPotentialCLM g x) =
      ∫ x : Real,
        (-(fun y : Real => (Δ f) y * g y)) x +
          guinandWeilPiOscillatorPotentialCLM f x * g x
  have hnegflap :
      (∫ x : Real, (-(fun y : Real => f y * (Δ g) y)) x) =
        -(∫ x : Real, f x * (Δ g) x) := by
    simpa using
      (integral_neg' (μ := volume) (fun x : Real => f x * (Δ g) x))
  have hneglapg :
      (∫ x : Real, (-(fun y : Real => (Δ f) y * g y)) x) =
        -(∫ x : Real, (Δ f) x * g x) := by
    simpa using
      (integral_neg' (μ := volume) (fun x : Real => (Δ f) x * g x))
  rw [integral_add hflap.neg hfpot, integral_add hlapg.neg hpotg,
    hnegflap, hneglapg, hlap]
  simpa [guinandWeilPiSchwartzBilinearPairing] using hpot

/-- The unnormalized `n`th Hermite coefficient of a project Schwartz test. -/
noncomputable def guinandWeilPiHermiteCoefficient
    (n : Nat) (f : SchwartzLineTestFunction) : Complex :=
  guinandWeilPiSchwartzBilinearPairing
    (guinandWeilPiOscillatorHermiteSchwartz n) f

/-- Hermite coefficient against the normalized spectral test. -/
noncomputable def guinandWeilPiNormalizedHermiteCoefficient
    (n : Nat) (f : SchwartzLineTestFunction) : Complex :=
  guinandWeilPiSchwartzBilinearPairing
    (guinandWeilPiNormalizedHermiteSchwartz n) f

/-- The normalized Hermite coefficient as a continuous linear functional. -/
noncomputable def guinandWeilPiNormalizedHermiteCoefficientCLM
    (n : Nat) : SchwartzLineTestFunction →L[Complex] Complex :=
  SchwartzMap.integralCLM Complex volume ∘L
    SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex)
      (guinandWeilPiNormalizedHermiteSchwartz n)

@[simp]
theorem guinandWeilPiNormalizedHermiteCoefficientCLM_apply
    (n : Nat) (f : SchwartzLineTestFunction) :
    guinandWeilPiNormalizedHermiteCoefficientCLM n f =
      guinandWeilPiNormalizedHermiteCoefficient n f :=
  rfl

/-- Cauchy--Schwarz bounds a normalized Hermite coefficient by the actual
`L2` norm of the Schwartz test, with no basis-dependent constant. -/
theorem norm_guinandWeilPiNormalizedHermiteCoefficient_le_l2
    (n : Nat) (f : SchwartzLineTestFunction) :
    ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ ≤
      (∫ x : Real, ‖f x‖ ^ (2 : Real)) ^ (1 / (2 : Real)) := by
  rw [guinandWeilPiNormalizedHermiteCoefficient,
    guinandWeilPiSchwartzBilinearPairing]
  calc
    ‖∫ x : Real, guinandWeilPiNormalizedHermiteSchwartz n x * f x‖ ≤
        ∫ x : Real,
          ‖guinandWeilPiNormalizedHermiteSchwartz n x * f x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : Real,
          ‖guinandWeilPiNormalizedHermiteSchwartz n x‖ * ‖f x‖ := by
      congr 1
      funext x
      exact norm_mul _ _
    _ ≤
        (∫ x : Real,
            ‖guinandWeilPiNormalizedHermiteSchwartz n x‖ ^ (2 : Real)) ^
          (1 / (2 : Real)) *
        (∫ x : Real, ‖f x‖ ^ (2 : Real)) ^ (1 / (2 : Real)) := by
      exact integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        ((guinandWeilPiNormalizedHermiteSchwartz n).memLp
          (ENNReal.ofReal (2 : Real)) volume)
        (f.memLp (ENNReal.ofReal (2 : Real)) volume)
    _ = (∫ x : Real, ‖f x‖ ^ (2 : Real)) ^ (1 / (2 : Real)) := by
      rw [show
          (∫ x : Real,
              ‖guinandWeilPiNormalizedHermiteSchwartz n x‖ ^ (2 : Real)) =
            1 by
          simpa [Real.rpow_two] using
            integral_norm_sq_guinandWeilPiNormalizedHermiteSchwartz n]
      norm_num

/-- The finite normalized Hermite spectral truncation. -/
noncomputable def guinandWeilPiHermiteTruncation
    (N : Nat) (f : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  ∑ n ∈ Finset.range N,
    guinandWeilPiNormalizedHermiteCoefficient n f •
      guinandWeilPiNormalizedHermiteSchwartz n

/-- One oscillator can be transferred from the Hermite factor to the test. -/
theorem guinandWeilPiHermiteCoefficient_oscillator
    (n : Nat) (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteCoefficient n
        (guinandWeilPiHarmonicOscillatorSchwartzCLM f) =
      (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) *
        guinandWeilPiHermiteCoefficient n f := by
  rw [guinandWeilPiHermiteCoefficient,
    guinandWeilPiSchwartzBilinearPairing_oscillator_right_eq_left,
    guinandWeilPiHarmonicOscillatorSchwartzCLM_hermite]
  change
    (∫ x : Real,
      ((guinandWeilPiOscillatorScale *
          ((2 * n + 1 : Nat) : Real) : Real) : Complex) *
        guinandWeilPiOscillatorHermiteSchwartz n x * f x) = _
  calc
    _ = ∫ x : Real,
        ((guinandWeilPiOscillatorScale *
            ((2 * n + 1 : Nat) : Real) : Real) : Complex) *
          (guinandWeilPiOscillatorHermiteSchwartz n x * f x) := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
    _ = ((guinandWeilPiOscillatorScale *
            ((2 * n + 1 : Nat) : Real) : Real) : Complex) *
          (∫ x : Real,
            guinandWeilPiOscillatorHermiteSchwartz n x * f x) := by
          rw [integral_const_mul]
    _ = _ := by
      rw [guinandWeilPiHermiteCoefficient,
        guinandWeilPiSchwartzBilinearPairing]
      push_cast
      ring

/-- Repeated oscillator transfer gives arbitrary polynomial coefficient decay input. -/
theorem guinandWeilPiHermiteCoefficient_iterate_oscillator
    (k n : Nat) (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteCoefficient n
        (guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f) =
      (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) ^ k *
        guinandWeilPiHermiteCoefficient n f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply',
        guinandWeilPiHermiteCoefficient_oscillator, ih, pow_succ]
      ring

/-- One oscillator transfers through a normalized Hermite coefficient. -/
theorem guinandWeilPiNormalizedHermiteCoefficient_oscillator
    (n : Nat) (f : SchwartzLineTestFunction) :
    guinandWeilPiNormalizedHermiteCoefficient n
        (guinandWeilPiHarmonicOscillatorSchwartzCLM f) =
      (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) *
        guinandWeilPiNormalizedHermiteCoefficient n f := by
  rw [guinandWeilPiNormalizedHermiteCoefficient,
    guinandWeilPiNormalizedHermiteSchwartz,
    guinandWeilPiSchwartzBilinearPairing_real_smul_left,
    guinandWeilPiNormalizedHermiteCoefficient,
    guinandWeilPiNormalizedHermiteSchwartz,
    guinandWeilPiSchwartzBilinearPairing_real_smul_left]
  have hcoefficient := guinandWeilPiHermiteCoefficient_oscillator n f
  unfold guinandWeilPiHermiteCoefficient at hcoefficient
  rw [hcoefficient]
  ring

/-- Arbitrary oscillator powers transfer through normalized coefficients. -/
theorem guinandWeilPiNormalizedHermiteCoefficient_iterate_oscillator
    (k n : Nat) (f : SchwartzLineTestFunction) :
    guinandWeilPiNormalizedHermiteCoefficient n
        (guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f) =
      (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) ^ k *
        guinandWeilPiNormalizedHermiteCoefficient n f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply',
        guinandWeilPiNormalizedHermiteCoefficient_oscillator, ih, pow_succ]
      ring

/-- Every oscillator power gives a weighted `L2` bound for the normalized
Hermite coefficient.  Since the eigenvalue grows linearly in `n`, this is the
rapid coefficient-decay estimate required by the Hermite density argument. -/
theorem guinandWeilPiHermiteEigenvalue_pow_mul_norm_coefficient_le_l2
    (k n : Nat) (f : SchwartzLineTestFunction) :
    (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) ^ k *
        ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ ≤
      (∫ x : Real,
          ‖(guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f) x‖ ^
            (2 : Real)) ^ (1 / (2 : Real)) := by
  have heigen_nonneg :
      0 ≤ guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real) := by
    exact (mul_pos guinandWeilPiOscillatorScale_pos (by positivity)).le
  have htransfer :=
    guinandWeilPiNormalizedHermiteCoefficient_iterate_oscillator k n f
  have htransfer' :
      guinandWeilPiNormalizedHermiteCoefficient n
          (guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f) =
        (((guinandWeilPiOscillatorScale *
            ((2 * n + 1 : Nat) : Real)) ^ k : Real) : Complex) *
          guinandWeilPiNormalizedHermiteCoefficient n f := by
    rw [htransfer]
    push_cast
    ring
  calc
    (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) ^ k *
          ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ =
        ‖(((guinandWeilPiOscillatorScale *
              ((2 * n + 1 : Nat) : Real)) ^ k : Real) : Complex) *
            guinandWeilPiNormalizedHermiteCoefficient n f‖ := by
      rw [norm_mul]
      rw [Complex.norm_real]
      rw [Real.norm_of_nonneg (pow_nonneg heigen_nonneg k)]
    _ = ‖guinandWeilPiNormalizedHermiteCoefficient n
          (guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f)‖ := by
      rw [htransfer']
    _ ≤ _ :=
      norm_guinandWeilPiNormalizedHermiteCoefficient_le_l2 n
        (guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f)

/-- The weighted coefficient estimate is controlled by finitely many project
Schwartz seminorms of the corresponding oscillator power, uniformly in the
Hermite index. -/
theorem exists_schwartzSeminorm_bound_guinandWeilPiHermiteCoefficient
    (k : Nat) :
    ∃ (m : Nat) (C : Real), 0 ≤ C ∧
      ∀ (n : Nat) (f : SchwartzLineTestFunction),
        (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) ^ k *
            ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ ≤
          C * (Finset.Iic (m, 0)).sup
            (schwartzSeminormFamily Complex Real Complex)
            (guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f) := by
  rcases SchwartzMap.norm_toLp_le_seminorm
      (E := Real) Complex Complex (2 : ENNReal) volume with
    ⟨m, C, hC, hbound⟩
  refine ⟨m, C, hC, fun n f => ?_⟩
  apply le_trans
    (guinandWeilPiHermiteEigenvalue_pow_mul_norm_coefficient_le_l2 k n f)
  rw [guinandWeilPiSchwartz_l2_eq_norm_toLp]
  exact hbound (guinandWeilPiHarmonicOscillatorSchwartzCLM^[k] f)

/-- Normalized Hermite coefficients of a Schwartz test are rapidly decreasing:
after multiplication by any fixed polynomial weight, their norms remain
summable. -/
theorem summable_nat_add_one_pow_mul_norm_guinandWeilPiNormalizedHermiteCoefficient
    (r : Nat) (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      (((n + 1 : Nat) : Real) ^ r) *
        ‖guinandWeilPiNormalizedHermiteCoefficient n f‖) := by
  let C : Real :=
    (∫ x : Real,
        ‖(guinandWeilPiHarmonicOscillatorSchwartzCLM^[r + 2] f) x‖ ^
          (2 : Real)) ^ (1 / (2 : Real))
  have hbase : Summable (fun n : Nat =>
      1 / (((n + 1 : Nat) : Real) ^ 2)) := by
    have hzero : Summable (fun n : Nat => 1 / ((n : Real) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    simpa using
      (summable_nat_add_iff
        (f := fun n : Nat => 1 / ((n : Real) ^ 2)) 1).mpr hzero
  have hmajorant : Summable (fun n : Nat =>
      (C / guinandWeilPiOscillatorScale ^ (r + 2)) *
        (1 / (((n + 1 : Nat) : Real) ^ 2))) :=
    hbase.mul_left (C / guinandWeilPiOscillatorScale ^ (r + 2))
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (pow_nonneg (by positivity) r) (norm_nonneg _))
    ?_ hmajorant
  intro n
  have hindex :
      ((n + 1 : Nat) : Real) ≤ ((2 * n + 1 : Nat) : Real) := by
    exact_mod_cast (by omega : n + 1 ≤ 2 * n + 1)
  have heigen_mono :
      (guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) ^ (r + 2) ≤
        (guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real)) ^
          (r + 2) := by
    exact pow_le_pow_left₀
      (mul_nonneg guinandWeilPiOscillatorScale_pos.le (by positivity))
      (mul_le_mul_of_nonneg_left hindex
        guinandWeilPiOscillatorScale_pos.le) _
  have hraw :=
    guinandWeilPiHermiteEigenvalue_pow_mul_norm_coefficient_le_l2
      (r + 2) n f
  have hscaled :
      (guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) ^ (r + 2) *
          ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ ≤ C := by
    apply le_trans
      (mul_le_mul_of_nonneg_right heigen_mono (norm_nonneg _))
    simpa [C] using hraw
  have hscale_pow_pos :
      0 < guinandWeilPiOscillatorScale ^ (r + 2) :=
    pow_pos guinandWeilPiOscillatorScale_pos _
  have hindex_sq_pos : 0 < (((n + 1 : Nat) : Real) ^ 2) := by
    positivity
  have hgoal :
      ((n + 1 : Nat) : Real) ^ r *
          ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ ≤
        (C / guinandWeilPiOscillatorScale ^ (r + 2)) /
          (((n + 1 : Nat) : Real) ^ 2) := by
    apply (le_div_iff₀ hindex_sq_pos).2
    apply (le_div_iff₀ hscale_pow_pos).2
    calc
      (((n + 1 : Nat) : Real) ^ r *
            ‖guinandWeilPiNormalizedHermiteCoefficient n f‖) *
            ((n + 1 : Nat) : Real) ^ 2 *
          guinandWeilPiOscillatorScale ^ (r + 2) =
        (guinandWeilPiOscillatorScale * ((n + 1 : Nat) : Real)) ^ (r + 2) *
          ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ := by
        rw [mul_pow, pow_add]
        ring
      _ ≤ C := hscaled
  simpa [div_eq_mul_inv] using hgoal

/-- The `L2` Hermite series determined by the normalized coefficients of a
Schwartz test.  Identifying this sum with the original test is the separate
Hermite completeness step. -/
noncomputable def guinandWeilPiHermiteL2Expansion
    (f : SchwartzLineTestFunction) :
    Lp Complex (2 : ENNReal) (volume : Measure Real) :=
  ∑' n : Nat,
    guinandWeilPiNormalizedHermiteCoefficient n f •
      (guinandWeilPiNormalizedHermiteSchwartz n).toLp
        (2 : ENNReal) volume

/-- Rapid coefficient decay makes the normalized Hermite series absolutely
summable in `L2`. -/
theorem summable_guinandWeilPiNormalizedHermiteSeries_toLp
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      guinandWeilPiNormalizedHermiteCoefficient n f •
        (guinandWeilPiNormalizedHermiteSchwartz n).toLp
          (2 : ENNReal) volume) := by
  have hcoeff : Summable (fun n : Nat =>
      ‖guinandWeilPiNormalizedHermiteCoefficient n f‖) := by
    simpa using
      summable_nat_add_one_pow_mul_norm_guinandWeilPiNormalizedHermiteCoefficient
        0 f
  refine hcoeff.of_norm_bounded (fun n => ?_)
  rw [norm_smul, norm_toLp_guinandWeilPiNormalizedHermiteSchwartz]
  simp

/-- The actual finite Hermite truncations converge in `L2` to their Hermite
series.  Completeness is exactly the remaining assertion that this series is
the canonical `L2` image of `f`. -/
theorem tendsto_guinandWeilPiHermiteTruncation_toLp
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun N : Nat =>
        (guinandWeilPiHermiteTruncation N f).toLp
          (2 : ENNReal) volume)
      Filter.atTop
      (nhds (guinandWeilPiHermiteL2Expansion f)) := by
  let term : Nat → Lp Complex (2 : ENNReal) (volume : Measure Real) :=
    fun n => guinandWeilPiNormalizedHermiteCoefficient n f •
      (guinandWeilPiNormalizedHermiteSchwartz n).toLp
        (2 : ENNReal) volume
  have hsum : Summable term := by
    simpa [term] using
      summable_guinandWeilPiNormalizedHermiteSeries_toLp f
  have htend :
      Filter.Tendsto (fun N : Nat => ∑ n ∈ Finset.range N, term n)
        Filter.atTop (nhds (∑' n : Nat, term n)) :=
    (Summable.hasSum_iff_tendsto_nat hsum).mp hsum.hasSum
  have htrunc (N : Nat) :
      (guinandWeilPiHermiteTruncation N f).toLp
          (2 : ENNReal) volume =
        ∑ n ∈ Finset.range N, term n := by
    change
      SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
          (guinandWeilPiHermiteTruncation N f) = _
    simp [guinandWeilPiHermiteTruncation, term]
  simpa only [htrunc, guinandWeilPiHermiteL2Expansion, term] using htend

/-- Distinct oscillator Hermite tests are orthogonal for the bilinear pairing. -/
theorem guinandWeilPiSchwartzBilinearPairing_hermite_eq_zero
    {m n : Nat} (hmn : m ≠ n) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiOscillatorHermiteSchwartz m)
        (guinandWeilPiOscillatorHermiteSchwartz n) = 0 := by
  let cmn := guinandWeilPiSchwartzBilinearPairing
    (guinandWeilPiOscillatorHermiteSchwartz m)
    (guinandWeilPiOscillatorHermiteSchwartz n)
  have hsym :=
    guinandWeilPiSchwartzBilinearPairing_oscillator_right_eq_left
      (guinandWeilPiOscillatorHermiteSchwartz m)
      (guinandWeilPiOscillatorHermiteSchwartz n)
  rw [guinandWeilPiHarmonicOscillatorSchwartzCLM_hermite,
    guinandWeilPiHarmonicOscillatorSchwartzCLM_hermite,
    guinandWeilPiSchwartzBilinearPairing_real_smul_right,
    guinandWeilPiSchwartzBilinearPairing_real_smul_left] at hsym
  have heigen :
      guinandWeilPiOscillatorScale * ((2 * n + 1 : Nat) : Real) ≠
        guinandWeilPiOscillatorScale * ((2 * m + 1 : Nat) : Real) := by
    intro h
    have hcast :
        ((2 * n + 1 : Nat) : Real) = ((2 * m + 1 : Nat) : Real) :=
      mul_left_cancel₀ guinandWeilPiOscillatorScale_ne_zero h
    have hnat : 2 * n + 1 = 2 * m + 1 := by
      exact_mod_cast hcast
    apply hmn
    omega
  have heigenC :
      ((guinandWeilPiOscillatorScale *
          ((2 * n + 1 : Nat) : Real) : Real) : Complex) ≠
        ((guinandWeilPiOscillatorScale *
          ((2 * m + 1 : Nat) : Real) : Real) : Complex) := by
    exact_mod_cast heigen
  have hzero :
      (((guinandWeilPiOscillatorScale *
            ((2 * n + 1 : Nat) : Real) : Real) : Complex) -
          ((guinandWeilPiOscillatorScale *
            ((2 * m + 1 : Nat) : Real) : Real) : Complex)) * cmn = 0 := by
    dsimp [cmn]
    calc
      _ =
          ((guinandWeilPiOscillatorScale *
              ((2 * n + 1 : Nat) : Real) : Real) : Complex) *
              guinandWeilPiSchwartzBilinearPairing
                (guinandWeilPiOscillatorHermiteSchwartz m)
                (guinandWeilPiOscillatorHermiteSchwartz n) -
            ((guinandWeilPiOscillatorScale *
              ((2 * m + 1 : Nat) : Real) : Real) : Complex) *
              guinandWeilPiSchwartzBilinearPairing
                (guinandWeilPiOscillatorHermiteSchwartz m)
                (guinandWeilPiOscillatorHermiteSchwartz n) := by ring
      _ = 0 := sub_eq_zero.mpr hsym
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr heigenC)

/-- Distinct normalized Hermite tests remain orthogonal. -/
theorem guinandWeilPiSchwartzBilinearPairing_normalizedHermite_eq_zero
    {m n : Nat} (hmn : m ≠ n) :
    guinandWeilPiSchwartzBilinearPairing
        (guinandWeilPiNormalizedHermiteSchwartz m)
        (guinandWeilPiNormalizedHermiteSchwartz n) = 0 := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  rw [guinandWeilPiSchwartzBilinearPairing_real_smul_left,
    guinandWeilPiSchwartzBilinearPairing_real_smul_right,
    guinandWeilPiSchwartzBilinearPairing_hermite_eq_zero hmn]
  ring

/-- A finite Hermite truncation preserves every coefficient below its cutoff. -/
theorem guinandWeilPiNormalizedHermiteCoefficient_truncation
    {m N : Nat} (hmN : m < N) (f : SchwartzLineTestFunction) :
    guinandWeilPiNormalizedHermiteCoefficient m
        (guinandWeilPiHermiteTruncation N f) =
      guinandWeilPiNormalizedHermiteCoefficient m f := by
  rw [← guinandWeilPiNormalizedHermiteCoefficientCLM_apply]
  simp only [guinandWeilPiHermiteTruncation, map_sum, map_smul,
    guinandWeilPiNormalizedHermiteCoefficientCLM_apply]
  rw [Finset.sum_eq_single m]
  · simp only [guinandWeilPiNormalizedHermiteCoefficient]
    rw [guinandWeilPiSchwartzBilinearPairing_normalizedHermite_self]
    simp
  · intro n hn hnm
    simp only [guinandWeilPiNormalizedHermiteCoefficient]
    rw [guinandWeilPiSchwartzBilinearPairing_normalizedHermite_eq_zero
      (Ne.symm hnm)]
    simp
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hmN)).elim

end

end RiemannHypothesisProject
