import Mathlib.Analysis.Complex.RealDeriv
import RiemannHypothesisProject.GuinandWeilConcrete.PolynomialGaussianStripSource
import RiemannHypothesisProject.SchwartzExplicitFormula

/-!
# Real-line Schwartz realization of polynomial-Gaussian sources

This module proves that the real restriction of every complex
polynomial-times-`pi`-Gaussian source is a project Schwartz test function.  The
proof identifies all real iterated derivatives with the already checked
complex Hermite recurrence and then uses the bounded-strip rapid-decay theorem
at height zero.

These are analytic source and normalization theorems; no zero-side or p-series
endpoint package is assumed.
-/

namespace RiemannHypothesisProject

open scoped ComplexConjugate

noncomputable section

/-- The real restriction of a polynomial-Gaussian is smooth to all orders. -/
theorem contDiff_guinandWeilPiPolynomialGaussianSource_real
    (p : Polynomial Complex) :
    ContDiff Real (⊤ : ℕ∞)
      (fun x : Real =>
        guinandWeilPiPolynomialGaussianSource p (x : Complex)) := by
  have hcomplex :
      ContDiff Complex (⊤ : ℕ∞)
        (guinandWeilPiPolynomialGaussianSource p) :=
    (p.differentiable_aeval.mul
      differentiable_guinandWeilPiGaussianSource).contDiff
  have hreal :
      ContDiff Real (⊤ : ℕ∞)
        (guinandWeilPiPolynomialGaussianSource p) :=
    hcomplex.restrict_scalars Real
  exact hreal.comp Complex.ofRealCLM.contDiff

/--
The real derivative of a polynomial-Gaussian restriction is the restriction
of its complex derivative and hence applies the same Hermite update step.
-/
theorem deriv_guinandWeilPiPolynomialGaussianSource_real
    (p : Polynomial Complex) (x : Real) :
    deriv
        (fun t : Real =>
          guinandWeilPiPolynomialGaussianSource p (t : Complex)) x =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiPolynomialGaussianDerivativeStep p) (x : Complex) := by
  have hd :
      DifferentiableAt Complex
        (guinandWeilPiPolynomialGaussianSource p) (x : Complex) :=
    (p.differentiable_aeval.mul
      differentiable_guinandWeilPiGaussianSource).differentiableAt
  have hderiv := hd.hasDerivAt
  rw [deriv_guinandWeilPiPolynomialGaussianSource] at hderiv
  exact hderiv.comp_ofReal.deriv

/--
Every real iterated derivative is the real restriction of the corresponding
polynomial-Gaussian Hermite iterate.
-/
theorem iteratedDeriv_guinandWeilPiPolynomialGaussianSource_real
    (m : Nat) (p : Polynomial Complex) (x : Real) :
    iteratedDeriv m
        (fun t : Real =>
          guinandWeilPiPolynomialGaussianSource p (t : Complex)) x =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiPolynomialGaussianDerivativePolynomial m p)
        (x : Complex) := by
  induction m generalizing x with
  | zero =>
      simp [guinandWeilPiPolynomialGaussianDerivativePolynomial]
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv m
              (fun t : Real =>
                guinandWeilPiPolynomialGaussianSource p (t : Complex)) =
            fun t : Real =>
              guinandWeilPiPolynomialGaussianSource
                (guinandWeilPiPolynomialGaussianDerivativePolynomial m p)
                (t : Complex) := by
        funext t
        exact ih t
      rw [hfun]
      simpa [guinandWeilPiPolynomialGaussianDerivativePolynomial] using
        deriv_guinandWeilPiPolynomialGaussianSource_real
          (guinandWeilPiPolynomialGaussianDerivativePolynomial m p) x

/--
Every real derivative of a polynomial-Gaussian satisfies every Schwartz
polynomial seminorm bound.
-/
theorem exists_bound_abs_pow_mul_norm_iteratedDeriv_guinandWeilPiPolynomialGaussianSource_real
    (m : Nat) (p : Polynomial Complex) (k : Nat) :
    ∃ C : Real, ∀ x : Real,
      |x| ^ k *
          norm (iteratedDeriv m
            (fun t : Real =>
              guinandWeilPiPolynomialGaussianSource p (t : Complex)) x) <=
        C := by
  rcases
    exists_bound_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_horizontalStrip
      m p k (A := 0) (le_refl 0) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x
  have hbound := hC x 0 (by simp)
  have hxpow : |x| ^ k <= (|x| + 2) ^ k := by
    exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) k
  rw [iteratedDeriv_guinandWeilPiPolynomialGaussianSource_real]
  calc
    |x| ^ k *
        norm (guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiPolynomialGaussianDerivativePolynomial m p)
          (x : Complex))
        = norm (guinandWeilPiPolynomialGaussianSource
            (guinandWeilPiPolynomialGaussianDerivativePolynomial m p)
            (x : Complex)) * |x| ^ k := by
              ring
    _ <= norm (guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiPolynomialGaussianDerivativePolynomial m p)
          (x : Complex)) * (|x| + 2) ^ k := by
            exact mul_le_mul_of_nonneg_left hxpow (norm_nonneg _)
    _ <= C := by
      simpa [iteratedDeriv_guinandWeilPiPolynomialGaussianSource,
        Complex.norm_real, Real.norm_eq_abs] using hbound

/--
The real restriction of a polynomial-Gaussian as an actual project Schwartz
test function.
-/
noncomputable def guinandWeilPiPolynomialGaussianSchwartz
    (p : Polynomial Complex) : SchwartzLineTestFunction where
  toFun := fun x : Real =>
    guinandWeilPiPolynomialGaussianSource p (x : Complex)
  smooth' := contDiff_guinandWeilPiPolynomialGaussianSource_real p
  decay' k m := by
    rcases
      exists_bound_abs_pow_mul_norm_iteratedDeriv_guinandWeilPiPolynomialGaussianSource_real
        m p k with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC x

@[simp]
theorem guinandWeilPiPolynomialGaussianSchwartz_apply
    (p : Polynomial Complex) (x : Real) :
    guinandWeilPiPolynomialGaussianSchwartz p x =
      guinandWeilPiPolynomialGaussianSource p (x : Complex) :=
  rfl

/--
Polynomial-Gaussian sources with real coefficients commute with complex
conjugation.
-/
theorem guinandWeilPiPolynomialGaussianSource_map_real_conj
    (p : Polynomial Real) (z : Complex) :
    guinandWeilPiPolynomialGaussianSource
        (p.map (algebraMap Real Complex)) (conj z) =
      conj
        (guinandWeilPiPolynomialGaussianSource
          (p.map (algebraMap Real Complex)) z) := by
  rw [guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiPolynomialGaussianSource]
  have hp :
      (p.map (algebraMap Real Complex)).aeval (conj z) =
        conj ((p.map (algebraMap Real Complex)).aeval z) := by
    simpa using (Polynomial.aeval_conj p z)
  rw [hp, guinandWeilPiGaussianSource_conj]
  simp [map_mul]

/-- Real-coefficient polynomial-Gaussians are real-valued on the real axis. -/
theorem guinandWeilPiPolynomialGaussianSource_map_real_ofReal_im
    (p : Polynomial Real) (x : Real) :
    (guinandWeilPiPolynomialGaussianSource
      (p.map (algebraMap Real Complex)) (x : Complex)).im = 0 := by
  have h :=
    guinandWeilPiPolynomialGaussianSource_map_real_conj p (x : Complex)
  have hconj :
      conj
          (guinandWeilPiPolynomialGaussianSource
            (p.map (algebraMap Real Complex)) (x : Complex)) =
        guinandWeilPiPolynomialGaussianSource
          (p.map (algebraMap Real Complex)) (x : Complex) := by
    simpa using h.symm
  exact Complex.conj_eq_iff_im.mp hconj

end

end RiemannHypothesisProject
