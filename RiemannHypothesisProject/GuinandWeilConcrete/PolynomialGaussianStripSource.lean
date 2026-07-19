import RiemannHypothesisProject.GuinandWeilConcrete.GaussianStripSource

/-!
# Polynomial-Gaussian Guinand-Weil strip sources

This module extends the concrete `pi`-normalized Gaussian source to the
polynomial-Gaussian family.  This is the natural Hermite-type analytic source
family: it is closed under complex differentiation and every finite derivative
has rapid polynomial decay on bounded horizontal strips.

The results here are source theorems.  They do not assume a p-series
certificate, zero-side summability, or an endpoint formula package.
-/

namespace RiemannHypothesisProject

open Filter

noncomputable section

/-- A complex polynomial multiplying the `pi`-normalized Gaussian. -/
def guinandWeilPiPolynomialGaussianSource
    (p : Polynomial Complex) (z : Complex) : Complex :=
  p.aeval z * guinandWeilPiGaussianSource z

/--
The polynomial update induced by differentiating a polynomial times the
`pi`-normalized Gaussian.
-/
def guinandWeilPiPolynomialGaussianDerivativeStep
    (p : Polynomial Complex) : Polynomial Complex :=
  p.derivative -
    Polynomial.C ((2 : Complex) * (Real.pi : Complex)) * Polynomial.X * p

/-- The polynomial factor after `m` derivatives of a polynomial-Gaussian. -/
def guinandWeilPiPolynomialGaussianDerivativePolynomial :
    Nat -> Polynomial Complex -> Polynomial Complex
  | 0, p => p
  | m + 1, p =>
      guinandWeilPiPolynomialGaussianDerivativeStep
        (guinandWeilPiPolynomialGaussianDerivativePolynomial m p)

/-- Every polynomial-Gaussian source is entire. -/
theorem analyticOnNhd_guinandWeilPiPolynomialGaussianSource
    (p : Polynomial Complex) :
    AnalyticOnNhd Complex (guinandWeilPiPolynomialGaussianSource p)
      Set.univ := by
  have hd :
      Differentiable Complex (guinandWeilPiPolynomialGaussianSource p) := by
    exact p.differentiable_aeval.mul
      differentiable_guinandWeilPiGaussianSource
  intro z _hz
  exact hd.analyticAt z

/-- Every polynomial-Gaussian source is analytic on each horizontal strip. -/
theorem analyticOnNhd_guinandWeilPiPolynomialGaussianSource_horizontalStrip
    (p : Polynomial Complex) (A : Real) :
    AnalyticOnNhd Complex (guinandWeilPiPolynomialGaussianSource p)
      {z : Complex | abs z.im <= A} := by
  exact
    (analyticOnNhd_guinandWeilPiPolynomialGaussianSource p).mono
      (by intro z _hz; simp)

/-- Differentiating a polynomial-Gaussian applies the Hermite update step. -/
theorem deriv_guinandWeilPiPolynomialGaussianSource
    (p : Polynomial Complex) (z : Complex) :
    deriv (guinandWeilPiPolynomialGaussianSource p) z =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiPolynomialGaussianDerivativeStep p) z := by
  rw [show guinandWeilPiPolynomialGaussianSource p =
      (fun w : Complex => p.aeval w) * guinandWeilPiGaussianSource by rfl]
  rw [deriv_mul p.differentiableAt_aeval
    differentiable_guinandWeilPiGaussianSource.differentiableAt]
  rw [Polynomial.deriv_aeval, deriv_guinandWeilPiGaussianSource]
  simp [guinandWeilPiPolynomialGaussianSource,
    guinandWeilPiPolynomialGaussianDerivativeStep]
  ring

/--
Every finite complex derivative of a polynomial-Gaussian is another member of
the same polynomial-Gaussian family.
-/
theorem iteratedDeriv_guinandWeilPiPolynomialGaussianSource
    (m : Nat) (p : Polynomial Complex) (z : Complex) :
    iteratedDeriv m (guinandWeilPiPolynomialGaussianSource p) z =
      guinandWeilPiPolynomialGaussianSource
        (guinandWeilPiPolynomialGaussianDerivativePolynomial m p) z := by
  induction m generalizing z with
  | zero =>
      simp [guinandWeilPiPolynomialGaussianDerivativePolynomial]
  | succ m ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv m (guinandWeilPiPolynomialGaussianSource p) =
            guinandWeilPiPolynomialGaussianSource
              (guinandWeilPiPolynomialGaussianDerivativePolynomial m p) := by
        funext w
        exact ih w
      rw [hfun]
      simpa [guinandWeilPiPolynomialGaussianDerivativePolynomial] using
        deriv_guinandWeilPiPolynomialGaussianSource
          (guinandWeilPiPolynomialGaussianDerivativePolynomial m p) z

/--
Global shifted-radius rapid-decay envelope for a polynomial-Gaussian on every
bounded horizontal strip.
-/
theorem exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_horizontalStrip
    (p : Polynomial Complex) (k : Nat) {A : Real} (hA : 0 <= A) :
    exists C : Real, forall x y : Real, abs y <= A ->
      norm (guinandWeilPiPolynomialGaussianSource p
          ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <= C := by
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow p with
    ⟨B, hB_pos, hB⟩
  rcases
    exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_horizontalStrip
      (p.natDegree + k) hA with ⟨C, hC⟩
  refine ⟨B * C, ?_⟩
  intro x y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  let R : Real := norm z + 2
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hsource :
      norm (guinandWeilPiPolynomialGaussianSource p z) <=
        B * R ^ p.natDegree * norm (guinandWeilPiGaussianSource z) := by
    rw [guinandWeilPiPolynomialGaussianSource, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [R] using hB z) (norm_nonneg _)
  calc
    norm (guinandWeilPiPolynomialGaussianSource p
        ((x : Complex) + (y : Complex) * Complex.I)) *
      (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (guinandWeilPiPolynomialGaussianSource p z) * R ^ k := by
            rfl
    _ <= (B * R ^ p.natDegree * norm (guinandWeilPiGaussianSource z)) *
        R ^ k := by
          exact mul_le_mul_of_nonneg_right hsource (pow_nonneg hR_nonneg k)
    _ = B * (norm (guinandWeilPiGaussianSource z) *
        R ^ (p.natDegree + k)) := by
          rw [pow_add]
          ring
    _ <= B * C := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [z, R] using hC x y hy) hB_pos.le

/--
Uniform epsilon-form shifted-radius decay for a polynomial-Gaussian on every
bounded horizontal strip.
-/
theorem eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_le_of_horizontalStrip
    (p : Polynomial Complex) (k : Nat) {A epsilon : Real} (hA : 0 <= A)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        norm (guinandWeilPiPolynomialGaussianSource p
            ((x : Complex) + (y : Complex) * Complex.I)) *
          (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  rcases exists_pos_bound_norm_polynomial_aeval_le_shiftedRadius_pow p with
    ⟨B, hB_pos, hB⟩
  have hsmall :
      ∀ᶠ x : Real in cocompact Real,
        ∀ y : Real, abs y <= A ->
          norm (guinandWeilPiGaussianSource
              ((x : Complex) + (y : Complex) * Complex.I)) *
            (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^
              (p.natDegree + k) <=
          epsilon / B :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiGaussianSource_le_of_horizontalStrip
      (p.natDegree + k) hA (div_pos hepsilon hB_pos)
  filter_upwards [hsmall] with x hx y hy
  let z : Complex := (x : Complex) + (y : Complex) * Complex.I
  let R : Real := norm z + 2
  have hR_nonneg : 0 <= R := by
    dsimp [R]
    linarith [norm_nonneg z]
  have hsource :
      norm (guinandWeilPiPolynomialGaussianSource p z) <=
        B * R ^ p.natDegree * norm (guinandWeilPiGaussianSource z) := by
    rw [guinandWeilPiPolynomialGaussianSource, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [R] using hB z) (norm_nonneg _)
  calc
    norm (guinandWeilPiPolynomialGaussianSource p
        ((x : Complex) + (y : Complex) * Complex.I)) *
      (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k
        = norm (guinandWeilPiPolynomialGaussianSource p z) * R ^ k := by
            rfl
    _ <= (B * R ^ p.natDegree * norm (guinandWeilPiGaussianSource z)) *
        R ^ k := by
          exact mul_le_mul_of_nonneg_right hsource (pow_nonneg hR_nonneg k)
    _ = B * (norm (guinandWeilPiGaussianSource z) *
        R ^ (p.natDegree + k)) := by
          rw [pow_add]
          ring
    _ <= B * (epsilon / B) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [z, R] using hx y hy) hB_pos.le
    _ = epsilon := by
      field_simp [ne_of_gt hB_pos]

/--
All finite derivatives of a polynomial-Gaussian have global shifted-radius
rapid-decay envelopes on bounded horizontal strips.
-/
theorem exists_bound_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_horizontalStrip
    (m : Nat) (p : Polynomial Complex) (k : Nat) {A : Real} (hA : 0 <= A) :
    exists C : Real, forall x y : Real, abs y <= A ->
      norm (iteratedDeriv m (guinandWeilPiPolynomialGaussianSource p)
          ((x : Complex) + (y : Complex) * Complex.I)) *
        (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <= C := by
  rcases
    exists_bound_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_horizontalStrip
      (guinandWeilPiPolynomialGaussianDerivativePolynomial m p) k hA with
    ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x y hy
  rw [iteratedDeriv_guinandWeilPiPolynomialGaussianSource]
  exact hC x y hy

/--
All finite derivatives of a polynomial-Gaussian tend rapidly to zero,
uniformly on every bounded horizontal strip.
-/
theorem eventually_forall_norm_iteratedDeriv_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_le_of_horizontalStrip
    (m : Nat) (p : Polynomial Complex) (k : Nat) {A epsilon : Real}
    (hA : 0 <= A) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : Real in cocompact Real,
      ∀ y : Real, abs y <= A ->
        norm (iteratedDeriv m (guinandWeilPiPolynomialGaussianSource p)
            ((x : Complex) + (y : Complex) * Complex.I)) *
          (norm ((x : Complex) + (y : Complex) * Complex.I) + 2) ^ k <=
        epsilon := by
  have hsmall :=
    eventually_forall_norm_mul_shiftedRadius_pow_guinandWeilPiPolynomialGaussianSource_le_of_horizontalStrip
      (guinandWeilPiPolynomialGaussianDerivativePolynomial m p) k hA hepsilon
  filter_upwards [hsmall] with x hx y hy
  rw [iteratedDeriv_guinandWeilPiPolynomialGaussianSource]
  exact hx y hy

end

end RiemannHypothesisProject
