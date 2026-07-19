import RiemannHypothesisProject.GuinandWeilConcrete.HermiteCompleteness

/-!
# Even real Hermite density

This module restricts Hermite completeness to the formula-compatible real,
even Schwartz sector and identifies finite spectral approximants with the
real even polynomial-Gaussian source.
-/

namespace RiemannHypothesisProject

open Filter MeasureTheory Module Submodule Topology

noncomputable section

/-- Coefficients under reflection `X ↦ -X`. -/
theorem Polynomial.coeff_comp_neg_X (p : Polynomial Real) (m : Nat) :
    (p.comp (-Polynomial.X)).coeff m =
      (-1 : Real) ^ m * p.coeff m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [hp, hq, mul_add]
  | monomial n c =>
      by_cases hmn : m = n
      · subst m
        rw [show -Polynomial.X =
          (-1 : Polynomial Real) * Polynomial.X by ring,
          Polynomial.monomial_comp, mul_pow]
        rw [show (-1 : Polynomial Real) ^ n =
          Polynomial.C ((-1 : Real) ^ n) by simp]
        rw [Polynomial.C_mul_X_pow_eq_monomial]
        simp
        ring
      · rw [show -Polynomial.X =
          (-1 : Polynomial Real) * Polynomial.X by ring,
          Polynomial.monomial_comp, mul_pow]
        rw [show (-1 : Polynomial Real) ^ n =
          Polynomial.C ((-1 : Real) ^ n) by simp]
        rw [Polynomial.C_mul_X_pow_eq_monomial]
        rw [Polynomial.C_mul_monomial,
          Polynomial.coeff_monomial, Polynomial.coeff_monomial]
        simp [Ne.symm hmn]

/-- The intended real, even project Schwartz sector. -/
def guinandWeilRealEvenSchwartzSubmodule :
    Submodule Real SchwartzLineTestFunction where
  carrier := {f | (∀ x : Real, f (-x) = f x) ∧
    ∀ x : Real, (f x).im = 0}
  zero_mem' := by simp
  add_mem' := fun {f g} hf hg => by
    constructor
    · intro x
      simp only [SchwartzMap.add_apply, hf.1 x, hg.1 x]
    · intro x
      simp only [SchwartzMap.add_apply, Complex.add_im, hf.2 x, hg.2 x, add_zero]
  smul_mem' := fun c {f} hf => by
    constructor
    · intro x
      simp only [SchwartzMap.smul_apply, hf.1 x]
    · intro x
      simp only [SchwartzMap.smul_apply, Complex.smul_im, hf.2 x]
      exact smul_zero c

/-- Normalized odd Hermite tests are odd. -/
theorem guinandWeilPiNormalizedHermiteSchwartz_odd
    (n : Nat) (x : Real) :
    guinandWeilPiNormalizedHermiteSchwartz (2 * n + 1) (-x) =
      -guinandWeilPiNormalizedHermiteSchwartz (2 * n + 1) x := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  change
    (Real.sqrt (guinandWeilPiHermiteNormSq (2 * n + 1)))⁻¹ •
        guinandWeilPiOscillatorHermiteSchwartz (2 * n + 1) (-x) = _
  rw [guinandWeilPiOscillatorHermiteSchwartz_neg]
  simp [pow_succ, pow_mul]

/-- An integrable odd function on the real line has zero integral. -/
theorem integral_eq_zero_of_neg_eq_neg
    (F : Real → Complex)
    (hodd : ∀ x : Real, F (-x) = -F x) :
    (∫ x : Real, F x) = 0 := by
  have hreflect : (∫ x : Real, F (-x)) = ∫ x : Real, F x := by
    exact integral_neg_eq_self F volume
  have hneg : (∫ x : Real, F (-x)) = -(∫ x : Real, F x) := by
    rw [show (fun x : Real => F (-x)) = fun x => -F x by
      funext x
      exact hodd x]
    exact integral_neg F
  have hself : (∫ x : Real, F x) = -(∫ x : Real, F x) :=
    hreflect.symm.trans hneg
  have htwo : (2 : Complex) * (∫ x : Real, F x) = 0 := by
    linear_combination hself
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Odd Hermite coefficients vanish on even Schwartz tests. -/
theorem guinandWeilPiNormalizedHermiteCoefficient_odd_eq_zero
    (f : SchwartzLineTestFunction)
    (heven : ∀ x : Real, f (-x) = f x)
    (n : Nat) :
    guinandWeilPiNormalizedHermiteCoefficient (2 * n + 1) f = 0 := by
  unfold guinandWeilPiNormalizedHermiteCoefficient
    guinandWeilPiSchwartzBilinearPairing
  apply integral_eq_zero_of_neg_eq_neg
  · intro x
    rw [guinandWeilPiNormalizedHermiteSchwartz_odd, heven]
    ring

/-- Hermite coefficients of real-valued Schwartz tests are real. -/
theorem guinandWeilPiNormalizedHermiteCoefficient_im_eq_zero
    (f : SchwartzLineTestFunction)
    (hreal : ∀ x : Real, (f x).im = 0)
    (n : Nat) :
    (guinandWeilPiNormalizedHermiteCoefficient n f).im = 0 := by
  let F : Real → Complex := fun x =>
    guinandWeilPiNormalizedHermiteSchwartz n x * f x
  have hF : Integrable F :=
    (SchwartzMap.pairing (ContinuousLinearMap.mul Complex Complex)
      (guinandWeilPiNormalizedHermiteSchwartz n) f).integrable
  unfold guinandWeilPiNormalizedHermiteCoefficient
    guinandWeilPiSchwartzBilinearPairing
  change (∫ x : Real, F x).im = 0
  have him := integral_im hF
  change (∫ x : Real, (F x).im) = (∫ x : Real, F x).im at him
  rw [← him]
  have hfun : (fun x : Real => (F x).im) = 0 := by
    funext x
    simp [F, Complex.mul_im,
      guinandWeilPiNormalizedHermiteSchwartz_im, hreal]
  rw [hfun]
  simp

/-- The real span of the even normalized Hermite tests. -/
noncomputable def guinandWeilPiEvenNormalizedHermiteSpan :
    Submodule Real SchwartzLineTestFunction :=
  Submodule.span Real
    (Set.range (fun n : Nat => guinandWeilPiNormalizedHermiteSchwartz (2 * n)))

/-- Every Hermite truncation of a real, even test lies in the real even
Hermite span. -/
theorem guinandWeilPiHermiteTruncation_mem_evenNormalizedHermiteSpan
    (f : SchwartzLineTestFunction)
    (heven : ∀ x : Real, f (-x) = f x)
    (hreal : ∀ x : Real, (f x).im = 0)
    (N : Nat) :
    guinandWeilPiHermiteTruncation N f ∈
      guinandWeilPiEvenNormalizedHermiteSpan := by
  rw [guinandWeilPiHermiteTruncation]
  apply Submodule.sum_mem
  intro n hn
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have him :=
      guinandWeilPiNormalizedHermiteCoefficient_im_eq_zero f hreal (2 * k)
    have hcoeff :
        guinandWeilPiNormalizedHermiteCoefficient (2 * k) f =
          ((guinandWeilPiNormalizedHermiteCoefficient (2 * k) f).re : Complex) := by
      apply Complex.ext
      · simp
      · simpa using him
    rw [hcoeff]
    change (guinandWeilPiNormalizedHermiteCoefficient (2 * k) f).re •
        guinandWeilPiNormalizedHermiteSchwartz (2 * k) ∈
      guinandWeilPiEvenNormalizedHermiteSpan
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, rfl⟩)
  · rw [guinandWeilPiNormalizedHermiteCoefficient_odd_eq_zero f heven k]
    simp

/-- Sequential density of the even Hermite span in the intended real, even
Schwartz sector. -/
theorem exists_evenHermiteSpan_approximation
    (f : guinandWeilRealEvenSchwartzSubmodule) :
    ∃ u : Nat → SchwartzLineTestFunction,
      (∀ N, u N ∈ guinandWeilPiEvenNormalizedHermiteSpan) ∧
      Tendsto u atTop (𝓝 (f : SchwartzLineTestFunction)) := by
  refine ⟨fun N => guinandWeilPiHermiteTruncation N f, ?_, ?_⟩
  · intro N
    exact guinandWeilPiHermiteTruncation_mem_evenNormalizedHermiteSpan
      f f.property.1 f.property.2 N
  · exact tendsto_guinandWeilPiHermiteTruncation_schwartz_self f

/-- Compress the exponents of a polynomial whose support is even. -/
noncomputable def guinandWeilEvenPolynomialCompression (p : Polynomial Real) :
    Polynomial Real :=
  ∑ i ∈ p.support, Polynomial.monomial (i / 2) (p.coeff i)

/-- Compression inverts substitution by `X^2` when every supported exponent
is even. -/
theorem guinandWeilEvenPolynomialCompression_comp_X_sq
    (p : Polynomial Real)
    (hsupport : ∀ i ∈ p.support, Even i) :
    (guinandWeilEvenPolynomialCompression p).comp (Polynomial.X ^ 2) = p := by
  rw [guinandWeilEvenPolynomialCompression, Polynomial.sum_comp]
  conv_rhs => rw [p.as_sum_support]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hsupport i hi with ⟨k, rfl⟩
  rw [Polynomial.monomial_comp]
  have hdiv : (k + k) / 2 = k := by omega
  rw [hdiv, ← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

/-- Even-indexed oscillator Hermite polynomials are fixed by reflection. -/
theorem guinandWeilPiOscillatorHermiteRealPolynomial_even_comp_neg_X
    (n : Nat) :
    (guinandWeilPiOscillatorHermiteRealPolynomial (2 * n)).comp
        (-Polynomial.X) =
      guinandWeilPiOscillatorHermiteRealPolynomial (2 * n) := by
  apply Polynomial.funext
  intro x
  simp [Polynomial.eval_comp,
    guinandWeilPiOscillatorHermiteRealPolynomial_eval_neg, pow_mul]

/-- Every supported exponent of an even-indexed oscillator Hermite polynomial
is even. -/
theorem even_support_guinandWeilPiOscillatorHermiteRealPolynomial
    (n i : Nat)
    (hi : i ∈ (guinandWeilPiOscillatorHermiteRealPolynomial (2 * n)).support) :
    Even i := by
  by_contra hnot
  have hodd : Odd i := Nat.not_even_iff_odd.mp hnot
  rcases hodd with ⟨k, rfl⟩
  let p := guinandWeilPiOscillatorHermiteRealPolynomial (2 * n)
  have hreflect :=
    guinandWeilPiOscillatorHermiteRealPolynomial_even_comp_neg_X n
  have hcoeff := congrArg (fun q : Polynomial Real => q.coeff (2 * k + 1)) hreflect
  rw [Polynomial.coeff_comp_neg_X] at hcoeff
  have hzero : p.coeff (2 * k + 1) = 0 := by
    dsimp only [p] at hcoeff ⊢
    have hsign : (-1 : Real) ^ (2 * k + 1) = -1 := by
      simp [pow_succ, pow_mul]
    rw [hsign] at hcoeff
    linarith
  exact (Polynomial.mem_support_iff.mp hi) hzero

/-- Every even-indexed oscillator Hermite polynomial is a polynomial in
`X^2`. -/
theorem exists_evenPolynomial_guinandWeilPiOscillatorHermiteRealPolynomial
    (n : Nat) :
    ∃ q : Polynomial Real,
      q.comp (Polynomial.X ^ 2) =
        guinandWeilPiOscillatorHermiteRealPolynomial (2 * n) := by
  let p := guinandWeilPiOscillatorHermiteRealPolynomial (2 * n)
  refine ⟨guinandWeilEvenPolynomialCompression p, ?_⟩
  exact guinandWeilEvenPolynomialCompression_comp_X_sq p
    (fun i hi =>
      even_support_guinandWeilPiOscillatorHermiteRealPolynomial n i hi)

/-- Each normalized even Hermite test lies in the exact real even
polynomial-Gaussian source range. -/
theorem guinandWeilPiNormalizedHermiteSchwartz_even_mem_sourceRange
    (n : Nat) :
    guinandWeilPiNormalizedHermiteSchwartz (2 * n) ∈
      LinearMap.range guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap := by
  rcases exists_evenPolynomial_guinandWeilPiOscillatorHermiteRealPolynomial n with
    ⟨q, hq⟩
  let c : Real := (Real.sqrt (guinandWeilPiHermiteNormSq (2 * n)))⁻¹
  have hsource :
      guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap q =
        guinandWeilPiOscillatorHermiteSchwartz (2 * n) := by
    ext x
    change guinandWeilPiPolynomialGaussianSchwartz
        (guinandWeilPiEvenPolynomial q) x =
      guinandWeilPiPolynomialGaussianSchwartz
        ((guinandWeilPiOscillatorHermiteRealPolynomial (2 * n)).map
          (algebraMap Real Complex)) x
    rw [guinandWeilPiEvenPolynomial, hq]
  refine ⟨c • q, ?_⟩
  rw [map_smul]
  unfold guinandWeilPiNormalizedHermiteSchwartz
  change c • guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap q =
    c • guinandWeilPiOscillatorHermiteSchwartz (2 * n)
  rw [hsource]

/-- The even Hermite span is contained in the exact formula-compatible source
range. -/
theorem guinandWeilPiEvenNormalizedHermiteSpan_le_sourceRange :
    guinandWeilPiEvenNormalizedHermiteSpan ≤
      LinearMap.range guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact guinandWeilPiNormalizedHermiteSchwartz_even_mem_sourceRange n

/-- Every real, even Schwartz test is a Schwartz-topology limit of exact
`p(X^2) exp(-pi X^2)` source tests. -/
theorem exists_evenPolynomialGaussianSource_approximation
    (f : guinandWeilRealEvenSchwartzSubmodule) :
    ∃ p : Nat → Polynomial Real,
      Tendsto (fun N =>
        guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap (p N))
        atTop (𝓝 (f : SchwartzLineTestFunction)) := by
  have hmem (N : Nat) :
      guinandWeilPiHermiteTruncation N f ∈
        LinearMap.range guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap :=
    guinandWeilPiEvenNormalizedHermiteSpan_le_sourceRange
      (guinandWeilPiHermiteTruncation_mem_evenNormalizedHermiteSpan
        f f.property.1 f.property.2 N)
  choose p hp using hmem
  refine ⟨p, ?_⟩
  have hfun : (fun N =>
      guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap (p N)) =
        fun N => guinandWeilPiHermiteTruncation N f := by
    funext N
    exact hp N
  rw [hfun]
  exact tendsto_guinandWeilPiHermiteTruncation_schwartz_self f

/-- The exact even polynomial-Gaussian source map, with codomain restricted to
the intended real, even Schwartz sector. -/
noncomputable def guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap :
    Polynomial Real →ₗ[Real] guinandWeilRealEvenSchwartzSubmodule :=
  guinandWeilPiEvenPolynomialGaussianSchwartzLinearMap.codRestrict
    guinandWeilRealEvenSchwartzSubmodule
    (fun p => ⟨guinandWeilPiEvenPolynomialGaussianSchwartz_neg p,
      guinandWeilPiEvenPolynomialGaussianSchwartz_im p⟩)

/-- The formula-compatible real even polynomial-Gaussian source has dense
range in the intended real, even Schwartz topology. -/
theorem denseRange_guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap :
    DenseRange guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  rcases exists_evenPolynomialGaussianSource_approximation f with ⟨p, hp⟩
  have hsub : Tendsto
      (fun N => guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap (p N))
      atTop (𝓝 f) := by
    rw [tendsto_subtype_rng]
    simpa [guinandWeilPiEvenPolynomialGaussianRealEvenLinearMap] using hp
  exact mem_closure_of_tendsto hsub
    (Eventually.of_forall fun N => Set.mem_range_self (p N))

end

end RiemannHypothesisProject
