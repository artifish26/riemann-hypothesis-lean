import RiemannHypothesisProject.RiemannVonMangoldt.RealAxisEndpoints
import RiemannHypothesisProject.RiemannWeilShiftedRadius.StripGeometry
import RiemannHypothesisProject.SchwartzRiemannWeilWeight

/-!
# Trivial-axis shifted-radius geometry

This module contains Riemann-Weil zero-argument coordinate facts, indexed
trivial-zero heights, positive-imaginary-axis shifted-radius estimates, and
closed-strip membership facts for nontrivial zero arguments.
-/

namespace RiemannHypothesisProject

/-- The real part of the Riemann-Weil zero argument is the zeta zero ordinate. -/
theorem riemannWeilZeroArgument_re (z : Complex) :
    (riemannWeilZeroArgument z).re = z.im := by
  unfold riemannWeilZeroArgument
  simp [Complex.normSq, Complex.I_re, Complex.I_im]

/-- The imaginary part of the Riemann-Weil zero argument records displacement
from the critical-line real part. -/
theorem riemannWeilZeroArgument_im (z : Complex) :
    (riemannWeilZeroArgument z).im = (1 / 2 : Real) - z.re := by
  unfold riemannWeilZeroArgument
  simp [Complex.normSq, Complex.I_re, Complex.I_im]

/-- The imaginary-axis height of the Riemann-Weil argument of the `n`th trivial zero. -/
noncomputable def riemannWeilTrivialZeroArgumentHeight (n : Nat) : Real :=
  2 * ((n : Real) + 1) + 1 / 2

/-- Trivial-zero argument heights are positive. -/
theorem riemannWeilTrivialZeroArgumentHeight_pos (n : Nat) :
    0 < riemannWeilTrivialZeroArgumentHeight n := by
  dsimp [riemannWeilTrivialZeroArgumentHeight]
  positivity

/-- The indexed trivial-zero argument heights start at `5 / 2`. -/
theorem riemannWeilTrivialZeroArgumentHeight_ge_five_halves (n : Nat) :
    (5 / 2 : Real) <= riemannWeilTrivialZeroArgumentHeight n := by
  dsimp [riemannWeilTrivialZeroArgumentHeight]
  have hn : 0 <= (n : Real) := by exact_mod_cast Nat.zero_le n
  linarith

/-- The indexed trivial-zero argument heights are monotone in the index. -/
theorem riemannWeilTrivialZeroArgumentHeight_mono {m n : Nat} (hmn : m <= n) :
    riemannWeilTrivialZeroArgumentHeight m <=
      riemannWeilTrivialZeroArgumentHeight n := by
  dsimp [riemannWeilTrivialZeroArgumentHeight]
  have hmn_real : (m : Real) <= (n : Real) := by exact_mod_cast hmn
  linarith

/-- The norm of the indexed trivial-zero imaginary-axis argument. -/
theorem norm_trivialZeroArgumentHeight_mul_I (n : Nat) :
    norm ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I) =
      riemannWeilTrivialZeroArgumentHeight n := by
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))]

/--
The Riemann-Weil argument of the project-known `n`th trivial zeta zero lies on
the positive imaginary axis at height `2 * (n + 1) + 1 / 2`.
-/
theorem riemannWeilZeroArgument_trivialZero_eq_height_mul_I
    (n : Nat) :
    riemannWeilZeroArgument (-2 * ((n : Complex) + 1)) =
      (riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I := by
  apply Complex.ext
  · rw [riemannWeilZeroArgument_re]
    simp [riemannWeilTrivialZeroArgumentHeight]
  · rw [riemannWeilZeroArgument_im]
    simp [riemannWeilTrivialZeroArgumentHeight]
    ring

/-- Every project-known trivial zeta zero has an indexed imaginary-axis argument. -/
theorem exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
    {s : Complex} (htrivial : IsTrivialZetaZero s) :
    exists n : Nat,
      riemannWeilZeroArgument s =
        (riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I := by
  rcases htrivial with ⟨n, hs⟩
  refine ⟨n, ?_⟩
  rw [hs]
  exact riemannWeilZeroArgument_trivialZero_eq_height_mul_I n

/--
A uniform weighted estimate on the positive imaginary axis controls the
indexed trivial-zero argument ray.

This is a real analytic narrowing of the p-series blocker: the remaining
trivial-zero estimate can be proved as a one-dimensional ray estimate in the
height variable, rather than as a separate indexed condition.
-/
theorem trivialAxis_weighted_norm_le_of_imaginaryAxis_nonnegative_height_bound
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (imaginaryAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (y + 2) ^ (k : Real) <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    norm
        (system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)) *
        (riemannWeilTrivialZeroArgumentHeight n + 2) ^ (k : Real) <=
      axisConstant f := by
  exact imaginaryAxis_weighted_norm_le f
    (riemannWeilTrivialZeroArgumentHeight n)
    (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))

/--
On the positive imaginary axis, a `(1 + y)^k` weighted estimate implies the
shifted `(y + 2)^k` estimate used by the p-series certificate, up to the
explicit factor `2^k`.
-/
theorem imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_nat
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (imaginaryAxis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (1 + y) ^ k <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (y : Real)
    (hy : 0 <= y) :
    norm (system.extension f ((y : Complex) * Complex.I)) *
        (y + 2) ^ k <=
      (2 : Real) ^ k * axisConstant f := by
  let axisValue : Real :=
    norm (system.extension f ((y : Complex) * Complex.I))
  have hshift_base :
      y + 2 <= (2 : Real) * (1 + y) := by
    linarith
  have hshift_pow :
      (y + 2) ^ k <= ((2 : Real) * (1 + y)) ^ k := by
    exact pow_le_pow_left₀ (by linarith) hshift_base k
  have hshift_pow' :
      (y + 2) ^ k <= (2 : Real) ^ k * (1 + y) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hweighted :
      axisValue * (1 + y) ^ k <= axisConstant f := by
    simpa [axisValue] using imaginaryAxis_oneAdd_weighted_norm_le f y hy
  have hfirst :
      axisValue * (y + 2) ^ k <=
        axisValue * ((2 : Real) ^ k * (1 + y) ^ k) := by
    exact mul_le_mul_of_nonneg_left hshift_pow' (by positivity)
  have hscaled :
      (2 : Real) ^ k * (axisValue * (1 + y) ^ k) <=
        (2 : Real) ^ k * axisConstant f := by
    exact mul_le_mul_of_nonneg_left hweighted
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  calc
    norm (system.extension f ((y : Complex) * Complex.I)) * (y + 2) ^ k
        = axisValue * (y + 2) ^ k := by
          rfl
    _ <= axisValue * ((2 : Real) ^ k * (1 + y) ^ k) := hfirst
    _ = (2 : Real) ^ k * (axisValue * (1 + y) ^ k) := by
      ring
    _ <= (2 : Real) ^ k * axisConstant f := hscaled

/--
Real-exponent version of
`imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_nat`.
-/
theorem imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_rpow_natCast
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (imaginaryAxis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (1 + y) ^ (k : Real) <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (y : Real)
    (hy : 0 <= y) :
    norm (system.extension f ((y : Complex) * Complex.I)) *
        (y + 2) ^ (k : Real) <=
      (2 : Real) ^ k * axisConstant f := by
  simpa [Real.rpow_natCast] using
    imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_nat
      (system := system) axisConstant k
      (by
        intro f y hy
        simpa [Real.rpow_natCast] using
          imaginaryAxis_oneAdd_weighted_norm_le f y hy)
      f y hy

/--
Fixed-test positive-imaginary-axis geometry.

This is the source-class version of
`imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_rpow_natCast`:
it converts a `(1 + y)^k` estimate for one fixed profile into the shifted
`(y + 2)^k` estimate used by the trivial-zero ray.
-/
theorem fixedImaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_nat
    (extension : Complex -> Complex)
    (axisConstant : Real)
    (k : Nat)
    (imaginaryAxis_oneAdd_weighted_norm_le :
      forall y : Real,
        0 <= y ->
          norm (extension ((y : Complex) * Complex.I)) * (1 + y) ^ k <=
            axisConstant)
    (y : Real)
    (hy : 0 <= y) :
    norm (extension ((y : Complex) * Complex.I)) * (y + 2) ^ k <=
      (2 : Real) ^ k * axisConstant := by
  let axisValue : Real := norm (extension ((y : Complex) * Complex.I))
  have hshift_base :
      y + 2 <= (2 : Real) * (1 + y) := by
    linarith
  have hshift_pow :
      (y + 2) ^ k <= ((2 : Real) * (1 + y)) ^ k := by
    exact pow_le_pow_left₀ (by linarith) hshift_base k
  have hshift_pow' :
      (y + 2) ^ k <= (2 : Real) ^ k * (1 + y) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hweighted :
      axisValue * (1 + y) ^ k <= axisConstant := by
    simpa [axisValue] using imaginaryAxis_oneAdd_weighted_norm_le y hy
  have hfirst :
      axisValue * (y + 2) ^ k <=
        axisValue * ((2 : Real) ^ k * (1 + y) ^ k) := by
    exact mul_le_mul_of_nonneg_left hshift_pow' (by positivity)
  have hscaled :
      (2 : Real) ^ k * (axisValue * (1 + y) ^ k) <=
        (2 : Real) ^ k * axisConstant := by
    exact mul_le_mul_of_nonneg_left hweighted
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  calc
    norm (extension ((y : Complex) * Complex.I)) * (y + 2) ^ k
        = axisValue * (y + 2) ^ k := by
          rfl
    _ <= axisValue * ((2 : Real) ^ k * (1 + y) ^ k) := hfirst
    _ = (2 : Real) ^ k * (axisValue * (1 + y) ^ k) := by
      ring
    _ <= (2 : Real) ^ k * axisConstant := hscaled

/--
Real-exponent fixed-test version of
`fixedImaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_nat`.
-/
theorem fixedImaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_rpow_natCast
    (extension : Complex -> Complex)
    (axisConstant : Real)
    (k : Nat)
    (imaginaryAxis_oneAdd_weighted_norm_le :
      forall y : Real,
        0 <= y ->
          norm (extension ((y : Complex) * Complex.I)) *
              (1 + y) ^ (k : Real) <=
            axisConstant)
    (y : Real)
    (hy : 0 <= y) :
    norm (extension ((y : Complex) * Complex.I)) * (y + 2) ^ (k : Real) <=
      (2 : Real) ^ k * axisConstant := by
  simpa [Real.rpow_natCast] using
    fixedImaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_nat
      extension axisConstant k
      (by
        intro y hy
        simpa [Real.rpow_natCast] using
          imaginaryAxis_oneAdd_weighted_norm_le y hy)
      y hy

/--
One-height version of the positive-imaginary-axis weight conversion.

This is the local estimate needed for indexed trivial-zero tails: it pays the
same explicit `2^k` factor as the all-height axis lemma, but assumes the
`(1 + y)^k` bound only at the single height being used.
-/
theorem fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height
    (extension : Complex -> Complex)
    (axisConstant : Real)
    (k : Nat)
    {y : Real}
    (hy : 0 <= y)
    (oneAdd_weighted_norm_le :
      norm (extension ((y : Complex) * Complex.I)) *
          (1 + y) ^ (k : Real) <=
        axisConstant) :
    norm (extension ((y : Complex) * Complex.I)) *
        (norm ((y : Complex) * Complex.I) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * axisConstant := by
  let axisValue : Real := norm (extension ((y : Complex) * Complex.I))
  let shiftedPower : Real := (norm ((y : Complex) * Complex.I) + 2) ^ k
  let oneAddPower : Real := (1 + y) ^ k
  have haxis_norm : norm ((y : Complex) * Complex.I) = y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hy]
  have honeAdd_nonneg : 0 <= 1 + y := by
    linarith
  have hshift_nonneg : 0 <= norm ((y : Complex) * Complex.I) + 2 := by
    have hnorm_nonneg : 0 <= norm ((y : Complex) * Complex.I) := norm_nonneg _
    linarith
  have hshift_base :
      norm ((y : Complex) * Complex.I) + 2 <= (2 : Real) * (1 + y) := by
    rw [haxis_norm]
    linarith
  have hshift_pow :
      shiftedPower <= ((2 : Real) * (1 + y)) ^ k := by
    dsimp [shiftedPower]
    exact pow_le_pow_left₀ hshift_nonneg hshift_base k
  have hshift_pow' :
      shiftedPower <= (2 : Real) ^ k * oneAddPower := by
    dsimp [oneAddPower]
    simpa [mul_pow] using hshift_pow
  have hweighted :
      axisValue * oneAddPower <= axisConstant := by
    dsimp [axisValue, oneAddPower]
    simpa [Real.rpow_natCast] using oneAdd_weighted_norm_le
  have hfirst :
      axisValue * shiftedPower <=
        axisValue * ((2 : Real) ^ k * oneAddPower) := by
    exact mul_le_mul_of_nonneg_left hshift_pow' (by positivity)
  have hscaled :
      (2 : Real) ^ k * (axisValue * oneAddPower) <=
        (2 : Real) ^ k * axisConstant := by
    exact mul_le_mul_of_nonneg_left hweighted
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  calc
    norm (extension ((y : Complex) * Complex.I)) *
        (norm ((y : Complex) * Complex.I) + 2) ^ (k : Real)
        = axisValue * shiftedPower := by
          dsimp [axisValue, shiftedPower]
          simp [Real.rpow_natCast]
    _ <= axisValue * ((2 : Real) ^ k * oneAddPower) := hfirst
    _ = (2 : Real) ^ k * (axisValue * oneAddPower) := by
      ring
    _ <= (2 : Real) ^ k * axisConstant := hscaled

/--
Sharper one-height positive-axis conversion away from the origin.

At heights `5 / 2 <= y`, the shifted radius satisfies
`y + 2 <= (9 / 7) * (1 + y)`, improving the all-height `2^k` loss to
`(9 / 7)^k`. The indexed trivial-zero heights all satisfy this lower bound.
-/
theorem fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height_ge_five_halves
    (extension : Complex -> Complex)
    (axisConstant : Real)
    (k : Nat)
    {y : Real}
    (hy_lower : (5 / 2 : Real) <= y)
    (oneAdd_weighted_norm_le :
      norm (extension ((y : Complex) * Complex.I)) *
          (1 + y) ^ (k : Real) <=
        axisConstant) :
    norm (extension ((y : Complex) * Complex.I)) *
        (norm ((y : Complex) * Complex.I) + 2) ^ (k : Real) <=
      ((9 : Real) / 7) ^ k * axisConstant := by
  let axisValue : Real := norm (extension ((y : Complex) * Complex.I))
  let shiftedPower : Real := (norm ((y : Complex) * Complex.I) + 2) ^ k
  let oneAddPower : Real := (1 + y) ^ k
  have hy : 0 <= y := by linarith
  have haxis_norm : norm ((y : Complex) * Complex.I) = y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hy]
  have honeAdd_nonneg : 0 <= 1 + y := by linarith
  have hshift_nonneg : 0 <= norm ((y : Complex) * Complex.I) + 2 := by
    have hnorm_nonneg : 0 <= norm ((y : Complex) * Complex.I) := norm_nonneg _
    linarith
  have hshift_base :
      norm ((y : Complex) * Complex.I) + 2 <=
        ((9 : Real) / 7) * (1 + y) := by
    rw [haxis_norm]
    nlinarith
  have hshift_pow :
      shiftedPower <= (((9 : Real) / 7) * (1 + y)) ^ k := by
    dsimp [shiftedPower]
    exact pow_le_pow_left₀ hshift_nonneg hshift_base k
  have hshift_pow' :
      shiftedPower <= ((9 : Real) / 7) ^ k * oneAddPower := by
    dsimp [oneAddPower]
    simpa [mul_pow] using hshift_pow
  have hweighted :
      axisValue * oneAddPower <= axisConstant := by
    dsimp [axisValue, oneAddPower]
    simpa [Real.rpow_natCast] using oneAdd_weighted_norm_le
  have hfirst :
      axisValue * shiftedPower <=
        axisValue * (((9 : Real) / 7) ^ k * oneAddPower) := by
    exact mul_le_mul_of_nonneg_left hshift_pow' (by positivity)
  have hscaled :
      ((9 : Real) / 7) ^ k * (axisValue * oneAddPower) <=
        ((9 : Real) / 7) ^ k * axisConstant := by
    exact mul_le_mul_of_nonneg_left hweighted
      (pow_nonneg (by norm_num : (0 : Real) <= (9 : Real) / 7) k)
  calc
    norm (extension ((y : Complex) * Complex.I)) *
        (norm ((y : Complex) * Complex.I) + 2) ^ (k : Real)
        = axisValue * shiftedPower := by
          dsimp [axisValue, shiftedPower]
          simp [Real.rpow_natCast]
    _ <= axisValue * (((9 : Real) / 7) ^ k * oneAddPower) := hfirst
    _ = ((9 : Real) / 7) ^ k * (axisValue * oneAddPower) := by
      ring
    _ <= ((9 : Real) / 7) ^ k * axisConstant := hscaled

/--
Sharper one-add conversion at the actual indexed trivial-zero heights.

This avoids paying the all-height `2^k` loss on the trivial-zero tail; the
checked height lower bound gives the smaller factor `(9 / 7)^k`.
-/
theorem fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight
    (extension : Complex -> Complex)
    (axisConstant : Real)
    (k n : Nat)
    (oneAdd_weighted_norm_le :
      norm
          (extension
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I)) *
          (1 + riemannWeilTrivialZeroArgumentHeight n) ^ (k : Real) <=
        axisConstant) :
    norm
        (extension
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real) <=
      ((9 : Real) / 7) ^ k * axisConstant := by
  exact
    fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height_ge_five_halves
      extension axisConstant k
      (riemannWeilTrivialZeroArgumentHeight_ge_five_halves n)
      oneAdd_weighted_norm_le

/--
Cutoff-dependent one-height positive-axis conversion.

If the indexed tail begins at a visible lower height `lower`, the conversion
from `(1 + y)^k` to the shifted radius uses the exact tail factor
`((lower + 2) / (1 + lower))^k`. This is stronger than the global `(9 / 7)^k`
factor once the finite prefix has been moved past the first trivial-zero
height.
-/
theorem fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height_ge
    (extension : Complex -> Complex)
    (axisConstant : Real)
    (k : Nat)
    {lower y : Real}
    (hlower_nonneg : 0 <= lower)
    (hy_lower : lower <= y)
    (oneAdd_weighted_norm_le :
      norm (extension ((y : Complex) * Complex.I)) *
          (1 + y) ^ (k : Real) <=
        axisConstant) :
    norm (extension ((y : Complex) * Complex.I)) *
        (norm ((y : Complex) * Complex.I) + 2) ^ (k : Real) <=
      ((lower + 2) / (1 + lower)) ^ k * axisConstant := by
  let axisValue : Real := norm (extension ((y : Complex) * Complex.I))
  let shiftedPower : Real := (norm ((y : Complex) * Complex.I) + 2) ^ k
  let oneAddPower : Real := (1 + y) ^ k
  let tailFactor : Real := (lower + 2) / (1 + lower)
  have hy : 0 <= y := le_trans hlower_nonneg hy_lower
  have haxis_norm : norm ((y : Complex) * Complex.I) = y := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hy]
  have hden_pos : 0 < 1 + lower := by linarith
  have htailFactor_nonneg : 0 <= tailFactor := by
    dsimp [tailFactor]
    exact div_nonneg (by linarith) (le_of_lt hden_pos)
  have hshift_nonneg : 0 <= norm ((y : Complex) * Complex.I) + 2 := by
    have hnorm_nonneg : 0 <= norm ((y : Complex) * Complex.I) := norm_nonneg _
    linarith
  have hshift_base :
      norm ((y : Complex) * Complex.I) + 2 <= tailFactor * (1 + y) := by
    rw [haxis_norm]
    have hmul :
        (y + 2) * (1 + lower) <= (lower + 2) * (1 + y) := by
      nlinarith
    calc
      y + 2 = ((y + 2) * (1 + lower)) / (1 + lower) := by
        field_simp [hden_pos.ne']
      _ <= ((lower + 2) * (1 + y)) / (1 + lower) :=
        div_le_div_of_nonneg_right hmul (le_of_lt hden_pos)
      _ = tailFactor * (1 + y) := by
        dsimp [tailFactor]
        field_simp [hden_pos.ne']
  have hshift_pow :
      shiftedPower <= (tailFactor * (1 + y)) ^ k := by
    dsimp [shiftedPower]
    exact pow_le_pow_left₀ hshift_nonneg hshift_base k
  have hshift_pow' :
      shiftedPower <= tailFactor ^ k * oneAddPower := by
    dsimp [oneAddPower]
    simpa [mul_pow] using hshift_pow
  have hweighted :
      axisValue * oneAddPower <= axisConstant := by
    dsimp [axisValue, oneAddPower]
    simpa [Real.rpow_natCast] using oneAdd_weighted_norm_le
  have hfirst :
      axisValue * shiftedPower <=
        axisValue * (tailFactor ^ k * oneAddPower) := by
    exact mul_le_mul_of_nonneg_left hshift_pow' (by positivity)
  have hscaled :
      tailFactor ^ k * (axisValue * oneAddPower) <=
        tailFactor ^ k * axisConstant := by
    exact mul_le_mul_of_nonneg_left hweighted
      (pow_nonneg htailFactor_nonneg k)
  calc
    norm (extension ((y : Complex) * Complex.I)) *
        (norm ((y : Complex) * Complex.I) + 2) ^ (k : Real)
        = axisValue * shiftedPower := by
          dsimp [axisValue, shiftedPower]
          simp [Real.rpow_natCast]
    _ <= axisValue * (tailFactor ^ k * oneAddPower) := hfirst
    _ = tailFactor ^ k * (axisValue * oneAddPower) := by
      ring
    _ <= tailFactor ^ k * axisConstant := hscaled

/--
Cutoff-dependent one-add conversion at indexed trivial-zero heights.

For a tail `cutoff <= n`, the exact conversion factor is determined by the
first height left in the tail.
-/
theorem fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight_ge_cutoff
    (extension : Complex -> Complex)
    (axisConstant : Real)
    (k cutoff n : Nat)
    (hn : cutoff <= n)
    (oneAdd_weighted_norm_le :
      norm
          (extension
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I)) *
          (1 + riemannWeilTrivialZeroArgumentHeight n) ^ (k : Real) <=
        axisConstant) :
    norm
        (extension
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real) <=
      ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
        axisConstant := by
  exact
    fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height_ge
      extension axisConstant k
      (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos cutoff))
      (riemannWeilTrivialZeroArgumentHeight_mono hn)
      oneAdd_weighted_norm_le

/-- The cutoff-dependent indexed-tail factor is `1 + 1 / (1 + height)`. -/
theorem riemannWeilTrivialZeroArgumentHeight_tailFactor_eq_one_add_inv
    (cutoff : Nat) :
    (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
        (1 + riemannWeilTrivialZeroArgumentHeight cutoff) =
      1 + 1 / (1 + riemannWeilTrivialZeroArgumentHeight cutoff) := by
  have hden_pos : 0 < 1 + riemannWeilTrivialZeroArgumentHeight cutoff := by
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    linarith
  field_simp [hden_pos.ne']
  ring

/-- The cutoff-dependent indexed-tail factor has the closed form `1 + 2 / (4N + 7)`. -/
theorem riemannWeilTrivialZeroArgumentHeight_tailFactor_eq_one_add_two_div
    (cutoff : Nat) :
    (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
        (1 + riemannWeilTrivialZeroArgumentHeight cutoff) =
      1 + 2 / ((4 : Real) * cutoff + 7) := by
  rw [riemannWeilTrivialZeroArgumentHeight_tailFactor_eq_one_add_inv]
  have hden : (4 : Real) * cutoff + 7 ≠ 0 := by
    have hcutoff_nonneg : (0 : Real) <= cutoff := by
      exact_mod_cast Nat.zero_le cutoff
    nlinarith
  have hheight :
      1 + riemannWeilTrivialZeroArgumentHeight cutoff =
        ((4 : Real) * cutoff + 7) / 2 := by
    dsimp [riemannWeilTrivialZeroArgumentHeight]
    ring
  rw [hheight]
  field_simp [hden]

/-- The cutoff-dependent indexed-tail factor is always at least `1`. -/
theorem one_le_riemannWeilTrivialZeroArgumentHeight_tailFactor
    (cutoff : Nat) :
    1 <=
      (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
        (1 + riemannWeilTrivialZeroArgumentHeight cutoff) := by
  rw [riemannWeilTrivialZeroArgumentHeight_tailFactor_eq_one_add_two_div]
  have hden_pos : 0 < (4 : Real) * cutoff + 7 := by
    have hcutoff_nonneg : (0 : Real) <= cutoff := by
      exact_mod_cast Nat.zero_le cutoff
    nlinarith
  have hfrac_nonneg : 0 <= 2 / ((4 : Real) * cutoff + 7) := by
    positivity
  linarith

/-- Increasing the finite prefix cutoff can only improve the indexed-tail factor. -/
theorem riemannWeilTrivialZeroArgumentHeight_tailFactor_antitone
    {cutoff cutoff' : Nat} (hcutoff : cutoff <= cutoff') :
    (riemannWeilTrivialZeroArgumentHeight cutoff' + 2) /
        (1 + riemannWeilTrivialZeroArgumentHeight cutoff') <=
      (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
        (1 + riemannWeilTrivialZeroArgumentHeight cutoff) := by
  rw [riemannWeilTrivialZeroArgumentHeight_tailFactor_eq_one_add_two_div cutoff']
  rw [riemannWeilTrivialZeroArgumentHeight_tailFactor_eq_one_add_two_div cutoff]
  have hcutoff_real : (cutoff : Real) <= cutoff' := by
    exact_mod_cast hcutoff
  have hden_pos :
      0 < (4 : Real) * cutoff + 7 := by
    have hcutoff_nonneg : (0 : Real) <= cutoff := by
      exact_mod_cast Nat.zero_le cutoff
    nlinarith
  have hden_le :
      (4 : Real) * cutoff + 7 <= (4 : Real) * cutoff' + 7 := by
    nlinarith
  have hinv_le :
      1 / ((4 : Real) * cutoff' + 7) <=
        1 / ((4 : Real) * cutoff + 7) :=
    one_div_le_one_div_of_le hden_pos hden_le
  have hscaled :
      2 / ((4 : Real) * cutoff' + 7) <=
        2 / ((4 : Real) * cutoff + 7) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv_le (by norm_num : (0 : Real) <= 2)
  linarith

/--
The cutoff-dependent indexed-tail factor is eventually at most `1 + ε`.

This records the quantitative payoff from moving a longer finite prefix out of
the indexed trivial-zero tail: the one-add-to-shifted-radius loss tends to `1`.
-/
theorem eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le_one_add
    {ε : Real} (hε : 0 < ε) :
    exists cutoff₀ : Nat, forall cutoff : Nat, cutoff₀ <= cutoff ->
      (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff) <=
        1 + ε := by
  obtain ⟨cutoff₀, hcutoff₀⟩ := exists_nat_gt (1 / ε)
  refine ⟨cutoff₀, ?_⟩
  intro cutoff hcutoff
  have hcutoff₀_le_cutoff : (cutoff₀ : Real) <= cutoff := by
    exact_mod_cast hcutoff
  have hcutoff_le_den :
      (cutoff : Real) <=
        1 + riemannWeilTrivialZeroArgumentHeight cutoff := by
    dsimp [riemannWeilTrivialZeroArgumentHeight]
    have hcutoff_nonneg : 0 <= (cutoff : Real) := by
      exact_mod_cast Nat.zero_le cutoff
    linarith
  have hden_pos : 0 < 1 + riemannWeilTrivialZeroArgumentHeight cutoff := by
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    linarith
  have hden_gt : 1 / ε < 1 + riemannWeilTrivialZeroArgumentHeight cutoff := by
    linarith
  have hinv_lt : 1 / (1 + riemannWeilTrivialZeroArgumentHeight cutoff) < ε := by
    rw [div_lt_iff₀ hden_pos]
    have hmul := (div_lt_iff₀ hε).1 hden_gt
    nlinarith
  rw [riemannWeilTrivialZeroArgumentHeight_tailFactor_eq_one_add_inv]
  linarith

/-- The cutoff-dependent indexed-tail factor is eventually below any `loss > 1`. -/
theorem eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le
    {loss : Real} (hloss : 1 < loss) :
    exists cutoff₀ : Nat, forall cutoff : Nat, cutoff₀ <= cutoff ->
      (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff) <=
        loss := by
  have hε : 0 < loss - 1 := by linarith
  rcases eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le_one_add
      hε with ⟨cutoff₀, hcutoff₀⟩
  refine ⟨cutoff₀, ?_⟩
  intro cutoff hcutoff
  have hle := hcutoff₀ cutoff hcutoff
  linarith

/--
Current Mathlib/project zero-free input already puts every zeta zero strictly
to the left of `re = 1`, hence every Riemann-Weil zero argument lies strictly
above the lower boundary of the horizontal strip `im = -1/2`.
-/
theorem riemannWeilZeroArgument_im_gt_neg_half
    (rho : ZetaZeroSubtype) :
    -(1 / 2 : Real) <
      (riemannWeilZeroArgument (rho : Complex)).im := by
  rw [riemannWeilZeroArgument_im]
  have hz : IsZetaZero (rho : Complex) := by
    exact rho.property
  have hre_lt_one : (rho : Complex).re < 1 := hz.re_lt_one
  linarith

/-- A nontrivial zeta zero cannot lie in the open left half-plane. -/
theorem zetaZeroSubtype_re_nonneg_of_not_trivial
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    0 <= (rho : Complex).re := by
  by_contra hnot
  have hre_neg : (rho : Complex).re < 0 := lt_of_not_ge hnot
  exact hnotTrivial
    (ComplexCompactExhaustion.isTrivialZetaZero_of_isZetaZero_of_re_neg
      (s := (rho : Complex)) (by exact rho.property) hre_neg)

/--
If a zeta zero is nontrivial, its Riemann-Weil zero argument lies in the closed
horizontal strip `-1/2 <= im z <= 1/2`.
-/
theorem riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg
    (rho : ZetaZeroSubtype)
    (hre_nonneg : 0 <= (rho : Complex).re) :
    -(1 / 2 : Real) <=
        (riemannWeilZeroArgument (rho : Complex)).im /\
      (riemannWeilZeroArgument (rho : Complex)).im <= (1 / 2 : Real) := by
  rw [riemannWeilZeroArgument_im]
  have hz : IsZetaZero (rho : Complex) := by
    exact rho.property
  have hre_lt_one : (rho : Complex).re < 1 := hz.re_lt_one
  constructor <;> linarith

/--
The standard positive-imaginary-axis `(1 + y)^k` estimate gives the weighted
zero-locus estimate for project-known trivial zeroes.
-/
theorem trivialZeroArgument_weighted_norm_le_of_oneAddImaginaryAxis_rpow_natCast
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (imaginaryAxis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (1 + y) ^ (k : Real) <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (htrivial : IsTrivialZetaZero (rho : Complex)) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * axisConstant f := by
  rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
  have haxis :=
    imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_rpow_natCast
      (system := system) axisConstant k
      imaginaryAxis_oneAdd_weighted_norm_le f
      (riemannWeilTrivialZeroArgumentHeight n)
      (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
  have hheight_abs :
      |riemannWeilTrivialZeroArgumentHeight n| =
        riemannWeilTrivialZeroArgumentHeight n := by
    exact abs_of_nonneg
      (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
  simpa [harg, norm_trivialZeroArgumentHeight_mul_I n, hheight_abs]
    using haxis

/-- The weighted contribution of the `n`th project-known trivial-zero argument. -/
noncomputable def riemannWeilIndexedTrivialAxisWeightedTerm
    {system : SchwartzRiemannWeilExtensionSystem}
    (k : Nat) (f : SchwartzLineTestFunction) (n : Nat) : Real :=
  norm
      (system.extension f
        ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)) *
    (norm
        ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I) + 2) ^
      (k : Real)

theorem riemannWeilIndexedTrivialAxisWeightedTerm_nonneg
    {system : SchwartzRiemannWeilExtensionSystem}
    (k : Nat) (f : SchwartzLineTestFunction) (n : Nat) :
    0 <= riemannWeilIndexedTrivialAxisWeightedTerm (system := system) k f n := by
  dsimp [riemannWeilIndexedTrivialAxisWeightedTerm]
  exact mul_nonneg (norm_nonneg _)
    (le_of_lt
      (Real.rpow_pos_of_pos
        (by
          have hnorm_nonneg :
              0 <=
                norm
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) := norm_nonneg _
          linarith)
        (k : Real)))

/--
Automatic finite-prefix constant for the project-known trivial-zero sequence.

It is deliberately non-sharp: summing the first `cutoff` nonnegative weighted
terms is enough to bound each prefix term individually.
-/
noncomputable def riemannWeilIndexedTrivialAxisPrefixSumConstant
    {system : SchwartzRiemannWeilExtensionSystem}
    (cutoff k : Nat) (f : SchwartzLineTestFunction) : Real :=
  (Finset.range cutoff).sum
    (riemannWeilIndexedTrivialAxisWeightedTerm (system := system) k f)

theorem riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
    {system : SchwartzRiemannWeilExtensionSystem}
    (cutoff k : Nat) (f : SchwartzLineTestFunction) :
    0 <=
      riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k f := by
  dsimp [riemannWeilIndexedTrivialAxisPrefixSumConstant]
  exact Finset.sum_nonneg fun n _ =>
    riemannWeilIndexedTrivialAxisWeightedTerm_nonneg (system := system) k f n

/--
The automatic finite-prefix trivial-axis bound is monotone in the cutoff.

This lets later analytic arguments enlarge a cutoff to align several eventual
tail hypotheses without shrinking the already certified prefix majorant.
-/
theorem riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
    {system : SchwartzRiemannWeilExtensionSystem}
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (f : SchwartzLineTestFunction) :
    riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k f <=
      riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff' k f := by
  dsimp [riemannWeilIndexedTrivialAxisPrefixSumConstant]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?hsubset ?hnonneg
  · intro n hn
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hn).trans_le hcutoff)
  · intro n _hn' _hn
    exact riemannWeilIndexedTrivialAxisWeightedTerm_nonneg
      (system := system) k f n

/-- Continuity of one indexed trivial-axis weighted prefix term. -/
theorem riemannWeilIndexedTrivialAxisWeightedTerm_continuous
    {system : SchwartzRiemannWeilExtensionSystem}
    (k n : Nat)
    (extension_continuous :
      Continuous fun f : SchwartzLineTestFunction =>
        system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
            Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      riemannWeilIndexedTrivialAxisWeightedTerm (system := system) k f n := by
  dsimp [riemannWeilIndexedTrivialAxisWeightedTerm]
  exact extension_continuous.norm.mul continuous_const

/--
Continuity of the automatic finite-prefix trivial-axis constant.

This is the missing closedness ingredient for dense-source indexed-tail
majorant routes: if the extension is continuous at the finitely many
trivial-axis prefix heights, the automatically generated prefix bound is a
continuous function of the Schwartz test.
-/
theorem riemannWeilIndexedTrivialAxisPrefixSumConstant_continuous
    {system : SchwartzRiemannWeilExtensionSystem}
    (cutoff k : Nat)
    (extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k f := by
  dsimp [riemannWeilIndexedTrivialAxisPrefixSumConstant]
  exact
    continuous_finsetSum
      (s := Finset.range cutoff)
      (f := fun n f =>
        riemannWeilIndexedTrivialAxisWeightedTerm (system := system) k f n)
      (fun n hn =>
        riemannWeilIndexedTrivialAxisWeightedTerm_continuous
          (system := system) k n
          (extension_continuous n (Finset.mem_range.mp hn)))

theorem riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
    {system : SchwartzRiemannWeilExtensionSystem}
    (cutoff k : Nat) (f : SchwartzLineTestFunction) (n : Nat)
    (hn : n < cutoff) :
    norm
        (system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real) <=
      riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k f := by
  dsimp [riemannWeilIndexedTrivialAxisPrefixSumConstant,
    riemannWeilIndexedTrivialAxisWeightedTerm]
  refine
    Finset.single_le_sum
      (s := Finset.range cutoff)
      (a := n)
      (f := fun m : Nat =>
        norm
            (system.extension f
              ((riemannWeilTrivialZeroArgumentHeight m : Complex) *
                Complex.I)) *
          (norm
              ((riemannWeilTrivialZeroArgumentHeight m : Complex) *
                Complex.I) + 2) ^ (k : Real))
      ?nonneg (Finset.mem_range.mpr hn)
  intro m _hm
  exact mul_nonneg (norm_nonneg _)
    (le_of_lt
      (Real.rpow_pos_of_pos
        (by
          have hnorm_nonneg :
              0 <=
                norm
                  ((riemannWeilTrivialZeroArgumentHeight m : Complex) *
                    Complex.I) := norm_nonneg _
          linarith)
        (k : Real)))

/--
Indexed finite-prefix/tail control of the project-known trivial-zero
arguments.

This is closer to a source proof than the all-height imaginary-axis estimate:
one may check the finitely many heights `n < cutoff` separately and prove a
uniform tail estimate for `cutoff <= n`.
-/
theorem trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisPrefixTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (prefixAxisConstant tailAxisConstant : SchwartzLineTestFunction -> Real)
    (prefixAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixAxisConstant f)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (prefix_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          n < cutoff ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              prefixAxisConstant f)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (htrivial : IsTrivialZetaZero (rho : Complex)) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      prefixAxisConstant f + tailAxisConstant f := by
  rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
  by_cases hn : n < cutoff
  · have hprefix :
        norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          prefixAxisConstant f := by
      simpa [harg] using prefix_trivialAxis_weighted_norm_le f n hn
    exact hprefix.trans (by
      have htail_nonneg := tailAxisConstant_nonneg f
      linarith)
  · have hge : cutoff <= n := Nat.le_of_not_gt hn
    have htail :
        norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          tailAxisConstant f := by
      simpa [harg] using tail_trivialAxis_weighted_norm_le f n hge
    exact htail.trans (by
      have hprefix_nonneg := prefixAxisConstant_nonneg f
      linarith)

/--
Tail-only variant of the indexed trivial-axis theorem.

The finite prefix is bounded automatically by the explicit sum of the first
`cutoff` weighted trivial-zero terms; the only external analytic input is the
uniform tail estimate for `cutoff <= n`.
-/
theorem trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (tailAxisConstant : SchwartzLineTestFunction -> Real)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (htrivial : IsTrivialZetaZero (rho : Complex)) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        tailAxisConstant f := by
  exact
    trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisPrefixTail
      (system := system)
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k)
      tailAxisConstant
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k)
      tailAxisConstant_nonneg cutoff k
      (riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
        (system := system) cutoff k)
      tail_trivialAxis_weighted_norm_le f rho htrivial

/--
Indexed trivial-axis tail estimate from a standard `(1 + y)^k` bound at the
actual trivial-zero heights.

This is weaker than uniform control on the whole positive imaginary axis and
stronger than an opaque tail hypothesis: each height in the tail is converted
to the shifted-radius p-series normalization by the checked one-height
geometry, with the explicit `2^k` loss.
-/
theorem riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_oneAddImaginaryAxis
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
    (tail_axis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                  (k : Real) <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hn : cutoff <= n) :
    norm
        (system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
            Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * axisConstant f := by
  exact
    fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height
      (fun z : Complex => system.extension f z) (axisConstant f) k
      (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
      (tail_axis_oneAdd_weighted_norm_le f n hn)

/--
Sharper indexed trivial-axis tail estimate from a standard `(1 + y)^k` bound.

Because project-known trivial-zero heights start at `5 / 2`, the conversion
from `(1 + y)^k` to the shifted-radius weight pays `(9 / 7)^k`, not the
all-height factor `2^k`.
-/
theorem riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_oneAddImaginaryAxis_sharp
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
    (tail_axis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                  (k : Real) <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hn : cutoff <= n) :
    norm
        (system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
            Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real) <=
      ((9 : Real) / 7) ^ k * axisConstant f := by
  exact
    fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight
      (fun z : Complex => system.extension f z) (axisConstant f) k n
      (tail_axis_oneAdd_weighted_norm_le f n hn)

/--
Cutoff-dependent sharp indexed trivial-axis tail estimate.

The conversion factor is computed from the first indexed trivial-zero height
remaining after the finite prefix cutoff.
-/
theorem riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_oneAddImaginaryAxis_cutoffSharp
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
    (tail_axis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                  (k : Real) <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hn : cutoff <= n) :
    norm
        (system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
            Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real) <=
      ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
        axisConstant f := by
  exact
    fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight_ge_cutoff
      (fun z : Complex => system.extension f z) (axisConstant f) k cutoff n
      hn (tail_axis_oneAdd_weighted_norm_le f n hn)

/--
Eventually-indexed one-add tail control gives shifted-radius tail control with
any prescribed multiplicative loss greater than `1`.

This is the proof-facing version of the cutoff-sharp geometry: choose the
finite prefix long enough, then the remaining indexed trivial-zero tail pays
only `loss^k` in converting `(1 + y)^k` control to shifted-radius control.
-/
theorem exists_cutoff_riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_eventually_oneAddImaginaryAxis_loss
    {system : SchwartzRiemannWeilExtensionSystem}
    (axisConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    {loss : Real}
    (hloss : 1 < loss)
    (tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall f : SchwartzLineTestFunction,
            forall n : Nat,
              cutoff <= n ->
                norm
                    (system.extension f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisConstant f)
        (Filter.atTop : Filter Nat)) :
    exists cutoff : Nat,
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              loss ^ k * axisConstant f := by
  rcases eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le
      hloss with ⟨factorCutoff, hfactorCutoff⟩
  rw [Filter.eventually_atTop] at tail_axis_oneAdd_weighted_norm_le_eventually
  rcases tail_axis_oneAdd_weighted_norm_le_eventually with
    ⟨sourceCutoff, hsourceCutoff⟩
  let cutoff : Nat := max factorCutoff sourceCutoff
  have hfactor_le :
      (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff) <= loss := by
    exact hfactorCutoff cutoff (Nat.le_max_left factorCutoff sourceCutoff)
  have hfactor_nonneg :
      0 <=
        (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff) := by
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    exact div_nonneg (by linarith) (by linarith)
  have hfactor_pow_le :
      ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k <=
        loss ^ k := by
    exact pow_le_pow_left₀ hfactor_nonneg hfactor_le k
  have htail_oneAdd :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                  (k : Real) <=
              axisConstant f := by
    exact hsourceCutoff cutoff (Nat.le_max_right factorCutoff sourceCutoff)
  refine ⟨cutoff, ?_⟩
  intro f n hn
  have hcutoffSharp :=
    riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_oneAddImaginaryAxis_cutoffSharp
      (system := system) axisConstant cutoff k htail_oneAdd f n hn
  have haxis_nonneg : 0 <= axisConstant f := by
    have hone_pos : 0 < 1 + riemannWeilTrivialZeroArgumentHeight n := by
      have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos n
      linarith
    have hlhs_nonneg :
        0 <=
          norm
              (system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) *
            (1 + riemannWeilTrivialZeroArgumentHeight n) ^ (k : Real) := by
      exact mul_nonneg (norm_nonneg _)
        (le_of_lt (Real.rpow_pos_of_pos hone_pos (k : Real)))
    exact le_trans hlhs_nonneg (htail_oneAdd f n hn)
  exact hcutoffSharp.trans
    (mul_le_mul_of_nonneg_right hfactor_pow_le haxis_nonneg)

/--
Indexed trivial-axis tail estimate from domination by the real-axis Schwartz
value at the same height.

This turns the remaining trivial-axis tail obligation into a sharper source
theorem: prove that, on the explicit trivial-zero tail, the extension is
bounded by a nonnegative multiple of `‖f height‖`. Ordinary Schwartz decay on
the real axis then supplies the weighted tail bound.
-/
theorem riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_realHeightComparison
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (cutoff k : Nat)
    (trivialAxis_norm_le_realHeight :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) <=
              comparisonConstant f *
                ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hn : cutoff <= n) :
    norm
        (system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
            Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real) <=
      comparisonConstant f * schwartzLineRealAxisShiftedSeminormConstant k f := by
  let height : Real := riemannWeilTrivialZeroArgumentHeight n
  let radiusPower : Real :=
    (norm ((height : Complex) * Complex.I) + 2) ^ (k : Real)
  have hradiusPower_nonneg : 0 <= radiusPower := by
    dsimp [radiusPower]
    exact le_of_lt
      (Real.rpow_pos_of_pos
        (by
          have hnorm_nonneg : 0 <= norm ((height : Complex) * Complex.I) :=
            norm_nonneg _
          linarith)
        (k : Real))
  have hnorm :
      norm
          (system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I)) <=
        comparisonConstant f *
          ‖f (riemannWeilTrivialZeroArgumentHeight n)‖ :=
    trivialAxis_norm_le_realHeight f n hn
  have hweighted :
      norm
          (system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I)) *
          radiusPower <=
        (comparisonConstant f *
          ‖f (riemannWeilTrivialZeroArgumentHeight n)‖) *
          radiusPower :=
    mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
  have hheight_nonneg : 0 <= height := by
    dsimp [height]
    exact le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n)
  have hreal_norm : norm ((height : Complex)) = height := by
    rw [Complex.norm_real, Real.norm_of_nonneg hheight_nonneg]
  have haxis_norm : norm ((height : Complex) * Complex.I) = norm ((height : Complex)) := by
    rw [norm_mul, Complex.norm_I, mul_one]
  have hschwartz :
      ‖f (riemannWeilTrivialZeroArgumentHeight n)‖ *
          radiusPower <=
        schwartzLineRealAxisShiftedSeminormConstant k f := by
    simpa [height, radiusPower, haxis_norm, hreal_norm] using
      schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast
        k f height
  have hscaled :
      comparisonConstant f *
          (‖f (riemannWeilTrivialZeroArgumentHeight n)‖ *
            radiusPower) <=
        comparisonConstant f * schwartzLineRealAxisShiftedSeminormConstant k f :=
    mul_le_mul_of_nonneg_left hschwartz (comparisonConstant_nonneg f)
  calc
    norm
        (system.extension f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
            Complex.I)) *
        (norm
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I) + 2) ^ (k : Real)
        = norm
            (system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) * radiusPower := by
          rfl
    _ <= (comparisonConstant f *
          ‖f (riemannWeilTrivialZeroArgumentHeight n)‖) *
          radiusPower := hweighted
    _ = comparisonConstant f *
          (‖f (riemannWeilTrivialZeroArgumentHeight n)‖ *
            radiusPower) := by
      ring
    _ <= comparisonConstant f *
        schwartzLineRealAxisShiftedSeminormConstant k f := hscaled

end RiemannHypothesisProject
