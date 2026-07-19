import RiemannHypothesisProject.RiemannWeilShiftedRadius.RealSchwartzSeminorms
import RiemannHypothesisProject.SchwartzRiemannWeilWeight

/-!
# Horizontal-strip shifted-radius geometry

This module contains the elementary closed-strip radius comparisons and the
first real-part comparison estimates used by the shifted-radius p-series route.
-/

namespace RiemannHypothesisProject

/--
On a bounded horizontal strip, the shifted complex radius is controlled by the
shifted radius of the real part.  This is the elementary geometry needed to
turn a vertical real-part domination estimate into a full strip decay estimate.
-/
theorem complex_norm_add_two_le_two_realPart_norm_add_two_of_abs_im_le_one
    {z : Complex} (him : |z.im| <= 1) :
    norm z + 2 <= 2 * (norm ((z.re : Complex)) + 2) := by
  have hnorm_le : norm z <= norm ((z.re : Complex)) + |z.im| := by
    calc
      norm z = norm ((z.re : Complex) + (z.im : Complex) * Complex.I) := by
        rw [Complex.re_add_im]
      _ <= norm ((z.re : Complex)) +
          norm ((z.im : Complex) * Complex.I) := norm_add_le _ _
      _ = norm ((z.re : Complex)) + |z.im| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  have hreal_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
  calc
    norm z + 2 <= norm ((z.re : Complex)) + |z.im| + 2 := by
      linarith
    _ <= norm ((z.re : Complex)) + 1 + 2 := by
      linarith
    _ <= 2 * (norm ((z.re : Complex)) + 2) := by
      linarith

/--
On the actual critical closed strip, the shifted complex radius is controlled
more sharply by the shifted real-part radius.
-/
theorem complex_norm_add_two_le_five_fourths_realPart_norm_add_two_of_abs_im_le_half
    {z : Complex} (him : |z.im| <= (1 / 2 : Real)) :
    norm z + 2 <= ((5 : Real) / 4) * (norm ((z.re : Complex)) + 2) := by
  have hnorm_le : norm z <= norm ((z.re : Complex)) + |z.im| := by
    calc
      norm z = norm ((z.re : Complex) + (z.im : Complex) * Complex.I) := by
        rw [Complex.re_add_im]
      _ <= norm ((z.re : Complex)) +
          norm ((z.im : Complex) * Complex.I) := norm_add_le _ _
      _ = norm ((z.re : Complex)) + |z.im| := by
        simp [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  let realRadius : Real := norm ((z.re : Complex)) + 2
  have hrealRadius_ge_two : (2 : Real) <= realRadius := by
    dsimp [realRadius]
    have hreal_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
    linarith
  calc
    norm z + 2 <= norm ((z.re : Complex)) + |z.im| + 2 := by
      linarith
    _ <= realRadius + (1 / 2 : Real) := by
      dsimp [realRadius]
      linarith
    _ <= ((5 : Real) / 4) * realRadius := by
      nlinarith

/-- The closed strip `-1/2 <= im z <= 1/2` satisfies the radius comparison. -/
theorem complex_norm_add_two_le_two_realPart_norm_add_two_of_mem_closedHorizontalStrip
    {z : Complex}
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm z + 2 <= 2 * (norm ((z.re : Complex)) + 2) := by
  have him_half : |z.im| <= (1 / 2 : Real) := abs_le.mpr ⟨hlow, hhigh⟩
  have him_one : |z.im| <= (1 : Real) := by linarith
  exact complex_norm_add_two_le_two_realPart_norm_add_two_of_abs_im_le_one
    him_one

/-- The closed strip `-1/2 <= im z <= 1/2` satisfies the sharp radius comparison. -/
theorem complex_norm_add_two_le_five_fourths_realPart_norm_add_two_of_mem_closedHorizontalStrip
    {z : Complex}
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm z + 2 <= ((5 : Real) / 4) * (norm ((z.re : Complex)) + 2) := by
  have him_half : |z.im| <= (1 / 2 : Real) := abs_le.mpr ⟨hlow, hhigh⟩
  exact
    complex_norm_add_two_le_five_fourths_realPart_norm_add_two_of_abs_im_le_half
      him_half

/--
If an extension is dominated on the critical horizontal strip by the real-axis
Schwartz value at the same real part, then ordinary real-axis Schwartz decay
gives the desired horizontal-strip weighted estimate.

This reduces the off-real p-series blocker to a sharper analytic theorem:
prove the vertical real-part domination estimate for the chosen source
extension and normalization.
-/
theorem horizontalStrip_weighted_norm_le_of_realPartComparison_nat
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (k : Nat)
    (f : SchwartzLineTestFunction)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (system.extension f z) * (norm z + 2) ^ k <=
      comparisonConstant f *
        ((2 : Real) ^ k * schwartzLineRealAxisShiftedSeminormConstant k f) := by
  let realRadius : Real := norm ((z.re : Complex)) + 2
  have hstrip_radius :
      norm z + 2 <= (2 : Real) * realRadius := by
    simpa [realRadius] using
      complex_norm_add_two_le_two_realPart_norm_add_two_of_mem_closedHorizontalStrip
        hlow hhigh
  have hbase_nonneg : 0 <= norm z + 2 := by
    have hnorm_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hrealRadius_nonneg : 0 <= realRadius := by
    dsimp [realRadius]
    have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
    linarith
  have hpow :
      (norm z + 2) ^ k <= (2 : Real) ^ k * realRadius ^ k := by
    have hpow_raw :
        (norm z + 2) ^ k <= ((2 : Real) * realRadius) ^ k :=
      pow_le_pow_left₀ hbase_nonneg hstrip_radius k
    simpa [mul_pow] using hpow_raw
  have hcomparison :=
    strip_extension_norm_le_realAxis f z hlow hhigh
  have hcomparison_rhs_nonneg :
      0 <= comparisonConstant f * ‖f z.re‖ := by
    exact mul_nonneg (comparisonConstant_nonneg f) (norm_nonneg (f z.re))
  have hfirst :
      norm (system.extension f z) * (norm z + 2) ^ k <=
        (comparisonConstant f * ‖f z.re‖) *
          ((2 : Real) ^ k * realRadius ^ k) := by
    exact mul_le_mul hcomparison hpow
      (pow_nonneg hbase_nonneg k) hcomparison_rhs_nonneg
  have hreal :=
    schwartzLine_realAxis_complexShifted_weighted_norm_le_nat k f z.re
  have hscaled :
      (2 : Real) ^ k * (‖f z.re‖ * realRadius ^ k) <=
        (2 : Real) ^ k * schwartzLineRealAxisShiftedSeminormConstant k f := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [realRadius] using hreal)
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  calc
    norm (system.extension f z) * (norm z + 2) ^ k
        <= (comparisonConstant f * ‖f z.re‖) *
          ((2 : Real) ^ k * realRadius ^ k) := hfirst
    _ = comparisonConstant f *
          ((2 : Real) ^ k * (‖f z.re‖ * realRadius ^ k)) := by
      ring
    _ <= comparisonConstant f *
          ((2 : Real) ^ k *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
      exact mul_le_mul_of_nonneg_left hscaled (comparisonConstant_nonneg f)

/--
Real-exponent version of
`horizontalStrip_weighted_norm_le_of_realPartComparison_nat`, matching the
certificate exponent convention.
-/
theorem horizontalStrip_weighted_norm_le_of_realPartComparison_rpow_natCast
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (k : Nat)
    (f : SchwartzLineTestFunction)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
      comparisonConstant f *
        ((2 : Real) ^ k * schwartzLineRealAxisShiftedSeminormConstant k f) := by
  rw [Real.rpow_natCast]
  exact horizontalStrip_weighted_norm_le_of_realPartComparison_nat
    comparisonConstant comparisonConstant_nonneg
    strip_extension_norm_le_realAxis k f z hlow hhigh

/--
Horizontal-strip decay from a real-radius seminorm envelope.

This is the viable replacement for pointwise vertical domination by
`norm (f z.re)`: prove directly that the extension is controlled by a
nonvanishing real-axis radius envelope. The checked strip-radius geometry then
converts that into the shifted complex-radius p-series weight, losing only the
explicit factor `2^k`.
-/
theorem horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ k <=
              stripConstant f)
    (f : SchwartzLineTestFunction)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (system.extension f z) * (norm z + 2) ^ k <=
      (2 : Real) ^ k * stripConstant f := by
  let realRadius : Real := norm ((z.re : Complex)) + 2
  let extensionNorm : Real := norm (system.extension f z)
  have hstrip_radius :
      norm z + 2 <= (2 : Real) * realRadius := by
    simpa [realRadius] using
      complex_norm_add_two_le_two_realPart_norm_add_two_of_mem_closedHorizontalStrip
        hlow hhigh
  have hbase_nonneg : 0 <= norm z + 2 := by
    have hnorm_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hpow :
      (norm z + 2) ^ k <= (2 : Real) ^ k * realRadius ^ k := by
    have hpow_raw :
        (norm z + 2) ^ k <= ((2 : Real) * realRadius) ^ k :=
      pow_le_pow_left₀ hbase_nonneg hstrip_radius k
    simpa [mul_pow] using hpow_raw
  have henvelope :
      extensionNorm * realRadius ^ k <= stripConstant f := by
    simpa [extensionNorm, realRadius] using
      strip_extension_weighted_norm_le_realRadius f z hlow hhigh
  have hfirst :
      extensionNorm * (norm z + 2) ^ k <=
        extensionNorm * ((2 : Real) ^ k * realRadius ^ k) := by
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hscaled :
      (2 : Real) ^ k * (extensionNorm * realRadius ^ k) <=
        (2 : Real) ^ k * stripConstant f := by
    exact mul_le_mul_of_nonneg_left henvelope
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  calc
    norm (system.extension f z) * (norm z + 2) ^ k
        = extensionNorm * (norm z + 2) ^ k := by
          rfl
    _ <= extensionNorm * ((2 : Real) ^ k * realRadius ^ k) := hfirst
    _ = (2 : Real) ^ k * (extensionNorm * realRadius ^ k) := by
      ring
    _ <= (2 : Real) ^ k * stripConstant f := hscaled

/--
Real-exponent version of
`horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat`.
-/
theorem horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (f : SchwartzLineTestFunction)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
      (2 : Real) ^ k * stripConstant f := by
  simpa [Real.rpow_natCast] using
    horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat
      (system := system) stripConstant k
      (by
        intro f z hlow hhigh
        simpa [Real.rpow_natCast] using
          strip_extension_weighted_norm_le_realRadius f z hlow hhigh)
      f z hlow hhigh

/--
Fixed-test horizontal-strip geometry for a real-radius envelope.

This is the source-class version of
`horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast`: it
does not ask for an estimate on every project Schwartz test, only for one
fixed profile `extension`.
-/
theorem fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat
    (extension : Complex -> Complex)
    (stripConstant : Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (extension z) * (norm ((z.re : Complex)) + 2) ^ k <=
              stripConstant)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (extension z) * (norm z + 2) ^ k <=
      (2 : Real) ^ k * stripConstant := by
  let realRadius : Real := norm ((z.re : Complex)) + 2
  let extensionNorm : Real := norm (extension z)
  have hstrip_radius :
      norm z + 2 <= (2 : Real) * realRadius := by
    simpa [realRadius] using
      complex_norm_add_two_le_two_realPart_norm_add_two_of_mem_closedHorizontalStrip
        hlow hhigh
  have hbase_nonneg : 0 <= norm z + 2 := by
    have hnorm_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hpow :
      (norm z + 2) ^ k <= (2 : Real) ^ k * realRadius ^ k := by
    have hpow_raw :
        (norm z + 2) ^ k <= ((2 : Real) * realRadius) ^ k :=
      pow_le_pow_left₀ hbase_nonneg hstrip_radius k
    simpa [mul_pow] using hpow_raw
  have henvelope :
      extensionNorm * realRadius ^ k <= stripConstant := by
    simpa [extensionNorm, realRadius] using
      strip_extension_weighted_norm_le_realRadius z hlow hhigh
  have hfirst :
      extensionNorm * (norm z + 2) ^ k <=
        extensionNorm * ((2 : Real) ^ k * realRadius ^ k) := by
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hscaled :
      (2 : Real) ^ k * (extensionNorm * realRadius ^ k) <=
        (2 : Real) ^ k * stripConstant := by
    exact mul_le_mul_of_nonneg_left henvelope
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  calc
    norm (extension z) * (norm z + 2) ^ k
        = extensionNorm * (norm z + 2) ^ k := by
          rfl
    _ <= extensionNorm * ((2 : Real) ^ k * realRadius ^ k) := hfirst
    _ = (2 : Real) ^ k * (extensionNorm * realRadius ^ k) := by
      ring
    _ <= (2 : Real) ^ k * stripConstant := hscaled

/--
Real-exponent fixed-test version of
`fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat`.
-/
theorem fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
    (extension : Complex -> Complex)
    (stripConstant : Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (extension z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (extension z) * (norm z + 2) ^ (k : Real) <=
      (2 : Real) ^ k * stripConstant := by
  simpa [Real.rpow_natCast] using
    fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat
      extension stripConstant k
      (by
        intro z hlow hhigh
        simpa [Real.rpow_natCast] using
          strip_extension_weighted_norm_le_realRadius z hlow hhigh)
      z hlow hhigh

/--
Sharp horizontal-strip decay from a real-radius seminorm envelope.

On the actual closed strip `|im z| <= 1 / 2`, the shifted complex radius costs
only `(5 / 4)^k` relative to the shifted real-part radius.
-/
theorem horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat_sharp
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ k <=
              stripConstant f)
    (f : SchwartzLineTestFunction)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (system.extension f z) * (norm z + 2) ^ k <=
      ((5 : Real) / 4) ^ k * stripConstant f := by
  let realRadius : Real := norm ((z.re : Complex)) + 2
  let extensionNorm : Real := norm (system.extension f z)
  have hstrip_radius :
      norm z + 2 <= ((5 : Real) / 4) * realRadius := by
    simpa [realRadius] using
      complex_norm_add_two_le_five_fourths_realPart_norm_add_two_of_mem_closedHorizontalStrip
        hlow hhigh
  have hbase_nonneg : 0 <= norm z + 2 := by
    have hnorm_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hpow :
      (norm z + 2) ^ k <= ((5 : Real) / 4) ^ k * realRadius ^ k := by
    have hpow_raw :
        (norm z + 2) ^ k <= (((5 : Real) / 4) * realRadius) ^ k :=
      pow_le_pow_left₀ hbase_nonneg hstrip_radius k
    simpa [mul_pow] using hpow_raw
  have henvelope :
      extensionNorm * realRadius ^ k <= stripConstant f := by
    simpa [extensionNorm, realRadius] using
      strip_extension_weighted_norm_le_realRadius f z hlow hhigh
  have hfirst :
      extensionNorm * (norm z + 2) ^ k <=
        extensionNorm * (((5 : Real) / 4) ^ k * realRadius ^ k) := by
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hscaled :
      ((5 : Real) / 4) ^ k * (extensionNorm * realRadius ^ k) <=
        ((5 : Real) / 4) ^ k * stripConstant f := by
    exact mul_le_mul_of_nonneg_left henvelope
      (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
  calc
    norm (system.extension f z) * (norm z + 2) ^ k
        = extensionNorm * (norm z + 2) ^ k := by
          rfl
    _ <= extensionNorm * (((5 : Real) / 4) ^ k * realRadius ^ k) := hfirst
    _ = ((5 : Real) / 4) ^ k * (extensionNorm * realRadius ^ k) := by
      ring
    _ <= ((5 : Real) / 4) ^ k * stripConstant f := hscaled

/--
Real-exponent version of
`horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat_sharp`.
-/
theorem horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant : SchwartzLineTestFunction -> Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (f : SchwartzLineTestFunction)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k * stripConstant f := by
  simpa [Real.rpow_natCast] using
    horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat_sharp
      (system := system) stripConstant k
      (by
        intro f z hlow hhigh
        simpa [Real.rpow_natCast] using
          strip_extension_weighted_norm_le_realRadius f z hlow hhigh)
      f z hlow hhigh

/--
Sharp fixed-test horizontal-strip geometry for a real-radius envelope.
-/
theorem fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat_sharp
    (extension : Complex -> Complex)
    (stripConstant : Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (extension z) * (norm ((z.re : Complex)) + 2) ^ k <=
              stripConstant)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (extension z) * (norm z + 2) ^ k <=
      ((5 : Real) / 4) ^ k * stripConstant := by
  let realRadius : Real := norm ((z.re : Complex)) + 2
  let extensionNorm : Real := norm (extension z)
  have hstrip_radius :
      norm z + 2 <= ((5 : Real) / 4) * realRadius := by
    simpa [realRadius] using
      complex_norm_add_two_le_five_fourths_realPart_norm_add_two_of_mem_closedHorizontalStrip
        hlow hhigh
  have hbase_nonneg : 0 <= norm z + 2 := by
    have hnorm_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hpow :
      (norm z + 2) ^ k <= ((5 : Real) / 4) ^ k * realRadius ^ k := by
    have hpow_raw :
        (norm z + 2) ^ k <= (((5 : Real) / 4) * realRadius) ^ k :=
      pow_le_pow_left₀ hbase_nonneg hstrip_radius k
    simpa [mul_pow] using hpow_raw
  have henvelope :
      extensionNorm * realRadius ^ k <= stripConstant := by
    simpa [extensionNorm, realRadius] using
      strip_extension_weighted_norm_le_realRadius z hlow hhigh
  have hfirst :
      extensionNorm * (norm z + 2) ^ k <=
        extensionNorm * (((5 : Real) / 4) ^ k * realRadius ^ k) := by
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hscaled :
      ((5 : Real) / 4) ^ k * (extensionNorm * realRadius ^ k) <=
        ((5 : Real) / 4) ^ k * stripConstant := by
    exact mul_le_mul_of_nonneg_left henvelope
      (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
  calc
    norm (extension z) * (norm z + 2) ^ k
        = extensionNorm * (norm z + 2) ^ k := by
          rfl
    _ <= extensionNorm * (((5 : Real) / 4) ^ k * realRadius ^ k) := hfirst
    _ = ((5 : Real) / 4) ^ k * (extensionNorm * realRadius ^ k) := by
      ring
    _ <= ((5 : Real) / 4) ^ k * stripConstant := hscaled

/--
Real-exponent fixed-test version of
`fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat_sharp`.
-/
theorem fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
    (extension : Complex -> Complex)
    (stripConstant : Real)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (extension z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant)
    (z : Complex)
    (hlow : -(1 / 2 : Real) <= z.im)
    (hhigh : z.im <= (1 / 2 : Real)) :
    norm (extension z) * (norm z + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k * stripConstant := by
  simpa [Real.rpow_natCast] using
    fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_nat_sharp
      extension stripConstant k
      (by
        intro z hlow hhigh
        simpa [Real.rpow_natCast] using
          strip_extension_weighted_norm_le_realRadius z hlow hhigh)
      z hlow hhigh

end RiemannHypothesisProject
