import RiemannHypothesisProject.RiemannWeilShiftedRadius.TrivialAxisGeometry

/-!
# Finite-component shifted-radius majorants

This module contains finite-component majorant nonnegativity, monotonicity,
and continuity facts used by the shifted-radius p-series route.
-/

namespace RiemannHypothesisProject

/--
The assembled real-radius indexed-tail majorant is nonnegative.

This is the global closedness-side bound used by source proofs whose strip
component constants and real-height tail constants are controlled by
nonnegative ambient majorants. The automatic finite trivial-axis prefix remains
explicit.
-/
theorem finiteComponentRealIndexedTailMajorant_nonneg
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
    (cutoff k : Nat)
    (f : SchwartzLineTestFunction) :
    0 <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (Finset.univ.sum fun i : Index => comparisonMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hstrip_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => stripMajorant i f := by
    exact Finset.sum_nonneg fun i _ => stripMajorant_nonneg i f
  have hcomparison_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => comparisonMajorant i f := by
    exact Finset.sum_nonneg fun i _ => comparisonMajorant_nonneg i f
  exact add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
      hstrip_sum_nonneg)
    (add_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f)
      (mul_nonneg hcomparison_sum_nonneg
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)))

/--
The assembled indexed one-add tail majorant is nonnegative.

This is the nonnegativity companion to
`finiteComponentOneAddIndexedTailMajorant_mono_cutoff`, used when a source
estimate supplies a direct `(1 + y)^k` tail constant rather than a real-axis
Schwartz seminorm comparison.
-/
theorem finiteComponentOneAddIndexedTailMajorant_nonneg
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
    (cutoff k : Nat)
    (f : SchwartzLineTestFunction) :
    0 <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => stripMajorant i f := by
    exact Finset.sum_nonneg fun i _ => stripMajorant_nonneg i f
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisMajorant i f := by
    exact Finset.sum_nonneg fun i _ => axisMajorant_nonneg i f
  exact add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
      hstrip_sum_nonneg)
    (add_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        haxis_sum_nonneg))

/--
The assembled indexed one-add tail majorant with the sharp indexed-tail
constant is nonnegative.

The strip side still uses the ordinary `2^k` conversion, while the indexed
trivial-zero tail keeps the checked `(9 / 7)^k` constant.
-/
theorem finiteComponentOneAddIndexedTailMajorant_sharp_nonneg
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
    (cutoff k : Nat)
    (f : SchwartzLineTestFunction) :
    0 <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => stripMajorant i f := by
    exact Finset.sum_nonneg fun i _ => stripMajorant_nonneg i f
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisMajorant i f := by
    exact Finset.sum_nonneg fun i _ => axisMajorant_nonneg i f
  exact add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
      hstrip_sum_nonneg)
    (add_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
        haxis_sum_nonneg))

/--
The combined sharp indexed one-add tail majorant is nonnegative.

Both checked geometric improvements are visible: `(5 / 4)^k` on the strip sum
and `(9 / 7)^k` on the indexed tail sum.
-/
theorem finiteComponentOneAddIndexedTailMajorant_sharpStrip_sharpTail_nonneg
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
    (cutoff k : Nat)
    (f : SchwartzLineTestFunction) :
    0 <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => stripMajorant i f := by
    exact Finset.sum_nonneg fun i _ => stripMajorant_nonneg i f
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisMajorant i f := by
    exact Finset.sum_nonneg fun i _ => axisMajorant_nonneg i f
  exact add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
      hstrip_sum_nonneg)
    (add_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
        haxis_sum_nonneg))

/--
The assembled indexed one-add tail majorant with sharp strip constant and an
arbitrary tail-loss factor is nonnegative.
-/
theorem finiteComponentOneAddIndexedTailMajorant_sharpStrip_loss_nonneg
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
    (cutoff k : Nat)
    {loss : Real}
    (hloss_nonneg : 0 <= loss)
    (f : SchwartzLineTestFunction) :
    0 <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          loss ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => stripMajorant i f := by
    exact Finset.sum_nonneg fun i _ => stripMajorant_nonneg i f
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisMajorant i f := by
    exact Finset.sum_nonneg fun i _ => axisMajorant_nonneg i f
  exact add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
      hstrip_sum_nonneg)
    (add_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f)
      (mul_nonneg (pow_nonneg hloss_nonneg k) haxis_sum_nonneg))

/--
The sharp-tail one-add majorant is bounded by the older uniform `2^k`
one-add majorant.
-/
theorem finiteComponentOneAddIndexedTailMajorant_sharp_le
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
    (cutoff k : Nat)
    (f : SchwartzLineTestFunction) :
    (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisMajorant i f := by
    exact Finset.sum_nonneg fun i _ => axisMajorant_nonneg i f
  have haxis_factor_le :
      ((9 : Real) / 7) ^ k <= (2 : Real) ^ k := by
    exact pow_le_pow_left₀
      (by norm_num : (0 : Real) <= (9 / 7))
      (by norm_num : ((9 : Real) / 7) <= 2) k
  have haxis_scaled :
      ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index => axisMajorant i f) <=
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisMajorant i f) :=
    mul_le_mul_of_nonneg_right haxis_factor_le haxis_sum_nonneg
  linarith

/--
The checked sharp strip/tail one-add majorant is bounded by the older uniform
`2^k` one-add majorant.

This records the actual gain from the closed-strip `(5 / 4)^k` and indexed-tail
`(9 / 7)^k` constants when the component majorants are nonnegative.
-/
theorem finiteComponentOneAddIndexedTailMajorant_sharpStrip_sharpTail_le
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
    (cutoff k : Nat)
    (f : SchwartzLineTestFunction) :
    ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => stripMajorant i f := by
    exact Finset.sum_nonneg fun i _ => stripMajorant_nonneg i f
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisMajorant i f := by
    exact Finset.sum_nonneg fun i _ => axisMajorant_nonneg i f
  have hstrip_factor_le :
      ((5 : Real) / 4) ^ k <= (2 : Real) ^ k := by
    exact pow_le_pow_left₀
      (by norm_num : (0 : Real) <= (5 / 4))
      (by norm_num : ((5 : Real) / 4) <= 2) k
  have haxis_factor_le :
      ((9 : Real) / 7) ^ k <= (2 : Real) ^ k := by
    exact pow_le_pow_left₀
      (by norm_num : (0 : Real) <= (9 / 7))
      (by norm_num : ((9 : Real) / 7) <= 2) k
  have hstrip_scaled :
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) <=
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) :=
    mul_le_mul_of_nonneg_right hstrip_factor_le hstrip_sum_nonneg
  have haxis_scaled :
      ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index => axisMajorant i f) <=
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisMajorant i f) :=
    mul_le_mul_of_nonneg_right haxis_factor_le haxis_sum_nonneg
  linarith

/-- The real-radius indexed-tail majorant is monotone in the finite cutoff. -/
theorem finiteComponentRealIndexedTailMajorant_mono_cutoff
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (f : SchwartzLineTestFunction) :
    (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (Finset.univ.sum fun i : Index => comparisonMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          (Finset.univ.sum fun i : Index => comparisonMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff f
  linarith

/-- The indexed one-add tail majorant is monotone in the finite cutoff. -/
theorem finiteComponentOneAddIndexedTailMajorant_mono_cutoff
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (f : SchwartzLineTestFunction) :
    (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff f
  linarith

/--
The sharp-tail indexed one-add tail majorant is monotone in the finite cutoff.
-/
theorem finiteComponentOneAddIndexedTailMajorant_mono_cutoff_sharp
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (f : SchwartzLineTestFunction) :
    (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff f
  linarith

/--
The combined sharp indexed one-add tail majorant is monotone in the finite
cutoff.

The strip and tail component sums keep the checked `(5 / 4)^k` and `(9 / 7)^k`
constants; only the explicit trivial-axis finite prefix changes.
-/
theorem finiteComponentOneAddIndexedTailMajorant_mono_cutoff_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (f : SchwartzLineTestFunction) :
    ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff f
  linarith

/--
The combined sharp-strip arbitrary-loss one-add majorant is monotone in the
finite cutoff.

The strip and tail component sums keep `(5 / 4)^k` and `loss^k`; only the
explicit trivial-axis finite prefix changes.
-/
theorem finiteComponentOneAddIndexedTailMajorant_mono_cutoff_sharpStrip_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    {loss : Real}
    (f : SchwartzLineTestFunction) :
    ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          loss ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          loss ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff f
  linarith

/--
Continuity of the assembled real-radius indexed-tail majorant.

This names the continuity proof needed by dense-source real-radius indexed-tail
routes: continuous component majorants, continuity of the finitely many prefix
extension evaluations, and continuity of the shifted real-axis Schwartz
seminorm together give continuity of the full certificate constant.
-/
theorem finiteComponentRealIndexedTailMajorant_continuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (comparisonMajorant_continuous :
      forall i : Index, Continuous (comparisonMajorant i))
    (cutoff k : Nat)
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (Finset.univ.sum fun i : Index => comparisonMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hstrip_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => stripMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => stripMajorant i f)
        (fun i _hi => stripMajorant_continuous i))
  have hcomparison_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => comparisonMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => comparisonMajorant i f)
        (fun i _hi => comparisonMajorant_continuous i))
  have hprefix_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_continuous
      (system := system) cutoff k prefix_trivialAxis_extension_continuous
  exact (continuous_const.mul hstrip_sum_cont).add
    (hprefix_cont.add
      (hcomparison_sum_cont.mul
        (schwartzLineRealAxisShiftedSeminormConstant_continuous k)))

/--
Continuity of the assembled indexed one-add tail majorant.

This is the closedness-side majorant for source estimates that give direct
component `(1 + y)^k` control at the indexed trivial-zero heights.  The finite
prefix is continuous from the fixed trivial-axis evaluations, and the tail
constant is just a continuous finite sum.
-/
theorem finiteComponentOneAddIndexedTailMajorant_continuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (cutoff k : Nat)
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => stripMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => stripMajorant i f)
        (fun i _hi => stripMajorant_continuous i))
  have haxis_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => axisMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => axisMajorant i f)
        (fun i _hi => axisMajorant_continuous i))
  have hprefix_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_continuous
      (system := system) cutoff k prefix_trivialAxis_extension_continuous
  exact (continuous_const.mul hstrip_sum_cont).add
    (hprefix_cont.add (continuous_const.mul haxis_sum_cont))

/--
Continuity of the assembled sharp-tail indexed one-add majorant.

This is the continuous global-majorant fact for routes that keep the ordinary
strip constant but use the sharper indexed trivial-zero tail constant.
-/
theorem finiteComponentOneAddIndexedTailMajorant_continuous_sharp
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (cutoff k : Nat)
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => stripMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => stripMajorant i f)
        (fun i _hi => stripMajorant_continuous i))
  have haxis_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => axisMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => axisMajorant i f)
        (fun i _hi => axisMajorant_continuous i))
  have hprefix_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_continuous
      (system := system) cutoff k prefix_trivialAxis_extension_continuous
  exact (continuous_const.mul hstrip_sum_cont).add
    (hprefix_cont.add (continuous_const.mul haxis_sum_cont))

/--
Continuity of the assembled combined-sharp indexed one-add majorant.

This names the continuous global-majorant fact with `(5 / 4)^k` on the strip
sum and `(9 / 7)^k` on the indexed trivial-zero tail sum.
-/
theorem finiteComponentOneAddIndexedTailMajorant_continuous_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (cutoff k : Nat)
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => stripMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => stripMajorant i f)
        (fun i _hi => stripMajorant_continuous i))
  have haxis_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => axisMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => axisMajorant i f)
        (fun i _hi => axisMajorant_continuous i))
  have hprefix_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_continuous
      (system := system) cutoff k prefix_trivialAxis_extension_continuous
  exact (continuous_const.mul hstrip_sum_cont).add
    (hprefix_cont.add (continuous_const.mul haxis_sum_cont))

/--
Continuity of the assembled sharp-strip arbitrary-loss indexed one-add
majorant.

This is the closedness-side majorant fact with `(5 / 4)^k` on the strip sum
and a prescribed `loss^k` on the indexed trivial-zero tail sum.
-/
theorem finiteComponentOneAddIndexedTailMajorant_continuous_sharpStrip_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (cutoff k : Nat)
    {loss : Real}
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripMajorant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          loss ^ k *
            (Finset.univ.sum fun i : Index => axisMajorant i f)) := by
  have hstrip_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => stripMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => stripMajorant i f)
        (fun i _hi => stripMajorant_continuous i))
  have haxis_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => axisMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => axisMajorant i f)
        (fun i _hi => axisMajorant_continuous i))
  have hprefix_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_continuous
      (system := system) cutoff k prefix_trivialAxis_extension_continuous
  exact (continuous_const.mul hstrip_sum_cont).add
    (hprefix_cont.add (continuous_const.mul haxis_sum_cont))

/--
The assembled real/Fourier indexed-tail majorant is nonnegative.

This is the concrete source-estimate bound used by the real/Fourier profile
route: strip majorants multiply the real-axis seminorms of `f` and `Fourier f`,
and the indexed trivial-axis tail majorant multiplies the real-axis seminorm of
`f`, with the automatic finite prefix kept explicit.
-/
theorem finiteComponentRealFourierIndexedTailMajorant_nonneg
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
    (cutoff k : Nat)
    (f : SchwartzLineTestFunction) :
    0 <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripRealMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k f +
              stripFourierMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier f)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (Finset.univ.sum fun i : Index => tailMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hstrip_sum_nonneg :
      0 <=
        (Finset.univ.sum fun i : Index =>
          stripRealMajorant i f *
              schwartzLineRealAxisShiftedSeminormConstant k f +
            stripFourierMajorant i f *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier f)) := by
    exact Finset.sum_nonneg fun i _ => by
      exact add_nonneg
        (mul_nonneg (stripRealMajorant_nonneg i f)
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
        (mul_nonneg (stripFourierMajorant_nonneg i f)
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
            (SchwartzLineTestFunction.fourier f)))
  have htail_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => tailMajorant i f := by
    exact Finset.sum_nonneg fun i _ => tailMajorant_nonneg i f
  exact add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
      hstrip_sum_nonneg)
    (add_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f)
      (mul_nonneg htail_sum_nonneg
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)))

/-- The real/Fourier indexed-tail majorant is monotone in the finite cutoff. -/
theorem finiteComponentRealFourierIndexedTailMajorant_mono_cutoff
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (f : SchwartzLineTestFunction) :
    (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripRealMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k f +
              stripFourierMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier f)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (Finset.univ.sum fun i : Index => tailMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripRealMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k f +
              stripFourierMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier f)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          (Finset.univ.sum fun i : Index => tailMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff f
  linarith

/--
Continuity of the assembled real/Fourier indexed-tail majorant.

This discharges the closedness-side global-majorant obligation for source
proofs whose strip estimate is controlled by continuous real/Fourier component
majorants and whose finite trivial-axis prefix has continuous extension
evaluations.
-/
theorem finiteComponentRealFourierIndexedTailMajorant_continuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripRealMajorant_continuous :
      forall i : Index, Continuous (stripRealMajorant i))
    (stripFourierMajorant_continuous :
      forall i : Index, Continuous (stripFourierMajorant i))
    (tailMajorant_continuous :
      forall i : Index, Continuous (tailMajorant i))
    (cutoff k : Nat)
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) :
    Continuous fun f : SchwartzLineTestFunction =>
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripRealMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k f +
              stripFourierMajorant i f *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier f)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (Finset.univ.sum fun i : Index => tailMajorant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hstrip_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index =>
          stripRealMajorant i f *
              schwartzLineRealAxisShiftedSeminormConstant k f +
            stripFourierMajorant i f *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier f) := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f =>
          stripRealMajorant i f *
              schwartzLineRealAxisShiftedSeminormConstant k f +
            stripFourierMajorant i f *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier f))
        (fun i _hi =>
          ((stripRealMajorant_continuous i).mul
              (schwartzLineRealAxisShiftedSeminormConstant_continuous k)).add
            ((stripFourierMajorant_continuous i).mul
              (schwartzLineFourierRealAxisShiftedSeminormConstant_continuous k))))
  have htail_sum_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => tailMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => tailMajorant i f)
        (fun i _hi => tailMajorant_continuous i))
  have hprefix_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_continuous
      (system := system) cutoff k prefix_trivialAxis_extension_continuous
  exact (continuous_const.mul hstrip_sum_cont).add
    (hprefix_cont.add
      (htail_sum_cont.mul
        (schwartzLineRealAxisShiftedSeminormConstant_continuous k)))

end RiemannHypothesisProject
