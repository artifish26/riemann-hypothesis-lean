import RiemannHypothesisProject.RiemannWeilShiftedRadius.FiniteComponentMajorants

/-!
# Finite-component zero-argument one-add core

This module contains the project and source one-add zero-argument estimates that start the shifted-radius finite-component bridge.
-/

namespace RiemannHypothesisProject
/--
The real-radius strip envelope gives the weighted zero-locus estimate for
nontrivial zeroes. This is the precise nontrivial-zero half of the repaired
p-series target.
-/
theorem nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
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
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * stripConstant f := by
  have hstrip_bounds :=
    riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
      (zetaZeroSubtype_re_nonneg_of_not_trivial rho hnotTrivial)
  exact
    horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
      (system := system) stripConstant k
      strip_extension_weighted_norm_le_realRadius f
      (riemannWeilZeroArgument (rho : Complex))
      hstrip_bounds.1 hstrip_bounds.2

/--
The sharp real-radius strip envelope gives the weighted zero-locus estimate
for nontrivial zeroes with the closed-strip `(5 / 4)^k` geometry loss.
-/
theorem nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
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
    (rho : ZetaZeroSubtype)
    (hnotTrivial : Not (IsTrivialZetaZero (rho : Complex))) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k * stripConstant f := by
  have hstrip_bounds :=
    riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
      (zetaZeroSubtype_re_nonneg_of_not_trivial rho hnotTrivial)
  exact
    horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
      (system := system) stripConstant k
      strip_extension_weighted_norm_le_realRadius f
      (riemannWeilZeroArgument (rho : Complex))
      hstrip_bounds.1 hstrip_bounds.2

/--
Direct zero-locus weighted decay from the two repaired analytic inputs:

* a real-radius envelope on the checked horizontal strip for nontrivial zeroes;
* a standard `(1 + y)^k` estimate on the positive imaginary axis for trivial
  zeroes.

This is the actual case split behind the current p-series blocker, stated
without hiding the two remaining analytic estimates inside a structure field.
-/
theorem zeroArgument_weighted_norm_le_of_realPartEnvelopeAndOneAddImaginaryAxisControl
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant axisConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (axisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= axisConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (imaginaryAxis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (1 + y) ^ (k : Real) <=
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * stripConstant f +
        (2 : Real) ^ k * axisConstant f := by
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have haxis :=
      trivialZeroArgument_weighted_norm_le_of_oneAddImaginaryAxis_rpow_natCast
        (system := system) axisConstant k
        imaginaryAxis_oneAdd_weighted_norm_le f rho htrivial
    exact haxis.trans (by
      have hstrip_nonneg :
          0 <= (2 : Real) ^ k * stripConstant f := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (stripConstant_nonneg f)
      linarith)
  · have hstrip :=
      nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (system := system) stripConstant k
        strip_extension_weighted_norm_le_realRadius f rho htrivial
    exact hstrip.trans (by
      have haxis_nonneg :
          0 <= (2 : Real) ^ k * axisConstant f := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (axisConstant_nonneg f)
      linarith)

/--
Finite-component weighted zero-locus decay from the repaired strip/axis
inputs.

This is the componentwise version of
`zeroArgument_weighted_norm_le_of_realPartEnvelopeAndOneAddImaginaryAxisControl`:
prove finite-sum decompositions on the horizontal strip and positive imaginary
axis, then prove the corresponding weighted estimate for each component. Lean
combines the components by the triangle inequality and supplies the global
zero-locus weighted estimate.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            system.extension f ((y : Complex) * Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f ((y : Complex) * Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall y : Real,
            0 <= y ->
              norm (component i f ((y : Complex) * Complex.I)) *
                  (1 + y) ^ (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let axisConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => axisComponentConstant i f
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have haxis_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= axisConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have haxis :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (1 + y) ^ (k : Real) <=
              axisConstant f := by
    intro f y hy
    let radiusPower : Real := (1 + y) ^ (k : Real)
    have hbase_pos : 0 < 1 + y := by linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f ((y : Complex) * Complex.I)) <=
          (Finset.univ.sum fun i : Index =>
            norm (component i f ((y : Complex) * Complex.I))) := by
      rw [axis_extension_eq_component_sum f y hy]
      exact norm_sum_le Finset.univ
        (fun i : Index => component i f ((y : Complex) * Complex.I))
    calc
      norm (system.extension f ((y : Complex) * Complex.I)) * radiusPower
          <= (Finset.univ.sum fun i : Index =>
              norm (component i f ((y : Complex) * Complex.I))) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f ((y : Complex) * Complex.I)) *
              radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => axisComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_axis_oneAdd_weighted_norm_le i f y hy
  simpa [stripConstant, axisConstant] using
    zeroArgument_weighted_norm_le_of_realPartEnvelopeAndOneAddImaginaryAxisControl
      (system := system) stripConstant axisConstant hstrip_nonneg
      haxis_nonneg k hstrip haxis f rho

/--
Finite-component indexed-tail version of the positive-imaginary-axis route.

Unlike
`zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl`,
the component decomposition and `(1 + y)^k` estimates are required only on the
explicit trivial-zero tail `cutoff <= n`. The finite prefix is absorbed by the
concrete system-level prefix sum, and each tail component pays only the
checked `2^k` shift from `(1 + y)^k` to the p-series radius.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisComponentConstant i f)) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let axisConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => axisComponentConstant i f
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have htail_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= (2 : Real) ^ k * axisConstant f := by
    intro f
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
      (Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f)
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have htail :
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
              (2 : Real) ^ k * axisConstant f := by
    intro f n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hheight_nonneg : 0 <= height := by
      dsimp [height]
      exact le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (component i f axisPoint) := by
      dsimp [axisPoint, height]
      rw [tail_axis_extension_eq_component_sum f n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        component i f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension f axisPoint) * shiftedPower <=
          (2 : Real) ^ k * axisConstant f := by
      calc
        norm (system.extension f axisPoint) * shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (component i f axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (component i f axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              (2 : Real) ^ k * axisComponentConstant i f :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (component i f axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  axisComponentConstant i f := by
              dsimp [axisPoint, height]
              simpa using
                component_tail_axis_oneAdd_weighted_norm_le i f n hn
            simpa [axisPoint, shiftedPower] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height
                (fun z : Complex => component i f z)
                (axisComponentConstant i f) k hheight_nonneg honeAdd
        _ = (2 : Real) ^ k * axisConstant f := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have haxis :=
      trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisTail
        (system := system) (fun f => (2 : Real) ^ k * axisConstant f)
        htail_nonneg cutoff k htail f rho htrivial
    exact haxis.trans (by
      have hstrip_part_nonneg :
          0 <= (2 : Real) ^ k * stripConstant f := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (hstrip_nonneg f)
      linarith)
  · have hstrip_bound :=
      nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (system := system) stripConstant k hstrip f rho htrivial
    exact hstrip_bound.trans (by
      have htail_part_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              (2 : Real) ^ k * axisConstant f := by
        exact add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (htail_nonneg f)
      linarith)

/--
Sharp finite-component indexed-tail version of the positive-imaginary-axis
route.

The strip component still pays the usual `2^k` real-radius shift, but the
indexed trivial-zero tail is evaluated only at heights `5 / 2, 9 / 2, ...`;
there the one-add-to-shifted conversion costs `(9 / 7)^k` instead of `2^k`.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisComponentConstant i f)) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let axisConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => axisComponentConstant i f
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have htail_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= ((9 : Real) / 7) ^ k * axisConstant f := by
    intro f
    exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
      (Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f)
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have htail :
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
              ((9 : Real) / 7) ^ k * axisConstant f := by
    intro f n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (component i f axisPoint) := by
      dsimp [axisPoint, height]
      rw [tail_axis_extension_eq_component_sum f n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        component i f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension f axisPoint) * shiftedPower <=
          ((9 : Real) / 7) ^ k * axisConstant f := by
      calc
        norm (system.extension f axisPoint) * shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (component i f axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (component i f axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              ((9 : Real) / 7) ^ k * axisComponentConstant i f :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (component i f axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  axisComponentConstant i f := by
              dsimp [axisPoint, height]
              simpa using
                component_tail_axis_oneAdd_weighted_norm_le i f n hn
            simpa [axisPoint, shiftedPower] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight
                (fun z : Complex => component i f z)
                (axisComponentConstant i f) k n honeAdd
        _ = ((9 : Real) / 7) ^ k * axisConstant f := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have haxis :=
      trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisTail
        (system := system)
        (fun f => ((9 : Real) / 7) ^ k * axisConstant f)
        htail_nonneg cutoff k htail f rho htrivial
    exact haxis.trans (by
      have hstrip_part_nonneg :
          0 <= (2 : Real) ^ k * stripConstant f := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (hstrip_nonneg f)
      linarith)
  · have hstrip_bound :=
      nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (system := system) stripConstant k hstrip f rho htrivial
    exact hstrip_bound.trans (by
      have htail_part_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              ((9 : Real) / 7) ^ k * axisConstant f := by
        exact add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (htail_nonneg f)
      linarith)

/--
Cutoff-dependent sharp finite-component indexed-tail route.

For an indexed tail beginning at `cutoff`, the trivial-axis one-add conversion
uses the exact tail factor from the first remaining trivial-zero height,
`((h_cutoff + 2) / (1 + h_cutoff))^k`, instead of the uniform first-height
factor `(9 / 7)^k`.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_cutoffSharp
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisComponentConstant i f)) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let axisConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => axisComponentConstant i f
  let tailFactor : Real :=
    (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
      (1 + riemannWeilTrivialZeroArgumentHeight cutoff)
  have htailFactor_nonneg : 0 <= tailFactor := by
    dsimp [tailFactor]
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    exact div_nonneg (by linarith) (by linarith)
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have htail_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= tailFactor ^ k * axisConstant f := by
    intro f
    exact mul_nonneg (pow_nonneg htailFactor_nonneg k)
      (Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f)
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have htail :
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
              tailFactor ^ k * axisConstant f := by
    intro f n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (component i f axisPoint) := by
      dsimp [axisPoint, height]
      rw [tail_axis_extension_eq_component_sum f n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        component i f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension f axisPoint) * shiftedPower <=
          tailFactor ^ k * axisConstant f := by
      calc
        norm (system.extension f axisPoint) * shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (component i f axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (component i f axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              tailFactor ^ k * axisComponentConstant i f :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (component i f axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  axisComponentConstant i f := by
              dsimp [axisPoint, height]
              simpa using
                component_tail_axis_oneAdd_weighted_norm_le i f n hn
            simpa [axisPoint, shiftedPower, tailFactor] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight_ge_cutoff
                (fun z : Complex => component i f z)
                (axisComponentConstant i f) k cutoff n hn honeAdd
        _ = tailFactor ^ k * axisConstant f := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have haxis :=
      trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisTail
        (system := system)
        (fun f => tailFactor ^ k * axisConstant f)
        htail_nonneg cutoff k htail f rho htrivial
    exact haxis.trans (by
      have hstrip_part_nonneg :
          0 <= (2 : Real) ^ k * stripConstant f := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (hstrip_nonneg f)
      linarith)
  · have hstrip_bound :=
      nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (system := system) stripConstant k hstrip f rho htrivial
    exact hstrip_bound.trans (by
      have htail_part_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              tailFactor ^ k * axisConstant f := by
        exact add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (htail_nonneg f)
      linarith)

/--
Finite-component indexed-tail estimate with both the sharp closed-strip factor
and the cutoff-dependent trivial-tail factor.

The nontrivial strip side pays only `(5 / 4)^k`, while the indexed tail uses
the exact first-remaining-height factor after the finite prefix cutoff.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisComponentConstant i f)) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let axisConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => axisComponentConstant i f
  let tailFactor : Real :=
    (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
      (1 + riemannWeilTrivialZeroArgumentHeight cutoff)
  have htailFactor_nonneg : 0 <= tailFactor := by
    dsimp [tailFactor]
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    exact div_nonneg (by linarith) (by linarith)
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have htail_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= tailFactor ^ k * axisConstant f := by
    intro f
    exact mul_nonneg (pow_nonneg htailFactor_nonneg k)
      (Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f)
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have htail :
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
              tailFactor ^ k * axisConstant f := by
    intro f n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (component i f axisPoint) := by
      dsimp [axisPoint, height]
      rw [tail_axis_extension_eq_component_sum f n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        component i f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension f axisPoint) * shiftedPower <=
          tailFactor ^ k * axisConstant f := by
      calc
        norm (system.extension f axisPoint) * shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (component i f axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (component i f axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              tailFactor ^ k * axisComponentConstant i f :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (component i f axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  axisComponentConstant i f := by
              dsimp [axisPoint, height]
              simpa using
                component_tail_axis_oneAdd_weighted_norm_le i f n hn
            simpa [axisPoint, shiftedPower, tailFactor] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight_ge_cutoff
                (fun z : Complex => component i f z)
                (axisComponentConstant i f) k cutoff n hn honeAdd
        _ = tailFactor ^ k * axisConstant f := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have haxis :=
      trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisTail
        (system := system)
        (fun f => tailFactor ^ k * axisConstant f)
        htail_nonneg cutoff k htail f rho htrivial
    exact haxis.trans (by
      have hstrip_part_nonneg :
          0 <= ((5 : Real) / 4) ^ k * stripConstant f := by
        exact mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          (hstrip_nonneg f)
      linarith)
  · have hstrip_bound :=
      nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
        (system := system) stripConstant k hstrip f rho htrivial
    exact hstrip_bound.trans (by
      have htail_part_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              tailFactor ^ k * axisConstant f := by
        exact add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (htail_nonneg f)
      linarith)

/--
Exact-denominator form of
`zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail`.
-/
theorem zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hweighted :
      norm (system.extension f zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <=
        bound := by
    simpa [zeroArgument, bound] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
        (system := system) component stripComponentConstant
        axisComponentConstant stripComponentConstant_nonneg
        axisComponentConstant_nonneg cutoff k strip_extension_eq_component_sum
        tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_oneAdd_weighted_norm_le f rho
  let radiusPower : Real := (norm zeroArgument + 2) ^ (k : Real)
  have hbase_pos : 0 < norm zeroArgument + 2 := by
    have hnorm_nonneg : 0 <= norm zeroArgument := norm_nonneg zeroArgument
    linarith
  have hradiusPower_pos : 0 < radiusPower := by
    dsimp [radiusPower]
    exact Real.rpow_pos_of_pos hbase_pos (k : Real)
  have hdiv :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower <=
        bound / radiusPower :=
    div_le_div_of_nonneg_right
      (by simpa [radiusPower] using hweighted)
      (le_of_lt hradiusPower_pos)
  have hleft :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower =
        norm (system.extension f zeroArgument) := by
    field_simp [hradiusPower_pos.ne']
  have hright :
      bound / radiusPower = bound * (1 / radiusPower) := by
    ring
  calc
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex)))
        = norm (system.extension f zeroArgument) := by
          rfl
    _ = norm (system.extension f zeroArgument) * radiusPower / radiusPower := by
      rw [hleft]
    _ <= bound / radiusPower := hdiv
    _ = bound * (1 / radiusPower) := hright
    _ = ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
      rfl

/--
Source-side finite-component weighted zero-locus decay.

This is the dense-source workhorse for the repaired p-series target: prove the
finite-sum identities and component estimates only for admissible source tests.
Lean then derives the weighted zero-locus estimate for the image
`testData.toSchwartz g`.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall y : Real,
            0 <= y ->
              system.extension (testData.toSchwartz g)
                  ((y : Complex) * Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g ((y : Complex) * Complex.I))
    (source_component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) *
                      (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                    sourceStripComponentConstant i g)
    (source_component_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall y : Real,
              0 <= y ->
                norm
                    (sourceComponent i g ((y : Complex) * Complex.I)) *
                    (1 + y) ^ (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => sourceStripComponentConstant i g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) := by
  let stripConstant : Real :=
    Finset.univ.sum fun i : Index => sourceStripComponentConstant i g
  let axisConstant : Real :=
    Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g
  have hstrip_nonneg : 0 <= stripConstant := by
    exact Finset.sum_nonneg fun i _ =>
      sourceStripComponentConstant_nonneg i g hg
  have haxis_nonneg : 0 <= axisConstant := by
    exact Finset.sum_nonneg fun i _ =>
      sourceAxisComponentConstant_nonneg i g hg
  have hstrip :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension (testData.toSchwartz g) z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant := by
    intro z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension (testData.toSchwartz g) z) <=
          (Finset.univ.sum fun i : Index => norm (sourceComponent i g z)) := by
      rw [source_strip_extension_eq_component_sum g hg z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => sourceComponent i g z)
    calc
      norm (system.extension (testData.toSchwartz g) z) * radiusPower
          <= (Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g z)) * radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            source_component_strip_weighted_norm_le_realRadius i g hg z hlow
              hhigh
  have haxis :
      forall y : Real,
        0 <= y ->
          norm
              (system.extension (testData.toSchwartz g)
                ((y : Complex) * Complex.I)) *
              (1 + y) ^ (k : Real) <=
            axisConstant := by
    intro y hy
    let radiusPower : Real := (1 + y) ^ (k : Real)
    have hbase_pos : 0 < 1 + y := by linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm
            (system.extension (testData.toSchwartz g)
              ((y : Complex) * Complex.I)) <=
          (Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g ((y : Complex) * Complex.I))) := by
      rw [source_axis_extension_eq_component_sum g hg y hy]
      exact norm_sum_le Finset.univ
        (fun i : Index => sourceComponent i g ((y : Complex) * Complex.I))
    calc
      norm
            (system.extension (testData.toSchwartz g)
              ((y : Complex) * Complex.I)) *
            radiusPower
          <= (Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g ((y : Complex) * Complex.I))) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g ((y : Complex) * Complex.I)) *
              radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            source_component_axis_oneAdd_weighted_norm_le i g hg y hy
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    have haxis_shifted :=
      fixedImaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_rpow_natCast
        (fun z : Complex => system.extension (testData.toSchwartz g) z)
        axisConstant k haxis
        (riemannWeilTrivialZeroArgumentHeight n)
        (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
    have hheight_abs :
        |riemannWeilTrivialZeroArgumentHeight n| =
          riemannWeilTrivialZeroArgumentHeight n := by
      exact abs_of_nonneg
        (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
    have haxis_zeroArgument :
        norm
            (system.extension (testData.toSchwartz g)
              (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          (2 : Real) ^ k * axisConstant := by
      simpa [harg, norm_trivialZeroArgumentHeight_mul_I n, hheight_abs]
        using haxis_shifted
    exact haxis_zeroArgument.trans (by
      have hstrip_nonneg' :
          0 <= (2 : Real) ^ k * stripConstant := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_nonneg
      linarith)
  · have hstrip_bounds :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    have hstrip_shifted :=
      fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (fun z : Complex => system.extension (testData.toSchwartz g) z)
        stripConstant k hstrip (riemannWeilZeroArgument (rho : Complex))
        hstrip_bounds.1 hstrip_bounds.2
    exact hstrip_shifted.trans (by
      have haxis_nonneg' :
          0 <= (2 : Real) ^ k * axisConstant := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          haxis_nonneg
      linarith)

/--
Convert a shifted-radius weighted estimate into the exact p-series denominator
form.

This is the denominator counterpart to
`weighted_norm_le_of_norm_le_mul_inv_shiftedRadius`: a checked weighted
zero-locus inequality immediately yields the exact-norm estimate with the
positive shifted-radius denominator.
-/
theorem norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
    (value zeroArgument : Complex) (k : Nat) (bound : Real)
    (hweighted :
      norm value * (norm zeroArgument + 2) ^ (k : Real) <= bound) :
    norm value <= bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
  let radiusPower : Real := (norm zeroArgument + 2) ^ (k : Real)
  have hbase_pos : 0 < norm zeroArgument + 2 := by
    have hnorm_nonneg : 0 <= norm zeroArgument := norm_nonneg zeroArgument
    linarith
  have hradiusPower_pos : 0 < radiusPower := by
    dsimp [radiusPower]
    exact Real.rpow_pos_of_pos hbase_pos (k : Real)
  have hdiv :
      norm value * radiusPower / radiusPower <= bound / radiusPower :=
    div_le_div_of_nonneg_right
      (by simpa [radiusPower] using hweighted)
      (le_of_lt hradiusPower_pos)
  have hleft :
      norm value * radiusPower / radiusPower = norm value := by
    field_simp [hradiusPower_pos.ne']
  have hright :
      bound / radiusPower = bound * (1 / radiusPower) := by
    ring
  calc
    norm value = norm value * radiusPower / radiusPower := by
      rw [hleft]
    _ <= bound / radiusPower := hdiv
    _ = bound * (1 / radiusPower) := hright
    _ = bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
      rfl

/--
The indexed one-add tail weighted estimate survives enlarging the finite
prefix cutoff.

This is the cutoff-alignment form for the standard `(1 + y)^k` tail route:
prove the tail decomposition and component one-add estimates at one cutoff,
then enlarge the visible finite prefix without changing the tail constant.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_mono_cutoff
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisComponentConstant i f)) := by
  have hbase :=
    zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant
      axisComponentConstant stripComponentConstant_nonneg
      axisComponentConstant_nonneg cutoff k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le f rho
  have hmono :=
    finiteComponentOneAddIndexedTailMajorant_mono_cutoff
      (system := system) stripComponentConstant axisComponentConstant
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff f
  exact hbase.trans hmono

/--
The indexed one-add tail exact-denominator estimate survives enlarging the
finite prefix cutoff.
-/
theorem zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_mono_cutoff
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff' k f +
            (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k f +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hweighted :
      norm (system.extension f zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <=
        bound := by
    simpa [zeroArgument, bound] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_mono_cutoff
        (system := system) component stripComponentConstant
        axisComponentConstant stripComponentConstant_nonneg
        axisComponentConstant_nonneg hcutoff strip_extension_eq_component_sum
        tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_oneAdd_weighted_norm_le f rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hweighted

/--
Eventual-tail exact-denominator version of the indexed one-add route.

This is the source-proof shape usually needed in practice: the tail
decomposition and component `(1 + y)^k` estimates only have to hold for all
sufficiently large indexed trivial-zero heights. Lean extracts a cutoff and
keeps the finite prefix explicit.
-/
theorem exists_cutoff_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I))
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripComponentConstant i f) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              (2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  axisComponentConstant i f))) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) ∧
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
    zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant
      axisComponentConstant stripComponentConstant_nonneg
      axisComponentConstant_nonneg cutoff k strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventual-tail weighted version of the indexed one-add route.

Lean extracts a cutoff from eventual indexed tail hypotheses and returns the
weighted zero-locus estimate directly, with the one-add tail constant and
finite prefix still visible.
-/
theorem exists_cutoff_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I))
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) ∧
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
    zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant
      axisComponentConstant stripComponentConstant_nonneg
      axisComponentConstant_nonneg cutoff k strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventual-tail weighted indexed one-add route with arbitrary tail loss.

After choosing a sufficiently long finite prefix, the indexed trivial-axis
one-add tail can be converted to the shifted-radius zero-locus estimate with
any prescribed multiplicative loss `loss^k` for `1 < loss`.
-/
theorem exists_cutoff_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (k : Nat)
    {loss : Real}
    (hloss : 1 < loss)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I))
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            loss ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) ∧
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨sourceCutoff, hsourceCutoff⟩
  rcases eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le
      hloss with ⟨factorCutoff, hfactorCutoff⟩
  let cutoff : Nat := max sourceCutoff factorCutoff
  have hsource := hsourceCutoff cutoff (Nat.le_max_left sourceCutoff factorCutoff)
  have hfactor_le :
      (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff) <= loss := by
    exact hfactorCutoff cutoff (Nat.le_max_right sourceCutoff factorCutoff)
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
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisComponentConstant i f := by
    exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
  refine ⟨cutoff, ?_⟩
  have hcutoffSharp :=
    zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_cutoffSharp
      (system := system) component stripComponentConstant
      axisComponentConstant stripComponentConstant_nonneg
      axisComponentConstant_nonneg cutoff k strip_extension_eq_component_sum
      (fun f n hn => hsource.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hsource.2 n hn i f)
      f rho
  exact hcutoffSharp.trans (by
    have htail_compare :
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index => axisComponentConstant i f) <=
          loss ^ k *
            (Finset.univ.sum fun i : Index => axisComponentConstant i f) := by
      exact mul_le_mul_of_nonneg_right hfactor_pow_le haxis_sum_nonneg
    linarith)

/--
Eventual-tail weighted indexed one-add route with the sharp strip factor and
arbitrary tail loss.

After choosing a sufficiently long finite prefix, the nontrivial strip side
pays `(5 / 4)^k` and the indexed trivial-axis tail pays any prescribed
multiplicative loss `loss^k` for `1 < loss`.
-/
theorem exists_cutoff_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharpStrip_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (k : Nat)
    {loss : Real}
    (hloss : 1 < loss)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I))
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        ((5 : Real) / 4) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            loss ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨sourceCutoff, hsourceCutoff⟩
  rcases eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le
      hloss with ⟨factorCutoff, hfactorCutoff⟩
  let cutoff : Nat := max sourceCutoff factorCutoff
  have hsource := hsourceCutoff cutoff (Nat.le_max_left sourceCutoff factorCutoff)
  have hfactor_le :
      (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff) <= loss := by
    exact hfactorCutoff cutoff (Nat.le_max_right sourceCutoff factorCutoff)
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
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisComponentConstant i f := by
    exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
  refine ⟨cutoff, ?_⟩
  have hcutoffSharp :=
    zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp
      (system := system) component stripComponentConstant
      axisComponentConstant stripComponentConstant_nonneg
      axisComponentConstant_nonneg cutoff k strip_extension_eq_component_sum
      (fun f n hn => hsource.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hsource.2 n hn i f)
      f rho
  exact hcutoffSharp.trans (by
    have htail_compare :
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index => axisComponentConstant i f) <=
          loss ^ k *
            (Finset.univ.sum fun i : Index => axisComponentConstant i f) := by
      exact mul_le_mul_of_nonneg_right hfactor_pow_le haxis_sum_nonneg
    linarith)

/--
Eventual-tail weighted indexed one-add route with the sharp strip factor,
arbitrary tail loss, and an arbitrary larger visible finite prefix.

Lean extracts one cutoff from the eventual decomposition, component one-add
tail estimate, and cutoff-factor bound.  Every larger displayed cutoff still
satisfies the same weighted zero-locus estimate with `(5 / 4)^k` on the strip
and the prescribed `loss^k` on the indexed tail.
-/
theorem exists_cutoff_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_mono_cutoff_sharpStrip_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (axisComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisComponentConstant i f)
    (k : Nat)
    {loss : Real}
    (hloss : 1 < loss)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I))
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      forall cutoff' : Nat,
        cutoff <= cutoff' ->
          norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            ((5 : Real) / 4) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripComponentConstant i f) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff' k f +
                loss ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisComponentConstant i f)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨sourceCutoff, hsourceCutoff⟩
  rcases eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le
      hloss with ⟨factorCutoff, hfactorCutoff⟩
  let cutoff : Nat := max sourceCutoff factorCutoff
  refine ⟨cutoff, ?_⟩
  intro cutoff' hcutoff'
  have hsource :
      (forall n : Nat,
        cutoff' <= n ->
          forall f : SchwartzLineTestFunction,
            system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) /\
      (forall n : Nat,
        cutoff' <= n ->
          forall i : Index,
            forall f : SchwartzLineTestFunction,
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                  (k : Real) <=
              axisComponentConstant i f) := by
    exact hsourceCutoff cutoff'
      (le_trans (Nat.le_max_left sourceCutoff factorCutoff) hcutoff')
  have hfactor_le :
      (riemannWeilTrivialZeroArgumentHeight cutoff' + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff') <= loss := by
    exact hfactorCutoff cutoff'
      (le_trans (Nat.le_max_right sourceCutoff factorCutoff) hcutoff')
  have hfactor_nonneg :
      0 <=
        (riemannWeilTrivialZeroArgumentHeight cutoff' + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff') := by
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff'
    exact div_nonneg (by linarith) (by linarith)
  have hfactor_pow_le :
      ((riemannWeilTrivialZeroArgumentHeight cutoff' + 2) /
          (1 + riemannWeilTrivialZeroArgumentHeight cutoff')) ^ k <=
        loss ^ k := by
    exact pow_le_pow_left₀ hfactor_nonneg hfactor_le k
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => axisComponentConstant i f := by
    exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
  have hcutoffSharp :=
    zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp
      (system := system) component stripComponentConstant
      axisComponentConstant stripComponentConstant_nonneg
      axisComponentConstant_nonneg cutoff' k strip_extension_eq_component_sum
      (fun f n hn => hsource.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hsource.2 n hn i f)
      f rho
  exact hcutoffSharp.trans (by
    have htail_compare :
        ((riemannWeilTrivialZeroArgumentHeight cutoff' + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff')) ^ k *
            (Finset.univ.sum fun i : Index => axisComponentConstant i f) <=
          loss ^ k *
            (Finset.univ.sum fun i : Index => axisComponentConstant i f) := by
      exact mul_le_mul_of_nonneg_right hfactor_pow_le haxis_sum_nonneg
    linarith)

/--
Source-side exact-norm zero-locus decay from finite-component strip and
positive-imaginary-axis estimates.

This is the p-series denominator form of
`source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl`.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall y : Real,
            0 <= y ->
              system.extension (testData.toSchwartz g)
                  ((y : Complex) * Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g ((y : Complex) * Complex.I))
    (source_component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) *
                      (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                    sourceStripComponentConstant i g)
    (source_component_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall y : Real,
              0 <= y ->
                norm
                    (sourceComponent i g ((y : Complex) * Complex.I)) *
                    (1 + y) ^ (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceAxisComponentConstant i g)
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        k source_strip_extension_eq_component_sum
        source_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_axis_oneAdd_weighted_norm_le g hg rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted

end RiemannHypothesisProject
