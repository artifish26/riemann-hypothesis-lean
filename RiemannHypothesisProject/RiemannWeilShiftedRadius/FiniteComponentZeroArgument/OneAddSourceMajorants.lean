import RiemannHypothesisProject.RiemannWeilShiftedRadius.FiniteComponentZeroArgument.OneAddCore

/-!
# Finite-component one-add source majorants

This module contains the source one-add indexed-tail estimates and project-majorant bridges.
-/

namespace RiemannHypothesisProject
/--
Source-side finite-component weighted zero-locus decay from an explicit
indexed trivial-axis `(1 + y)^k` tail.

This is the source-level version of the indexed one-add route: the strip
estimate is a real-radius component envelope, while the trivial-zero tail only
requires the standard `(1 + y)^k` bound at the indexed trivial-zero heights.
The finite prefix remains the concrete system-level prefix sum.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
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
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g)) := by
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
          Finset.univ.sum fun i : Index => norm (sourceComponent i g z) := by
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
  have htail :
      forall n : Nat,
        cutoff <= n ->
          norm
              (system.extension (testData.toSchwartz g)
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) *
              (norm
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) + 2) ^ (k : Real) <=
            (2 : Real) ^ k * axisConstant := by
    intro n hn
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
        norm
            (system.extension (testData.toSchwartz g) axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g axisPoint) := by
      dsimp [axisPoint, height]
      rw [source_tail_axis_extension_eq_component_sum g hg n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        sourceComponent i g
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower <=
          (2 : Real) ^ k * axisConstant := by
      calc
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (sourceComponent i g axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              (2 : Real) ^ k * sourceAxisComponentConstant i g :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (sourceComponent i g axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  sourceAxisComponentConstant i g := by
              dsimp [axisPoint, height]
              simpa using
                source_component_tail_axis_oneAdd_weighted_norm_le i g hg n hn
            simpa [axisPoint, shiftedPower] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_height
                (fun z : Complex => sourceComponent i g z)
                (sourceAxisComponentConstant i g) k hheight_nonneg honeAdd
        _ = (2 : Real) ^ k * axisConstant := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    by_cases hn : n < cutoff
    · have hprefix :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) := by
        simpa [harg] using
          riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) n hn
      exact hprefix.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have htail_nonneg : 0 <= (2 : Real) ^ k * axisConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            haxis_nonneg
        linarith)
    · have hge : cutoff <= n := Nat.le_of_not_gt hn
      have htail_zeroArgument :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            (2 : Real) ^ k * axisConstant := by
        simpa [harg] using htail n hge
      exact htail_zeroArgument.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have hprefix_nonneg :
            0 <=
              riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) :=
          riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g)
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
      have hprefix_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) :=
        riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k (testData.toSchwartz g)
      have htail_nonneg : 0 <= (2 : Real) ^ k * axisConstant := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          haxis_nonneg
      linarith)

/--
Source-side sharp finite-component weighted zero-locus decay from an explicit
indexed trivial-axis `(1 + y)^k` tail.

This is the source-level analogue of
`zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp`:
the strip still uses the real-radius `2^k` conversion, while the indexed
trivial-zero tail uses the checked `(9 / 7)^k` conversion at the actual tail
heights.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
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
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g)) := by
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
          Finset.univ.sum fun i : Index => norm (sourceComponent i g z) := by
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
  have htail :
      forall n : Nat,
        cutoff <= n ->
          norm
              (system.extension (testData.toSchwartz g)
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) *
              (norm
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) + 2) ^ (k : Real) <=
            ((9 : Real) / 7) ^ k * axisConstant := by
    intro n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm
            (system.extension (testData.toSchwartz g) axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g axisPoint) := by
      dsimp [axisPoint, height]
      rw [source_tail_axis_extension_eq_component_sum g hg n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        sourceComponent i g
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower <=
          ((9 : Real) / 7) ^ k * axisConstant := by
      calc
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (sourceComponent i g axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              ((9 : Real) / 7) ^ k * sourceAxisComponentConstant i g :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (sourceComponent i g axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  sourceAxisComponentConstant i g := by
              dsimp [axisPoint, height]
              simpa using
                source_component_tail_axis_oneAdd_weighted_norm_le i g hg n hn
            simpa [axisPoint, shiftedPower] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight
                (fun z : Complex => sourceComponent i g z)
                (sourceAxisComponentConstant i g) k n honeAdd
        _ = ((9 : Real) / 7) ^ k * axisConstant := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    by_cases hn : n < cutoff
    · have hprefix :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) := by
        simpa [harg] using
          riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) n hn
      exact hprefix.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have htail_nonneg :
            0 <= ((9 : Real) / 7) ^ k * axisConstant := by
          exact mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_nonneg
        linarith)
    · have hge : cutoff <= n := Nat.le_of_not_gt hn
      have htail_zeroArgument :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            ((9 : Real) / 7) ^ k * axisConstant := by
        simpa [harg] using htail n hge
      exact htail_zeroArgument.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have hprefix_nonneg :
            0 <=
              riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) :=
          riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g)
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
      have hprefix_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) :=
        riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k (testData.toSchwartz g)
      have htail_nonneg :
          0 <= ((9 : Real) / 7) ^ k * axisConstant := by
        exact mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
          haxis_nonneg
      linarith)

/--
Source-side cutoff-sharp finite-component weighted zero-locus decay from an
explicit indexed trivial-axis `(1 + y)^k` tail.

For a fixed finite-prefix cutoff, the indexed tail uses the exact conversion
factor from the first remaining trivial-zero height instead of the uniform
first-height `(9 / 7)^k` bound.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_cutoffSharp
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
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g)) := by
  let stripConstant : Real :=
    Finset.univ.sum fun i : Index => sourceStripComponentConstant i g
  let axisConstant : Real :=
    Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g
  let tailFactor : Real :=
    (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
      (1 + riemannWeilTrivialZeroArgumentHeight cutoff)
  have htailFactor_nonneg : 0 <= tailFactor := by
    dsimp [tailFactor]
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    exact div_nonneg (by linarith) (by linarith)
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
          Finset.univ.sum fun i : Index => norm (sourceComponent i g z) := by
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
  have htail :
      forall n : Nat,
        cutoff <= n ->
          norm
              (system.extension (testData.toSchwartz g)
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) *
              (norm
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) + 2) ^ (k : Real) <=
            tailFactor ^ k * axisConstant := by
    intro n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm
            (system.extension (testData.toSchwartz g) axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g axisPoint) := by
      dsimp [axisPoint, height]
      rw [source_tail_axis_extension_eq_component_sum g hg n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        sourceComponent i g
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower <=
          tailFactor ^ k * axisConstant := by
      calc
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (sourceComponent i g axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              tailFactor ^ k * sourceAxisComponentConstant i g :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (sourceComponent i g axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  sourceAxisComponentConstant i g := by
              dsimp [axisPoint, height]
              simpa using
                source_component_tail_axis_oneAdd_weighted_norm_le i g hg n hn
            simpa [axisPoint, shiftedPower, tailFactor] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight_ge_cutoff
                (fun z : Complex => sourceComponent i g z)
                (sourceAxisComponentConstant i g) k cutoff n hn honeAdd
        _ = tailFactor ^ k * axisConstant := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    by_cases hn : n < cutoff
    · have hprefix :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) := by
        simpa [harg] using
          riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) n hn
      exact hprefix.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have htail_nonneg : 0 <= tailFactor ^ k * axisConstant := by
          exact mul_nonneg (pow_nonneg htailFactor_nonneg k) haxis_nonneg
        linarith)
    · have hge : cutoff <= n := Nat.le_of_not_gt hn
      have htail_zeroArgument :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            tailFactor ^ k * axisConstant := by
        simpa [harg] using htail n hge
      exact htail_zeroArgument.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have hprefix_nonneg :
            0 <=
              riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) :=
          riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g)
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
      have hprefix_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) :=
        riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k (testData.toSchwartz g)
      have htail_nonneg : 0 <= tailFactor ^ k * axisConstant := by
        exact mul_nonneg (pow_nonneg htailFactor_nonneg k) haxis_nonneg
      linarith)

/--
Source-side cutoff-sharp finite-component weighted zero-locus decay with the
sharp closed-strip factor.

For a fixed finite-prefix cutoff, the nontrivial strip side pays `(5 / 4)^k`
and the indexed tail uses the exact conversion factor from the first remaining
trivial-zero height.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp
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
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g)) := by
  let stripConstant : Real :=
    Finset.univ.sum fun i : Index => sourceStripComponentConstant i g
  let axisConstant : Real :=
    Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g
  let tailFactor : Real :=
    (riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
      (1 + riemannWeilTrivialZeroArgumentHeight cutoff)
  have htailFactor_nonneg : 0 <= tailFactor := by
    dsimp [tailFactor]
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    exact div_nonneg (by linarith) (by linarith)
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
          Finset.univ.sum fun i : Index => norm (sourceComponent i g z) := by
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
  have htail :
      forall n : Nat,
        cutoff <= n ->
          norm
              (system.extension (testData.toSchwartz g)
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) *
              (norm
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) + 2) ^ (k : Real) <=
            tailFactor ^ k * axisConstant := by
    intro n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm
            (system.extension (testData.toSchwartz g) axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g axisPoint) := by
      dsimp [axisPoint, height]
      rw [source_tail_axis_extension_eq_component_sum g hg n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        sourceComponent i g
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower <=
          tailFactor ^ k * axisConstant := by
      calc
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (sourceComponent i g axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              tailFactor ^ k * sourceAxisComponentConstant i g :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (sourceComponent i g axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  sourceAxisComponentConstant i g := by
              dsimp [axisPoint, height]
              simpa using
                source_component_tail_axis_oneAdd_weighted_norm_le i g hg n hn
            simpa [axisPoint, shiftedPower, tailFactor] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight_ge_cutoff
                (fun z : Complex => sourceComponent i g z)
                (sourceAxisComponentConstant i g) k cutoff n hn honeAdd
        _ = tailFactor ^ k * axisConstant := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    by_cases hn : n < cutoff
    · have hprefix :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) := by
        simpa [harg] using
          riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) n hn
      exact hprefix.trans (by
        have hstrip_nonneg' :
            0 <= ((5 : Real) / 4) ^ k * stripConstant := by
          exact mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
            hstrip_nonneg
        have htail_nonneg : 0 <= tailFactor ^ k * axisConstant := by
          exact mul_nonneg (pow_nonneg htailFactor_nonneg k) haxis_nonneg
        linarith)
    · have hge : cutoff <= n := Nat.le_of_not_gt hn
      have htail_zeroArgument :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            tailFactor ^ k * axisConstant := by
        simpa [harg] using htail n hge
      exact htail_zeroArgument.trans (by
        have hstrip_nonneg' :
            0 <= ((5 : Real) / 4) ^ k * stripConstant := by
          exact mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
            hstrip_nonneg
        have hprefix_nonneg :
            0 <=
              riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) :=
          riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g)
        linarith)
  · have hstrip_bounds :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    have hstrip_shifted :=
      fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
        (fun z : Complex => system.extension (testData.toSchwartz g) z)
        stripConstant k hstrip (riemannWeilZeroArgument (rho : Complex))
        hstrip_bounds.1 hstrip_bounds.2
    exact hstrip_shifted.trans (by
      have hprefix_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) :=
        riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k (testData.toSchwartz g)
      have htail_nonneg : 0 <= tailFactor ^ k * axisConstant := by
        exact mul_nonneg (pow_nonneg htailFactor_nonneg k) haxis_nonneg
      linarith)

/--
Source-side eventual indexed one-add route with arbitrary tail loss.

This is the source-boundary theorem for the cutoff-sharp geometry: eventual
source decomposition and component one-add tail estimates imply a weighted
zero-locus estimate with any prescribed tail loss `loss^k`, after moving a
sufficiently long finite prefix into the explicit prefix constant.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_loss
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
    {loss : Real}
    (hloss : 1 < loss)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceStripComponentConstant i g) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            loss ^ k *
              (Finset.univ.sum fun i : Index =>
                sourceAxisComponentConstant i g)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) ∧
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
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
      0 <= Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g := by
    exact Finset.sum_nonneg fun i _ =>
      sourceAxisComponentConstant_nonneg i g hg
  refine ⟨cutoff, ?_⟩
  have hcutoffSharp :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_cutoffSharp
      (system := system) testData sourceComponent sourceStripComponentConstant
      sourceAxisComponentConstant sourceStripComponentConstant_nonneg
      sourceAxisComponentConstant_nonneg cutoff k source_strip_extension_eq_component_sum
      (fun g hg n hn => hsource.1 g hg n hn)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hsource.2 g hg n hn i)
      g hg rho
  exact hcutoffSharp.trans (by
    have htail_compare :
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) <=
          loss ^ k *
            (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) := by
      exact mul_le_mul_of_nonneg_right hfactor_pow_le haxis_sum_nonneg
    linarith)

/--
Source-side eventual indexed one-add route with the sharp strip factor and
arbitrary tail loss.

This keeps the closed-strip contribution at `(5 / 4)^k` while extracting a
sufficiently long finite prefix so that the indexed trivial-axis tail pays any
prescribed `loss^k` for `1 < loss`.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharpStrip_loss
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
    {loss : Real}
    (hloss : 1 < loss)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        ((5 : Real) / 4) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceStripComponentConstant i g) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            loss ^ k *
              (Finset.univ.sum fun i : Index =>
                sourceAxisComponentConstant i g)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) /\
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
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
      0 <= Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g := by
    exact Finset.sum_nonneg fun i _ =>
      sourceAxisComponentConstant_nonneg i g hg
  refine ⟨cutoff, ?_⟩
  have hcutoffSharp :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp
      (system := system) testData sourceComponent sourceStripComponentConstant
      sourceAxisComponentConstant sourceStripComponentConstant_nonneg
      sourceAxisComponentConstant_nonneg cutoff k source_strip_extension_eq_component_sum
      (fun g hg n hn => hsource.1 g hg n hn)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hsource.2 g hg n hn i)
      g hg rho
  exact hcutoffSharp.trans (by
    have htail_compare :
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) <=
          loss ^ k *
            (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) := by
      exact mul_le_mul_of_nonneg_right hfactor_pow_le haxis_sum_nonneg
    linarith)

/--
Source-side eventual indexed one-add route with the sharp strip factor,
arbitrary tail loss, and an arbitrary larger visible finite prefix.

Lean extracts one cutoff from the source-tail hypotheses and the asymptotic
tail-factor estimate.  Every larger displayed cutoff still satisfies the same
weighted zero-locus estimate with source constants and the prescribed
`loss^k` tail.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_mono_cutoff_sharpStrip_loss
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
    {loss : Real}
    (hloss : 1 < loss)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      forall cutoff' : Nat,
        cutoff <= cutoff' ->
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            ((5 : Real) / 4) ^ k *
                (Finset.univ.sum fun i : Index =>
                  sourceStripComponentConstant i g) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff' k (testData.toSchwartz g) +
                loss ^ k *
                  (Finset.univ.sum fun i : Index =>
                    sourceAxisComponentConstant i g)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) /\
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨sourceCutoff, hsourceCutoff⟩
  rcases eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le
      hloss with ⟨factorCutoff, hfactorCutoff⟩
  let cutoff : Nat := max sourceCutoff factorCutoff
  refine ⟨cutoff, ?_⟩
  intro cutoff' hcutoff'
  have hsource :
      (forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff' <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) /\
      (forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff' <= n ->
              forall i : Index,
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                sourceAxisComponentConstant i g) := by
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
      0 <= Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g := by
    exact Finset.sum_nonneg fun i _ =>
      sourceAxisComponentConstant_nonneg i g hg
  have hcutoffSharp :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp
      (system := system) testData sourceComponent sourceStripComponentConstant
      sourceAxisComponentConstant sourceStripComponentConstant_nonneg
      sourceAxisComponentConstant_nonneg cutoff' k source_strip_extension_eq_component_sum
      (fun g hg n hn => hsource.1 g hg n hn)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hsource.2 g hg n hn i)
      g hg rho
  exact hcutoffSharp.trans (by
    have htail_compare :
        ((riemannWeilTrivialZeroArgumentHeight cutoff' + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff')) ^ k *
            (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) <=
          loss ^ k *
            (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) := by
      exact mul_le_mul_of_nonneg_right hfactor_pow_le haxis_sum_nonneg
    linarith)

/--
Source-side finite-component weighted zero-locus decay with both checked
geometric sharpenings.

The nontrivial strip side uses the closed-strip `(5 / 4)^k` radius comparison,
while the indexed trivial-zero tail uses the actual-height `(9 / 7)^k`
one-add-to-shifted conversion.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g)) := by
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
          Finset.univ.sum fun i : Index => norm (sourceComponent i g z) := by
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
  have htail :
      forall n : Nat,
        cutoff <= n ->
          norm
              (system.extension (testData.toSchwartz g)
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) *
              (norm
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) + 2) ^ (k : Real) <=
            ((9 : Real) / 7) ^ k * axisConstant := by
    intro n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm
            (system.extension (testData.toSchwartz g) axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g axisPoint) := by
      dsimp [axisPoint, height]
      rw [source_tail_axis_extension_eq_component_sum g hg n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        sourceComponent i g
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower <=
          ((9 : Real) / 7) ^ k * axisConstant := by
      calc
        norm (system.extension (testData.toSchwartz g) axisPoint) *
            shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (sourceComponent i g axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              ((9 : Real) / 7) ^ k * sourceAxisComponentConstant i g :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (sourceComponent i g axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  sourceAxisComponentConstant i g := by
              dsimp [axisPoint, height]
              simpa using
                source_component_tail_axis_oneAdd_weighted_norm_le i g hg n hn
            simpa [axisPoint, shiftedPower] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight
                (fun z : Complex => sourceComponent i g z)
                (sourceAxisComponentConstant i g) k n honeAdd
        _ = ((9 : Real) / 7) ^ k * axisConstant := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    by_cases hn : n < cutoff
    · have hprefix :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) := by
        simpa [harg] using
          riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) n hn
      exact hprefix.trans (by
        have hstrip_nonneg' :
            0 <= ((5 : Real) / 4) ^ k * stripConstant := by
          exact mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
            hstrip_nonneg
        have htail_nonneg :
            0 <= ((9 : Real) / 7) ^ k * axisConstant := by
          exact mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_nonneg
        linarith)
    · have hge : cutoff <= n := Nat.le_of_not_gt hn
      have htail_zeroArgument :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            ((9 : Real) / 7) ^ k * axisConstant := by
        simpa [harg] using htail n hge
      exact htail_zeroArgument.trans (by
        have hstrip_nonneg' :
            0 <= ((5 : Real) / 4) ^ k * stripConstant := by
          exact mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
            hstrip_nonneg
        have hprefix_nonneg :
            0 <=
              riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) :=
          riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g)
        linarith)
  · have hstrip_bounds :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    have hstrip_shifted :=
      fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
        (fun z : Complex => system.extension (testData.toSchwartz g) z)
        stripConstant k hstrip (riemannWeilZeroArgument (rho : Complex))
        hstrip_bounds.1 hstrip_bounds.2
    exact hstrip_shifted.trans (by
      have hprefix_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) :=
        riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k (testData.toSchwartz g)
      have htail_nonneg :
          0 <= ((9 : Real) / 7) ^ k * axisConstant := by
        exact mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
          haxis_nonneg
      linarith)

/--
Source-side exact-norm zero-locus decay with both checked geometric
sharpenings.

This is the denominator form of
`source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail`.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      (((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        cutoff k source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        g hg rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted

/--
Source-side exact-norm zero-locus decay from an indexed trivial-axis
`(1 + y)^k` tail estimate.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
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
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
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
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g))) *
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        cutoff k source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        g hg rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted

/--
Source indexed one-add majorants are bounded by the corresponding project-side
majorants.

This packages the finite-prefix expression used by the indexed `(1 + y)^k`
tail route: source strip and tail constants are compared after mapping the
source test through `toSchwartz`, while the automatic trivial-axis prefix is
left unchanged.
-/
theorem sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g)) <=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g))) := by
  have hstrip_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_stripComponentConstant_le_majorant i g hg
  have haxis_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceAxisComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          axisMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_axisComponentConstant_le_majorant i g hg
  have hstrip_scaled :
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) <=
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left hstrip_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  have haxis_scaled :
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g) <=
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left haxis_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  linarith

/--
Source indexed one-add majorants are bounded by project-side majorants with
the checked sharp strip and indexed-tail constants.

This is the sharpened comparison matching
`source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail`:
the closed-strip part scales by `(5 / 4)^k`, while the indexed trivial-axis
tail scales by `(9 / 7)^k`.
-/
theorem sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g)) <=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g))) := by
  have hstrip_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_stripComponentConstant_le_majorant i g hg
  have haxis_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceAxisComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          axisMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_axisComponentConstant_le_majorant i g hg
  have hstrip_scaled :
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) <=
        ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left hstrip_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
  have haxis_scaled :
      ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g) <=
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left haxis_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
  linarith

/--
Source indexed one-add majorants are bounded by project-side majorants with
the sharp strip constant and the exact cutoff-dependent tail factor.

This is the project-majorant comparison matching
`source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp`.
-/
theorem sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant_sharpStrip_cutoffSharp
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
            (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g)) <=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
            (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g))) := by
  have hstrip_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_stripComponentConstant_le_majorant i g hg
  have haxis_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceAxisComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          axisMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_axisComponentConstant_le_majorant i g hg
  have htailFactor_nonneg :
      0 <=
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
            (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k := by
    have hheight_pos := riemannWeilTrivialZeroArgumentHeight_pos cutoff
    exact pow_nonneg (div_nonneg (by linarith) (by linarith)) k
  have hstrip_scaled :
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) <=
        ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left hstrip_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
  have haxis_scaled :
      ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
            (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g) <=
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
            (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left haxis_sum_le htailFactor_nonneg
  linarith

/--
Source indexed one-add majorants are bounded by project-side majorants with
the sharp strip constant and an arbitrary tail-loss factor.

This comparison is used after the cutoff has been chosen so that the exact
tail factor is bounded by the prescribed `loss`.
-/
theorem sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant_sharpStrip_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
    {loss : Real}
    (hloss_nonneg : 0 <= loss)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        loss ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g)) <=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        loss ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g))) := by
  have hstrip_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_stripComponentConstant_le_majorant i g hg
  have haxis_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceAxisComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          axisMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_axisComponentConstant_le_majorant i g hg
  have hstrip_scaled :
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) <=
        ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left hstrip_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
  have haxis_scaled :
      loss ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g) <=
        loss ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left haxis_sum_le (pow_nonneg hloss_nonneg k)
  linarith

/--
Source-side indexed one-add weighted decay promoted to project-side majorants.

The analytic source proof may produce strip and indexed-tail constants
depending on the source test. If those constants are bounded by project-side
majorants after `toSchwartz`, Lean obtains the weighted zero-locus estimate
with the continuous project-side one-add indexed-tail majorant.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g))) := by
  let sourceBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  let projectBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hsource :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <= sourceBound := by
    simpa [sourceBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        cutoff k source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        g hg rho
  have hsourceBound_le_projectBound : sourceBound <= projectBound := by
    simpa [sourceBound, projectBound] using
      sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant
        (system := system) testData sourceStripComponentConstant
        sourceAxisComponentConstant stripMajorant axisMajorant cutoff k
        source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant g hg
  exact hsource.trans hsourceBound_le_projectBound

/--
Source-side indexed one-add exact-denominator decay promoted to project-side
majorants.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g)))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let projectBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= projectBound := by
    simpa [zeroArgument, projectBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        stripMajorant axisMajorant sourceStripComponentConstant_nonneg
        sourceAxisComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant g hg rho
  simpa [zeroArgument, projectBound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound)
      hweighted

/--
Source-side indexed one-add weighted decay promoted to project-side majorants
with both checked geometric sharpenings.

This is the project-majorant form of
`source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail`:
component source constants are compared to project-side majorants, and the
result keeps `(5 / 4)^k` on the strip sums and `(9 / 7)^k` on the indexed
trivial-axis tail sums.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (k : Real) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g))) := by
  let sourceBound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  let projectBound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hsource :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <= sourceBound := by
    simpa [sourceBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        cutoff k source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        g hg rho
  have hsourceBound_le_projectBound : sourceBound <= projectBound := by
    simpa [sourceBound, projectBound] using
      sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant_sharpStrip_sharpTail
        (system := system) testData sourceStripComponentConstant
        sourceAxisComponentConstant stripMajorant axisMajorant cutoff k
        source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant g hg
  exact hsource.trans hsourceBound_le_projectBound

/--
Source-side indexed one-add weighted decay promoted to project-side majorants
with the sharp strip constant and exact cutoff-dependent tail factor.

This is the project-majorant form of
`source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp`.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_cutoffSharp
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (k : Real) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g))) := by
  let sourceBound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
            (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  let projectBound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((riemannWeilTrivialZeroArgumentHeight cutoff + 2) /
            (1 + riemannWeilTrivialZeroArgumentHeight cutoff)) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hsource :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <= sourceBound := by
    simpa [sourceBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_cutoffSharp
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        cutoff k source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        g hg rho
  have hsourceBound_le_projectBound : sourceBound <= projectBound := by
    simpa [sourceBound, projectBound] using
      sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant_sharpStrip_cutoffSharp
        (system := system) testData sourceStripComponentConstant
        sourceAxisComponentConstant stripMajorant axisMajorant cutoff k
        source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant g hg
  exact hsource.trans hsourceBound_le_projectBound

/--
Eventual source indexed one-add weighted decay promoted to project-side
majorants with the sharp strip constant and arbitrary tail loss.

The analytic source proof supplies eventual source constants; after one
cutoff is chosen, source constants are compared to project majorants while
the displayed tail factor remains the prescribed `loss^k`.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (k : Nat)
    {loss : Real}
    (hloss : 1 < loss)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        ((5 : Real) / 4) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripMajorant i (testData.toSchwartz g)) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            loss ^ k *
              (Finset.univ.sum fun i : Index =>
                axisMajorant i (testData.toSchwartz g))) := by
  let sourceBound : Nat -> Real := fun cutoff =>
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        loss ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  let projectBound : Nat -> Real := fun cutoff =>
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        loss ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  rcases
    exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharpStrip_loss
      (system := system) testData sourceComponent sourceStripComponentConstant
      sourceAxisComponentConstant sourceStripComponentConstant_nonneg
      sourceAxisComponentConstant_nonneg k hloss
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      g hg rho with ⟨cutoff, hsource⟩
  refine ⟨cutoff, ?_⟩
  have hsource' :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <= sourceBound cutoff := by
    simpa [sourceBound] using hsource
  have hsourceBound_le_projectBound :
      sourceBound cutoff <= projectBound cutoff := by
    have hloss_nonneg : 0 <= loss := by linarith
    simpa [sourceBound, projectBound] using
      sourceFiniteComponentOneAddIndexedTailMajorant_le_projectMajorant_sharpStrip_loss
        (system := system) testData sourceStripComponentConstant
        sourceAxisComponentConstant stripMajorant axisMajorant cutoff k
        hloss_nonneg source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant g hg
  exact hsource'.trans hsourceBound_le_projectBound

/--
Eventual source indexed one-add project-majorant weighted decay with the sharp
strip factor, arbitrary tail loss, and an arbitrary larger visible finite
prefix.

Lean extracts one cutoff from the source-tail hypotheses and the cutoff-factor
bound.  Any larger cutoff may be displayed in the finite prefix while the
tail remains bounded by the prescribed `loss^k`.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_loss
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (k : Nat)
    {loss : Real}
    (hloss : 1 < loss)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      forall cutoff' : Nat,
        cutoff <= cutoff' ->
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            ((5 : Real) / 4) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripMajorant i (testData.toSchwartz g)) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff' k (testData.toSchwartz g) +
                loss ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisMajorant i (testData.toSchwartz g))) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) /\
          (forall g : testData.SourceTestFunction,
            testData.admissible g ->
              forall n : Nat,
                cutoff <= n ->
                  forall i : Index,
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    sourceAxisComponentConstant i g))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨sourceCutoff, hsourceCutoff⟩
  rcases eventually_riemannWeilTrivialZeroArgumentHeight_tailFactor_le
      hloss with ⟨factorCutoff, hfactorCutoff⟩
  let cutoff : Nat := max sourceCutoff factorCutoff
  refine ⟨cutoff, ?_⟩
  intro cutoff' hcutoff'
  have hsource :
      (forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff' <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) /\
      (forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff' <= n ->
              forall i : Index,
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                sourceAxisComponentConstant i g) := by
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
      0 <=
        Finset.univ.sum fun i : Index =>
          axisMajorant i (testData.toSchwartz g) := by
    exact Finset.sum_nonneg fun i _ =>
      le_trans (sourceAxisComponentConstant_nonneg i g hg)
        (source_axisComponentConstant_le_majorant i g hg)
  have hcutoffSharp :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_cutoffSharp
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant sourceStripComponentConstant_nonneg
      sourceAxisComponentConstant_nonneg cutoff' k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hsource.1 g hg n hn)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hsource.2 g hg n hn i)
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant
      g hg rho
  exact hcutoffSharp.trans (by
    have htail_compare :
        ((riemannWeilTrivialZeroArgumentHeight cutoff' + 2) /
              (1 + riemannWeilTrivialZeroArgumentHeight cutoff')) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g)) <=
          loss ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g)) := by
      exact mul_le_mul_of_nonneg_right hfactor_pow_le haxis_sum_nonneg
    linarith)

/--
Source-side indexed one-add exact-denominator decay promoted to project-side
majorants with both checked geometric sharpenings.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (cutoff k : Nat)
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      (((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g)))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let projectBound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= projectBound := by
    simpa [zeroArgument, projectBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        stripMajorant axisMajorant sourceStripComponentConstant_nonneg
        sourceAxisComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant g hg rho
  simpa [zeroArgument, projectBound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound)
      hweighted

/--
Source-side one-add project-majorant weighted decay with both checked
sharpenings survives enlarging the finite prefix cutoff.

The source tail proof is used at `cutoff`; the visible sharp project-side
majorant may use any larger `cutoff'`.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (k : Real) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g))) := by
  have hbase :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant sourceStripComponentConstant_nonneg
      sourceAxisComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant
      g hg rho
  have hmono :=
    finiteComponentOneAddIndexedTailMajorant_mono_cutoff_sharpStrip_sharpTail
      (system := system) stripMajorant axisMajorant
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff
      (testData.toSchwartz g)
  exact hbase.trans hmono

/--
Source-side one-add project-majorant exact-denominator decay with both checked
sharpenings survives enlarging the finite prefix cutoff.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (source_strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => sourceComponent i g z)
    (source_tail_axis_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall n : Nat,
            cutoff <= n ->
              system.extension (testData.toSchwartz g)
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I) =
                Finset.univ.sum fun i : Index =>
                  sourceComponent i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  sourceAxisComponentConstant i g)
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      (((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g)))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let projectBound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= projectBound := by
    simpa [zeroArgument, projectBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        stripMajorant axisMajorant sourceStripComponentConstant_nonneg
        sourceAxisComponentConstant_nonneg hcutoff
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant
        g hg rho
  simpa [zeroArgument, projectBound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound)
      hweighted

/--
Eventual source indexed one-add project-majorant weighted decay with both
checked sharpenings and an arbitrary larger visible finite prefix.

Lean extracts one source-tail cutoff.  Any `cutoff'` above it may be used in
the displayed project-side prefix without changing the checked `(5 / 4)^k`
strip or `(9 / 7)^k` indexed-tail constants.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
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
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall g : testData.SourceTestFunction,
                  testData.admissible g ->
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                        (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                          (k : Real) <=
                      sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      forall cutoff' : Nat,
        cutoff <= cutoff' ->
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            ((5 : Real) / 4) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripMajorant i (testData.toSchwartz g)) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff' k (testData.toSchwartz g) +
                ((9 : Real) / 7) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisMajorant i (testData.toSchwartz g))) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall g : testData.SourceTestFunction,
                  testData.admissible g ->
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                        (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                          (k : Real) <=
                      sourceAxisComponentConstant i g))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff_base := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro cutoff' hcutoff
  exact
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff_base.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff_base.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant
      g hg rho

/--
Eventual source indexed one-add project-majorant exact-denominator decay with
both checked sharpenings and an arbitrary larger visible finite prefix.
-/
theorem exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
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
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall g : testData.SourceTestFunction,
                  testData.admissible g ->
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                        (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                          (k : Real) <=
                      sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      forall cutoff' : Nat,
        cutoff <= cutoff' ->
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) <=
            (((5 : Real) / 4) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripMajorant i (testData.toSchwartz g)) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff' k (testData.toSchwartz g) +
                ((9 : Real) / 7) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisMajorant i (testData.toSchwartz g)))) *
              (1 /
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  (k : Real)) := by
  have hweighted :=
    exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant g hg rho
  rcases hweighted with ⟨cutoff, hcutoff_all⟩
  refine ⟨cutoff, ?_⟩
  intro cutoff' hcutoff
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let projectBound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hweighted_at_cutoff :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= projectBound := by
    simpa [zeroArgument, projectBound] using hcutoff_all cutoff' hcutoff
  simpa [zeroArgument, projectBound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound)
      hweighted_at_cutoff

/--
Eventually-valid source indexed one-add project-majorant weighted decay with
both checked sharpenings.

Once the source indexed trivial-axis decomposition and one-add tail domination
hold eventually, the sharp project-majorant weighted estimate holds for every
sufficiently large visible finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
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
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall g : testData.SourceTestFunction,
                  testData.admissible g ->
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                        (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                          (k : Real) <=
                      sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    Filter.Eventually
      (fun cutoff : Nat =>
        norm
            (system.extension (testData.toSchwartz g)
              (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          ((5 : Real) / 4) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripMajorant i (testData.toSchwartz g)) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) +
              ((9 : Real) / 7) ^ k *
                (Finset.univ.sum fun i : Index =>
                  axisMajorant i (testData.toSchwartz g))))
      (Filter.atTop : Filter Nat) := by
  obtain ⟨cutoff, hcutoff_all⟩ :=
    exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant g hg rho
  rw [Filter.eventually_atTop]
  exact ⟨cutoff, fun cutoff' hcutoff => hcutoff_all cutoff' hcutoff⟩

/--
Eventually-valid source indexed one-add project-majorant exact-denominator
decay with both checked sharpenings.

This is the exact-norm counterpart of the weighted eventual estimate: after the
source tail hypotheses hold, the sharp project-side denominator bound holds for
every sufficiently large visible finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
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
    (source_tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  system.extension (testData.toSchwartz g)
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I) =
                    Finset.univ.sum fun i : Index =>
                      sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I))
        (Filter.atTop : Filter Nat))
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
    (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall g : testData.SourceTestFunction,
                  testData.admissible g ->
                    norm
                        (sourceComponent i g
                          ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                            Complex.I)) *
                        (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                          (k : Real) <=
                      sourceAxisComponentConstant i g)
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceAxisComponentConstant i g <=
              axisMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    Filter.Eventually
      (fun cutoff : Nat =>
        norm
            (system.extension (testData.toSchwartz g)
              (riemannWeilZeroArgument (rho : Complex))) <=
          (((5 : Real) / 4) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripMajorant i (testData.toSchwartz g)) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) +
              ((9 : Real) / 7) ^ k *
                (Finset.univ.sum fun i : Index =>
                  axisMajorant i (testData.toSchwartz g)))) *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)))
      (Filter.atTop : Filter Nat) := by
  obtain ⟨cutoff, hcutoff_all⟩ :=
    exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant g hg rho
  rw [Filter.eventually_atTop]
  exact ⟨cutoff, fun cutoff' hcutoff => hcutoff_all cutoff' hcutoff⟩

end RiemannHypothesisProject
