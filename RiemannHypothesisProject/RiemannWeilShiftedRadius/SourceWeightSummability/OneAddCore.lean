import RiemannHypothesisProject.RiemannWeilShiftedRadius.FiniteComponentZeroArgument.RealFourierTail
import RiemannHypothesisProject.RiemannWeilAntitoneRadialSplitPSeriesBridge

/-!
# Source-weight one-add core

This module contains the source-weight closed-ball shell bounds and summability estimates for the one-add finite-component tail route.
-/

namespace RiemannHypothesisProject
/--
Clear a positive shifted-radius denominator from an exact p-series bound.

This is the algebraic estimate that turns the denominator form
`‖value‖ ≤ bound / (‖z‖ + 2)^k` into the weighted zero-locus form consumed by
closedness arguments.
-/
theorem weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
    (value zeroArgument : Complex) (k : Nat) (bound : Real)
    (hbound :
      norm value <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real))) :
    norm value * (norm zeroArgument + 2) ^ (k : Real) <= bound := by
  let radiusPower : Real := (norm zeroArgument + 2) ^ (k : Real)
  have hbase_pos : 0 < norm zeroArgument + 2 := by
    have hnorm_nonneg : 0 <= norm zeroArgument := norm_nonneg zeroArgument
    linarith
  have hradiusPower_pos : 0 < radiusPower := by
    dsimp [radiusPower]
    exact Real.rpow_pos_of_pos hbase_pos (k : Real)
  have hweighted :
      norm value * radiusPower <=
        (bound * (1 / radiusPower)) * radiusPower := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [radiusPower] using hbound)
      (le_of_lt hradiusPower_pos)
  have hright :
      (bound * (1 / radiusPower)) * radiusPower = bound := by
    field_simp [hradiusPower_pos.ne']
  calc
    norm value * (norm zeroArgument + 2) ^ (k : Real)
        = norm value * radiusPower := by
          rfl
    _ <= (bound * (1 / radiusPower)) * radiusPower := hweighted
    _ = bound := hright

/--
An exact shifted-radius denominator bound for the zero-argument extension gives
the corresponding closed-ball cutoff-1 direct p-series bound for the actual
real zero-side weight.

This is the pointwise direct-weight version of the source finite-component
handoff: after `norm (system.weight f rho) <= norm (system.zeroValue f rho)`,
the closed-ball first-entry lower-radius comparison changes the shifted-radius
denominator into the shell denominator consumed by the direct p-series route.
-/
theorem norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (bound : Real)
    (k : Nat)
    (bound_nonneg : 0 <= bound)
    (zeroArgument_norm_le :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real))) :
    norm (system.weight f rho) <=
      bound *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let n :=
    ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho
  change
    norm (system.weight f rho) <=
      bound * (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
  have hweight_le_extension :
      norm (system.weight f rho) <=
        norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) := by
    simpa [SchwartzRiemannWeilExtensionSystem.zeroValue] using
      system.norm_weight_le_norm_zeroValue f rho
  have hshifted :
      norm (system.weight f rho) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) :=
    hweight_le_extension.trans zeroArgument_norm_le
  by_cases hn : 1 <= n
  · have hindex : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    have hlower :
        ComplexCompactExhaustion.closedBallZeroArgumentShellLowerBound
            ((n - 1) + 1) <
          norm (riemannWeilZeroArgument (rho : Complex)) := by
      simpa [n, hindex] using
        ComplexCompactExhaustion.closedBallZero_firstEntryIndex_argumentShellLowerBound_lt
          rho
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) <=
          (1 / |((n - 1 : Nat) : Real) + 1| ^ (k : Real)) :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_tailFactor_of_succ_argumentShellLowerBound
        (n - 1) (by positivity) hlower
    exact hshifted.trans
      (mul_le_mul_of_nonneg_left hfactor bound_nonneg)
  · have hn_zero : n = 0 := by omega
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) <= 1 :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_one_of_nonneg_radius
        (norm_nonneg (riemannWeilZeroArgument (rho : Complex)))
        (by positivity)
    have hprefix :
        bound *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)) <=
          bound :=
      (mul_le_mul_of_nonneg_left hfactor bound_nonneg).trans_eq
        (mul_one bound)
    exact hshifted.trans
      (by
        simpa [n, hn_zero] using hprefix)

/--
The source indexed one-add finite-component estimate gives a direct
closed-ball p-series shell bound for the actual real zero-side weight.

This is the `system.weight` consequence of the source one-add route: the source
proof controls the zero-argument extension with an indexed `(1 + y)^k` tail
constant, and the closed-ball first-entry comparison converts the shifted
radius denominator into the direct p-series shell denominator.
-/
theorem source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
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
    norm (system.weight (testData.toSchwartz g) rho) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g := by
      exact Finset.sum_nonneg fun i _ =>
        sourceStripComponentConstant_nonneg i g hg
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g := by
      exact Finset.sum_nonneg fun i _ =>
        sourceAxisComponentConstant_nonneg i g hg
    simpa [bound] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g))
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            haxis_sum_nonneg))
  have hzero :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        cutoff k source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        g hg rho
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) (testData.toSchwartz g) rho bound k
      hbound_nonneg hzero

/--
The sharp source indexed one-add finite-component estimate gives a direct
closed-ball p-series shell bound for the actual real zero-side weight.

This is the pointwise p-series consequence of the checked trivial-zero height
lower bound: the strip side still pays `2^k`, while the indexed tail entering
the shell estimate pays only `(9 / 7)^k`.
-/
theorem source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
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
    norm (system.weight (testData.toSchwartz g) rho) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g := by
      exact Finset.sum_nonneg fun i _ =>
        sourceStripComponentConstant_nonneg i g hg
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g := by
      exact Finset.sum_nonneg fun i _ =>
        sourceAxisComponentConstant_nonneg i g hg
    simpa [bound] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g))
          (mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
        cutoff k source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        g hg rho
  have hzero :
      norm (system.extension (testData.toSchwartz g) zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using
      norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
        (value := system.extension (testData.toSchwartz g) zeroArgument)
        (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted
  simpa [zeroArgument, bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) (testData.toSchwartz g) rho bound k
      hbound_nonneg hzero

/--
The source indexed one-add finite-component estimate gives a direct
closed-ball p-series shell bound with both checked geometric sharpenings.

The source-weight shell constant has `(5 / 4)^k` on the strip component sum
and `(9 / 7)^k` on the indexed trivial-zero tail component sum.
-/
theorem source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    norm (system.weight (testData.toSchwartz g) rho) <=
      (((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceAxisComponentConstant i g))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
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
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g := by
      exact Finset.sum_nonneg fun i _ =>
        sourceStripComponentConstant_nonneg i g hg
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g := by
      exact Finset.sum_nonneg fun i _ =>
        sourceAxisComponentConstant_nonneg i g hg
    simpa [bound] using
      add_nonneg
        (mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g))
          (mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
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
  have hzero :
      norm (system.extension (testData.toSchwartz g) zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using
      norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
        (value := system.extension (testData.toSchwartz g) zeroArgument)
        (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted
  simpa [zeroArgument, bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) (testData.toSchwartz g) rho bound k
      hbound_nonneg hzero

/--
The source indexed one-add project-majorant estimate gives a direct closed-ball
p-series shell bound with both checked geometric sharpenings.

This is the actual `system.weight` consequence of the sharp project-majorant
zero-argument estimate: the project-side bound has `(5 / 4)^k` on strip
majorants and `(9 / 7)^k` on indexed-tail majorants, then the closed-ball
first-entry comparison converts the shifted-radius denominator to the shell
denominator used by the p-series route.
-/
theorem source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
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
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
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
    norm (system.weight (testData.toSchwartz g) rho) <=
      (((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g)))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g) := by
      exact Finset.sum_nonneg fun i _ =>
        stripMajorant_nonneg i (testData.toSchwartz g)
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g) := by
      exact Finset.sum_nonneg fun i _ =>
        axisMajorant_nonneg i (testData.toSchwartz g)
    simpa [bound] using
      add_nonneg
        (mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g))
          (mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  have hzero :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
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
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) (testData.toSchwartz g) rho bound k
      hbound_nonneg hzero

/--
The sharp source indexed one-add project-majorant shell estimate survives
enlarging the visible finite prefix cutoff.

The source tail proof is used at `cutoff`; the closed-ball shell bound may use
any larger `cutoff'`, keeping the same checked `(5 / 4)^k` strip and
`(9 / 7)^k` indexed-tail constants.
-/
theorem source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
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
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
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
    norm (system.weight (testData.toSchwartz g) rho) <=
      (((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisMajorant i (testData.toSchwartz g)))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k (testData.toSchwartz g) +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g)))
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g) := by
      exact Finset.sum_nonneg fun i _ =>
        stripMajorant_nonneg i (testData.toSchwartz g)
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            axisMajorant i (testData.toSchwartz g) := by
      exact Finset.sum_nonneg fun i _ =>
        axisMajorant_nonneg i (testData.toSchwartz g)
    simpa [bound] using
      add_nonneg
        (mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff' k (testData.toSchwartz g))
          (mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  have hzero :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceAxisComponentConstant
        stripMajorant axisMajorant sourceStripComponentConstant_nonneg
        sourceAxisComponentConstant_nonneg
        (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_oneAdd_weighted_norm_le
        source_stripComponentConstant_le_majorant
        source_axisComponentConstant_le_majorant g hg rho
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) (testData.toSchwartz g) rho bound k
      hbound_nonneg hzero

/--
Eventual source indexed one-add project-majorant estimates give a sharp
closed-ball shell bound for every larger visible finite prefix.

Lean extracts one shared source-tail cutoff.  Any `cutoff'` above it may then be
used in the displayed project-side finite prefix while preserving the checked
`(5 / 4)^k` strip and `(9 / 7)^k` indexed-tail constants.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
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
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
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
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall cutoff' : Nat,
        cutoff <= cutoff' ->
          forall rho : ZetaZeroSubtype,
            norm (system.weight (testData.toSchwartz g) rho) <=
              (((5 : Real) / 4) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    stripMajorant i (testData.toSchwartz g)) +
                (riemannWeilIndexedTrivialAxisPrefixSumConstant
                    (system := system) cutoff' k (testData.toSchwartz g) +
                  ((9 : Real) / 7) ^ k *
                    (Finset.univ.sum fun i : Index =>
                      axisMajorant i (testData.toSchwartz g)))) *
                (1 /
                  |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                      rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
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
  intro cutoff' hcutoff rho
  exact
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      stripMajorant_nonneg axisMajorant_nonneg
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff_base.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff_base.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant
      g hg rho

/--
Eventual source indexed one-add project-majorant estimates give the sharp
direct closed-ball p-series shell bound for the actual real zero-side weight.

Lean extracts one shared indexed trivial-axis cutoff from the eventual source
decomposition and component `(1 + y)^k` tail hypotheses, then uses the fixed
sharp project-majorant shell estimate uniformly for every zero.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
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
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
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
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight (testData.toSchwartz g) rho) <=
          (((5 : Real) / 4) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripMajorant i (testData.toSchwartz g)) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) +
              ((9 : Real) / 7) ^ k *
                (Finset.univ.sum fun i : Index =>
                  axisMajorant i (testData.toSchwartz g)))) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
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
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      stripMajorant_nonneg axisMajorant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant
      g hg rho

/--
Eventually-valid sharp source indexed one-add project-majorant shell bound for
the actual real zero-side weight.

This is the `Filter.Eventually` form of the enlarged-prefix shell estimate:
after the source indexed trivial-axis hypotheses hold, the sharp closed-ball
shell bound holds for every sufficiently large visible finite-prefix cutoff.
-/
theorem eventually_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
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
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
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
    (hg : testData.admissible g) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight (testData.toSchwartz g) rho) <=
            (((5 : Real) / 4) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripMajorant i (testData.toSchwartz g)) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k (testData.toSchwartz g) +
                ((9 : Real) / 7) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisMajorant i (testData.toSchwartz g)))) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
  obtain ⟨cutoff, hcutoff_all⟩ :=
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_mono_cutoff_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      stripMajorant_nonneg axisMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant g hg
  rw [Filter.eventually_atTop]
  exact ⟨cutoff, fun cutoff' hcutoff rho => hcutoff_all cutoff' hcutoff rho⟩

/--
Eventual source indexed one-add project-majorant estimates plus cutoff-1
closed-ball polynomial counting give absolute summability of the actual
zero-side weight.

The decay package uses the sharp project-side majorant: `(5 / 4)^k` on the
strip majorant sum and `(9 / 7)^k` on the indexed-tail majorant sum.
-/
theorem summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (system.weight (testData.toSchwartz g) rho)) := by
  rcases
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      stripMajorant_nonneg axisMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant g hg with
    ⟨cutoff, hshell⟩
  let sourceF : SchwartzLineTestFunction := testData.toSchwartz g
  let projectConstant : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i sourceF) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k sourceF +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            axisMajorant i sourceF))
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            stripMajorant i sourceF := by
      exact Finset.sum_nonneg fun i _ =>
        stripMajorant_nonneg i sourceF
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index =>
            axisMajorant i sourceF := by
      exact Finset.sum_nonneg fun i _ =>
        axisMajorant_nonneg i sourceF
    simpa [projectConstant, sourceF] using
      add_nonneg
        (mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k sourceF)
          (mul_nonneg
            (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  let sourceWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight sourceF rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := sourceWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
          (one_div_nonneg.mpr
            (Real.rpow_nonneg
              (abs_nonneg ((((n - 1 : Nat) : Real) + 1)))
              (k : Real)))
      tail_shellBound_le := by
        intro _f n
        dsimp
        simp
      norm_weight_le_shellBound := by
        intro _f rho
        simpa [sourceWeight, projectConstant, sourceF] using hshell rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, sourceWeight, sourceF] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight
      sourceF

/--
The same sharp one-add project-majorant hypotheses make the signed
`system.weight` series summable for the admissible source test.
-/
theorem summable_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Summable (system.weight (testData.toSchwartz g)) := by
  have hnorm :
      Summable
        (fun rho : ZetaZeroSubtype =>
          norm (system.weight (testData.toSchwartz g) rho)) :=
    summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      stripMajorant_nonneg axisMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k g hg
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

end RiemannHypothesisProject
