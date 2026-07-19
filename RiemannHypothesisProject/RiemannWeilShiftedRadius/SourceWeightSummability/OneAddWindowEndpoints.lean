import RiemannHypothesisProject.RiemannWeilShiftedRadius.SourceWeightSummability.OneAddCore

/-!
# Source-weight one-add window endpoints

This module contains the finite zero-window convergence and tail endpoints for the one-add finite-component source-weight route.
-/

namespace RiemannHypothesisProject
section FiniteComponentOneAddMajorantClosedBallCountingWindowEndpoints

variable {Index : Type*} [Fintype Index]
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (testData : GuinandWeilSourceTestFunctionClass)
variable (sourceComponent :
  Index -> testData.SourceTestFunction -> Complex -> Complex)
variable (sourceStripComponentConstant sourceAxisComponentConstant :
  Index -> testData.SourceTestFunction -> Real)
variable (stripMajorant axisMajorant :
  Index -> SchwartzLineTestFunction -> Real)
variable (sourceStripComponentConstant_nonneg :
  forall i : Index, forall g : testData.SourceTestFunction,
    testData.admissible g -> 0 <= sourceStripComponentConstant i g)
variable (sourceAxisComponentConstant_nonneg :
  forall i : Index, forall g : testData.SourceTestFunction,
    testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
variable (stripMajorant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= stripMajorant i f)
variable (axisMajorant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= axisMajorant i f)
variable (k : Nat)
variable (source_strip_extension_eq_component_sum :
  forall g : testData.SourceTestFunction,
    testData.admissible g ->
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension (testData.toSchwartz g) z =
              Finset.univ.sum fun i : Index => sourceComponent i g z)
variable (source_tail_axis_extension_eq_component_sum_eventually :
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
variable (source_component_strip_weighted_norm_le_realRadius :
  forall i : Index,
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (sourceComponent i g z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                sourceStripComponentConstant i g)
variable (source_component_tail_axis_oneAdd_weighted_norm_le_eventually :
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
variable (source_stripComponentConstant_le_majorant :
  forall i : Index,
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        sourceStripComponentConstant i g <=
          stripMajorant i (testData.toSchwartz g))
variable (source_axisComponentConstant_le_majorant :
  forall i : Index,
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        sourceAxisComponentConstant i g <=
          axisMajorant i (testData.toSchwartz g))
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include sourceComponent sourceStripComponentConstant
  sourceAxisComponentConstant stripMajorant axisMajorant
  sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
  stripMajorant_nonneg axisMajorant_nonneg k
  source_strip_extension_eq_component_sum
  source_tail_axis_extension_eq_component_sum_eventually
  source_component_strip_weighted_norm_le_realRadius
  source_component_tail_axis_oneAdd_weighted_norm_le_eventually
  source_stripComponentConstant_le_majorant
  source_axisComponentConstant_le_majorant counting counting_cutoff_eq
  growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the actual source-side `system.weight`
converge to the signed infinite zero-side series under the sharp one-add
project-majorant p-series hypotheses.
-/
theorem tendsto_source_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
    (windowExhaustion : ComplexCompactExhaustion)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n
          (system.weight (testData.toSchwartz g)))
      Filter.atTop
      (nhds
        (tsum
          (fun rho : ZetaZeroSubtype =>
            system.weight (testData.toSchwartz g) rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
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
      counting counting_cutoff_eq growth_add_one_lt_k g hg)

/-- The signed finite-window source error norm tends to zero. -/
theorem tendsto_source_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
    (windowExhaustion : ComplexCompactExhaustion)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum
              (fun rho : ZetaZeroSubtype =>
                system.weight (testData.toSchwartz g) rho) -
            windowExhaustion.zetaZeroWindowSum n
              (system.weight (testData.toSchwartz g))))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_source_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
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
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum
            (fun rho : ZetaZeroSubtype =>
              system.weight (testData.toSchwartz g) rho))
        Filter.atTop
        (nhds
          (tsum
            (fun rho : ZetaZeroSubtype =>
              system.weight (testData.toSchwartz g) rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/--
For every positive tolerance, the signed source finite-window error is
eventually below that tolerance.
-/
theorem eventually_source_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
    (windowExhaustion : ComplexCompactExhaustion)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum
                (fun rho : ZetaZeroSubtype =>
                  system.weight (testData.toSchwartz g) rho) -
              windowExhaustion.zetaZeroWindowSum n
                (system.weight (testData.toSchwartz g))) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_source_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
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
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the fixed source-side `system.weight` series outside
growing compact zero windows tends to zero.
-/
theorem tendsto_norm_source_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
    (windowExhaustion : ComplexCompactExhaustion)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
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
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)))
        Filter.atTop
        (nhds
          (tsum
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)))
        Filter.atTop
        (nhds
          (tsum
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the absolute norm tail of the source-side
`system.weight` series is eventually below that tolerance.
-/
theorem eventually_norm_source_weight_zetaZeroWindowTail_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
    (windowExhaustion : ComplexCompactExhaustion)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype =>
              norm (system.weight (testData.toSchwartz g) rho)) <
        epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_source_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_of_majorants_closedBallPolynomialCounting_sharpStrip_sharpTail
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
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

end FiniteComponentOneAddMajorantClosedBallCountingWindowEndpoints

end RiemannHypothesisProject
