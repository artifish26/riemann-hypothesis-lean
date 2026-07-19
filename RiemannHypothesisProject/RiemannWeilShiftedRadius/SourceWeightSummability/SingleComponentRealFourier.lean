import RiemannHypothesisProject.RiemannWeilShiftedRadius.SourceWeightSummability.RealFourierTail

/-!
# Source-weight single-component real/Fourier endpoints

This module contains the single-component real/Fourier summability and window endpoints.
-/

namespace RiemannHypothesisProject
section SingleComponentRealFourierEventuallyIndexedTailClosedBallCounting

variable {system : SchwartzRiemannWeilExtensionSystem}
variable (testData : GuinandWeilSourceTestFunctionClass)
variable (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
  sourceTailComparisonConstant :
  testData.SourceTestFunction -> Real)
variable (stripRealMajorant stripFourierMajorant tailMajorant :
  SchwartzLineTestFunction -> Real)
variable (sourceStripRealComparisonConstant_nonneg :
  forall g : testData.SourceTestFunction,
    testData.admissible g -> 0 <= sourceStripRealComparisonConstant g)
variable (sourceStripFourierComparisonConstant_nonneg :
  forall g : testData.SourceTestFunction,
    testData.admissible g -> 0 <= sourceStripFourierComparisonConstant g)
variable (sourceTailComparisonConstant_nonneg :
  forall g : testData.SourceTestFunction,
    testData.admissible g -> 0 <= sourceTailComparisonConstant g)
variable (stripRealMajorant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= stripRealMajorant f)
variable (stripFourierMajorant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= stripFourierMajorant f)
variable (tailMajorant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= tailMajorant f)
variable (k : Nat)
variable (source_strip_norm_le_real_fourier :
  forall g : testData.SourceTestFunction,
    testData.admissible g ->
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension (testData.toSchwartz g) z) <=
              sourceStripRealComparisonConstant g *
                  norm ((testData.toSchwartz g) z.re) +
                sourceStripFourierComparisonConstant g *
                  norm ((testData.sourceFourier g) z.re))
variable (source_tail_axis_norm_le_realHeight_eventually :
  Filter.Eventually
    (fun cutoff : Nat =>
      forall n : Nat,
        cutoff <= n ->
          forall g : testData.SourceTestFunction,
            testData.admissible g ->
              norm
                  (system.extension (testData.toSchwartz g)
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                sourceTailComparisonConstant g *
                  norm
                    ((testData.toSchwartz g)
                      (riemannWeilTrivialZeroArgumentHeight n)))
    (Filter.atTop : Filter Nat))
variable (sourceStripRealComparisonConstant_le_majorant :
  forall g : testData.SourceTestFunction,
    testData.admissible g ->
      sourceStripRealComparisonConstant g <=
        stripRealMajorant (testData.toSchwartz g))
variable (sourceStripFourierComparisonConstant_le_majorant :
  forall g : testData.SourceTestFunction,
    testData.admissible g ->
      sourceStripFourierComparisonConstant g <=
        stripFourierMajorant (testData.toSchwartz g))
variable (sourceTailComparisonConstant_le_majorant :
  forall g : testData.SourceTestFunction,
    testData.admissible g ->
      sourceTailComparisonConstant g <=
        tailMajorant (testData.toSchwartz g))
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
  sourceTailComparisonConstant stripRealMajorant stripFourierMajorant
  tailMajorant sourceStripRealComparisonConstant_nonneg
  sourceStripFourierComparisonConstant_nonneg
  sourceTailComparisonConstant_nonneg stripRealMajorant_nonneg
  stripFourierMajorant_nonneg tailMajorant_nonneg k
  source_strip_norm_le_real_fourier
  source_tail_axis_norm_le_realHeight_eventually
  sourceStripRealComparisonConstant_le_majorant
  sourceStripFourierComparisonConstant_le_majorant
  sourceTailComparisonConstant_le_majorant counting counting_cutoff_eq
  growth_add_one_lt_k

/--
Single-component source real/Fourier eventual-tail estimates plus cutoff-1
closed-ball polynomial counting give absolute summability of the actual
source-side `system.weight` series.
-/
theorem summable_norm_source_weight_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (system.weight (testData.toSchwartz g) rho)) := by
  simpa using
    summable_norm_source_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) (Index := Unit) testData
      (fun _ g z => system.extension (testData.toSchwartz g) z)
      (fun _ g => sourceStripRealComparisonConstant g)
      (fun _ g => sourceStripFourierComparisonConstant g)
      (fun _ g => sourceTailComparisonConstant g)
      (fun _ f => stripRealMajorant f)
      (fun _ f => stripFourierMajorant f)
      (fun _ f => tailMajorant f)
      (by
        intro _ g hg
        exact sourceStripRealComparisonConstant_nonneg g hg)
      (by
        intro _ g hg
        exact sourceStripFourierComparisonConstant_nonneg g hg)
      (by
        intro _ g hg
        exact sourceTailComparisonConstant_nonneg g hg)
      (by
        intro _ f
        exact stripRealMajorant_nonneg f)
      (by
        intro _ f
        exact stripFourierMajorant_nonneg f)
      (by
        intro _ f
        exact tailMajorant_nonneg f)
      k
      (by
        intro g _hg z _hlow _hhigh
        simp)
      (Filter.Eventually.of_forall
        (fun _cutoff n _hn g _hg => by simp))
      (by
        intro _ g hg z hlow hhigh
        exact source_strip_norm_le_real_fourier g hg z hlow hhigh)
      (source_tail_axis_norm_le_realHeight_eventually.mono
        (fun _cutoff htail n hn _ g hg => htail n hn g hg))
      (by
        intro _ g hg
        exact sourceStripRealComparisonConstant_le_majorant g hg)
      (by
        intro _ g hg
        exact sourceStripFourierComparisonConstant_le_majorant g hg)
      (by
        intro _ g hg
        exact sourceTailComparisonConstant_le_majorant g hg)
      counting counting_cutoff_eq growth_add_one_lt_k g hg

/--
The same single-component source estimates make the signed `system.weight`
series summable for the fixed admissible source test.
-/
theorem summable_source_weight_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Summable (system.weight (testData.toSchwartz g)) := by
  have hnorm :
      Summable
        (fun rho : ZetaZeroSubtype =>
          norm (system.weight (testData.toSchwartz g) rho)) :=
    summable_norm_source_weight_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceStripRealComparisonConstant
      sourceStripFourierComparisonConstant sourceTailComparisonConstant
      stripRealMajorant stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k source_strip_norm_le_real_fourier
      source_tail_axis_norm_le_realHeight_eventually
      sourceStripRealComparisonConstant_le_majorant
      sourceStripFourierComparisonConstant_le_majorant
      sourceTailComparisonConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k g hg
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

/--
Finite compact-exhaustion source windows of `system.weight` converge to the
signed infinite zero-side series under the single-component real/Fourier
eventual-tail hypotheses.
-/
theorem tendsto_source_weight_zetaZeroWindowSum_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (summable_source_weight_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceStripRealComparisonConstant
      sourceStripFourierComparisonConstant sourceTailComparisonConstant
      stripRealMajorant stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k source_strip_norm_le_real_fourier
      source_tail_axis_norm_le_realHeight_eventually
      sourceStripRealComparisonConstant_le_majorant
      sourceStripFourierComparisonConstant_le_majorant
      sourceTailComparisonConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k g hg)

/-- The signed finite-window source error norm tends to zero. -/
theorem tendsto_source_weight_zetaZeroWindowErrorNorm_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    tendsto_source_weight_zetaZeroWindowSum_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceStripRealComparisonConstant
      sourceStripFourierComparisonConstant sourceTailComparisonConstant
      stripRealMajorant stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k source_strip_norm_le_real_fourier
      source_tail_axis_norm_le_realHeight_eventually
      sourceStripRealComparisonConstant_le_majorant
      sourceStripFourierComparisonConstant_le_majorant
      sourceTailComparisonConstant_le_majorant
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
theorem eventually_source_weight_zetaZeroWindowErrorNorm_lt_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (tendsto_source_weight_zetaZeroWindowErrorNorm_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceStripRealComparisonConstant
      sourceStripFourierComparisonConstant sourceTailComparisonConstant
      stripRealMajorant stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k source_strip_norm_le_real_fourier
      source_tail_axis_norm_le_realHeight_eventually
      sourceStripRealComparisonConstant_le_majorant
      sourceStripFourierComparisonConstant_le_majorant
      sourceTailComparisonConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the fixed single-component source-side
`system.weight` series outside growing compact zero windows tends to zero.
-/
theorem tendsto_norm_source_weight_zetaZeroWindowTail_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    summable_norm_source_weight_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceStripRealComparisonConstant
      sourceStripFourierComparisonConstant sourceTailComparisonConstant
      stripRealMajorant stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k source_strip_norm_le_real_fourier
      source_tail_axis_norm_le_realHeight_eventually
      sourceStripRealComparisonConstant_le_majorant
      sourceStripFourierComparisonConstant_le_majorant
      sourceTailComparisonConstant_le_majorant
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
For every positive tolerance, the absolute norm tail of the single-component
source-side `system.weight` series is eventually below that tolerance.
-/
theorem eventually_norm_source_weight_zetaZeroWindowTail_lt_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (tendsto_norm_source_weight_zetaZeroWindowTail_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceStripRealComparisonConstant
      sourceStripFourierComparisonConstant sourceTailComparisonConstant
      stripRealMajorant stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k source_strip_norm_le_real_fourier
      source_tail_axis_norm_le_realHeight_eventually
      sourceStripRealComparisonConstant_le_majorant
      sourceStripFourierComparisonConstant_le_majorant
      sourceTailComparisonConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

end SingleComponentRealFourierEventuallyIndexedTailClosedBallCounting

end RiemannHypothesisProject
