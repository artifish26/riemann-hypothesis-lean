import RiemannHypothesisProject.RiemannWeilShiftedRadius.SourceWeightSummability.OneAddSummability

/-!
# Source-weight real-height tails

This module contains real-height finite-component source-weight shell bounds, summability, and window endpoints.
-/

namespace RiemannHypothesisProject
/--
The source real-radius finite-component estimate gives a direct closed-ball
p-series shell bound for the actual real zero-side weight.

This is the pointwise `system.weight` consequence of the exact source
real-radius estimate: the project-side indexed-tail majorant bounds the
zero-argument extension, and the closed-ball first-entry comparison converts
that shifted-radius denominator to the shell denominator used by the direct
p-series route.
-/
theorem source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
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
    (source_component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall n : Nat,
              cutoff <= n ->
                norm
                    (sourceComponent i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) <=
                  sourceComparisonComponentConstant i g *
                    norm
                      ((testData.toSchwartz g)
                        (riemannWeilTrivialZeroArgumentHeight n)))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_comparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceComparisonComponentConstant i g <=
              comparisonMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm (system.weight (testData.toSchwartz g) rho) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              comparisonMajorant i (testData.toSchwartz g)) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            comparisonMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hbound_nonneg : 0 <= bound := by
    simpa [bound] using
      finiteComponentRealIndexedTailMajorant_nonneg
        (system := system) stripMajorant comparisonMajorant
        stripMajorant_nonneg comparisonMajorant_nonneg cutoff k
        (testData.toSchwartz g)
  have hzero :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceComparisonComponentConstant
        stripMajorant comparisonMajorant
        sourceStripComponentConstant_nonneg
        sourceComparisonComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_norm_le_realHeight
        source_stripComponentConstant_le_majorant
        source_comparisonComponentConstant_le_majorant
        g hg rho
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) (testData.toSchwartz g) rho bound k
      hbound_nonneg hzero

/--
Eventual source real-radius finite-component estimates give a direct
closed-ball p-series shell bound for the actual real zero-side weight.

Lean extracts one indexed trivial-axis cutoff from the eventual source
decomposition and tail-domination hypotheses, then lands in the direct
`system.weight` shell bound consumed by the polynomial-counting p-series route.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
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
    (source_component_tail_axis_norm_le_realHeight_eventually :
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
                            Complex.I)) <=
                      sourceComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_comparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceComparisonComponentConstant i g <=
              comparisonMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight (testData.toSchwartz g) rho) <=
          ((2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripMajorant i (testData.toSchwartz g)) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) +
              (Finset.univ.sum fun i : Index =>
                  comparisonMajorant i (testData.toSchwartz g)) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g))) *
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
                            Complex.I)) <=
                      sourceComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n))))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      g hg rho

/--
Eventually-valid source real-radius project-majorant shell bound for the
actual real zero-side weight.

The eventual source indexed-tail hypotheses keep the direct closed-ball
`system.weight` shell estimate valid for every sufficiently large finite-prefix
cutoff, before any polynomial counting assumption is applied.
-/
theorem eventually_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
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
    (source_component_tail_axis_norm_le_realHeight_eventually :
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
                            Complex.I)) <=
                      sourceComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_comparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceComparisonComponentConstant i g <=
              comparisonMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight (testData.toSchwartz g) rho) <=
            ((2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripMajorant i (testData.toSchwartz g)) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k (testData.toSchwartz g) +
                (Finset.univ.sum fun i : Index =>
                    comparisonMajorant i (testData.toSchwartz g)) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g))) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
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
                            Complex.I)) <=
                      sourceComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n))))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff rho =>
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      g hg rho

/--
Eventual source real-radius project-majorant estimates plus cutoff-1
closed-ball polynomial counting give absolute summability of the actual
zero-side weight for a fixed admissible source test.
-/
theorem summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
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
    (source_component_tail_axis_norm_le_realHeight_eventually :
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
                            Complex.I)) <=
                      sourceComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_comparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceComparisonComponentConstant i g <=
              comparisonMajorant i (testData.toSchwartz g))
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
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant g hg with
    ⟨cutoff, hshell⟩
  let sourceF : SchwartzLineTestFunction := testData.toSchwartz g
  let sourceConstant : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripMajorant i sourceF) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k sourceF +
        (Finset.univ.sum fun i : Index => comparisonMajorant i sourceF) *
          schwartzLineRealAxisShiftedSeminormConstant k sourceF)
  have hsourceConstant_nonneg : 0 <= sourceConstant := by
    simpa [sourceConstant, sourceF] using
      finiteComponentRealIndexedTailMajorant_nonneg
        (system := system) stripMajorant comparisonMajorant
        stripMajorant_nonneg comparisonMajorant_nonneg cutoff k sourceF
  let sourceWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight sourceF rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := sourceWeight
      cutoff := 1
      shellBound := fun _f n =>
        sourceConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => sourceConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hsourceConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hsourceConstant_nonneg
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
        simpa [sourceWeight, sourceConstant, sourceF] using hshell rho }
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
The same fixed-source eventual real-radius majorant hypotheses make the signed
`system.weight` series summable for the admissible source test.
-/
theorem summable_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
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
    (source_component_tail_axis_norm_le_realHeight_eventually :
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
                            Complex.I)) <=
                      sourceComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (source_stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripComponentConstant i g <=
              stripMajorant i (testData.toSchwartz g))
    (source_comparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceComparisonComponentConstant i g <=
              comparisonMajorant i (testData.toSchwartz g))
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
    summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k g hg
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

section FiniteComponentRealPartEnvelopeClosedBallCountingWindowEndpoints

variable {Index : Type*} [Fintype Index]
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (testData : GuinandWeilSourceTestFunctionClass)
variable (sourceComponent :
  Index -> testData.SourceTestFunction -> Complex -> Complex)
variable (sourceStripComponentConstant sourceComparisonComponentConstant :
  Index -> testData.SourceTestFunction -> Real)
variable (stripMajorant comparisonMajorant :
  Index -> SchwartzLineTestFunction -> Real)
variable (sourceStripComponentConstant_nonneg :
  forall i : Index, forall g : testData.SourceTestFunction,
    testData.admissible g -> 0 <= sourceStripComponentConstant i g)
variable (sourceComparisonComponentConstant_nonneg :
  forall i : Index, forall g : testData.SourceTestFunction,
    testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
variable (stripMajorant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= stripMajorant i f)
variable (comparisonMajorant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= comparisonMajorant i f)
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
variable (source_component_tail_axis_norm_le_realHeight_eventually :
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
                        Complex.I)) <=
                  sourceComparisonComponentConstant i g *
                    norm
                      ((testData.toSchwartz g)
                        (riemannWeilTrivialZeroArgumentHeight n)))
    (Filter.atTop : Filter Nat))
variable (source_stripComponentConstant_le_majorant :
  forall i : Index,
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        sourceStripComponentConstant i g <=
          stripMajorant i (testData.toSchwartz g))
variable (source_comparisonComponentConstant_le_majorant :
  forall i : Index,
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        sourceComparisonComponentConstant i g <=
          comparisonMajorant i (testData.toSchwartz g))
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include sourceComponent sourceStripComponentConstant
  sourceComparisonComponentConstant stripMajorant comparisonMajorant
  sourceStripComponentConstant_nonneg sourceComparisonComponentConstant_nonneg
  stripMajorant_nonneg comparisonMajorant_nonneg k
  source_strip_extension_eq_component_sum
  source_tail_axis_extension_eq_component_sum_eventually
  source_component_strip_weighted_norm_le_realRadius
  source_component_tail_axis_norm_le_realHeight_eventually
  source_stripComponentConstant_le_majorant
  source_comparisonComponentConstant_le_majorant counting counting_cutoff_eq
  growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the actual source-side `system.weight`
converge to the signed infinite zero-side series under the real-radius
eventual source majorant and cutoff-1 closed-ball counting hypotheses.
-/
theorem tendsto_source_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (summable_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k g hg)

/-- The signed finite-window source error norm tends to zero. -/
theorem tendsto_source_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    tendsto_source_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
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
theorem eventually_source_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (tendsto_source_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the fixed source-side `system.weight` series outside
growing compact zero windows tends to zero.
-/
theorem tendsto_norm_source_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
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
theorem eventually_norm_source_weight_zetaZeroWindowTail_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (tendsto_norm_source_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

end FiniteComponentRealPartEnvelopeClosedBallCountingWindowEndpoints

end RiemannHypothesisProject
