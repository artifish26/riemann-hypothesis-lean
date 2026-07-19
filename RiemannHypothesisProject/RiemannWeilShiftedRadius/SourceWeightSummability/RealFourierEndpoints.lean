import RiemannHypothesisProject.RiemannWeilShiftedRadius.SourceWeightSummability.SingleComponentRealFourier

/-!
# Source-weight real/Fourier endpoint bridges

This module contains the final real/Fourier source-zero-argument and weighted endpoint bridges.
-/

namespace RiemannHypothesisProject
/--
Eventual source real/Fourier project-majorant decay in the weighted zero-locus
form.

This packages the same eventual analytic hypotheses as the exact denominator
estimate above, then clears the positive shifted-radius denominator for the
fixed zero argument.  It is the source-side shape needed by dense closedness:
an eventual indexed-tail proof produces a weighted zero-locus inequality with
the project-side real/Fourier majorants.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant i g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant i g)
    (sourceTailComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonComponentConstant i g)
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
    (source_component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) <=
                    sourceStripRealComparisonConstant i g *
                        norm ((testData.toSchwartz g) z.re) +
                      sourceStripFourierComparisonConstant i g *
                        norm ((testData.sourceFourier g) z.re))
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
                      sourceTailComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (source_stripRealComparisonConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripRealComparisonConstant i g <=
              stripRealMajorant i (testData.toSchwartz g))
    (source_stripFourierComparisonConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripFourierComparisonConstant i g <=
              stripFourierMajorant i (testData.toSchwartz g))
    (source_tailComparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceTailComparisonComponentConstant i g <=
              tailMajorant i (testData.toSchwartz g))
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
              stripRealMajorant i (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                stripFourierMajorant i (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (SchwartzLineTestFunction.fourier
                      (testData.toSchwartz g))) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                tailMajorant i (testData.toSchwartz g)) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g)) := by
  rcases
    exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      g hg rho with
    ⟨cutoff, hnorm⟩
  refine ⟨cutoff, ?_⟩
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let projectBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripRealMajorant i (testData.toSchwartz g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) +
            stripFourierMajorant i (testData.toSchwartz g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier
                  (testData.toSchwartz g))) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            tailMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hnorm' :
      norm (system.extension (testData.toSchwartz g) zeroArgument) <=
        projectBound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, projectBound] using hnorm
  simpa [zeroArgument, projectBound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound) hnorm'

/--
Eventually-valid source real/Fourier exact-norm decay promoted to project-side
majorants.

Once the source two-profile indexed-tail hypotheses hold eventually, the
project-side real/Fourier majorant exact denominator estimate holds for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant i g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant i g)
    (sourceTailComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonComponentConstant i g)
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
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (source_component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) <=
                    sourceStripRealComparisonConstant i g *
                        norm ((testData.toSchwartz g) z.re) +
                      sourceStripFourierComparisonConstant i g *
                        norm ((testData.sourceFourier g) z.re))
    (source_component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n)))
    (source_stripRealComparisonConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripRealComparisonConstant i g <=
              stripRealMajorant i (testData.toSchwartz g))
    (source_stripFourierComparisonConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripFourierComparisonConstant i g <=
              stripFourierMajorant i (testData.toSchwartz g))
    (source_tailComparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceTailComparisonComponentConstant i g <=
              tailMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripRealMajorant i (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                stripFourierMajorant i (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (SchwartzLineTestFunction.fourier
                      (testData.toSchwartz g))) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                tailMajorant i (testData.toSchwartz g)) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g))) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
  have htail_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
                        Complex.I)) ∧
        (forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n))) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      g hg rho

/--
Eventually-valid source real/Fourier weighted decay promoted to project-side
majorants.

The source two-profile asymptotic tail proof keeps the weighted project
real/Fourier majorant estimate valid for every sufficiently large cutoff.
-/
theorem eventually_source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant i g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant i g)
    (sourceTailComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonComponentConstant i g)
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
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (source_component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) <=
                    sourceStripRealComparisonConstant i g *
                        norm ((testData.toSchwartz g) z.re) +
                      sourceStripFourierComparisonConstant i g *
                        norm ((testData.sourceFourier g) z.re))
    (source_component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n)))
    (source_stripRealComparisonConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripRealComparisonConstant i g <=
              stripRealMajorant i (testData.toSchwartz g))
    (source_stripFourierComparisonConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceStripFourierComparisonConstant i g <=
              stripFourierMajorant i (testData.toSchwartz g))
    (source_tailComparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            sourceTailComparisonComponentConstant i g <=
              tailMajorant i (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripRealMajorant i (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                stripFourierMajorant i (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (SchwartzLineTestFunction.fourier
                      (testData.toSchwartz g))) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                tailMajorant i (testData.toSchwartz g)) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g)) := by
  have htail_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
                        Complex.I)) ∧
        (forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n))) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      g hg rho

/--
Source-side eventual-tail p-series estimate from two real-line profiles.

The strip component estimate may be stated against the source test and source
Fourier profiles, while the indexed trivial-axis decomposition and real-height
tail domination only need to hold eventually. Lean extracts the cutoff and
keeps the finite prefix explicit in the exact-norm bound.
-/
theorem exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant i g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant i g)
    (sourceTailComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonComponentConstant i g)
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
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (source_component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) <=
                    sourceStripRealComparisonConstant i g *
                        norm ((testData.toSchwartz g) z.re) +
                      sourceStripFourierComparisonConstant i g *
                        norm ((testData.sourceFourier g) z.re))
    (source_component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n)))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceStripRealComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                sourceStripFourierComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.sourceFourier g)) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceTailComparisonComponentConstant i g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g))) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
  have htail_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
                        Complex.I)) ∧
        (forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n))) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
    source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Eventual source-side weighted zero-locus decay from two real-line profiles.

The indexed trivial-axis decomposition and real-height tail domination may be
eventual source facts. Lean extracts a cutoff through the exact source theorem
and then clears the positive shifted-radius denominator, leaving a direct
weighted estimate with the source real/Fourier strip constants and finite
prefix explicit.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant i g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant i g)
    (sourceTailComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonComponentConstant i g)
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
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (source_component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) <=
                    sourceStripRealComparisonConstant i g *
                        norm ((testData.toSchwartz g) z.re) +
                      sourceStripFourierComparisonConstant i g *
                        norm ((testData.sourceFourier g) z.re))
    (source_component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n)))
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
              sourceStripRealComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                sourceStripFourierComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.sourceFourier g)) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceTailComparisonComponentConstant i g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g)) := by
  rcases
    exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually g hg rho with
  ⟨cutoff, hnorm⟩
  refine ⟨cutoff, ?_⟩
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripRealComparisonConstant i g *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) +
            sourceStripFourierComparisonConstant i g *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.sourceFourier g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            sourceTailComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hnorm' :
      norm (system.extension (testData.toSchwartz g) zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using hnorm
  simpa [zeroArgument, bound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := bound) hnorm'

/--
Eventually-valid source exact-denominator real/Fourier indexed-tail estimate.

Once the source indexed trivial-axis decomposition and component real-height
domination hold eventually, the two-profile exact zero-locus estimate holds
for every sufficiently large finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant i g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant i g)
    (sourceTailComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonComponentConstant i g)
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
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (source_component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) <=
                    sourceStripRealComparisonConstant i g *
                        norm ((testData.toSchwartz g) z.re) +
                      sourceStripFourierComparisonConstant i g *
                        norm ((testData.sourceFourier g) z.re))
    (source_component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n)))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceStripRealComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                sourceStripFourierComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.sourceFourier g)) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceTailComparisonComponentConstant i g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g))) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
  have htail_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
                        Complex.I)) ∧
        (forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n))) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Eventually-valid source weighted real/Fourier indexed-tail estimate.

This is the source-level two-profile weighted form for every sufficiently
large finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant i g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant i g)
    (sourceTailComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonComponentConstant i g)
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
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (source_component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) <=
                    sourceStripRealComparisonConstant i g *
                        norm ((testData.toSchwartz g) z.re) +
                      sourceStripFourierComparisonConstant i g *
                        norm ((testData.sourceFourier g) z.re))
    (source_component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n)))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceStripRealComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                sourceStripFourierComparisonConstant i g *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.sourceFourier g)) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceTailComparisonComponentConstant i g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g)) := by
  have htail_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
                        Complex.I)) ∧
        (forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall g : testData.SourceTestFunction,
                testData.admissible g ->
                  norm
                      (sourceComponent i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    sourceTailComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n))) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

end RiemannHypothesisProject
