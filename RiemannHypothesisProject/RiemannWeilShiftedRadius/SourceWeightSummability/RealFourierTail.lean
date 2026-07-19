import RiemannHypothesisProject.RiemannWeilShiftedRadius.SourceWeightSummability.RealHeightTail

/-!
# Source-weight real/Fourier tails

This module contains finite-component real/Fourier source-weight shell bounds, summability, and window endpoints.
-/

namespace RiemannHypothesisProject
/--
Source-side real/Fourier exact-norm decay promoted to project-side continuous
majorants.

The analytic source estimate may produce component constants depending on the
source test.  If those constants are bounded by project-side majorants after
mapping through `toSchwartz`, Lean rewrites the packaged source Fourier profile
to the project Fourier transform and obtains the exact p-series denominator
bound with the project-side real/Fourier indexed-tail majorant.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
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
  let sourceBound : Real :=
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
  let radiusInv : Real :=
    1 /
      (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
        (k : Real)
  have hsource :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        sourceBound * radiusInv := by
    simpa [sourceBound, radiusInv] using
      source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
        (system := system) testData sourceComponent
        sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
        sourceTailComparisonComponentConstant
        sourceStripRealComparisonConstant_nonneg
        sourceStripFourierComparisonConstant_nonneg
        sourceTailComparisonComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_norm_le_real_fourier
        source_component_tail_axis_norm_le_realHeight g hg rho
  have hsourceBound_le_projectBound : sourceBound <= projectBound := by
    simpa [sourceBound, projectBound] using
      sourceRealFourierIndexedTailMajorant_le_projectMajorant
        (system := system) testData sourceStripRealComparisonConstant
        sourceStripFourierComparisonConstant
        sourceTailComparisonComponentConstant stripRealMajorant
        stripFourierMajorant tailMajorant cutoff k
        source_stripRealComparisonConstant_le_majorant
        source_stripFourierComparisonConstant_le_majorant
        source_tailComparisonComponentConstant_le_majorant g hg
  have hradiusInv_nonneg : 0 <= radiusInv := by
    dsimp [radiusInv]
    exact one_div_nonneg.mpr
      (le_of_lt
        (Real.rpow_pos_of_pos
          (by
            have hnorm_nonneg :
                0 <= norm (riemannWeilZeroArgument (rho : Complex)) :=
              norm_nonneg _
            linarith)
          (k : Real)))
  exact hsource.trans
    (by
      simpa [sourceBound, projectBound, radiusInv] using
        mul_le_mul_of_nonneg_right hsourceBound_le_projectBound
          hradiusInv_nonneg)

/--
The source real/Fourier finite-component estimate gives a direct closed-ball
p-series shell bound for the actual real zero-side weight.

This is the pointwise `system.weight` consequence of the exact source estimate:
the project-side real/Fourier indexed-tail majorant bounds the zero-argument
extension, and the closed-ball first-entry comparison converts that shifted
radius bound to the denominator used by the direct p-series route.
-/
theorem source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
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
    norm (system.weight (testData.toSchwartz g) rho) <=
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
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
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
  have hprojectBound_nonneg : 0 <= projectBound := by
    simpa [projectBound] using
      finiteComponentRealFourierIndexedTailMajorant_nonneg
        (system := system) stripRealMajorant stripFourierMajorant
        tailMajorant stripRealMajorant_nonneg stripFourierMajorant_nonneg
        tailMajorant_nonneg cutoff k (testData.toSchwartz g)
  have hzeroArgument_norm_le :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        projectBound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [projectBound] using
      source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
        (system := system) testData sourceComponent
        sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
        sourceTailComparisonComponentConstant stripRealMajorant
        stripFourierMajorant tailMajorant
        sourceStripRealComparisonConstant_nonneg
        sourceStripFourierComparisonConstant_nonneg
        sourceTailComparisonComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_norm_le_real_fourier
        source_component_tail_axis_norm_le_realHeight
        source_stripRealComparisonConstant_le_majorant
        source_stripFourierComparisonConstant_le_majorant
        source_tailComparisonComponentConstant_le_majorant
        g hg rho
  simpa [projectBound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) (f := testData.toSchwartz g) (rho := rho)
      (bound := projectBound) (k := k) hprojectBound_nonneg
      hzeroArgument_norm_le

/--
Source-side real/Fourier project-majorant decay in the weighted zero-locus
form.

This is the algebraic companion to the exact p-series denominator estimate
above.  The denominator form is multiplied by the strictly positive shifted
radius power, producing the weighted inequality consumed by the dense
closedness route.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
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
  have hnorm :
      norm (system.extension (testData.toSchwartz g) zeroArgument) <=
        projectBound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, projectBound] using
      source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
        (system := system) testData sourceComponent
        sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
        sourceTailComparisonComponentConstant stripRealMajorant
        stripFourierMajorant tailMajorant
        sourceStripRealComparisonConstant_nonneg
        sourceStripFourierComparisonConstant_nonneg
        sourceTailComparisonComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_norm_le_real_fourier
        source_component_tail_axis_norm_le_realHeight
        source_stripRealComparisonConstant_le_majorant
        source_stripFourierComparisonConstant_le_majorant
        source_tailComparisonComponentConstant_le_majorant
        g hg rho
  simpa [zeroArgument, projectBound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound) hnorm

/--
Source-side real/Fourier project-majorant weighted decay survives enlarging
the finite prefix cutoff.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants_mono_cutoff
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
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              tailMajorant i (testData.toSchwartz g)) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g)) := by
  have hbase :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      g hg rho
  have hmono :=
    finiteComponentRealFourierIndexedTailMajorant_mono_cutoff
      (system := system) stripRealMajorant stripFourierMajorant tailMajorant
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff
      (testData.toSchwartz g)
  exact hbase.trans hmono

/--
Source-side real/Fourier project-majorant exact-norm decay survives enlarging
the finite prefix cutoff.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants_mono_cutoff
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
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              tailMajorant i (testData.toSchwartz g)) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
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
          (system := system) cutoff' k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            tailMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= projectBound := by
    simpa [zeroArgument, projectBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants_mono_cutoff
        (system := system) testData sourceComponent
        sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
        sourceTailComparisonComponentConstant stripRealMajorant
        stripFourierMajorant tailMajorant
        sourceStripRealComparisonConstant_nonneg
        sourceStripFourierComparisonConstant_nonneg
        sourceTailComparisonComponentConstant_nonneg hcutoff
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_norm_le_real_fourier
        source_component_tail_axis_norm_le_realHeight
        source_stripRealComparisonConstant_le_majorant
        source_stripFourierComparisonConstant_le_majorant
        source_tailComparisonComponentConstant_le_majorant
        g hg rho
  simpa [zeroArgument, projectBound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound)
      hweighted

/--
Eventual source real/Fourier exact-norm decay promoted to project-side
continuous majorants.

This is the source-majorant form expected from an analytic proof: component
strip bounds are controlled by source real/Fourier profiles, the indexed
trivial-axis decomposition and tail domination hold only eventually, and the
source component constants are bounded by project-side majorants. Lean extracts
the cutoff, rewrites the source Fourier profile to project Fourier, and keeps
the finite prefix explicit in the exact p-series denominator bound.
-/
theorem exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
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
    exists cutoff : Nat,
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
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
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
Eventual source real/Fourier finite-component estimates give a direct
closed-ball p-series shell bound for the actual real zero-side weight.

This is the eventual-tail version of
`source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants`:
Lean extracts the indexed trivial-axis cutoff from the source theorem
hypotheses and immediately lands in the direct `system.weight` shell bound
consumed by the polynomial-counting p-series route.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight (testData.toSchwartz g) rho) <=
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
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      g hg rho

/--
Eventually-valid source real/Fourier project-majorant shell bound for the
actual real zero-side weight.

The finite-component real/Fourier source hypotheses keep the direct
closed-ball `system.weight` shell estimate valid for every sufficiently large
indexed-tail cutoff, before any polynomial counting assumption is applied.
-/
theorem eventually_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    (hg : testData.admissible g) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight (testData.toSchwartz g) rho) <=
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
                      sourceTailComparisonComponentConstant i g *
                        norm
                          ((testData.toSchwartz g)
                            (riemannWeilTrivialZeroArgumentHeight n))))
        (Filter.atTop : Filter Nat) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff rho =>
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      g hg rho

/--
Single-component source real/Fourier eventual-tail estimates give the
exact-denominator zero-locus bound with project-side majorants.

This is the source-facing exact form for analytic proofs that estimate the
extension itself. Lean specializes the finite-component theorem to one
component and discharges the strip and tail finite-sum identities automatically.
-/
theorem exists_cutoff_source_zeroArgument_norm_le_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonConstant :
      testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      SchwartzLineTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant g)
    (sourceTailComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonConstant g)
    (k : Nat)
    (source_strip_norm_le_real_fourier :
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
    (source_tail_axis_norm_le_realHeight_eventually :
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
    (sourceStripRealComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripRealComparisonConstant g <=
            stripRealMajorant (testData.toSchwartz g))
    (sourceStripFourierComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripFourierComparisonConstant g <=
            stripFourierMajorant (testData.toSchwartz g))
    (sourceTailComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceTailComparisonConstant g <=
            tailMajorant (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
            (stripRealMajorant (testData.toSchwartz g) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g) +
              stripFourierMajorant (testData.toSchwartz g) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier
                    (testData.toSchwartz g))) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            tailMajorant (testData.toSchwartz g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g))) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
  simpa using
    exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
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
      g hg rho

/--
Single-component source real/Fourier eventual-tail estimates give the weighted
zero-locus bound with project-side majorants.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonConstant :
      testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      SchwartzLineTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant g)
    (sourceTailComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonConstant g)
    (k : Nat)
    (source_strip_norm_le_real_fourier :
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
    (source_tail_axis_norm_le_realHeight_eventually :
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
    (sourceStripRealComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripRealComparisonConstant g <=
            stripRealMajorant (testData.toSchwartz g))
    (sourceStripFourierComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripFourierComparisonConstant g <=
            stripFourierMajorant (testData.toSchwartz g))
    (sourceTailComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceTailComparisonConstant g <=
            tailMajorant (testData.toSchwartz g))
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
            (stripRealMajorant (testData.toSchwartz g) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g) +
              stripFourierMajorant (testData.toSchwartz g) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier
                    (testData.toSchwartz g))) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            tailMajorant (testData.toSchwartz g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g)) := by
  rcases
    exists_cutoff_source_zeroArgument_norm_le_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceStripRealComparisonConstant
      sourceStripFourierComparisonConstant sourceTailComparisonConstant
      stripRealMajorant stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonConstant_nonneg k
      source_strip_norm_le_real_fourier
      source_tail_axis_norm_le_realHeight_eventually
      sourceStripRealComparisonConstant_le_majorant
      sourceStripFourierComparisonConstant_le_majorant
      sourceTailComparisonConstant_le_majorant g hg rho with
  ⟨cutoff, hnorm⟩
  refine ⟨cutoff, ?_⟩
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (stripRealMajorant (testData.toSchwartz g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g) +
          stripFourierMajorant (testData.toSchwartz g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (SchwartzLineTestFunction.fourier
                (testData.toSchwartz g))) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        tailMajorant (testData.toSchwartz g) *
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
Single-component source real/Fourier eventual-tail estimates give a direct
closed-ball p-series shell bound for the actual real zero-side weight.

This is the source-estimate form for analytic proofs that bound the extension
itself by admitted real and Fourier profiles, with the indexed trivial-axis
tail only eventually controlled. Lean specializes the finite-component theorem
to one component and discharges the finite-sum identities automatically.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_realFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonConstant :
      testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      SchwartzLineTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant g)
    (sourceTailComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonConstant g)
    (stripRealMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripRealMajorant f)
    (stripFourierMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripFourierMajorant f)
    (tailMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailMajorant f)
    (k : Nat)
    (source_strip_norm_le_real_fourier :
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
    (source_tail_axis_norm_le_realHeight_eventually :
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
    (sourceStripRealComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripRealComparisonConstant g <=
            stripRealMajorant (testData.toSchwartz g))
    (sourceStripFourierComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripFourierComparisonConstant g <=
            stripFourierMajorant (testData.toSchwartz g))
    (sourceTailComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceTailComparisonConstant g <=
            tailMajorant (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight (testData.toSchwartz g) rho) <=
          ((2 : Real) ^ k *
              (stripRealMajorant (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g) +
                stripFourierMajorant (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (SchwartzLineTestFunction.fourier
                      (testData.toSchwartz g))) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) +
              tailMajorant (testData.toSchwartz g) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g))) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  simpa using
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
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
      g hg

/--
Eventually-valid single-component source real/Fourier project-majorant shell
bound for the actual real zero-side weight.

This keeps the direct `system.weight` shell estimate available at every
sufficiently large indexed-tail cutoff before a counting estimate chooses the
p-series package.
-/
theorem eventually_source_weight_norm_le_closedBall_cutoffOneShellBound_of_realFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonConstant :
      testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      SchwartzLineTestFunction -> Real)
    (sourceStripRealComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripRealComparisonConstant g)
    (sourceStripFourierComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripFourierComparisonConstant g)
    (sourceTailComparisonConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceTailComparisonConstant g)
    (stripRealMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripRealMajorant f)
    (stripFourierMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripFourierMajorant f)
    (tailMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailMajorant f)
    (k : Nat)
    (source_strip_norm_le_real_fourier :
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
    (source_tail_axis_norm_le_realHeight_eventually :
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
    (sourceStripRealComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripRealComparisonConstant g <=
            stripRealMajorant (testData.toSchwartz g))
    (sourceStripFourierComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripFourierComparisonConstant g <=
            stripFourierMajorant (testData.toSchwartz g))
    (sourceTailComparisonConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceTailComparisonConstant g <=
            tailMajorant (testData.toSchwartz g))
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight (testData.toSchwartz g) rho) <=
            ((2 : Real) ^ k *
                (stripRealMajorant (testData.toSchwartz g) *
                    schwartzLineRealAxisShiftedSeminormConstant k
                      (testData.toSchwartz g) +
                  stripFourierMajorant (testData.toSchwartz g) *
                    schwartzLineRealAxisShiftedSeminormConstant k
                      (SchwartzLineTestFunction.fourier
                        (testData.toSchwartz g))) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k (testData.toSchwartz g) +
                tailMajorant (testData.toSchwartz g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g))) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
  simpa using
    eventually_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_of_majorants
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
      g hg

/--
Eventual source real/Fourier project-majorant estimates plus cutoff-1
closed-ball polynomial counting give absolute summability of the actual
zero-side weight for a fixed admissible source test.

This is the source-test endpoint needed after extracting the indexed trivial
axis cutoff: the proof builds the abstract direct-weight polynomial decay
record with that single cutoff and feeds it to the checked polynomial
counting p-series machinery.
-/
theorem summable_norm_source_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant g hg with
    ⟨cutoff, hshell⟩
  let sourceF : SchwartzLineTestFunction := testData.toSchwartz g
  let sourceConstant : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripRealMajorant i sourceF *
              schwartzLineRealAxisShiftedSeminormConstant k sourceF +
            stripFourierMajorant i sourceF *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier sourceF)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k sourceF +
        (Finset.univ.sum fun i : Index => tailMajorant i sourceF) *
          schwartzLineRealAxisShiftedSeminormConstant k sourceF)
  have hsourceConstant_nonneg : 0 <= sourceConstant := by
    simpa [sourceConstant, sourceF] using
      finiteComponentRealFourierIndexedTailMajorant_nonneg
        (system := system) stripRealMajorant stripFourierMajorant
        tailMajorant stripRealMajorant_nonneg
        stripFourierMajorant_nonneg tailMajorant_nonneg cutoff k sourceF
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
The same fixed-source eventual majorant hypotheses make the signed
`system.weight` series summable for the admissible source test.

This consumes the absolute source-weight summability theorem above directly,
so the source-side route now reaches the actual zero-side series, not only its
norm.
-/
theorem summable_source_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    summable_norm_source_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k g hg
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

/--
Finite compact-exhaustion windows of the actual source-side `system.weight`
converge to the signed infinite zero-side series under the same eventual
source majorant and cutoff-1 closed-ball counting hypotheses.
-/
theorem tendsto_source_weight_zetaZeroWindowSum_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
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
            system.weight (testData.toSchwartz g) rho))) := by
  exact windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_source_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k g hg)

/--
The signed finite-window approximation error for the fixed source-side
`system.weight` series has norm tending to zero.
-/
theorem tendsto_source_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
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
    tendsto_source_weight_zetaZeroWindowSum_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
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
  have htail :
      Filter.Tendsto
        (fun n : Nat =>
          tsum
              (fun rho : ZetaZeroSubtype =>
                system.weight (testData.toSchwartz g) rho) -
            windowExhaustion.zetaZeroWindowSum n
              (system.weight (testData.toSchwartz g)))
        Filter.atTop
        (nhds 0) := by
    simpa using hconst.sub hwindow
  simpa using htail.norm

/--
For every positive tolerance, the fixed source-side finite-window
approximation error is eventually below that tolerance.
-/
theorem eventually_source_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop,
      norm
          (tsum
              (fun rho : ZetaZeroSubtype =>
                system.weight (testData.toSchwartz g) rho) -
            windowExhaustion.zetaZeroWindowSum n
              (system.weight (testData.toSchwartz g))) <
        epsilon := by
  simpa using
    (tendsto_source_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the fixed source-side `system.weight` series outside
growing compact zero windows tends to zero.
-/
theorem tendsto_norm_source_weight_zetaZeroWindowTail_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
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
    summable_norm_source_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
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
For every positive tolerance, the absolute norm tail of the fixed source-side
`system.weight` series is eventually below that tolerance.
-/
theorem eventually_norm_source_weight_zetaZeroWindowTail_lt_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
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
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
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
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    ∀ᶠ n in Filter.atTop,
      tsum
          (fun rho : ZetaZeroSubtype =>
            norm (system.weight (testData.toSchwartz g) rho)) -
        windowExhaustion.zetaZeroWindowSum n
          (fun rho : ZetaZeroSubtype =>
            norm (system.weight (testData.toSchwartz g) rho)) <
      epsilon := by
  simpa using
    (tendsto_norm_source_weight_zetaZeroWindowTail_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight_eventually
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion g hg).eventually
      (Iio_mem_nhds hepsilon)

end RiemannHypothesisProject
