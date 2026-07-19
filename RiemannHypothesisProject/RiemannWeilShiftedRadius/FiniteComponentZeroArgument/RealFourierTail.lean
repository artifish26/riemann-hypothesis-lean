import RiemannHypothesisProject.RiemannWeilShiftedRadius.FiniteComponentZeroArgument.RealHeightTail

/-!
# Finite-component real-Fourier tails

This module contains the real/Fourier strip comparison estimates and final finite-component majorant bridge.
-/

namespace RiemannHypothesisProject
/--
Source-side finite-component p-series estimate from two real-line profiles.

This is the source-normalized analogue of the project real/Fourier strip
comparison route: each strip component may be bounded by the source test and
the packaged source Fourier transform on the real part, while the indexed
trivial-axis tail is bounded by the real-axis source image. Lean converts the
two real-line profile bounds to a real-radius strip envelope using the checked
Schwartz seminorm decay, then applies the source indexed-tail exact-norm
theorem.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
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
  let sourceStripComponentConstant :
      Index -> testData.SourceTestFunction -> Real :=
    fun i g =>
      sourceStripRealComparisonConstant i g *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g) +
        sourceStripFourierComparisonConstant i g *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.sourceFourier g)
  have hsourceStripComponent_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g := by
    intro i g hg
    exact add_nonneg
      (mul_nonneg (sourceStripRealComparisonConstant_nonneg i g hg)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
          (testData.toSchwartz g)))
      (mul_nonneg (sourceStripFourierComparisonConstant_nonneg i g hg)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
          (testData.sourceFourier g)))
  have hcomponent_strip :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) *
                      (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                    sourceStripComponentConstant i g := by
    intro i g hg z hlow hhigh
    have hnorm :=
      source_component_strip_norm_le_real_fourier i g hg z hlow hhigh
    simpa [sourceStripComponentConstant] using
      sourceRealFourierProfile_bound_weighted_norm_le_shiftedSeminormMajorant
        testData k g hg z (sourceComponent i g z)
        (sourceStripRealComparisonConstant i g)
        (sourceStripFourierComparisonConstant i g)
        (sourceStripRealComparisonConstant_nonneg i g hg)
        (sourceStripFourierComparisonConstant_nonneg i g hg) hnorm
  simpa [sourceStripComponentConstant] using
    source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceTailComparisonComponentConstant
      hsourceStripComponent_nonneg sourceTailComparisonComponentConstant_nonneg
      cutoff k source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum hcomponent_strip
      source_component_tail_axis_norm_le_realHeight g hg rho

/--
Source-side weighted zero-locus decay from two real-line profiles.

This is the direct weighted companion to
`source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail`:
it keeps the source real/Fourier strip constants and indexed trivial-axis
finite prefix explicit, then clears the shifted-radius denominator into the
weighted form consumed by zero-locus closedness arguments.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
  let sourceStripComponentConstant :
      Index -> testData.SourceTestFunction -> Real :=
    fun i g =>
      sourceStripRealComparisonConstant i g *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g) +
        sourceStripFourierComparisonConstant i g *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.sourceFourier g)
  have hsourceStripComponent_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g := by
    intro i g hg
    exact add_nonneg
      (mul_nonneg (sourceStripRealComparisonConstant_nonneg i g hg)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
          (testData.toSchwartz g)))
      (mul_nonneg (sourceStripFourierComparisonConstant_nonneg i g hg)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
          (testData.sourceFourier g)))
  have hcomponent_strip :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (sourceComponent i g z) *
                      (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                    sourceStripComponentConstant i g := by
    intro i g hg z hlow hhigh
    have hnorm :=
      source_component_strip_norm_le_real_fourier i g hg z hlow hhigh
    simpa [sourceStripComponentConstant] using
      sourceRealFourierProfile_bound_weighted_norm_le_shiftedSeminormMajorant
        testData k g hg z (sourceComponent i g z)
        (sourceStripRealComparisonConstant i g)
        (sourceStripFourierComparisonConstant i g)
        (sourceStripRealComparisonConstant_nonneg i g hg)
        (sourceStripFourierComparisonConstant_nonneg i g hg) hnorm
  simpa [sourceStripComponentConstant] using
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceTailComparisonComponentConstant
      hsourceStripComponent_nonneg sourceTailComparisonComponentConstant_nonneg
      cutoff k source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum hcomponent_strip
      source_component_tail_axis_norm_le_realHeight g hg rho

/--
Source-side real/Fourier indexed-tail weighted decay survives enlarging the
finite prefix cutoff.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_mono_cutoff
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
            sourceStripRealComparisonConstant i g *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g) +
              sourceStripFourierComparisonConstant i g *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.sourceFourier g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              sourceTailComparisonComponentConstant i g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g)) := by
  have hbase :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum
      source_component_strip_norm_le_real_fourier
      source_component_tail_axis_norm_le_realHeight
      g hg rho
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff (testData.toSchwartz g)
  linarith

/--
Source-side real/Fourier indexed-tail exact-denominator decay survives
enlarging the finite prefix cutoff.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_mono_cutoff
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
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
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              sourceTailComparisonComponentConstant i g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
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
          (system := system) cutoff' k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            sourceTailComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_mono_cutoff
        (system := system) testData sourceComponent
        sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
        sourceTailComparisonComponentConstant
        sourceStripRealComparisonConstant_nonneg
        sourceStripFourierComparisonConstant_nonneg
        sourceTailComparisonComponentConstant_nonneg hcutoff
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_norm_le_real_fourier
        source_component_tail_axis_norm_le_realHeight
        g hg rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted

/--
Source finite-component indexed-tail majorants are bounded by the corresponding
project-side majorants.

This is the real-radius analogue of
`sourceRealFourierIndexedTailMajorant_le_projectMajorant`: component strip and
tail constants are compared after mapping a source test through `toSchwartz`,
and Lean preserves the finite trivial-axis prefix while multiplying the tail
comparison by the shifted real-axis Schwartz seminorm.
-/
theorem sourceFiniteComponentIndexedTailMajorant_le_projectMajorant
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
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
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            sourceComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g)) <=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            comparisonMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g)) := by
  have hstrip_sum_le :
      (Finset.univ.sum fun i : Index => sourceStripComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_stripComponentConstant_le_majorant i g hg
  have hcomparison_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceComparisonComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          comparisonMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      source_comparisonComponentConstant_le_majorant i g hg
  have hstrip_scaled :
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) <=
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left hstrip_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  have hcomparison_scaled :
      (Finset.univ.sum fun i : Index =>
          sourceComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g) <=
        (Finset.univ.sum fun i : Index =>
          comparisonMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g) :=
    mul_le_mul_of_nonneg_right hcomparison_sum_le
      (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
        (testData.toSchwartz g))
  linarith

/--
Source-side indexed-tail exact-norm decay promoted to project-side majorants.

The analytic source estimate may produce component strip and tail constants
depending on the source test.  If those constants are bounded by project-side
majorants after mapping through `toSchwartz`, Lean obtains the exact p-series
denominator bound with the project-side real-radius indexed-tail majorant.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
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
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
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
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let sourceBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            sourceComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  let projectBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            comparisonMajorant i (testData.toSchwartz g)) *
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
      source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceComparisonComponentConstant
        sourceStripComponentConstant_nonneg
        sourceComparisonComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_norm_le_realHeight g hg rho
  have hsourceBound_le_projectBound : sourceBound <= projectBound := by
    simpa [sourceBound, projectBound] using
      sourceFiniteComponentIndexedTailMajorant_le_projectMajorant
        (system := system) testData sourceStripComponentConstant
        sourceComparisonComponentConstant stripMajorant comparisonMajorant
        cutoff k source_stripComponentConstant_le_majorant
        source_comparisonComponentConstant_le_majorant g hg
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
Source-side indexed-tail project-majorant decay in the weighted zero-locus
form.

This is the weighted companion to
`source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants`:
the source finite-component weighted estimate is promoted to the project-side
real-radius indexed-tail majorant directly.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
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
          (Finset.univ.sum fun i : Index =>
              comparisonMajorant i (testData.toSchwartz g)) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g)) := by
  let sourceBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            sourceComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  let projectBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            comparisonMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hsource :
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <= sourceBound := by
    simpa [sourceBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceComparisonComponentConstant
        sourceStripComponentConstant_nonneg
        sourceComparisonComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_norm_le_realHeight g hg rho
  have hsourceBound_le_projectBound : sourceBound <= projectBound := by
    simpa [sourceBound, projectBound] using
      sourceFiniteComponentIndexedTailMajorant_le_projectMajorant
        (system := system) testData sourceStripComponentConstant
        sourceComparisonComponentConstant stripMajorant comparisonMajorant
        cutoff k source_stripComponentConstant_le_majorant
        source_comparisonComponentConstant_le_majorant g hg
  exact hsource.trans hsourceBound_le_projectBound

/--
Source-side real-radius project-majorant weighted decay survives enlarging the
finite prefix cutoff.

The source tail proof is used at `cutoff`; the visible project-side majorant
may use any larger `cutoff'`.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants_mono_cutoff
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
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              comparisonMajorant i (testData.toSchwartz g)) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g)) := by
  have hbase :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
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
  have hmono :=
    finiteComponentRealIndexedTailMajorant_mono_cutoff
      (system := system) stripMajorant comparisonMajorant
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff
      (testData.toSchwartz g)
  exact hbase.trans hmono

/--
Source-side real-radius project-majorant exact-norm decay survives enlarging
the finite prefix cutoff.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants_mono_cutoff
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
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              comparisonMajorant i (testData.toSchwartz g)) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g))) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let projectBound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripMajorant i (testData.toSchwartz g)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            comparisonMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= projectBound := by
    simpa [zeroArgument, projectBound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants_mono_cutoff
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceComparisonComponentConstant
        stripMajorant comparisonMajorant
        sourceStripComponentConstant_nonneg
        sourceComparisonComponentConstant_nonneg hcutoff
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_norm_le_realHeight
        source_stripComponentConstant_le_majorant
        source_comparisonComponentConstant_le_majorant
        g hg rho
  simpa [zeroArgument, projectBound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := projectBound)
      hweighted

/--
Eventual source-side indexed-tail exact-norm decay promoted to project-side
majorants.

This is the eventual-tail source analogue of
`source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants`:
Lean extracts a cutoff from the eventual source decomposition and tail
domination hypotheses, then applies the fixed-cutoff project-majorant bound.
-/
theorem exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
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
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
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
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
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
  exact
    source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      g hg rho

/--
Eventual source-side project-majorant decay in the weighted zero-locus form.

This packages the same eventual source real-radius hypotheses as the exact
denominator estimate above, then returns the weighted inequality directly
against the project-side real-radius indexed-tail majorant.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_of_majorants
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
              stripMajorant i (testData.toSchwartz g)) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                comparisonMajorant i (testData.toSchwartz g)) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g)) := by
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
  exact
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      g hg rho

/--
Eventually-valid source real-radius exact-norm decay promoted to project-side
majorants.

This strengthens the existential eventual source-majorant route: once the
source indexed trivial-axis decomposition and tail domination hold eventually,
the project-side majorant exact denominator estimate holds for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
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
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
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
                    sourceComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n))) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      g hg rho

/--
Eventually-valid source real-radius weighted decay promoted to project-side
majorants.

The source asymptotic tail proof keeps the weighted project-majorant estimate
valid for every sufficiently large finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
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
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
            (Finset.univ.sum fun i : Index =>
                comparisonMajorant i (testData.toSchwartz g)) *
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
                    sourceComparisonComponentConstant i g *
                      norm
                        ((testData.toSchwartz g)
                          (riemannWeilTrivialZeroArgumentHeight n))) :=
    source_tail_axis_extension_eq_component_sum_eventually.and
      source_component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_of_majorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant
      g hg rho

/--
Source real/Fourier indexed-tail majorants are bounded by the corresponding
project-side majorants.

This is the positive source-to-project comparison used by the continuous
majorant route: source strip constants are compared componentwise to ambient
real/Fourier majorants, source Fourier is rewritten to the project Fourier
transform, and the indexed tail constants are compared under the same shifted
real-axis seminorm.
-/
theorem sourceRealFourierIndexedTailMajorant_le_projectMajorant
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (cutoff k : Nat)
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
            (testData.toSchwartz g)) <=
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
  have hsourceFourier :
      testData.sourceFourier g =
        SchwartzLineTestFunction.fourier (testData.toSchwartz g) :=
    testData.sourceFourier_eq_projectFourier g hg
  have hstrip_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceStripRealComparisonConstant i g *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) +
            sourceStripFourierComparisonConstant i g *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.sourceFourier g)) <=
        Finset.univ.sum fun i : Index =>
          stripRealMajorant i (testData.toSchwartz g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) +
            stripFourierMajorant i (testData.toSchwartz g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier
                  (testData.toSchwartz g)) := by
    refine Finset.sum_le_sum ?_
    intro i _hi
    have hreal :
        sourceStripRealComparisonConstant i g *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g) <=
          stripRealMajorant i (testData.toSchwartz g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g) :=
      mul_le_mul_of_nonneg_right
        (source_stripRealComparisonConstant_le_majorant i g hg)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
          (testData.toSchwartz g))
    have hfourier :
        sourceStripFourierComparisonConstant i g *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.sourceFourier g) <=
          stripFourierMajorant i (testData.toSchwartz g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (SchwartzLineTestFunction.fourier (testData.toSchwartz g)) := by
      have hle :
          sourceStripFourierComparisonConstant i g *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.sourceFourier g) <=
            stripFourierMajorant i (testData.toSchwartz g) *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.sourceFourier g) :=
        mul_le_mul_of_nonneg_right
          (source_stripFourierComparisonConstant_le_majorant i g hg)
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
            (testData.sourceFourier g))
      simpa [hsourceFourier] using hle
    exact add_le_add hreal hfourier
  have htail_sum_le :
      (Finset.univ.sum fun i : Index =>
          sourceTailComparisonComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          tailMajorant i (testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _hi =>
      source_tailComparisonComponentConstant_le_majorant i g hg
  have hstrip_scaled :
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripRealComparisonConstant i g *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g) +
              sourceStripFourierComparisonConstant i g *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.sourceFourier g)) <=
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripRealMajorant i (testData.toSchwartz g) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g) +
              stripFourierMajorant i (testData.toSchwartz g) *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier
                    (testData.toSchwartz g))) :=
    mul_le_mul_of_nonneg_left hstrip_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  have htail_scaled :
      (Finset.univ.sum fun i : Index =>
          sourceTailComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g) <=
        (Finset.univ.sum fun i : Index =>
          tailMajorant i (testData.toSchwartz g)) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g) :=
    mul_le_mul_of_nonneg_right htail_sum_le
      (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
        (testData.toSchwartz g))
  linarith

end RiemannHypothesisProject
