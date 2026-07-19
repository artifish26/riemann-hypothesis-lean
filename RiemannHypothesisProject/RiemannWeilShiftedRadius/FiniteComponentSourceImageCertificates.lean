import RiemannHypothesisProject.RiemannWeilShiftedRadius.DenseSourceCertificates

/-!
# Finite-component source-image shifted-radius certificates

This module contains finite-component source-image certificate constructors and
project dense-core wrappers for the shifted-radius p-series route.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion
open MeasureTheory
open scoped Topology

namespace RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Dense-source constructor for the componentwise repaired strip/axis route.

This is the source-normalized positive p-series target after the no-go
theorems for exact all-Schwartz coverage.  The analytic work is to prove a
dense admissible source image, continuity of fixed-zero evaluations and of the
global seminorm `constant`, finite-sum identities on the source class, and the
componentwise real-radius/positive-axis estimates.  The final domination field
lets the source component constants be packaged into any continuous global
seminorm suitable for the dense-closedness promotion.
-/
noncomputable def ofSourceDenseFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceAxisComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (constant : SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceAxisComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisComponentConstant i g)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (constant_continuous : Continuous constant)
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
    (source_component_bound_le_constant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          (2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  sourceStripComponentConstant i g) +
              (2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  sourceAxisComponentConstant i g) <=
            constant (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseWeightedDecayOfContinuous
    (system := system) testData constant k constant_nonneg (by positivity)
    dense_admissible_image zeroArgument_extension_continuous
    constant_continuous
    (by
      intro g hg rho
      exact
        (source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
          (system := system) testData sourceComponent
          sourceStripComponentConstant sourceAxisComponentConstant
          sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
          k source_strip_extension_eq_component_sum
          source_axis_extension_eq_component_sum
          source_component_strip_weighted_norm_le_realRadius
      source_component_axis_oneAdd_weighted_norm_le g hg rho).trans
          (source_component_bound_le_constant g hg))

/--
Dense-source constructor for the componentwise indexed-tail p-series route.

Use this when the source decomposition is only known on a dense admissible
source class and the positive-axis work has been reduced to the explicit
trivial-zero sequence. The caller supplies a continuous ambient `constant`
dominating the checked source prefix/tail expression.
-/
noncomputable def ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (constant : SchwartzLineTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (cutoff k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (constant_continuous : Continuous constant)
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
    (source_component_bound_le_constant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          (2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  sourceStripComponentConstant i g) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k (testData.toSchwartz g) +
                (Finset.univ.sum fun i : Index =>
                    sourceComparisonComponentConstant i g) *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (testData.toSchwartz g)) <=
            constant (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseWeightedDecayOfContinuous
    (system := system) testData constant k constant_nonneg (by positivity)
    dense_admissible_image zeroArgument_extension_continuous
    constant_continuous
    (by
      intro g hg rho
      exact
        (source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
          (system := system) testData sourceComponent
          sourceStripComponentConstant sourceComparisonComponentConstant
          sourceStripComponentConstant_nonneg
          sourceComparisonComponentConstant_nonneg cutoff k
          source_strip_extension_eq_component_sum
          source_tail_axis_extension_eq_component_sum
          source_component_strip_weighted_norm_le_realRadius
          source_component_tail_axis_norm_le_realHeight g hg rho).trans
          (source_component_bound_le_constant g hg))

/--
Dense-source componentwise indexed-tail constructor with continuous global
majorants.

This is the explicit-cutoff analogue of
`ofSourceDenseFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants`.
Lean assembles the ambient certificate constant from continuous strip
majorants, the automatic finite trivial-axis prefix, and continuous tail
majorants multiplying the checked real-axis Schwartz seminorm.  The remaining
analytic inputs are the dense source image, continuity of fixed zero
evaluations and prefix trivial-axis evaluations, source strip/tail
decompositions, component estimates, and majorant inequalities.
-/
noncomputable def ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
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
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (comparisonMajorant_continuous :
      forall i : Index, Continuous (comparisonMajorant i))
    (cutoff k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I))
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
              comparisonMajorant i (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let constant : SchwartzLineTestFunction -> Real := fun f =>
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripMajorant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (Finset.univ.sum fun i : Index => comparisonMajorant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  refine
    ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuous
      (system := system) testData sourceComponent sourceStripComponentConstant
      sourceComparisonComponentConstant constant
      sourceStripComponentConstant_nonneg sourceComparisonComponentConstant_nonneg
      ?_ cutoff k dense_admissible_image zeroArgument_extension_continuous
      ?_ source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight ?_
  · intro f
    simpa [constant] using
      finiteComponentRealIndexedTailMajorant_nonneg
        (system := system) stripMajorant comparisonMajorant
        stripMajorant_nonneg comparisonMajorant_nonneg cutoff k f
  · simpa [constant] using
      finiteComponentRealIndexedTailMajorant_continuous
        (system := system) stripMajorant comparisonMajorant
        stripMajorant_continuous comparisonMajorant_continuous cutoff k
        prefix_trivialAxis_extension_continuous
  · intro g hg
    simpa [constant] using
      sourceFiniteComponentIndexedTailMajorant_le_projectMajorant
        (system := system) testData sourceStripComponentConstant
        sourceComparisonComponentConstant stripMajorant comparisonMajorant
        cutoff k source_stripComponentConstant_le_majorant
        source_comparisonComponentConstant_le_majorant g hg

/--
Dense-source real-radius indexed-tail constructor with eventual tail hypotheses
and continuous global majorants.

This is the real-radius source-image analogue of the eventual real/Fourier
route: strip decomposition and component real-radius envelopes hold on
admissible source tests, while the indexed trivial-axis decomposition and
real-height tail domination only need to hold eventually. Lean extracts a
uniform cutoff and reuses the fixed-cutoff continuous-majorant constructor.
-/
noncomputable def ofSourceDenseFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
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
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (comparisonMajorant_continuous :
      forall i : Index, Continuous (comparisonMajorant i))
    (k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (trivialAxis_extension_continuous :
      forall n : Nat,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
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
              comparisonMajorant i (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  classical
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
  let cutoff : Nat := Classical.choose htail_eventually
  have hcutoff_all := Classical.choose_spec htail_eventually
  have hcutoff := hcutoff_all cutoff le_rfl
  exact
    ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      stripMajorant comparisonMajorant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg
      stripMajorant_nonneg comparisonMajorant_nonneg
      stripMajorant_continuous comparisonMajorant_continuous cutoff k
      dense_admissible_image zeroArgument_extension_continuous
      (fun n _hn => trivialAxis_extension_continuous n)
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_comparisonComponentConstant_le_majorant

/--
Dense-source componentwise indexed one-add tail constructor with continuous
global majorants.

This is the source-image certificate form of the indexed `(1 + y)^k` route.
The strip side is controlled by real-radius component envelopes, while the
trivial-axis contribution is supplied directly at the indexed trivial-zero
heights. Lean assembles the continuous project-side one-add indexed-tail
majorant and applies dense closedness to the weighted zero-locus estimate.
-/
noncomputable def ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTailOfContinuousMajorants
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
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (cutoff k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I))
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
              axisMajorant i (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let constant : SchwartzLineTestFunction -> Real := fun f =>
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripMajorant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisMajorant i f))
  refine
    ofSourceDenseWeightedDecayOfContinuous
      (system := system) testData constant k ?_ (by positivity)
      dense_admissible_image zeroArgument_extension_continuous ?_ ?_
  · intro f
    simpa [constant] using
      finiteComponentOneAddIndexedTailMajorant_nonneg
        (system := system) stripMajorant axisMajorant
        stripMajorant_nonneg axisMajorant_nonneg cutoff k f
  · simpa [constant] using
      finiteComponentOneAddIndexedTailMajorant_continuous
        (system := system) stripMajorant axisMajorant
        stripMajorant_continuous axisMajorant_continuous cutoff k
        prefix_trivialAxis_extension_continuous
  · intro g hg rho
    simpa [constant] using
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
        source_axisComponentConstant_le_majorant
        g hg rho

/--
Dense-source componentwise indexed one-add tail constructor with eventual tail
hypotheses and continuous global majorants.

The source strip decomposition and real-radius component envelopes hold on
admissible source tests, while the indexed trivial-axis decomposition and
component `(1 + y)^k` estimates may hold only eventually. Lean extracts a
uniform cutoff and then uses the fixed-cutoff one-add certificate constructor.
-/
noncomputable def ofSourceDenseFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTailOfContinuousMajorants
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
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (trivialAxis_extension_continuous :
      forall n : Nat,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
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
              axisMajorant i (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  classical
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
  let cutoff : Nat := Classical.choose htail_eventually
  have hcutoff_all := Classical.choose_spec htail_eventually
  have hcutoff := hcutoff_all cutoff le_rfl
  exact
    ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTailOfContinuousMajorants
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      stripMajorant axisMajorant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      stripMajorant_nonneg axisMajorant_nonneg
      stripMajorant_continuous axisMajorant_continuous cutoff k
      dense_admissible_image zeroArgument_extension_continuous
      (fun n _hn => trivialAxis_extension_continuous n)
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripComponentConstant_le_majorant
      source_axisComponentConstant_le_majorant

/--
Dense-source componentwise real/Fourier indexed-tail constructor with
continuous global majorants.

This is the source-image certificate form of the real/Fourier route: source
strip components may be bounded by the admitted source test and its packaged
source Fourier transform, while the indexed trivial-axis contribution is
controlled by a real-height tail.  Lean assembles the project-side continuous
majorant, rewrites the source Fourier profile to the project Fourier transform
inside the weighted source theorem, and then applies dense closedness.
-/
noncomputable def ofSourceDenseFiniteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
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
    (stripRealMajorant_continuous :
      forall i : Index, Continuous (stripRealMajorant i))
    (stripFourierMajorant_continuous :
      forall i : Index, Continuous (stripFourierMajorant i))
    (tailMajorant_continuous :
      forall i : Index, Continuous (tailMajorant i))
    (cutoff k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I))
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
              tailMajorant i (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let constant : SchwartzLineTestFunction -> Real := fun f =>
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
          schwartzLineRealAxisShiftedSeminormConstant k f)
  refine
    ofSourceDenseWeightedDecayOfContinuous
      (system := system) testData constant k ?_ (by positivity)
      dense_admissible_image zeroArgument_extension_continuous ?_ ?_
  · intro f
    simpa [constant] using
      finiteComponentRealFourierIndexedTailMajorant_nonneg
        (system := system) stripRealMajorant stripFourierMajorant
        tailMajorant stripRealMajorant_nonneg
        stripFourierMajorant_nonneg tailMajorant_nonneg cutoff k f
  · simpa [constant] using
      finiteComponentRealFourierIndexedTailMajorant_continuous
        (system := system) stripRealMajorant stripFourierMajorant
        tailMajorant stripRealMajorant_continuous
        stripFourierMajorant_continuous tailMajorant_continuous cutoff k
        prefix_trivialAxis_extension_continuous
  · intro g hg rho
    simpa [constant] using
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

/--
Dense-source componentwise real/Fourier indexed-tail constructor with eventual
tail hypotheses and continuous global majorants.

This is the analytic source-class shape expected in practice: the strip
decomposition and real/Fourier strip comparison hold on admissible source
tests, while the indexed trivial-axis decomposition and real-height tail
domination only hold eventually.  Lean extracts a uniform cutoff from those
eventual hypotheses and then applies the fixed-cutoff source-image closedness
constructor.
-/
noncomputable def ofSourceDenseFiniteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
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
    (stripRealMajorant_continuous :
      forall i : Index, Continuous (stripRealMajorant i))
    (stripFourierMajorant_continuous :
      forall i : Index, Continuous (stripFourierMajorant i))
    (tailMajorant_continuous :
      forall i : Index, Continuous (tailMajorant i))
    (k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (trivialAxis_extension_continuous :
      forall n : Nat,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
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
              tailMajorant i (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  classical
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
  let cutoff : Nat := Classical.choose htail_eventually
  have hcutoff_all := Classical.choose_spec htail_eventually
  have hcutoff := hcutoff_all cutoff le_rfl
  exact
    ofSourceDenseFiniteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
      (system := system) testData sourceComponent
      sourceStripRealComparisonConstant sourceStripFourierComparisonConstant
      sourceTailComparisonComponentConstant stripRealMajorant
      stripFourierMajorant tailMajorant
      sourceStripRealComparisonConstant_nonneg
      sourceStripFourierComparisonConstant_nonneg
      sourceTailComparisonComponentConstant_nonneg
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg stripRealMajorant_continuous
      stripFourierMajorant_continuous tailMajorant_continuous cutoff k
      dense_admissible_image zeroArgument_extension_continuous
      (fun n _hn => trivialAxis_extension_continuous n)
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_norm_le_real_fourier
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      source_stripRealComparisonConstant_le_majorant
      source_stripFourierComparisonConstant_le_majorant
      source_tailComparisonComponentConstant_le_majorant

/--
Single-component dense-source real/Fourier indexed-tail constructor with
eventual tail hypotheses and continuous global majorants.

Use this when the restricted source proof estimates the extension itself by a
real/Fourier strip comparison and an eventual indexed trivial-axis real-height
tail. Lean specializes the finite-component source-image constructor to a
one-component decomposition, so the analytic source proof does not have to
manufacture a separate finite-sum identity.
-/
noncomputable def ofSourceDenseRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
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
    (stripRealMajorant_continuous : Continuous stripRealMajorant)
    (stripFourierMajorant_continuous : Continuous stripFourierMajorant)
    (tailMajorant_continuous : Continuous tailMajorant)
    (k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (trivialAxis_extension_continuous :
      forall n : Nat,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
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
            tailMajorant (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseFiniteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
    (system := system) (testData := testData) (Index := Unit)
    (sourceComponent := fun _ g z => system.extension (testData.toSchwartz g) z)
    (sourceStripRealComparisonConstant :=
      fun _ g => sourceStripRealComparisonConstant g)
    (sourceStripFourierComparisonConstant :=
      fun _ g => sourceStripFourierComparisonConstant g)
    (sourceTailComparisonComponentConstant :=
      fun _ g => sourceTailComparisonConstant g)
    (stripRealMajorant := fun _ f => stripRealMajorant f)
    (stripFourierMajorant := fun _ f => stripFourierMajorant f)
    (tailMajorant := fun _ f => tailMajorant f)
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
    (by
      intro _
      exact stripRealMajorant_continuous)
    (by
      intro _
      exact stripFourierMajorant_continuous)
    (by
      intro _
      exact tailMajorant_continuous)
    k dense_admissible_image zeroArgument_extension_continuous
    trivialAxis_extension_continuous
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

/--
Dense-source componentwise strip/axis constructor with a global seminorm built
from continuous component majorants.

This is the preferred analytic shape when the source component constants are
defined only on admissible source tests but are controlled by global continuous
Schwartz seminorms.  Lean assembles the global certificate constant from those
majorants and proves its nonnegativity and continuity.
-/
noncomputable def ofSourceDenseFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants
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
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
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
              axisMajorant i (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let constant : SchwartzLineTestFunction -> Real := fun f =>
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripMajorant i f) +
      (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => axisMajorant i f)
  refine
    ofSourceDenseFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuous
      (system := system) testData sourceComponent sourceStripComponentConstant
      sourceAxisComponentConstant constant sourceStripComponentConstant_nonneg
      sourceAxisComponentConstant_nonneg ?_ k dense_admissible_image
      zeroArgument_extension_continuous ?_ source_strip_extension_eq_component_sum
      source_axis_extension_eq_component_sum
      source_component_strip_weighted_norm_le_realRadius
      source_component_axis_oneAdd_weighted_norm_le ?_
  · intro f
    have hstrip_sum_nonneg :
        0 <= Finset.univ.sum fun i : Index => stripMajorant i f := by
      exact Finset.sum_nonneg fun i _ => stripMajorant_nonneg i f
    have haxis_sum_nonneg :
        0 <= Finset.univ.sum fun i : Index => axisMajorant i f := by
      exact Finset.sum_nonneg fun i _ => axisMajorant_nonneg i f
    dsimp [constant]
    exact add_nonneg
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        hstrip_sum_nonneg)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        haxis_sum_nonneg)
  · have hstrip_cont :
        Continuous fun f : SchwartzLineTestFunction =>
          Finset.univ.sum fun i : Index => stripMajorant i f := by
      simpa using
        (continuous_finsetSum
          (s := (Finset.univ : Finset Index))
          (f := fun i f => stripMajorant i f)
          (fun i _hi => stripMajorant_continuous i))
    have haxis_cont :
        Continuous fun f : SchwartzLineTestFunction =>
          Finset.univ.sum fun i : Index => axisMajorant i f := by
      simpa using
        (continuous_finsetSum
          (s := (Finset.univ : Finset Index))
          (f := fun i f => axisMajorant i f)
          (fun i _hi => axisMajorant_continuous i))
    dsimp [constant]
    exact (continuous_const.mul hstrip_cont).add
      (continuous_const.mul haxis_cont)
  · intro g hg
    have hstrip_sum_le :
        (Finset.univ.sum fun i : Index => sourceStripComponentConstant i g) <=
          Finset.univ.sum fun i : Index =>
            stripMajorant i (testData.toSchwartz g) :=
      Finset.sum_le_sum fun i _ =>
        source_stripComponentConstant_le_majorant i g hg
    have haxis_sum_le :
        (Finset.univ.sum fun i : Index => sourceAxisComponentConstant i g) <=
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
    dsimp [constant]
    linarith

/--
First-class actual-source finite-component strip/positive-axis p-series target.

This names the preferred post-closedness work package for a concrete
Guinand-Weil source class: prove dense admissible image, fixed-zero evaluation
continuity, finite component decompositions on the strip and positive imaginary
axis, component estimates, and continuous global majorants.  Lean then packages
the resulting finite-component estimate as a source-image zero-locus target.
-/
structure RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
    (Index : Type*) [Fintype Index]
    (system : SchwartzRiemannWeilExtensionSystem) where
  testData : GuinandWeilSourceTestFunctionClass
  dense_admissible_image :
    closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ
  sourceComponent :
    Index -> testData.SourceTestFunction -> Complex -> Complex
  sourceStripComponentConstant :
    Index -> testData.SourceTestFunction -> Real
  sourceAxisComponentConstant :
    Index -> testData.SourceTestFunction -> Real
  stripMajorant :
    Index -> SchwartzLineTestFunction -> Real
  axisMajorant :
    Index -> SchwartzLineTestFunction -> Real
  sourceStripComponentConstant_nonneg :
    forall i : Index, forall g : testData.SourceTestFunction,
      testData.admissible g -> 0 <= sourceStripComponentConstant i g
  sourceAxisComponentConstant_nonneg :
    forall i : Index, forall g : testData.SourceTestFunction,
      testData.admissible g -> 0 <= sourceAxisComponentConstant i g
  stripMajorant_nonneg :
    forall i : Index, forall f : SchwartzLineTestFunction,
      0 <= stripMajorant i f
  axisMajorant_nonneg :
    forall i : Index, forall f : SchwartzLineTestFunction,
      0 <= axisMajorant i f
  stripMajorant_continuous :
    forall i : Index, Continuous (stripMajorant i)
  axisMajorant_continuous :
    forall i : Index, Continuous (axisMajorant i)
  k : Nat
  zeroArgument_extension_continuous :
    forall rho : ZetaZeroSubtype,
      Continuous fun f : SchwartzLineTestFunction =>
        system.extension f (riemannWeilZeroArgument (rho : Complex))
  source_strip_extension_eq_component_sum :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension (testData.toSchwartz g) z =
                Finset.univ.sum fun i : Index => sourceComponent i g z
  source_axis_extension_eq_component_sum :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        forall y : Real,
          0 <= y ->
            system.extension (testData.toSchwartz g)
                ((y : Complex) * Complex.I) =
              Finset.univ.sum fun i : Index =>
                sourceComponent i g ((y : Complex) * Complex.I)
  source_component_strip_weighted_norm_le_realRadius :
    forall i : Index,
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (sourceComponent i g z) *
                    (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                  sourceStripComponentConstant i g
  source_component_axis_oneAdd_weighted_norm_le :
    forall i : Index,
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall y : Real,
            0 <= y ->
              norm
                  (sourceComponent i g ((y : Complex) * Complex.I)) *
                  (1 + y) ^ (k : Real) <=
                sourceAxisComponentConstant i g
  source_stripComponentConstant_le_majorant :
    forall i : Index,
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripComponentConstant i g <=
            stripMajorant i (testData.toSchwartz g)
  source_axisComponentConstant_le_majorant :
    forall i : Index,
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceAxisComponentConstant i g <=
            axisMajorant i (testData.toSchwartz g)

namespace RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget

/-- The global continuous certificate constant assembled from component majorants. -/
noncomputable def constant
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system) :
    SchwartzLineTestFunction -> Real :=
  fun f =>
    (2 : Real) ^ target.k *
        (Finset.univ.sum fun i : Index => target.stripMajorant i f) +
      (2 : Real) ^ target.k *
        (Finset.univ.sum fun i : Index => target.axisMajorant i f)

/-- The decay exponent supplied by the finite-component source theorem. -/
def decayExponent
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system) :
    Real :=
  target.k

/-- The assembled majorant constant is nonnegative. -/
theorem constant_nonneg
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system) :
    forall f : SchwartzLineTestFunction, 0 <= target.constant f := by
  intro f
  have hstrip_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => target.stripMajorant i f := by
    exact Finset.sum_nonneg fun i _ => target.stripMajorant_nonneg i f
  have haxis_sum_nonneg :
      0 <= Finset.univ.sum fun i : Index => target.axisMajorant i f := by
    exact Finset.sum_nonneg fun i _ => target.axisMajorant_nonneg i f
  dsimp [constant]
  exact add_nonneg
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) target.k)
      hstrip_sum_nonneg)
    (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) target.k)
      haxis_sum_nonneg)

/-- The assembled majorant constant is continuous on the project Schwartz space. -/
theorem constant_continuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system) :
    Continuous target.constant := by
  have hstrip_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => target.stripMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => target.stripMajorant i f)
        (fun i _hi => target.stripMajorant_continuous i))
  have haxis_cont :
      Continuous fun f : SchwartzLineTestFunction =>
        Finset.univ.sum fun i : Index => target.axisMajorant i f := by
    simpa using
      (continuous_finsetSum
        (s := (Finset.univ : Finset Index))
        (f := fun i f => target.axisMajorant i f)
        (fun i _hi => target.axisMajorant_continuous i))
  change Continuous fun f : SchwartzLineTestFunction =>
    (2 : Real) ^ target.k *
        (Finset.univ.sum fun i : Index => target.stripMajorant i f) +
      (2 : Real) ^ target.k *
        (Finset.univ.sum fun i : Index => target.axisMajorant i f)
  exact (continuous_const.mul hstrip_cont).add
    (continuous_const.mul haxis_cont)

/-- Source component constants are dominated by the assembled global majorant. -/
theorem source_component_bound_le_constant
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (g : target.testData.SourceTestFunction)
    (hg : target.testData.admissible g) :
    (2 : Real) ^ target.k *
          (Finset.univ.sum fun i : Index =>
            target.sourceStripComponentConstant i g) +
        (2 : Real) ^ target.k *
          (Finset.univ.sum fun i : Index =>
            target.sourceAxisComponentConstant i g) <=
      target.constant (target.testData.toSchwartz g) := by
  have hstrip_sum_le :
      (Finset.univ.sum fun i : Index =>
        target.sourceStripComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          target.stripMajorant i (target.testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      target.source_stripComponentConstant_le_majorant i g hg
  have haxis_sum_le :
      (Finset.univ.sum fun i : Index =>
        target.sourceAxisComponentConstant i g) <=
        Finset.univ.sum fun i : Index =>
          target.axisMajorant i (target.testData.toSchwartz g) :=
    Finset.sum_le_sum fun i _ =>
      target.source_axisComponentConstant_le_majorant i g hg
  have hstrip_scaled :
      (2 : Real) ^ target.k *
          (Finset.univ.sum fun i : Index =>
            target.sourceStripComponentConstant i g) <=
        (2 : Real) ^ target.k *
          (Finset.univ.sum fun i : Index =>
            target.stripMajorant i (target.testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left hstrip_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= 2) target.k)
  have haxis_scaled :
      (2 : Real) ^ target.k *
          (Finset.univ.sum fun i : Index =>
            target.sourceAxisComponentConstant i g) <=
        (2 : Real) ^ target.k *
          (Finset.univ.sum fun i : Index =>
            target.axisMajorant i (target.testData.toSchwartz g)) :=
    mul_le_mul_of_nonneg_left haxis_sum_le
      (pow_nonneg (by norm_num : (0 : Real) <= 2) target.k)
  dsimp [constant]
  linarith

/--
The finite-component strip/positive-axis package supplies the source-image
zero-locus weighted estimate on admissible source tests.
-/
theorem source_zeroArgument_weighted_norm_le
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system)
    (g : target.testData.SourceTestFunction)
    (hg : target.testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (target.testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          target.decayExponent <=
      target.constant (target.testData.toSchwartz g) := by
  have hcomponent :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
      (system := system) target.testData target.sourceComponent
      target.sourceStripComponentConstant target.sourceAxisComponentConstant
      target.sourceStripComponentConstant_nonneg
      target.sourceAxisComponentConstant_nonneg target.k
      target.source_strip_extension_eq_component_sum
      target.source_axis_extension_eq_component_sum
      target.source_component_strip_weighted_norm_le_realRadius
      target.source_component_axis_oneAdd_weighted_norm_le g hg rho
  exact (hcomponent.trans (target.source_component_bound_le_constant g hg))

/--
Turn the finite-component source theorem package into the closedness/source-image
zero-locus p-series target.
-/
noncomputable def toSourceImageZeroLocusPSeriesTarget
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system) :
    RiemannWeilSourceImageZeroLocusPSeriesTarget system where
  testData := target.testData
  dense_admissible_image := target.dense_admissible_image
  constant := target.constant
  decayExponent := target.decayExponent
  constant_nonneg := target.constant_nonneg
  decayExponent_nonneg := by
    dsimp [decayExponent]
    positivity
  zeroArgument_extension_continuous :=
    target.zeroArgument_extension_continuous
  constant_continuous := target.constant_continuous
  source_zeroArgument_weighted_norm_le :=
    target.source_zeroArgument_weighted_norm_le

/--
The finite-component target feeds the weighted zero-locus certificate through
the source-image closedness route.
-/
noncomputable def toWeightedDecayCertificate
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (target :
      RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget
        Index system) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  target.toSourceImageZeroLocusPSeriesTarget.toWeightedDecayCertificate

end RiemannWeilSourceImageFiniteComponentStripAxisPSeriesTarget

/--
Single-component source-dense strip/axis constructor with continuous global
majorants.

This is the source-class analogue of
`ofDenseCoreRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants`.
Use it when the real restricted source theorem estimates the extension itself
on admissible source tests, rather than first decomposing it into finitely many
components.  The remaining analytic inputs are dense admissible image,
fixed-zero evaluation continuity, source strip/axis estimates, and continuous
ambient majorants for the two source constants.
-/
noncomputable def ofSourceDenseRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceStripConstant sourceAxisConstant :
      testData.SourceTestFunction -> Real)
    (stripMajorant axisMajorant :
      SchwartzLineTestFunction -> Real)
    (sourceStripConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripConstant g)
    (sourceAxisConstant_nonneg :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceAxisConstant g)
    (stripMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripMajorant f)
    (axisMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= axisMajorant f)
    (stripMajorant_continuous : Continuous stripMajorant)
    (axisMajorant_continuous : Continuous axisMajorant)
    (k : Nat)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (source_strip_extension_weighted_norm_le_realRadius :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (system.extension (testData.toSchwartz g) z) *
                    (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                  sourceStripConstant g)
    (source_axis_oneAdd_weighted_norm_le :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall y : Real,
            0 <= y ->
              norm
                  (system.extension (testData.toSchwartz g)
                    ((y : Complex) * Complex.I)) *
                  (1 + y) ^ (k : Real) <=
                sourceAxisConstant g)
    (sourceStripConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceStripConstant g <= stripMajorant (testData.toSchwartz g))
    (sourceAxisConstant_le_majorant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          sourceAxisConstant g <= axisMajorant (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants
    (system := system) (testData := testData) (Index := Unit)
    (sourceComponent := fun _ g z => system.extension (testData.toSchwartz g) z)
    (sourceStripComponentConstant := fun _ g => sourceStripConstant g)
    (sourceAxisComponentConstant := fun _ g => sourceAxisConstant g)
    (stripMajorant := fun _ f => stripMajorant f)
    (axisMajorant := fun _ f => axisMajorant f)
    (by
      intro _ g hg
      exact sourceStripConstant_nonneg g hg)
    (by
      intro _ g hg
      exact sourceAxisConstant_nonneg g hg)
    (by
      intro _ f
      exact stripMajorant_nonneg f)
    (by
      intro _ f
      exact axisMajorant_nonneg f)
    (by
      intro _
      exact stripMajorant_continuous)
    (by
      intro _
      exact axisMajorant_continuous)
    k dense_admissible_image zeroArgument_extension_continuous
    (by
      intro g _hg z _hlow _hhigh
      simp)
    (by
      intro g _hg y _hy
      simp)
    (by
      intro _ g hg z hlow hhigh
      exact source_strip_extension_weighted_norm_le_realRadius g hg z hlow hhigh)
    (by
      intro _ g hg y hy
      exact source_axis_oneAdd_weighted_norm_le g hg y hy)
    (by
      intro _ g hg
      exact sourceStripConstant_le_majorant g hg)
    (by
      intro _ g hg
      exact sourceAxisConstant_le_majorant g hg)

/--
Dense-core model specialization of the source finite-component strip/axis
constructor.

This is the concrete work package for the next p-series attempt: choose a
dense core of project Schwartz tests, prove the finite-component strip and
positive-axis estimates on that core, and bound the resulting component
constants by a continuous global seminorm.  The wrapper packages the core as
`GuinandWeilSourceTestFunctionClass.ofDenseCore` and feeds the dense-source
closedness route.
-/
noncomputable def ofDenseCoreFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (component :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (constant : SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripComponentConstant i g)
    (axisComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= axisComponentConstant i g)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (constant_continuous : Continuous constant)
    (strip_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension g.1 z =
                Finset.univ.sum fun i : Index => component i g z)
    (axis_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall y : Real,
          0 <= y ->
            system.extension g.1 ((y : Complex) * Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i g ((y : Complex) * Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (component i g z) *
                    (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                  stripComponentConstant i g)
    (component_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall y : Real,
            0 <= y ->
              norm (component i g ((y : Complex) * Complex.I)) *
                  (1 + y) ^ (k : Real) <=
                axisComponentConstant i g)
    (component_bound_le_constant :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index => stripComponentConstant i g) +
            (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index => axisComponentConstant i g) <=
          constant g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let testData : GuinandWeilSourceTestFunctionClass :=
    GuinandWeilSourceTestFunctionClass.ofDenseCore core
  refine
    ofSourceDenseFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuous
      (system := system) (testData := testData) component
      stripComponentConstant axisComponentConstant constant ?_ ?_
      constant_nonneg k ?_ zeroArgument_extension_continuous
      constant_continuous ?_ ?_ ?_ ?_ ?_
  · intro i g _hg
    exact stripComponentConstant_nonneg i g
  · intro i g _hg
    exact axisComponentConstant_nonneg i g
  · simpa [testData, guinandWeilAdmissibleSchwartzImage] using
      GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
        (core := core) dense_core
  · intro g _hg z hlow hhigh
    simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
      strip_extension_eq_component_sum g z hlow hhigh
  · intro g _hg y hy
    simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
      axis_extension_eq_component_sum g y hy
  · intro i g _hg z hlow hhigh
    exact component_strip_weighted_norm_le_realRadius i g z hlow hhigh
  · intro i g _hg y hy
    exact component_axis_oneAdd_weighted_norm_le i g y hy
  · intro g _hg
    simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
      component_bound_le_constant g

/--
Dense-core specialization of the componentwise indexed-tail p-series route.

This packages a concrete dense core as a source class and feeds the
source-normalized trivial-axis tail constructor. The finite prefix remains the
explicit system-level prefix sum for the core test.
-/
noncomputable def ofDenseCoreFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuous
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (component :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Complex -> Complex)
    (stripComponentConstant comparisonComponentConstant :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (constant : SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripComponentConstant i g)
    (comparisonComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= comparisonComponentConstant i g)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (cutoff k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (constant_continuous : Continuous constant)
    (strip_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension g.1 z =
                Finset.univ.sum fun i : Index => component i g z)
    (tail_axis_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall n : Nat,
          cutoff <= n ->
            system.extension g.1
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i g
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (component i g z) *
                    (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                  stripComponentConstant i g)
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i g *
                  norm (g.1 (riemannWeilTrivialZeroArgumentHeight n)))
    (component_bound_le_constant :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripComponentConstant i g) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k g.1 +
              (Finset.univ.sum fun i : Index =>
                  comparisonComponentConstant i g) *
                schwartzLineRealAxisShiftedSeminormConstant k g.1) <=
          constant g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let testData : GuinandWeilSourceTestFunctionClass :=
    GuinandWeilSourceTestFunctionClass.ofDenseCore core
  refine
    ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuous
      (system := system) (testData := testData) component
      stripComponentConstant comparisonComponentConstant constant ?_ ?_
      constant_nonneg cutoff k ?_ zeroArgument_extension_continuous
      constant_continuous ?_ ?_ ?_ ?_ ?_
  · intro i g _hg
    exact stripComponentConstant_nonneg i g
  · intro i g _hg
    exact comparisonComponentConstant_nonneg i g
  · simpa [testData, guinandWeilAdmissibleSchwartzImage] using
      GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
        (core := core) dense_core
  · intro g _hg z hlow hhigh
    simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
      strip_extension_eq_component_sum g z hlow hhigh
  · intro g _hg n hn
    simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
      tail_axis_extension_eq_component_sum g n hn
  · intro i g _hg z hlow hhigh
    exact component_strip_weighted_norm_le_realRadius i g z hlow hhigh
  · intro i g _hg n hn
    simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
      component_tail_axis_norm_le_realHeight i g n hn
  · intro g _hg
    simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
      component_bound_le_constant g

/--
Dense-core indexed-tail constructor with continuous global component
majorants.

This is the concrete dense-core counterpart of
`ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants`.
The global certificate constant is built from continuous strip majorants, the
automatic finite trivial-axis prefix, and continuous tail majorants times the
checked real-axis Schwartz seminorm.  The analytic proof now only has to
control component constants on the dense core by those ambient majorants.
-/
noncomputable def ofDenseCoreFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (component :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Complex -> Complex)
    (stripComponentConstant comparisonComponentConstant :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripComponentConstant i g)
    (comparisonComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= comparisonComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (comparisonMajorant_continuous :
      forall i : Index, Continuous (comparisonMajorant i))
    (cutoff k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I))
    (strip_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension g.1 z =
                Finset.univ.sum fun i : Index => component i g z)
    (tail_axis_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall n : Nat,
          cutoff <= n ->
            system.extension g.1
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i g
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (component i g z) *
                    (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                  stripComponentConstant i g)
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i g *
                  norm (g.1 (riemannWeilTrivialZeroArgumentHeight n)))
    (stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          stripComponentConstant i g <= stripMajorant i g.1)
    (comparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          comparisonComponentConstant i g <= comparisonMajorant i g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let testData : GuinandWeilSourceTestFunctionClass :=
    GuinandWeilSourceTestFunctionClass.ofDenseCore core
  exact
    ofSourceDenseFiniteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
      (system := system) (testData := testData) component
      stripComponentConstant comparisonComponentConstant stripMajorant
      comparisonMajorant
      (by
        intro i g _hg
        exact stripComponentConstant_nonneg i g)
      (by
        intro i g _hg
        exact comparisonComponentConstant_nonneg i g)
      stripMajorant_nonneg comparisonMajorant_nonneg stripMajorant_continuous
      comparisonMajorant_continuous cutoff k
      (by
        simpa [testData, guinandWeilAdmissibleSchwartzImage] using
          GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
            (core := core) dense_core)
      zeroArgument_extension_continuous prefix_trivialAxis_extension_continuous
      (by
        intro g _hg z hlow hhigh
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          strip_extension_eq_component_sum g z hlow hhigh)
      (by
        intro g _hg n hn
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          tail_axis_extension_eq_component_sum g n hn)
      (by
        intro i g _hg z hlow hhigh
        exact component_strip_weighted_norm_le_realRadius i g z hlow hhigh)
      (by
        intro i g _hg n hn
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          component_tail_axis_norm_le_realHeight i g n hn)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          stripComponentConstant_le_majorant i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          comparisonComponentConstant_le_majorant i g)

/--
Dense-core real-radius indexed-tail constructor with eventual tail hypotheses
and continuous global component majorants.

This packages the model-core version of the repaired real-radius route: the
strip decomposition and component envelopes are proved on a dense core, while
the indexed trivial-axis decomposition and real-height tail domination may be
eventual. Lean turns the core into a source class, extracts the uniform cutoff,
and applies the source-image closedness constructor.
-/
noncomputable def ofDenseCoreFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (component :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Complex -> Complex)
    (stripComponentConstant comparisonComponentConstant :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (stripMajorant comparisonMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripComponentConstant i g)
    (comparisonComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= comparisonComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (comparisonMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonMajorant i f)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (comparisonMajorant_continuous :
      forall i : Index, Continuous (comparisonMajorant i))
    (k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (trivialAxis_extension_continuous :
      forall n : Nat,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
    (strip_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension g.1 z =
                Finset.univ.sum fun i : Index => component i g z)
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall g : {f : SchwartzLineTestFunction // f ∈ core},
                system.extension g.1
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I))
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (component i g z) *
                    (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                  stripComponentConstant i g)
    (component_tail_axis_norm_le_realHeight_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall g : {f : SchwartzLineTestFunction // f ∈ core},
                  norm
                      (component i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    comparisonComponentConstant i g *
                      norm (g.1 (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          stripComponentConstant i g <= stripMajorant i g.1)
    (comparisonComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          comparisonComponentConstant i g <= comparisonMajorant i g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let testData : GuinandWeilSourceTestFunctionClass :=
    GuinandWeilSourceTestFunctionClass.ofDenseCore core
  exact
    ofSourceDenseFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
      (system := system) (testData := testData) component
      stripComponentConstant comparisonComponentConstant stripMajorant
      comparisonMajorant
      (by
        intro i g _hg
        exact stripComponentConstant_nonneg i g)
      (by
        intro i g _hg
        exact comparisonComponentConstant_nonneg i g)
      stripMajorant_nonneg comparisonMajorant_nonneg stripMajorant_continuous
      comparisonMajorant_continuous k
      (by
        simpa [testData, guinandWeilAdmissibleSchwartzImage] using
          GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
            (core := core) dense_core)
      zeroArgument_extension_continuous trivialAxis_extension_continuous
      (by
        intro g _hg z hlow hhigh
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          strip_extension_eq_component_sum g z hlow hhigh)
      (by
        rw [Filter.eventually_atTop] at tail_axis_extension_eq_component_sum_eventually
        rcases tail_axis_extension_eq_component_sum_eventually with
          ⟨cutoff, hcutoff_all⟩
        rw [Filter.eventually_atTop]
        refine ⟨cutoff, ?_⟩
        intro cutoff' hcutoff' n hn g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          hcutoff_all cutoff' hcutoff' n hn g)
      (by
        intro i g _hg z hlow hhigh
        exact component_strip_weighted_norm_le_realRadius i g z hlow hhigh)
      (by
        rw [Filter.eventually_atTop] at component_tail_axis_norm_le_realHeight_eventually
        rcases component_tail_axis_norm_le_realHeight_eventually with
          ⟨cutoff, hcutoff_all⟩
        rw [Filter.eventually_atTop]
        refine ⟨cutoff, ?_⟩
        intro cutoff' hcutoff' n hn i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          hcutoff_all cutoff' hcutoff' n hn i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          stripComponentConstant_le_majorant i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          comparisonComponentConstant_le_majorant i g)

/--
Dense-core real/Fourier indexed-tail constructor with continuous global
component majorants.

This is the concrete dense-core version of the source real/Fourier route.  A
future analytic core supplies finite-component strip bounds in terms of the
core test and its Fourier transform, plus indexed trivial-axis tail bounds.
Lean packages the core as a source class, rewrites the source Fourier profile
to the project Fourier transform, assembles the continuous real/Fourier
majorant, and applies dense closedness.
-/
noncomputable def ofDenseCoreFiniteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (component :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Complex -> Complex)
    (stripRealComponentConstant stripFourierComponentConstant
      tailComponentConstant :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripRealComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripRealComponentConstant i g)
    (stripFourierComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripFourierComponentConstant i g)
    (tailComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= tailComponentConstant i g)
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
    (stripRealMajorant_continuous :
      forall i : Index, Continuous (stripRealMajorant i))
    (stripFourierMajorant_continuous :
      forall i : Index, Continuous (stripFourierMajorant i))
    (tailMajorant_continuous :
      forall i : Index, Continuous (tailMajorant i))
    (cutoff k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (prefix_trivialAxis_extension_continuous :
      forall n : Nat,
        n < cutoff ->
          Continuous fun f : SchwartzLineTestFunction =>
            system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I))
    (strip_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension g.1 z =
                Finset.univ.sum fun i : Index => component i g z)
    (tail_axis_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall n : Nat,
          cutoff <= n ->
            system.extension g.1
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i g
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I))
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (component i g z) <=
                  stripRealComponentConstant i g * norm (g.1 z.re) +
                    stripFourierComponentConstant i g *
                      norm ((SchwartzLineTestFunction.fourier g.1) z.re))
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i g
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                tailComponentConstant i g *
                  norm (g.1 (riemannWeilTrivialZeroArgumentHeight n)))
    (stripRealComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          stripRealComponentConstant i g <= stripRealMajorant i g.1)
    (stripFourierComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          stripFourierComponentConstant i g <= stripFourierMajorant i g.1)
    (tailComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          tailComponentConstant i g <= tailMajorant i g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let testData : GuinandWeilSourceTestFunctionClass :=
    GuinandWeilSourceTestFunctionClass.ofDenseCore core
  exact
    ofSourceDenseFiniteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTailOfContinuousMajorants
      (system := system) (testData := testData) component
      stripRealComponentConstant stripFourierComponentConstant
      tailComponentConstant stripRealMajorant stripFourierMajorant
      tailMajorant
      (by
        intro i g _hg
        exact stripRealComponentConstant_nonneg i g)
      (by
        intro i g _hg
        exact stripFourierComponentConstant_nonneg i g)
      (by
        intro i g _hg
        exact tailComponentConstant_nonneg i g)
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg stripRealMajorant_continuous
      stripFourierMajorant_continuous tailMajorant_continuous cutoff k
      (by
        simpa [testData, guinandWeilAdmissibleSchwartzImage] using
          GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
            (core := core) dense_core)
      zeroArgument_extension_continuous prefix_trivialAxis_extension_continuous
      (by
        intro g _hg z hlow hhigh
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          strip_extension_eq_component_sum g z hlow hhigh)
      (by
        intro g _hg n hn
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          tail_axis_extension_eq_component_sum g n hn)
      (by
        intro i g _hg z hlow hhigh
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          component_strip_norm_le_real_fourier i g z hlow hhigh)
      (by
        intro i g _hg n hn
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          component_tail_axis_norm_le_realHeight i g n hn)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          stripRealComponentConstant_le_majorant i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          stripFourierComponentConstant_le_majorant i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          tailComponentConstant_le_majorant i g)

/--
Dense-core real/Fourier indexed-tail constructor with eventual tail hypotheses
and continuous global component majorants.

This is the most flexible dense-core real/Fourier certificate target currently
available: the finite-component strip comparison is proved on the core, while
the indexed trivial-axis decomposition and tail domination are required only
eventually.  Lean packages the core as a source class and lets the source-dense
eventual constructor extract the uniform cutoff and close the weighted
zero-locus certificate.
-/
noncomputable def ofDenseCoreFiniteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (component :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Complex -> Complex)
    (stripRealComponentConstant stripFourierComponentConstant
      tailComponentConstant :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (stripRealMajorant stripFourierMajorant tailMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripRealComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripRealComponentConstant i g)
    (stripFourierComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripFourierComponentConstant i g)
    (tailComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= tailComponentConstant i g)
    (stripRealMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealMajorant i f)
    (stripFourierMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierMajorant i f)
    (tailMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailMajorant i f)
    (stripRealMajorant_continuous :
      forall i : Index, Continuous (stripRealMajorant i))
    (stripFourierMajorant_continuous :
      forall i : Index, Continuous (stripFourierMajorant i))
    (tailMajorant_continuous :
      forall i : Index, Continuous (tailMajorant i))
    (k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (trivialAxis_extension_continuous :
      forall n : Nat,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
    (strip_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension g.1 z =
                Finset.univ.sum fun i : Index => component i g z)
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall g : {f : SchwartzLineTestFunction // f ∈ core},
                system.extension g.1
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i g
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I))
        (Filter.atTop : Filter Nat))
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (component i g z) <=
                  stripRealComponentConstant i g * norm (g.1 z.re) +
                    stripFourierComponentConstant i g *
                      norm ((SchwartzLineTestFunction.fourier g.1) z.re))
    (component_tail_axis_norm_le_realHeight_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall g : {f : SchwartzLineTestFunction // f ∈ core},
                  norm
                      (component i g
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    tailComponentConstant i g *
                      norm (g.1 (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (stripRealComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          stripRealComponentConstant i g <= stripRealMajorant i g.1)
    (stripFourierComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          stripFourierComponentConstant i g <= stripFourierMajorant i g.1)
    (tailComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          tailComponentConstant i g <= tailMajorant i g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let testData : GuinandWeilSourceTestFunctionClass :=
    GuinandWeilSourceTestFunctionClass.ofDenseCore core
  exact
    ofSourceDenseFiniteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTailOfContinuousMajorants
      (system := system) (testData := testData) component
      stripRealComponentConstant stripFourierComponentConstant
      tailComponentConstant stripRealMajorant stripFourierMajorant
      tailMajorant
      (by
        intro i g _hg
        exact stripRealComponentConstant_nonneg i g)
      (by
        intro i g _hg
        exact stripFourierComponentConstant_nonneg i g)
      (by
        intro i g _hg
        exact tailComponentConstant_nonneg i g)
      stripRealMajorant_nonneg stripFourierMajorant_nonneg
      tailMajorant_nonneg stripRealMajorant_continuous
      stripFourierMajorant_continuous tailMajorant_continuous k
      (by
        simpa [testData, guinandWeilAdmissibleSchwartzImage] using
          GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
            (core := core) dense_core)
      zeroArgument_extension_continuous trivialAxis_extension_continuous
      (by
        intro g _hg z hlow hhigh
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          strip_extension_eq_component_sum g z hlow hhigh)
      (by
        rw [Filter.eventually_atTop] at tail_axis_extension_eq_component_sum_eventually
        rcases tail_axis_extension_eq_component_sum_eventually with
          ⟨cutoff, hcutoff_all⟩
        rw [Filter.eventually_atTop]
        refine ⟨cutoff, ?_⟩
        intro cutoff' hcutoff' n hn g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          hcutoff_all cutoff' hcutoff' n hn g)
      (by
        intro i g _hg z hlow hhigh
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          component_strip_norm_le_real_fourier i g z hlow hhigh)
      (by
        rw [Filter.eventually_atTop] at component_tail_axis_norm_le_realHeight_eventually
        rcases component_tail_axis_norm_le_realHeight_eventually with
          ⟨cutoff, hcutoff_all⟩
        rw [Filter.eventually_atTop]
        refine ⟨cutoff, ?_⟩
        intro cutoff' hcutoff' n hn i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          hcutoff_all cutoff' hcutoff' n hn i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          stripRealComponentConstant_le_majorant i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          stripFourierComponentConstant_le_majorant i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          tailComponentConstant_le_majorant i g)

/--
Dense-core specialization with a global seminorm assembled from continuous
component majorants.

This is the most concrete checked target for a future dense analytic core:
prove component strip/axis estimates on the core and prove that their constants
are bounded by continuous global majorants on the ambient Schwartz space.
-/
noncomputable def ofDenseCoreFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (component :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Complex -> Complex)
    (stripComponentConstant axisComponentConstant :
      Index -> {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (stripMajorant axisMajorant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= stripComponentConstant i g)
    (axisComponentConstant_nonneg :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          0 <= axisComponentConstant i g)
    (stripMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripMajorant i f)
    (axisMajorant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= axisMajorant i f)
    (stripMajorant_continuous :
      forall i : Index, Continuous (stripMajorant i))
    (axisMajorant_continuous :
      forall i : Index, Continuous (axisMajorant i))
    (k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (strip_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              system.extension g.1 z =
                Finset.univ.sum fun i : Index => component i g z)
    (axis_extension_eq_component_sum :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall y : Real,
          0 <= y ->
            system.extension g.1 ((y : Complex) * Complex.I) =
              Finset.univ.sum fun i : Index =>
                component i g ((y : Complex) * Complex.I))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (component i g z) *
                    (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                  stripComponentConstant i g)
    (component_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          forall y : Real,
            0 <= y ->
              norm (component i g ((y : Complex) * Complex.I)) *
                  (1 + y) ^ (k : Real) <=
                axisComponentConstant i g)
    (stripComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          stripComponentConstant i g <= stripMajorant i g.1)
    (axisComponentConstant_le_majorant :
      forall i : Index,
        forall g : {f : SchwartzLineTestFunction // f ∈ core},
          axisComponentConstant i g <= axisMajorant i g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let testData : GuinandWeilSourceTestFunctionClass :=
    GuinandWeilSourceTestFunctionClass.ofDenseCore core
  exact
    ofSourceDenseFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants
      (system := system) (testData := testData) component
      stripComponentConstant axisComponentConstant stripMajorant axisMajorant
      (by
        intro i g _hg
        exact stripComponentConstant_nonneg i g)
      (by
        intro i g _hg
        exact axisComponentConstant_nonneg i g)
      stripMajorant_nonneg axisMajorant_nonneg stripMajorant_continuous
      axisMajorant_continuous k
      (by
        simpa [testData, guinandWeilAdmissibleSchwartzImage] using
          GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
            (core := core) dense_core)
      zeroArgument_extension_continuous
      (by
        intro g _hg z hlow hhigh
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          strip_extension_eq_component_sum g z hlow hhigh)
      (by
        intro g _hg y hy
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          axis_extension_eq_component_sum g y hy)
      (by
        intro i g _hg z hlow hhigh
        exact component_strip_weighted_norm_le_realRadius i g z hlow hhigh)
      (by
        intro i g _hg y hy
        exact component_axis_oneAdd_weighted_norm_le i g y hy)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          stripComponentConstant_le_majorant i g)
      (by
        intro i g _hg
        simpa [testData, GuinandWeilSourceTestFunctionClass.ofDenseCore] using
          axisComponentConstant_le_majorant i g)

/--
Single-component dense-core strip/axis constructor with continuous global
majorants.

This is the first target to try when the candidate source proof gives direct
estimates for the extension itself rather than a finite Guinand-Weil component
decomposition.  The only analytic estimates are the real-radius strip envelope
and the positive-imaginary-axis `(1 + y)^k` bound on the dense core, together
with continuous ambient majorants for their constants.
-/
noncomputable def ofDenseCoreRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants
    {system : SchwartzRiemannWeilExtensionSystem}
    (core : Set SchwartzLineTestFunction)
    (stripConstant axisConstant :
      {f : SchwartzLineTestFunction // f ∈ core} -> Real)
    (stripMajorant axisMajorant :
      SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        0 <= stripConstant g)
    (axisConstant_nonneg :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        0 <= axisConstant g)
    (stripMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripMajorant f)
    (axisMajorant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= axisMajorant f)
    (stripMajorant_continuous : Continuous stripMajorant)
    (axisMajorant_continuous : Continuous axisMajorant)
    (k : Nat)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (strip_extension_weighted_norm_le_realRadius :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (system.extension g.1 z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripConstant g)
    (axis_oneAdd_weighted_norm_le :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        forall y : Real,
          0 <= y ->
            norm (system.extension g.1 ((y : Complex) * Complex.I)) *
                (1 + y) ^ (k : Real) <=
              axisConstant g)
    (stripConstant_le_majorant :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        stripConstant g <= stripMajorant g.1)
    (axisConstant_le_majorant :
      forall g : {f : SchwartzLineTestFunction // f ∈ core},
        axisConstant g <= axisMajorant g.1) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofDenseCoreFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControlOfContinuousMajorants
    (system := system) (core := core) (Index := Unit)
    (component := fun _ g z => system.extension g.1 z)
    (stripComponentConstant := fun _ g => stripConstant g)
    (axisComponentConstant := fun _ g => axisConstant g)
    (stripMajorant := fun _ f => stripMajorant f)
    (axisMajorant := fun _ f => axisMajorant f)
    (by
      intro _ g
      exact stripConstant_nonneg g)
    (by
      intro _ g
      exact axisConstant_nonneg g)
    (by
      intro _ f
      exact stripMajorant_nonneg f)
    (by
      intro _ f
      exact axisMajorant_nonneg f)
    (by
      intro _
      exact stripMajorant_continuous)
    (by
      intro _
      exact axisMajorant_continuous)
    k dense_core zeroArgument_extension_continuous
    (by
      intro g z _hlow _hhigh
      simp)
    (by
      intro g y _hy
      simp)
    (by
      intro _ g z hlow hhigh
      exact strip_extension_weighted_norm_le_realRadius g z hlow hhigh)
    (by
      intro _ g y hy
      exact axis_oneAdd_weighted_norm_le g y hy)
    (by
      intro _ g
      exact stripConstant_le_majorant g)
    (by
      intro _ g
      exact axisConstant_le_majorant g)

/--
Preferred all-zero-locus constructor from the split strip/trivial-axis analytic
input.
-/
noncomputable def ofSplitZeroLocusWeightedDecayInput
    {system : SchwartzRiemannWeilExtensionSystem}
    (input : RiemannWeilSplitZeroLocusWeightedDecayInput system) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  input.toZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Preferred constructor when the trivial zero contribution has been moved to the
gamma/trivial side and therefore vanishes from the zero-locus extension.
-/
noncomputable def ofHorizontalStripDecayAndTrivialVanishing
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ decayExponent <=
              constant f)
    (trivial_zeroArgument_extension_eq_zero :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        IsTrivialZetaZero (rho : Complex) ->
          system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  (RiemannWeilSplitZeroLocusWeightedDecayInput.ofStripDecayAndTrivialVanishing
    constant decayExponent constant_nonneg decayExponent_nonneg
    strip_weighted_norm_le trivial_zeroArgument_extension_eq_zero)
      |>.toZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Preferred certificate constructor when the analytic strip estimate is proved
via vertical domination by real-axis Schwartz values.
-/
noncomputable def ofRealPartComparisonAndTrivialVanishing
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (trivial_zeroArgument_extension_eq_zero :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        IsTrivialZetaZero (rho : Complex) ->
          system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  (RiemannWeilSplitZeroLocusWeightedDecayInput.ofRealPartComparisonAndTrivialVanishing
      comparisonConstant comparisonConstant_nonneg k
      strip_extension_norm_le_realAxis
      trivial_zeroArgument_extension_eq_zero)
    |>.toZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Preferred certificate constructor when the strip estimate is reduced to
vertical real-part domination and the trivial-zero contribution is controlled
on the explicit indexed imaginary-axis ray.
-/
noncomputable def ofRealPartComparisonAndTrivialAxisControl
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          norm
              (system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) *
              (riemannWeilTrivialZeroArgumentHeight n + 2) ^ (k : Real) <=
            comparisonConstant f *
              ((2 : Real) ^ k *
                schwartzLineRealAxisShiftedSeminormConstant k f)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  (RiemannWeilSplitZeroLocusWeightedDecayInput.ofRealPartComparisonAndTrivialAxisControl
      comparisonConstant comparisonConstant_nonneg k
      strip_extension_norm_le_realAxis trivialAxis_weighted_norm_le)
    |>.toZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Preferred certificate constructor when strip decay is reduced to vertical
real-part domination and trivial-zero control is reduced to a uniform positive
imaginary-axis estimate.
-/
noncomputable def ofRealPartComparisonAndImaginaryAxisControl
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant axisConstant : SchwartzLineTestFunction -> Real)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (axisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= axisConstant f)
    (k : Nat)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (imaginaryAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (y + 2) ^ (k : Real) <=
              axisConstant f) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  (RiemannWeilSplitZeroLocusWeightedDecayInput.ofRealPartComparisonAndImaginaryAxisControl
      comparisonConstant axisConstant comparisonConstant_nonneg
      axisConstant_nonneg k strip_extension_norm_le_realAxis
      imaginaryAxis_weighted_norm_le)
    |>.toZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Preferred certificate constructor when the imaginary-axis estimate is supplied
with the standard `(1 + y)^k` weight.
-/
noncomputable def ofRealPartComparisonAndOneAddImaginaryAxisControl
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant axisConstant : SchwartzLineTestFunction -> Real)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (axisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= axisConstant f)
    (k : Nat)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (imaginaryAxis_oneAdd_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (1 + y) ^ (k : Real) <=
              axisConstant f) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  (RiemannWeilSplitZeroLocusWeightedDecayInput.ofRealPartComparisonAndOneAddImaginaryAxisControl
      comparisonConstant axisConstant comparisonConstant_nonneg
      axisConstant_nonneg k strip_extension_norm_le_realAxis
      imaginaryAxis_oneAdd_weighted_norm_le)
    |>.toZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Preferred certificate constructor using the real-radius strip envelope that
avoids the real-zero obstruction of pointwise domination by `norm (f z.re)`.
-/
noncomputable def ofRealPartEnvelopeAndOneAddImaginaryAxisControl
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
              axisConstant f) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  (RiemannWeilSplitZeroLocusWeightedDecayInput.ofRealPartEnvelopeAndOneAddImaginaryAxisControl
      stripConstant axisConstant stripConstant_nonneg axisConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      imaginaryAxis_oneAdd_weighted_norm_le)
    |>.toZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
Componentwise certificate constructor for the repaired real-radius strip
envelope plus standard `(1 + y)^k` positive-imaginary-axis route.

The remaining analytic obligations are exactly the finite-sum identities on
the strip and positive imaginary axis, plus the componentwise weighted
strip/axis estimates.
-/
noncomputable def ofFiniteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
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
                axisComponentConstant i f) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  let certificateConstant : SchwartzLineTestFunction -> Real := fun f =>
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => axisComponentConstant i f)
  refine
    { constant := certificateConstant
      decayExponent := k
      constant_nonneg := ?_
      decayExponent_nonneg := by positivity
      zeroArgument_weighted_norm_le := ?_ }
  · intro f
    have hstrip_sum_nonneg :
        0 <=
          (Finset.univ.sum fun i : Index =>
            stripComponentConstant i f) := by
      exact Finset.sum_nonneg fun i _ =>
        stripComponentConstant_nonneg i f
    have haxis_sum_nonneg :
        0 <=
          (Finset.univ.sum fun i : Index =>
            axisComponentConstant i f) := by
      exact Finset.sum_nonneg fun i _ =>
        axisComponentConstant_nonneg i f
    dsimp [certificateConstant]
    exact add_nonneg
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        hstrip_sum_nonneg)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        haxis_sum_nonneg)
  · intro f rho
    simpa [certificateConstant] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
        (system := system) component stripComponentConstant
        axisComponentConstant stripComponentConstant_nonneg
        axisComponentConstant_nonneg k strip_extension_eq_component_sum
        axis_extension_eq_component_sum component_strip_weighted_norm_le_realRadius
        component_axis_oneAdd_weighted_norm_le f rho

/--
Weighted certificate constructor for the finite-component real-radius indexed
tail route with eventual trivial-axis hypotheses.

This is the weighted-certificate analogue of
`RiemannWeilZeroArgumentShiftedRadiusDecayCertificate.ofFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail`.
Lean extracts a shared cutoff from the eventual tail decomposition and
real-height domination hypotheses, builds the explicit finite-prefix constant,
and proves the weighted zero-locus certificate directly.
-/
noncomputable def ofFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripComponentConstant comparisonComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f)
    (comparisonComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= comparisonComponentConstant i f)
    (k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall f : SchwartzLineTestFunction,
                norm
                    (component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) <=
                  comparisonComponentConstant i f *
                    norm (f (riemannWeilTrivialZeroArgumentHeight n))) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  have htail_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
                        Complex.I)) <=
                  comparisonComponentConstant i f *
                    norm (f (riemannWeilTrivialZeroArgumentHeight n))) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_norm_le_realHeight_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  let cutoff : Nat := Classical.choose htail_eventually
  have hcutoff_all := Classical.choose_spec htail_eventually
  have hcutoff := hcutoff_all cutoff le_rfl
  let certificateConstant : SchwartzLineTestFunction -> Real := fun f =>
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  refine
    { constant := certificateConstant
      decayExponent := k
      constant_nonneg := ?_
      decayExponent_nonneg := by positivity
      zeroArgument_weighted_norm_le := ?_ }
  · intro f
    simpa [certificateConstant] using
      finiteComponentRealIndexedTailMajorant_nonneg
        (system := system) stripComponentConstant comparisonComponentConstant
        stripComponentConstant_nonneg comparisonComponentConstant_nonneg
        cutoff k f
  · intro f rho
    simpa [certificateConstant] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripComponentConstant
        comparisonComponentConstant stripComponentConstant_nonneg
        comparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum
        (fun f n hn => hcutoff.1 n hn f)
        component_strip_weighted_norm_le_realRadius
        (fun i f n hn => hcutoff.2 n hn i f)
        f rho

/--
Weighted certificate constructor for the finite-component real/Fourier
indexed-tail route with eventual trivial-axis hypotheses.

The strip component estimate may use the two real-line profiles `f` and
`Fourier f`; Lean extracts one tail cutoff and assembles the weighted
zero-locus certificate with the finite prefix left explicit.
-/
noncomputable def ofFiniteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (stripRealComparisonConstant stripFourierComparisonConstant
      tailComparisonComponentConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (stripRealComparisonConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripRealComparisonConstant i f)
    (stripFourierComparisonConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripFourierComparisonConstant i f)
    (tailComparisonComponentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= tailComparisonComponentConstant i f)
    (k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) <=
                stripRealComparisonConstant i f * norm (f z.re) +
                  stripFourierComparisonConstant i f *
                    norm ((SchwartzLineTestFunction.fourier f) z.re))
    (component_tail_axis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall i : Index,
              forall f : SchwartzLineTestFunction,
                norm
                    (component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) <=
                  tailComparisonComponentConstant i f *
                    norm (f (riemannWeilTrivialZeroArgumentHeight n))) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system := by
  have htail_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
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
                        Complex.I)) <=
                  tailComparisonComponentConstant i f *
                    norm (f (riemannWeilTrivialZeroArgumentHeight n))) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_norm_le_realHeight_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  let cutoff : Nat := Classical.choose htail_eventually
  have hcutoff_all := Classical.choose_spec htail_eventually
  have hcutoff := hcutoff_all cutoff le_rfl
  let certificateConstant : SchwartzLineTestFunction -> Real := fun f =>
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripRealComparisonConstant i f *
              schwartzLineRealAxisShiftedSeminormConstant k f +
            stripFourierComparisonConstant i f *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier f)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (Finset.univ.sum fun i : Index =>
            tailComparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  refine
    { constant := certificateConstant
      decayExponent := k
      constant_nonneg := ?_
      decayExponent_nonneg := by positivity
      zeroArgument_weighted_norm_le := ?_ }
  · intro f
    simpa [certificateConstant] using
      finiteComponentRealFourierIndexedTailMajorant_nonneg
        (system := system) stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg
        stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg cutoff k f
  · intro f rho
    simpa [certificateConstant] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum
        (fun f n hn => hcutoff.1 n hn f)
        component_strip_norm_le_real_fourier
        (fun i f n hn => hcutoff.2 n hn i f)
        f rho

end RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate
