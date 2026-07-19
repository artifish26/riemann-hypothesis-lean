import RiemannHypothesisProject.GuinandWeilDensityFormulaBridge
import RiemannHypothesisProject.RiemannWeilShiftedRadius.CertificateCore
import RiemannHypothesisProject.RiemannWeilShiftedRadius.CutoffApproximation
import RiemannHypothesisProject.RiemannWeilShiftedRadius.ZeroArgumentContinuity

/-!
# Dense-source shifted-radius certificates

This module contains dense-core/source-shaped certificate constructors and the
closed weighted zero-locus promotion layer for shifted-radius p-series targets.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion
open MeasureTheory
open scoped Topology

namespace RiemannWeilZeroArgumentShiftedRadiusDecayCertificate

/--
Certificate constructor for the finite-component real-radius envelope route.

This is the preferred repaired target after the shared-zero obstruction: each
strip component is controlled by a nonvanishing weighted real-radius envelope,
and the indexed trivial-zero component decomposition/tail domination only needs
to hold eventually. Lean extracts one cutoff and packages the resulting
zero-argument shifted-radius certificate for the p-series pipeline.
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
                    ‖f (riemannWeilTrivialZeroArgumentHeight n)‖) :
    RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system := by
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
                    ‖f (riemannWeilTrivialZeroArgumentHeight n)‖) :=
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
      zeroArgument_norm_le_shiftedRadialBound := ?_ }
  · intro f
    have hstrip_sum_nonneg :
        0 <=
          (Finset.univ.sum fun i : Index =>
            stripComponentConstant i f) := by
      exact Finset.sum_nonneg fun i _ =>
        stripComponentConstant_nonneg i f
    have hcomparison_sum_nonneg :
        0 <=
          (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) := by
      exact Finset.sum_nonneg fun i _ =>
        comparisonComponentConstant_nonneg i f
    dsimp [certificateConstant]
    exact add_nonneg
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        hstrip_sum_nonneg)
      (add_nonneg
        (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k f)
        (mul_nonneg hcomparison_sum_nonneg
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)))
  · intro f rho
    simpa [certificateConstant] using
      zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripComponentConstant
        comparisonComponentConstant stripComponentConstant_nonneg
        comparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum
        (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Source-coverage constructor for the repaired finite-component real-radius
envelope route.

This is the source-normalized version of
`ofFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail`:
the analytic decomposition and component estimates may be proved only for
admissible source tests, provided those admissible tests cover every project
Schwartz test after applying `toSchwartz`.
-/
noncomputable def ofSourceCoverageFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent : Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
    (sourceStripComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceStripComponentConstant i g)
    (sourceComparisonComponentConstant_nonneg :
      forall i : Index, forall g : testData.SourceTestFunction,
        testData.admissible g -> 0 <= sourceComparisonComponentConstant i g)
    (k : Nat)
    (coversSchwartz :
      forall f : SchwartzLineTestFunction,
        exists g : testData.SourceTestFunction,
          testData.admissible g /\ testData.toSchwartz g = f)
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
                      ‖testData.toSchwartz g
                        (riemannWeilTrivialZeroArgumentHeight n)‖) :
    RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system := by
  classical
  let sourceFor : SchwartzLineTestFunction -> testData.SourceTestFunction :=
    fun f => Classical.choose (coversSchwartz f)
  have sourceFor_admissible :
      forall f : SchwartzLineTestFunction,
        testData.admissible (sourceFor f) := by
    intro f
    exact (Classical.choose_spec (coversSchwartz f)).1
  have sourceFor_toSchwartz :
      forall f : SchwartzLineTestFunction,
        testData.toSchwartz (sourceFor f) = f := by
    intro f
    exact (Classical.choose_spec (coversSchwartz f)).2
  let component : Index -> SchwartzLineTestFunction -> Complex -> Complex :=
    fun i f z => sourceComponent i (sourceFor f) z
  let stripComponentConstant :
      Index -> SchwartzLineTestFunction -> Real :=
    fun i f => sourceStripComponentConstant i (sourceFor f)
  let comparisonComponentConstant :
      Index -> SchwartzLineTestFunction -> Real :=
    fun i f => sourceComparisonComponentConstant i (sourceFor f)
  refine
    ofFiniteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) component stripComponentConstant
      comparisonComponentConstant ?_ ?_ k ?_ ?_ ?_ ?_
  · intro i f
    exact sourceStripComponentConstant_nonneg i (sourceFor f)
      (sourceFor_admissible f)
  · intro i f
    exact sourceComparisonComponentConstant_nonneg i (sourceFor f)
      (sourceFor_admissible f)
  · intro f z hlow hhigh
    have hsource :=
      source_strip_extension_eq_component_sum (sourceFor f)
        (sourceFor_admissible f) z hlow hhigh
    simpa [component, sourceFor_toSchwartz f] using hsource
  · rw [Filter.eventually_atTop] at source_tail_axis_extension_eq_component_sum_eventually
    rcases source_tail_axis_extension_eq_component_sum_eventually with
      ⟨cutoff, hcutoff_all⟩
    rw [Filter.eventually_atTop]
    refine ⟨cutoff, ?_⟩
    intro cutoff' hcutoff' n hn f
    have hsource :=
      hcutoff_all cutoff' hcutoff' n hn (sourceFor f)
        (sourceFor_admissible f)
    simpa [component, sourceFor_toSchwartz f] using hsource
  · intro i f z hlow hhigh
    simpa [component, stripComponentConstant] using
      source_component_strip_weighted_norm_le_realRadius i (sourceFor f)
        (sourceFor_admissible f) z hlow hhigh
  · rw [Filter.eventually_atTop] at source_component_tail_axis_norm_le_realHeight_eventually
    rcases source_component_tail_axis_norm_le_realHeight_eventually with
      ⟨cutoff, hcutoff_all⟩
    rw [Filter.eventually_atTop]
    refine ⟨cutoff, ?_⟩
    intro cutoff' hcutoff' n hn i f
    have hsource :=
      hcutoff_all cutoff' hcutoff' n hn i (sourceFor f)
        (sourceFor_admissible f)
    simpa [component, comparisonComponentConstant, sourceFor_toSchwartz f] using hsource

/--
Certificate constructor for the source-shaped componentwise p-series target.

It accepts component strip comparison against the two real-line profiles
`f` and `Fourier f`, plus eventual tail decomposition/domination on the
indexed trivial-zero sequence. Lean extracts one cutoff from the eventual
tail hypotheses, builds the explicit finite-prefix constant for that cutoff,
and returns the exact zero-argument shifted-radius certificate consumed by
the downstream p-series zero-data constructors.
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
    RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system := by
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
      zeroArgument_norm_le_shiftedRadialBound := ?_ }
  · intro f
    have hstrip_sum_nonneg :
        0 <=
          (Finset.univ.sum fun i : Index =>
            stripRealComparisonConstant i f *
                schwartzLineRealAxisShiftedSeminormConstant k f +
              stripFourierComparisonConstant i f *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier f)) := by
      exact Finset.sum_nonneg fun i _ => by
        exact add_nonneg
          (mul_nonneg (stripRealComparisonConstant_nonneg i f)
            (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
          (mul_nonneg (stripFourierComparisonConstant_nonneg i f)
            (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
              (SchwartzLineTestFunction.fourier f)))
    have htail_sum_nonneg :
        0 <=
          (Finset.univ.sum fun i : Index =>
            tailComparisonComponentConstant i f) := by
      exact Finset.sum_nonneg fun i _ =>
        tailComparisonComponentConstant_nonneg i f
    dsimp [certificateConstant]
    exact add_nonneg
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        hstrip_sum_nonneg)
      (add_nonneg
        (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k f)
        (mul_nonneg htail_sum_nonneg
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)))
  · intro f rho
    simpa [certificateConstant] using
      zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum
        (fun f n hn => hcutoff.1 n hn f)
        component_strip_norm_le_real_fourier
        (fun i f n hn => hcutoff.2 n hn i f)
        f rho

end RiemannWeilZeroArgumentShiftedRadiusDecayCertificate

namespace RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
The closedness target for a fixed zero argument: the set of tests satisfying the
weighted zero-locus estimate at `rho`.
-/
def zeroArgumentWeightedDecaySet
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (rho : ZetaZeroSubtype) :
    Set SchwartzLineTestFunction :=
  {f : SchwartzLineTestFunction |
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          decayExponent <=
      constant f}

theorem mem_zeroArgumentWeightedDecaySet_iff
    {system : SchwartzRiemannWeilExtensionSystem}
    {constant : SchwartzLineTestFunction -> Real}
    {decayExponent : Real}
    {rho : ZetaZeroSubtype}
    {f : SchwartzLineTestFunction} :
    f ∈ zeroArgumentWeightedDecaySet
        (system := system) constant decayExponent rho <->
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            decayExponent <=
        constant f :=
  Iff.rfl

/--
Continuity in the test-function variable closes a fixed zero-argument weighted
decay inequality.

This is the analytic shape expected from a genuine source class: prove that
`f ↦ extension f (riemannWeilZeroArgument rho)` and the seminorm bound
`constant` are continuous; Lean then supplies the closedness hypothesis needed
by the dense-core promotion theorem.
-/
theorem zeroArgumentWeightedDecaySet_closed_of_continuous
    {system : SchwartzRiemannWeilExtensionSystem}
    {constant : SchwartzLineTestFunction -> Real}
    {decayExponent : Real}
    {rho : ZetaZeroSubtype}
    (extension_continuous :
      Continuous fun f : SchwartzLineTestFunction =>
        system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (constant_continuous : Continuous constant) :
    IsClosed
      (zeroArgumentWeightedDecaySet
        (system := system) constant decayExponent rho) := by
  let radiusPower : Real :=
    (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ decayExponent
  have hleft :
      Continuous fun f : SchwartzLineTestFunction =>
        norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          radiusPower :=
    extension_continuous.norm.mul continuous_const
  simpa [zeroArgumentWeightedDecaySet, radiusPower] using
    isClosed_le hleft constant_continuous

/-- Critical-line specialization of the closed weighted zero-locus inequality
set: if `rho = 1/2 + i t`, closedness follows from the concrete Schwartz
real-evaluation continuity theorem. -/
theorem zeroArgumentWeightedDecaySet_closed_of_criticalLinePoint
    {system : SchwartzRiemannWeilExtensionSystem}
    {constant : SchwartzLineTestFunction -> Real}
    {decayExponent : Real}
    {rho : ZetaZeroSubtype}
    (t : Real)
    (hrho : (rho : Complex) = criticalLinePoint t)
    (constant_continuous : Continuous constant) :
    IsClosed
      (zeroArgumentWeightedDecaySet
        (system := system) constant decayExponent rho) :=
  zeroArgumentWeightedDecaySet_closed_of_continuous
    (system := system) (constant := constant)
    (decayExponent := decayExponent) (rho := rho)
    (zeroArgument_extension_continuous_of_criticalLinePoint
      system t hrho)
    constant_continuous

/--
Dense-core replacement for exact all-Schwartz source coverage.

If the weighted zero-locus estimate holds on a dense core of Schwartz tests and
the inequality locus is closed for each zero, then it holds for every Schwartz
test.  This is the p-series analogue of the Guinand-Weil density-promotion
route and avoids the previously checked no-go for exact all-Schwartz coverage.
-/
noncomputable def ofDenseCoreWeightedDecay
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (core : Set SchwartzLineTestFunction)
    (dense_core : closure core = Set.univ)
    (weightedDecaySet_closed :
      forall rho : ZetaZeroSubtype,
        IsClosed
          (zeroArgumentWeightedDecaySet
            (system := system) constant decayExponent rho))
    (core_zeroArgument_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        f ∈ core ->
          forall rho : ZetaZeroSubtype,
            norm
                (system.extension f
                  (riemannWeilZeroArgument (rho : Complex))) *
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  decayExponent <=
              constant f) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system where
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  zeroArgument_weighted_norm_le := by
    intro f rho
    have hclosure_subset :
        closure core ⊆
          zeroArgumentWeightedDecaySet
            (system := system) constant decayExponent rho :=
      closure_minimal
        (by
          intro g hg
          exact core_zeroArgument_weighted_norm_le g hg rho)
        (weightedDecaySet_closed rho)
    have hf_closure : f ∈ closure core := by
      rw [dense_core]
      exact Set.mem_univ f
    exact hclosure_subset hf_closure

/--
Dense-core weighted decay constructor with closedness discharged by continuity
of the zero-argument evaluation maps and of the bound constant.
-/
noncomputable def ofDenseCoreWeightedDecayOfContinuous
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (core : Set SchwartzLineTestFunction)
    (dense_core : closure core = Set.univ)
    (zeroArgument_extension_continuous :
      forall rho : ZetaZeroSubtype,
        Continuous fun f : SchwartzLineTestFunction =>
          system.extension f (riemannWeilZeroArgument (rho : Complex)))
    (constant_continuous : Continuous constant)
    (core_zeroArgument_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        f ∈ core ->
          forall rho : ZetaZeroSubtype,
            norm
                (system.extension f
                  (riemannWeilZeroArgument (rho : Complex))) *
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  decayExponent <=
              constant f) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofDenseCoreWeightedDecay
    (system := system) constant decayExponent constant_nonneg
    decayExponent_nonneg core dense_core
    (fun rho =>
      zeroArgumentWeightedDecaySet_closed_of_continuous
        (system := system) (constant := constant)
        (decayExponent := decayExponent) (rho := rho)
        (zeroArgument_extension_continuous rho) constant_continuous)
    core_zeroArgument_weighted_norm_le

/--
First-class dense-core p-series target for the zero-locus estimate.

This is the named project-normalized package for the restricted dense-core
route after the all-Schwartz source-coverage obstruction.  A future analytic
source proof chooses `core`, proves `dense_core`, continuity of each fixed
zero-argument evaluation, continuity of the global bound `constant`, and the
weighted zero-locus estimate on the core.  Lean then supplies both the
dense-core closedness promotion and the equivalent model source-image handoff.
-/
structure RiemannWeilDenseCoreZeroLocusPSeriesTarget
    (system : SchwartzRiemannWeilExtensionSystem) where
  core : Set SchwartzLineTestFunction
  dense_core : closure core = Set.univ
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg : forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  zeroArgument_extension_continuous :
    forall rho : ZetaZeroSubtype,
      Continuous fun f : SchwartzLineTestFunction =>
        system.extension f (riemannWeilZeroArgument (rho : Complex))
  constant_continuous : Continuous constant
  core_zeroArgument_weighted_norm_le :
    forall f : SchwartzLineTestFunction,
      f ∈ core ->
        forall rho : ZetaZeroSubtype,
          norm
              (system.extension f
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                decayExponent <=
            constant f

namespace RiemannWeilDenseCoreZeroLocusPSeriesTarget

/-- Package the chosen dense core as the model Guinand-Weil source class. -/
noncomputable def testData
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system) :
    GuinandWeilSourceTestFunctionClass :=
  GuinandWeilSourceTestFunctionClass.ofDenseCore target.core

/-- The admissible image of the model source class is exactly the chosen core. -/
theorem admissibleSchwartzImage_eq_core
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system) :
    guinandWeilAdmissibleSchwartzImage target.testData = target.core := by
  simpa [testData] using
    GuinandWeilSourceTestFunctionClass.guinandWeilAdmissibleSchwartzImage_ofDenseCore
      target.core

/-- The chosen dense core gives a dense admissible source image. -/
theorem dense_admissible_image
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system) :
    closure (guinandWeilAdmissibleSchwartzImage target.testData) =
      Set.univ := by
  simpa [testData] using
    GuinandWeilSourceTestFunctionClass.dense_admissibleSchwartzImage_ofDenseCore
      (core := target.core) target.dense_core

/-- Continuity closes every fixed zero-argument weighted inequality locus. -/
theorem weightedDecaySet_closed
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (rho : ZetaZeroSubtype) :
    IsClosed
      (zeroArgumentWeightedDecaySet
        (system := system) target.constant target.decayExponent rho) :=
  zeroArgumentWeightedDecaySet_closed_of_continuous
    (system := system) (constant := target.constant)
    (decayExponent := target.decayExponent) (rho := rho)
    (target.zeroArgument_extension_continuous rho)
    target.constant_continuous

/-- The core lies inside each fixed zero-argument weighted inequality locus. -/
theorem core_subset_weightedDecaySet
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system)
    (rho : ZetaZeroSubtype) :
    target.core ⊆
      zeroArgumentWeightedDecaySet
        (system := system) target.constant target.decayExponent rho := by
  intro f hf
  exact target.core_zeroArgument_weighted_norm_le f hf rho

/--
The chosen dense-core target directly gives the weighted zero-locus
certificate by the dense closedness route.
-/
noncomputable def toWeightedDecayCertificate
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilDenseCoreZeroLocusPSeriesTarget system) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofDenseCoreWeightedDecayOfContinuous
    (system := system) target.constant target.decayExponent
    target.constant_nonneg target.decayExponent_nonneg target.core
    target.dense_core target.zeroArgument_extension_continuous
    target.constant_continuous target.core_zeroArgument_weighted_norm_le

end RiemannWeilDenseCoreZeroLocusPSeriesTarget

/--
Critical-line dense-core instance of the zero-locus p-series target.

If every zero is represented by an explicit critical-line height, the whole
Schwartz line test space is a dense core.  The fixed-zero continuity fields are
the concrete real-evaluation continuity theorem, and the weighted zero-locus
estimate is ordinary real-axis Schwartz decay read at the chosen height.
-/
noncomputable def criticalLineDenseCoreZeroLocusPSeriesTarget
    (system : SchwartzRiemannWeilExtensionSystem)
    (k : Nat)
    (criticalLineHeight : ZetaZeroSubtype -> Real)
    (criticalLineHeight_spec :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) = criticalLinePoint (criticalLineHeight rho)) :
    RiemannWeilDenseCoreZeroLocusPSeriesTarget system where
  core := Set.univ
  dense_core := by
    simp
  constant := fun f => schwartzLineRealAxisShiftedSeminormConstant k f
  decayExponent := (k : Real)
  constant_nonneg := fun f =>
    schwartzLineRealAxisShiftedSeminormConstant_nonneg k f
  decayExponent_nonneg := by
    positivity
  zeroArgument_extension_continuous := by
    intro rho
    exact
      zeroArgument_extension_continuous_of_criticalLinePoint
        system (criticalLineHeight rho) (criticalLineHeight_spec rho)
  constant_continuous :=
    schwartzLineRealAxisShiftedSeminormConstant_continuous k
  core_zeroArgument_weighted_norm_le := by
    intro f _hf rho
    exact
      criticalLine_zeroArgument_extension_weighted_norm_le
        system k f rho (criticalLineHeight rho) (criticalLineHeight_spec rho)


/--
Source-image dense-core constructor for the weighted zero-locus certificate.

This is the replacement target for source Guinand-Weil p-series work: prove the
weighted zero-locus estimate on admissible source tests, prove their image is
dense in the project Schwartz test space, and prove each weighted inequality
locus is closed.
-/
noncomputable def ofSourceDenseWeightedDecay
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (dense_admissible_image :
      closure
          {f : SchwartzLineTestFunction |
            exists g : testData.SourceTestFunction,
              testData.admissible g /\ testData.toSchwartz g = f} =
        Set.univ)
    (weightedDecaySet_closed :
      forall rho : ZetaZeroSubtype,
        IsClosed
          (zeroArgumentWeightedDecaySet
            (system := system) constant decayExponent rho))
    (source_zeroArgument_weighted_norm_le :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall rho : ZetaZeroSubtype,
            norm
                (system.extension (testData.toSchwartz g)
                  (riemannWeilZeroArgument (rho : Complex))) *
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  decayExponent <=
              constant (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofDenseCoreWeightedDecay
    (system := system) constant decayExponent constant_nonneg
    decayExponent_nonneg
    {f : SchwartzLineTestFunction |
      exists g : testData.SourceTestFunction,
        testData.admissible g /\ testData.toSchwartz g = f}
    dense_admissible_image weightedDecaySet_closed
    (by
      intro f hf rho
      rcases hf with ⟨g, hg_admissible, hgf⟩
      simpa [hgf] using
        source_zeroArgument_weighted_norm_le g hg_admissible rho)

/--
Source-image dense constructor with the closedness field reduced to continuity
of the zero-argument evaluation maps and of the bound constant.
-/
noncomputable def ofSourceDenseWeightedDecayOfContinuous
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
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
    (source_zeroArgument_weighted_norm_le :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall rho : ZetaZeroSubtype,
            norm
                (system.extension (testData.toSchwartz g)
                  (riemannWeilZeroArgument (rho : Complex))) *
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  decayExponent <=
              constant (testData.toSchwartz g)) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseWeightedDecay
    (system := system) testData constant decayExponent constant_nonneg
    decayExponent_nonneg dense_admissible_image
    (fun rho =>
      zeroArgumentWeightedDecaySet_closed_of_continuous
        (system := system) (constant := constant)
        (decayExponent := decayExponent) (rho := rho)
        (zeroArgument_extension_continuous rho) constant_continuous)
    source_zeroArgument_weighted_norm_le

/--
Source-image corrected p-series estimate from the Guinand-Weil strip route.

This is the course-correction bridge: a source theorem only has to prove
horizontal-strip weighted decay for admissible source tests, plus the
completed-zeta normalization statement that project-known trivial zeroes
vanish from the zero-side extension.  Lean supplies the split between
nontrivial-zero strip arguments and trivial-zero arguments.
-/
theorem source_zeroArgument_weighted_norm_le_of_stripDecayAndTrivialVanishing
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (source_strip_weighted_norm_le :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (system.extension (testData.toSchwartz g) z) *
                    (norm z + 2) ^ decayExponent <=
                  constant (testData.toSchwartz g))
    (source_trivial_zeroArgument_extension_eq_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall rho : ZetaZeroSubtype,
            IsTrivialZetaZero (rho : Complex) ->
              system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex)) = 0)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          decayExponent <=
      constant (testData.toSchwartz g) := by
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rw [source_trivial_zeroArgument_extension_eq_zero g hg rho htrivial]
    simpa using constant_nonneg (testData.toSchwartz g)
  · have hstrip :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    exact
      source_strip_weighted_norm_le g hg
        (riemannWeilZeroArgument (rho : Complex)) hstrip.1 hstrip.2

/--
Dense source-image certificate constructor for the corrected Guinand-Weil
route.  The source-class work is the horizontal-strip estimate and the
trivial-zero normalization bridge; dense image and continuity then promote the
estimate to the full zero-locus weighted certificate.
-/
noncomputable def ofSourceDenseStripDecayAndTrivialVanishingOfContinuous
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
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
    (source_strip_weighted_norm_le :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (system.extension (testData.toSchwartz g) z) *
                    (norm z + 2) ^ decayExponent <=
                  constant (testData.toSchwartz g))
    (source_trivial_zeroArgument_extension_eq_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall rho : ZetaZeroSubtype,
            IsTrivialZetaZero (rho : Complex) ->
              system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex)) = 0) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseWeightedDecayOfContinuous
    (system := system) testData constant decayExponent constant_nonneg
    decayExponent_nonneg dense_admissible_image
    zeroArgument_extension_continuous constant_continuous
    (source_zeroArgument_weighted_norm_le_of_stripDecayAndTrivialVanishing
      (system := system) testData constant decayExponent constant_nonneg
      source_strip_weighted_norm_le
      source_trivial_zeroArgument_extension_eq_zero)

/--
First-class source-image p-series target for the zero-locus estimate.

This is the source-class analogue of
`RiemannWeilDenseCoreZeroLocusPSeriesTarget`: a future Paley-Wiener or
paper-specific Guinand-Weil source class supplies a dense admissible image,
continuity of fixed zero-argument evaluations, continuity of the ambient bound,
and the weighted zero-locus estimate on admissible source tests. Lean then
applies the source-image dense closedness route directly.
-/
structure RiemannWeilSourceImageZeroLocusPSeriesTarget
    (system : SchwartzRiemannWeilExtensionSystem) where
  testData : GuinandWeilSourceTestFunctionClass
  dense_admissible_image :
    closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg : forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  zeroArgument_extension_continuous :
    forall rho : ZetaZeroSubtype,
      Continuous fun f : SchwartzLineTestFunction =>
        system.extension f (riemannWeilZeroArgument (rho : Complex))
  constant_continuous : Continuous constant
  source_zeroArgument_weighted_norm_le :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        forall rho : ZetaZeroSubtype,
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                decayExponent <=
            constant (testData.toSchwartz g)

namespace RiemannWeilSourceImageZeroLocusPSeriesTarget

/-- Continuity closes every fixed zero-argument weighted inequality locus. -/
theorem weightedDecaySet_closed
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (rho : ZetaZeroSubtype) :
    IsClosed
      (zeroArgumentWeightedDecaySet
        (system := system) target.constant target.decayExponent rho) :=
  zeroArgumentWeightedDecaySet_closed_of_continuous
    (system := system) (constant := target.constant)
    (decayExponent := target.decayExponent) (rho := rho)
    (target.zeroArgument_extension_continuous rho)
    target.constant_continuous

/-- The admissible source image lies inside each fixed weighted inequality locus. -/
theorem admissible_image_subset_weightedDecaySet
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system)
    (rho : ZetaZeroSubtype) :
    guinandWeilAdmissibleSchwartzImage target.testData ⊆
      zeroArgumentWeightedDecaySet
        (system := system) target.constant target.decayExponent rho := by
  intro f hf
  rcases hf with ⟨g, hg_admissible, hgf⟩
  simpa [zeroArgumentWeightedDecaySet, hgf] using
    target.source_zeroArgument_weighted_norm_le g hg_admissible rho

/--
The chosen source-image target directly gives the weighted zero-locus
certificate by the dense closedness route.
-/
noncomputable def toWeightedDecayCertificate
    {system : SchwartzRiemannWeilExtensionSystem}
    (target : RiemannWeilSourceImageZeroLocusPSeriesTarget system) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system :=
  ofSourceDenseWeightedDecayOfContinuous
    (system := system) target.testData target.constant target.decayExponent
    target.constant_nonneg target.decayExponent_nonneg
    target.dense_admissible_image
    target.zeroArgument_extension_continuous
    target.constant_continuous
    target.source_zeroArgument_weighted_norm_le

end RiemannWeilSourceImageZeroLocusPSeriesTarget

/--
Compact smooth source tests satisfy the direct critical-line weighted
zero-locus estimate in the project normalization.

This is the source-side 80% estimate for the compact smooth source under an
explicit critical-line height realization: the source test is first read as its
project Schwartz image, then the named critical-line real-axis decay theorem
controls the zero argument.
-/
theorem compactlySupportedSmoothLineSource_source_zeroArgument_weighted_norm_le_of_criticalLine
    (system : SchwartzRiemannWeilExtensionSystem)
    (k : Nat)
    (criticalLineHeight : ZetaZeroSubtype -> Real)
    (criticalLineHeight_spec :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) = criticalLinePoint (criticalLineHeight rho))
    (g : compactlySupportedSmoothLineSource.SourceTestFunction)
    (_hg : compactlySupportedSmoothLineSource.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension
          (compactlySupportedSmoothLineSource.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (k : Real) <=
      schwartzLineRealAxisShiftedSeminormConstant k
        (compactlySupportedSmoothLineSource.toSchwartz g) := by
  exact
    criticalLine_zeroArgument_extension_weighted_norm_le
      system k (compactlySupportedSmoothLineSource.toSchwartz g)
      rho (criticalLineHeight rho) (criticalLineHeight_spec rho)

/--
Critical-line p-series source-image target for the concrete compactly supported
smooth real-line source.

The source-side weighted zero-locus estimate is the named theorem
`compactlySupportedSmoothLineSource_source_zeroArgument_weighted_norm_le_of_criticalLine`.
The density field is supplied separately, so this constructor can be used with
the checked compact-source density theorem or with another density proof for the
same source class.
-/
noncomputable def compactlySupportedSmoothCriticalLineSourceImageZeroLocusPSeriesTarget
    (system : SchwartzRiemannWeilExtensionSystem)
    (k : Nat)
    (criticalLineHeight : ZetaZeroSubtype -> Real)
    (criticalLineHeight_spec :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) = criticalLinePoint (criticalLineHeight rho))
    (dense_compactlySupportedSmoothLineSource :
      closure
          (guinandWeilAdmissibleSchwartzImage
            compactlySupportedSmoothLineSource) =
        Set.univ) :
    RiemannWeilSourceImageZeroLocusPSeriesTarget system where
  testData := compactlySupportedSmoothLineSource
  dense_admissible_image := dense_compactlySupportedSmoothLineSource
  constant := fun f => schwartzLineRealAxisShiftedSeminormConstant k f
  decayExponent := (k : Real)
  constant_nonneg := fun f =>
    schwartzLineRealAxisShiftedSeminormConstant_nonneg k f
  decayExponent_nonneg := by
    positivity
  zeroArgument_extension_continuous := by
    intro rho
    exact
      zeroArgument_extension_continuous_of_criticalLinePoint
        system (criticalLineHeight rho) (criticalLineHeight_spec rho)
  constant_continuous :=
    schwartzLineRealAxisShiftedSeminormConstant_continuous k
  source_zeroArgument_weighted_norm_le := by
    intro g hg rho
    exact
      compactlySupportedSmoothLineSource_source_zeroArgument_weighted_norm_le_of_criticalLine
        system k criticalLineHeight criticalLineHeight_spec g hg rho

end RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate
