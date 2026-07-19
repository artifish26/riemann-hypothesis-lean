import RiemannHypothesisProject.RiemannWeilShiftedRadius.SourceWeightSummability.OneAddWindowEndpoints

/-!
# Source-weight one-add summability variants

This module contains the one-add eventual-cutoff and closed-ball counting summability variants used before the real-height route.
-/

namespace RiemannHypothesisProject
/--
Eventual source indexed one-add estimates give a direct closed-ball p-series
shell bound for the actual real zero-side weight.

Lean extracts one shared indexed trivial-axis cutoff from the eventual source
decomposition and component `(1 + y)^k` tail hypotheses, then uses that cutoff
uniformly for every zero.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
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
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      cutoff k source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Eventual source indexed one-add estimates give the sharp direct closed-ball
p-series shell bound for the actual real zero-side weight.

The extracted cutoff is the same kind of shared eventual cutoff as in the
unsharpened theorem, but the indexed trivial-zero tail constant is the checked
`(9 / 7)^k` constant from the actual tail heights.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharp
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
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
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      cutoff k source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Eventual source indexed one-add estimates give the combined-sharp direct
closed-ball p-series shell bound for the actual real zero-side weight.

The extracted cutoff is shared across the source decomposition and tail
estimates, and the shell constant keeps `(5 / 4)^k` on the strip side and
`(9 / 7)^k` on the indexed trivial-zero tail.
-/
theorem exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
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
    source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg
      cutoff k source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Eventual source indexed one-add estimates plus cutoff-1 closed-ball polynomial
counting give absolute summability of the actual zero-side weight for a fixed
admissible source test.
-/
theorem summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
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
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      g hg with
    ⟨cutoff, hshell⟩
  let sourceF : SchwartzLineTestFunction := testData.toSchwartz g
  let sourceConstant : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k sourceF +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  have hsourceConstant_nonneg : 0 <= sourceConstant := by
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
    simpa [sourceConstant, sourceF] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k sourceF)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            haxis_sum_nonneg))
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
Eventual source indexed one-add estimates plus cutoff-1 closed-ball polynomial
counting give absolute summability with the sharp indexed-tail constant.

The decay package is the same closed-ball p-series package as the unsharpened
theorem, but its source constant uses `(9 / 7)^k` on the indexed trivial-zero
tail.
-/
theorem summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharp
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      g hg with
    ⟨cutoff, hshell⟩
  let sourceF : SchwartzLineTestFunction := testData.toSchwartz g
  let sourceConstant : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k sourceF +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  have hsourceConstant_nonneg : 0 <= sourceConstant := by
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
    simpa [sourceConstant, sourceF] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
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
The same fixed-source eventual indexed one-add hypotheses make the signed
`system.weight` series summable for the admissible source test.
-/
theorem summable_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
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
    summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k g hg
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

/--
The sharp fixed-source eventual indexed one-add hypotheses make the signed
`system.weight` series summable for the admissible source test.
-/
theorem summable_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k g hg
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

/--
Eventual source indexed one-add estimates plus cutoff-1 closed-ball polynomial
counting give absolute summability with both checked geometric sharpenings.

The closed-ball p-series source constant keeps `(5 / 4)^k` on the strip
component sum and `(9 / 7)^k` on the indexed trivial-zero tail component sum.
-/
theorem summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    exists_cutoff_source_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      g hg with
    ⟨cutoff, hshell⟩
  let sourceF : SchwartzLineTestFunction := testData.toSchwartz g
  let sourceConstant : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k sourceF +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceAxisComponentConstant i g))
  have hsourceConstant_nonneg : 0 <= sourceConstant := by
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
    simpa [sourceConstant, sourceF] using
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
The combined-sharp fixed-source eventual indexed one-add hypotheses make the
signed `system.weight` series summable for the admissible source test.
-/
theorem summable_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    summable_norm_source_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceAxisComponentConstant
      sourceStripComponentConstant_nonneg sourceAxisComponentConstant_nonneg k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum_eventually
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k g hg
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

end RiemannHypothesisProject
