import RiemannHypothesisProject.RiemannWeilShiftedRadius.FiniteComponentZeroArgument.OneAddSourceMajorants

/-!
# Finite-component real-height tails

This module contains the source real-height indexed-tail estimates and their project-majorant bridges.
-/

namespace RiemannHypothesisProject
/--
Source-side finite-component weighted zero-locus decay from an explicit
indexed trivial-axis tail.

This is the dense-source analogue of the repaired p-series route when the
positive-axis estimate is available only on the project-known trivial-zero
sequence. The finite prefix is the concrete system-level prefix sum, and the
tail is controlled componentwise by real-axis Schwartz values.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              sourceComparisonComponentConstant i g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g)) := by
  let stripConstant : Real :=
    Finset.univ.sum fun i : Index => sourceStripComponentConstant i g
  let comparisonConstant : Real :=
    Finset.univ.sum fun i : Index => sourceComparisonComponentConstant i g
  have hstrip_nonneg : 0 <= stripConstant := by
    exact Finset.sum_nonneg fun i _ =>
      sourceStripComponentConstant_nonneg i g hg
  have hcomparison_nonneg : 0 <= comparisonConstant := by
    exact Finset.sum_nonneg fun i _ =>
      sourceComparisonComponentConstant_nonneg i g hg
  have hstrip :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension (testData.toSchwartz g) z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant := by
    intro z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension (testData.toSchwartz g) z) <=
          (Finset.univ.sum fun i : Index => norm (sourceComponent i g z)) := by
      rw [source_strip_extension_eq_component_sum g hg z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => sourceComponent i g z)
    calc
      norm (system.extension (testData.toSchwartz g) z) * radiusPower
          <= (Finset.univ.sum fun i : Index =>
              norm (sourceComponent i g z)) * radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (sourceComponent i g z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            source_component_strip_weighted_norm_le_realRadius i g hg z hlow
              hhigh
  have htail :
      forall n : Nat,
        cutoff <= n ->
          norm
              (system.extension (testData.toSchwartz g)
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) <=
            comparisonConstant *
              norm
                ((testData.toSchwartz g)
                  (riemannWeilTrivialZeroArgumentHeight n)) := by
    intro n hn
    have hnorm :
        norm
            (system.extension (testData.toSchwartz g)
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) <=
          Finset.univ.sum fun i : Index =>
            norm
              (sourceComponent i g
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) := by
      rw [source_tail_axis_extension_eq_component_sum g hg n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        sourceComponent i g
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    calc
      norm
          (system.extension (testData.toSchwartz g)
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
          <= Finset.univ.sum fun i : Index =>
              norm
                (sourceComponent i g
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) := hnorm
      _ <= Finset.univ.sum fun i : Index =>
            sourceComparisonComponentConstant i g *
              norm
                ((testData.toSchwartz g)
                  (riemannWeilTrivialZeroArgumentHeight n)) :=
        Finset.sum_le_sum fun i _ => by
          exact source_component_tail_axis_norm_le_realHeight i g hg n hn
      _ = (Finset.univ.sum fun i : Index =>
            sourceComparisonComponentConstant i g) *
          norm
            ((testData.toSchwartz g)
              (riemannWeilTrivialZeroArgumentHeight n)) := by
        simp [Finset.sum_mul]
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
      (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    by_cases hn : n < cutoff
    · have hprefix :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) := by
        simpa [harg] using
          riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) n hn
      exact hprefix.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have htail_nonneg :
            0 <= comparisonConstant *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (testData.toSchwartz g) := by
          exact mul_nonneg hcomparison_nonneg
            (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
              (testData.toSchwartz g))
        linarith)
    · have hge : cutoff <= n := Nat.le_of_not_gt hn
      let height : Real := riemannWeilTrivialZeroArgumentHeight n
      let radiusPower : Real :=
        (norm ((height : Complex) * Complex.I) + 2) ^ (k : Real)
      have hradiusPower_nonneg : 0 <= radiusPower := by
        dsimp [radiusPower]
        exact le_of_lt
          (Real.rpow_pos_of_pos
            (by
              have hnorm_nonneg :
                  0 <= norm ((height : Complex) * Complex.I) := norm_nonneg _
              linarith)
            (k : Real))
      have hnorm :
          norm
              (system.extension (testData.toSchwartz g)
                ((height : Complex) * Complex.I)) <=
            comparisonConstant * norm ((testData.toSchwartz g) height) := by
        simpa [height] using htail n hge
      have hweighted :
          norm
              (system.extension (testData.toSchwartz g)
                ((height : Complex) * Complex.I)) *
              radiusPower <=
            (comparisonConstant * norm ((testData.toSchwartz g) height)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      have hheight_nonneg : 0 <= height := by
        dsimp [height]
        exact le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n)
      have hreal_norm : norm ((height : Complex)) = height := by
        rw [Complex.norm_real, Real.norm_of_nonneg hheight_nonneg]
      have haxis_norm :
          norm ((height : Complex) * Complex.I) =
            norm ((height : Complex)) := by
        rw [norm_mul, Complex.norm_I, mul_one]
      have hschwartz :
          norm ((testData.toSchwartz g) height) * radiusPower <=
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g) := by
        simpa [height, radiusPower, haxis_norm, hreal_norm] using
          schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast
            k (testData.toSchwartz g) height
      have hscaled :
          comparisonConstant *
              (norm ((testData.toSchwartz g) height) * radiusPower) <=
            comparisonConstant *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) :=
        mul_le_mul_of_nonneg_left hschwartz hcomparison_nonneg
      have htail_weighted :
          norm
              (system.extension (testData.toSchwartz g)
                ((height : Complex) * Complex.I)) *
              (norm ((height : Complex) * Complex.I) + 2) ^ (k : Real) <=
            comparisonConstant *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) := by
        calc
          norm
              (system.extension (testData.toSchwartz g)
                ((height : Complex) * Complex.I)) *
              (norm ((height : Complex) * Complex.I) + 2) ^ (k : Real)
              = norm
                  (system.extension (testData.toSchwartz g)
                    ((height : Complex) * Complex.I)) *
                radiusPower := by
                  rfl
          _ <=
              (comparisonConstant *
                  norm ((testData.toSchwartz g) height)) * radiusPower :=
            hweighted
          _ = comparisonConstant *
              (norm ((testData.toSchwartz g) height) * radiusPower) := by
            ring
          _ <= comparisonConstant *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) := hscaled
      have htail_zeroArgument :
          norm
              (system.extension (testData.toSchwartz g)
                (riemannWeilZeroArgument (rho : Complex))) *
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real) <=
            comparisonConstant *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) := by
        simpa [harg, height] using htail_weighted
      exact htail_zeroArgument.trans (by
        have hstrip_nonneg' :
            0 <= (2 : Real) ^ k * stripConstant := by
          exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            hstrip_nonneg
        have hprefix_nonneg :
            0 <=
              riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k (testData.toSchwartz g) :=
          riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k (testData.toSchwartz g)
        linarith)
  · have hstrip_bounds :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    have hstrip_shifted :=
      fixedHorizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (fun z : Complex => system.extension (testData.toSchwartz g) z)
        stripConstant k hstrip (riemannWeilZeroArgument (rho : Complex))
        hstrip_bounds.1 hstrip_bounds.2
    exact hstrip_shifted.trans (by
      have hstrip_nonneg' :
          0 <= (2 : Real) ^ k * stripConstant := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_nonneg
      have hprefix_nonneg :
          0 <=
            riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) :=
        riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
          (system := system) cutoff k (testData.toSchwartz g)
      have htail_nonneg :
          0 <= comparisonConstant *
              schwartzLineRealAxisShiftedSeminormConstant k
                (testData.toSchwartz g) := by
        exact mul_nonneg hcomparison_nonneg
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
            (testData.toSchwartz g))
      linarith)

/--
Source-side real-radius indexed-tail weighted decay survives enlarging the
finite prefix cutoff.

The component tail proof is used at `cutoff`; the explicit source finite
prefix may be reported at any larger `cutoff'`.
-/
theorem source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              sourceComparisonComponentConstant i g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g)) := by
  have hbase :=
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      source_tail_axis_extension_eq_component_sum
      source_component_strip_weighted_norm_le_realRadius
      source_component_tail_axis_norm_le_realHeight
      g hg rho
  have hprefix :=
    riemannWeilIndexedTrivialAxisPrefixSumConstant_mono
      (system := system) (cutoff := cutoff) (cutoff' := cutoff') (k := k)
      hcutoff (testData.toSchwartz g)
  linarith

/--
Source-side real-radius indexed-tail exact-denominator decay survives
enlarging the finite prefix cutoff.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              sourceComparisonComponentConstant i g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g))) *
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            sourceComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceComparisonComponentConstant
        sourceStripComponentConstant_nonneg
        sourceComparisonComponentConstant_nonneg hcutoff
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_norm_le_realHeight
        g hg rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted

/--
Source-side exact-norm zero-locus decay from a finite-component real-radius
strip estimate and an indexed trivial-axis real-height tail estimate.

This is the source-level p-series denominator form of the indexed-tail
finite-component estimate; it keeps the finite trivial-axis prefix explicit
and bounds only the tail by real-axis Schwartz decay.
-/
theorem source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    norm
        (system.extension (testData.toSchwartz g)
          (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            sourceStripComponentConstant i g) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k (testData.toSchwartz g) +
          (Finset.univ.sum fun i : Index =>
              sourceComparisonComponentConstant i g) *
            schwartzLineRealAxisShiftedSeminormConstant k
              (testData.toSchwartz g))) *
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          sourceStripComponentConstant i g) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k (testData.toSchwartz g) +
        (Finset.univ.sum fun i : Index =>
            sourceComparisonComponentConstant i g) *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g))
  have hweighted :
      norm (system.extension (testData.toSchwartz g) zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) testData sourceComponent
        sourceStripComponentConstant sourceComparisonComponentConstant
        sourceStripComponentConstant_nonneg
        sourceComparisonComponentConstant_nonneg cutoff k
        source_strip_extension_eq_component_sum
        source_tail_axis_extension_eq_component_sum
        source_component_strip_weighted_norm_le_realRadius
        source_component_tail_axis_norm_le_realHeight g hg rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension (testData.toSchwartz g) zeroArgument)
      (zeroArgument := zeroArgument) (k := k) (bound := bound) hweighted

/--
Source-side eventual-tail exact-norm zero-locus decay.

Analytic source estimates often prove the trivial-axis decomposition and
real-height domination only for all sufficiently large indexed trivial zeroes.
This theorem extracts a cutoff from those eventual hypotheses and applies the
source-level indexed-tail exact-norm estimate with the finite prefix left
explicit.
-/
theorem exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceStripComponentConstant i g) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceComparisonComponentConstant i g) *
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
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
    source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Source-side eventual-tail weighted zero-locus decay from finite-component
real-radius strip envelopes.

This is the weighted companion to
`exists_cutoff_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail`.
Lean extracts a cutoff from the eventual indexed trivial-axis decomposition
and tail domination hypotheses, then applies the fixed-cutoff weighted source
estimate with the finite prefix left explicit.
-/
theorem exists_cutoff_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
              sourceStripComponentConstant i g) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceComparisonComponentConstant i g) *
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
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Eventually-valid source exact-denominator real-radius indexed-tail estimate.

Once the source indexed trivial-axis decomposition and component real-height
domination hold eventually, the source exact zero-locus decay estimate holds
for every sufficiently large finite-prefix cutoff.
-/
theorem eventually_source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm
          (system.extension (testData.toSchwartz g)
            (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              sourceStripComponentConstant i g) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceComparisonComponentConstant i g) *
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
    source_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

/--
Eventually-valid source weighted real-radius indexed-tail estimate.

This keeps the finite prefix visible while allowing source trivial-axis
decomposition and component real-height domination only eventually.
-/
theorem eventually_source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceComponent :
      Index -> testData.SourceTestFunction -> Complex -> Complex)
    (sourceStripComponentConstant sourceComparisonComponentConstant :
      Index -> testData.SourceTestFunction -> Real)
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
              sourceStripComponentConstant i g) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k (testData.toSchwartz g) +
            (Finset.univ.sum fun i : Index =>
                sourceComparisonComponentConstant i g) *
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
    source_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) testData sourceComponent
      sourceStripComponentConstant sourceComparisonComponentConstant
      sourceStripComponentConstant_nonneg
      sourceComparisonComponentConstant_nonneg cutoff k
      source_strip_extension_eq_component_sum
      (fun g hg n hn => hcutoff.1 n hn g hg)
      source_component_strip_weighted_norm_le_realRadius
      (fun i g hg n hn => hcutoff.2 n hn i g hg)
      g hg rho

end RiemannHypothesisProject
