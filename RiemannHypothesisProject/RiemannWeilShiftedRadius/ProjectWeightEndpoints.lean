import RiemannHypothesisProject.RiemannWeilShiftedRadius.SourceWeightSummability.RealFourierEndpoints

/-!
# Project-side shifted-radius weight endpoints

This module contains project-side zero-argument weighted/norm estimates and
system.weight closed-ball shell bounds that sit downstream of the source
summability helpers.
-/

namespace RiemannHypothesisProject

/--
Exact-denominator bound for the completed-zeta normalized zero weight from
horizontal-strip decay only.

The trivial-zero branch is zero by normalization.  The nontrivial branch uses
the checked fact that the zero argument lies in the closed horizontal strip.
-/
theorem completedZetaNormalizedZeroWeight_norm_le_of_horizontalStripDecay
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (completedZetaNormalizedZeroWeight system f rho) <=
      constant f *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  classical
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have hfactor_nonneg :
        0 <=
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
      exact one_div_nonneg.mpr
        (Real.rpow_nonneg
          (by
            have hnorm_nonneg :
                0 <= norm (riemannWeilZeroArgument (rho : Complex)) :=
              norm_nonneg _
            linarith)
          (k : Real))
    have hright_nonneg :
        0 <=
          constant f *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)) :=
      mul_nonneg (constant_nonneg f) hfactor_nonneg
    simpa [completedZetaNormalizedZeroWeight, htrivial] using hright_nonneg
  · have hstrip :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    have hweighted :
        norm
            (system.extension f
              (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          constant f :=
      horizontal_strip_weighted_norm_le f
        (riemannWeilZeroArgument (rho : Complex)) hstrip.1 hstrip.2
    have hzero :
        norm
            (system.extension f
              (riemannWeilZeroArgument (rho : Complex))) <=
          constant f *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)) :=
      norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
        (value := system.extension f
          (riemannWeilZeroArgument (rho : Complex)))
        (zeroArgument := riemannWeilZeroArgument (rho : Complex))
        (k := k) (bound := constant f) hweighted
    have hweight_le :
        norm (system.weight f rho) <=
          norm
            (system.extension f
              (riemannWeilZeroArgument (rho : Complex))) := by
      simpa [SchwartzRiemannWeilExtensionSystem.zeroValue] using
        system.norm_weight_le_norm_zeroValue f rho
    exact
      (by
        simpa [completedZetaNormalizedZeroWeight, htrivial] using
          hweight_le.trans hzero)

/--
Closed-ball cutoff-1 shell bound for the completed-zeta normalized zero weight
from horizontal-strip decay only.
-/
theorem completedZetaNormalizedZeroWeight_norm_le_closedBall_cutoffOneShellBound_of_horizontalStripDecay
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (completedZetaNormalizedZeroWeight system f rho) <=
      constant f *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  classical
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have hfactor_nonneg :
        0 <=
          (1 /
            |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
      exact one_div_nonneg.mpr
        (Real.rpow_nonneg
          (abs_nonneg
            ((((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                rho - 1 : Nat) : Real) + 1)))
          (k : Real))
    have hright_nonneg :
        0 <=
          constant f *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) :=
      mul_nonneg (constant_nonneg f) hfactor_nonneg
    simpa [completedZetaNormalizedZeroWeight, htrivial] using hright_nonneg
  · have hstrip :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    have hweighted :
        norm
            (system.extension f
              (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          constant f :=
      horizontal_strip_weighted_norm_le f
        (riemannWeilZeroArgument (rho : Complex)) hstrip.1 hstrip.2
    have hzero :
        norm
            (system.extension f
              (riemannWeilZeroArgument (rho : Complex))) <=
          constant f *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)) :=
      norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
        (value := system.extension f
          (riemannWeilZeroArgument (rho : Complex)))
        (zeroArgument := riemannWeilZeroArgument (rho : Complex))
        (k := k) (bound := constant f) hweighted
    have hshell :
        norm (system.weight f rho) <=
          constant f *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) :=
      norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
        (system := system) f rho (constant f) k (constant_nonneg f) hzero
    simpa [completedZetaNormalizedZeroWeight, htrivial] using hshell

/--
Horizontal-strip decay plus cutoff-1 closed-ball polynomial counting gives
absolute summability of the completed-zeta normalized zero weight.
-/
theorem summable_norm_completedZetaNormalizedZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable
      (fun rho : ZetaZeroSubtype =>
        norm (completedZetaNormalizedZeroWeight system f rho)) := by
  let normalizedWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    completedZetaNormalizedZeroWeight system
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := normalizedWeight
      cutoff := 1
      shellBound := fun f n =>
        constant f * (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := constant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := constant_nonneg
      shellBound_nonneg := by
        intro f n
        exact mul_nonneg (constant_nonneg f)
          (one_div_nonneg.mpr
            (Real.rpow_nonneg
              (abs_nonneg ((((n - 1 : Nat) : Real) + 1)))
              (k : Real)))
      tail_shellBound_le := by
        intro _f _n
        dsimp
        simp
      norm_weight_le_shellBound := by
        intro f rho
        simpa [normalizedWeight] using
          completedZetaNormalizedZeroWeight_norm_le_closedBall_cutoffOneShellBound_of_horizontalStripDecay
            (system := system) constant constant_nonneg k
            horizontal_strip_weighted_norm_le f rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, normalizedWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The completed-zeta normalized zero weight is summable under horizontal-strip
decay and closed-ball polynomial counting.
-/
theorem summable_completedZetaNormalizedZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (completedZetaNormalizedZeroWeight system f) := by
  have hnorm :
      Summable
        (fun rho : ZetaZeroSubtype =>
          norm (completedZetaNormalizedZeroWeight system f rho)) :=
    summable_norm_completedZetaNormalizedZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

/--
Horizontal-strip decay plus cutoff-1 closed-ball polynomial counting gives
absolute summability of the nontrivial-zero project weight.
-/
theorem summable_norm_nontrivialZetaZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable
      (fun rho : ↑nontrivialZetaZeroSet =>
        norm (nontrivialZetaZeroWeight system f rho)) := by
  have hnorm :
      Summable
        (fun rho : ZetaZeroSubtype =>
          norm (completedZetaNormalizedZeroWeight system f rho)) :=
    summable_norm_completedZetaNormalizedZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k f
  exact
    (summable_norm_completedZetaNormalizedZeroWeight_iff_summable_norm_nontrivialZetaZeroWeight
      system f).mp hnorm

/--
Horizontal-strip decay plus cutoff-1 closed-ball polynomial counting gives
summability of the nontrivial-zero project weight.
-/
theorem summable_nontrivialZetaZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (nontrivialZetaZeroWeight system f) := by
  have hnorm :
      Summable
        (fun rho : ↑nontrivialZetaZeroSet =>
          norm (nontrivialZetaZeroWeight system f rho)) :=
    summable_norm_nontrivialZetaZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k f
  exact hnorm.of_norm

section CompletedZetaNormalizedZeroWeightWindowEndpoints

variable {system : SchwartzRiemannWeilExtensionSystem}
variable (constant : SchwartzLineTestFunction -> Real)
variable (constant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= constant f)
variable (k : Nat)
variable (horizontal_strip_weighted_norm_le :
  forall (f : SchwartzLineTestFunction) (z : Complex),
    -(1 / 2 : Real) <= z.im ->
      z.im <= (1 / 2 : Real) ->
        norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
          constant f)
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include constant constant_nonneg k horizontal_strip_weighted_norm_le
  counting counting_cutoff_eq growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the completed-zeta normalized zero weight
converge to the corresponding infinite zero-side sum.
-/
theorem tendsto_completedZetaNormalizedZeroWeight_zetaZeroWindowSum_of_horizontalStripDecay_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n
          (completedZetaNormalizedZeroWeight system f))
      Filter.atTop
      (nhds
        (tsum
          (fun rho : ZetaZeroSubtype =>
            completedZetaNormalizedZeroWeight system f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_completedZetaNormalizedZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k f)

/--
Finite compact-exhaustion windows of the completed-zeta normalized zero weight
converge to the nontrivial-zero subtype sum.
-/
theorem tendsto_completedZetaNormalizedZeroWeight_zetaZeroWindowSum_to_nontrivialZetaZeroWeight_tsum_of_horizontalStripDecay_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        windowExhaustion.zetaZeroWindowSum n
          (completedZetaNormalizedZeroWeight system f))
      Filter.atTop
      (nhds (tsum (nontrivialZetaZeroWeight system f))) := by
  simpa [tsum_completedZetaNormalizedZeroWeight_eq_tsum_nontrivialZetaZeroWeight]
    using
      tendsto_completedZetaNormalizedZeroWeight_zetaZeroWindowSum_of_horizontalStripDecay_closedBallPolynomialCounting
        (system := system) constant constant_nonneg k
        horizontal_strip_weighted_norm_le counting counting_cutoff_eq
        growth_add_one_lt_k windowExhaustion f

/--
Filtered nontrivial subwindows of a compact exhaustion converge to the
nontrivial-zero subtype sum.
-/
theorem tendsto_nontrivialZetaZeroFinset_sum_to_nontrivialZetaZeroWeight_tsum_of_horizontalStripDecay_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        (nontrivialZetaZeroFinset
          (windowExhaustion.zetaZeroSubtypeFinset n)).sum
          (system.weight f))
      Filter.atTop
      (nhds (tsum (nontrivialZetaZeroWeight system f))) := by
  have hwindow :=
    tendsto_completedZetaNormalizedZeroWeight_zetaZeroWindowSum_to_nontrivialZetaZeroWeight_tsum_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k windowExhaustion f
  simpa [ComplexCompactExhaustion.zetaZeroWindowSum,
    sum_completedZetaNormalizedZeroWeight_eq_sum_nontrivialZetaZeroFinset]
    using hwindow

/--
The signed finite-window error for the completed-zeta normalized zero weight
tends to zero.
-/
theorem tendsto_completedZetaNormalizedZeroWeight_zetaZeroWindowErrorNorm_of_horizontalStripDecay_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum
              (fun rho : ZetaZeroSubtype =>
                completedZetaNormalizedZeroWeight system f rho) -
            windowExhaustion.zetaZeroWindowSum n
              (completedZetaNormalizedZeroWeight system f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_completedZetaNormalizedZeroWeight_zetaZeroWindowSum_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum
            (fun rho : ZetaZeroSubtype =>
              completedZetaNormalizedZeroWeight system f rho))
        Filter.atTop
        (nhds
          (tsum
            (fun rho : ZetaZeroSubtype =>
              completedZetaNormalizedZeroWeight system f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/--
For every positive tolerance, the completed-zeta normalized finite-window
signed error is eventually below that tolerance.
-/
theorem eventually_completedZetaNormalizedZeroWeight_zetaZeroWindowErrorNorm_lt_of_horizontalStripDecay_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum
                (fun rho : ZetaZeroSubtype =>
                  completedZetaNormalizedZeroWeight system f rho) -
              windowExhaustion.zetaZeroWindowSum n
                (completedZetaNormalizedZeroWeight system f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_completedZetaNormalizedZeroWeight_zetaZeroWindowErrorNorm_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the completed-zeta normalized zero weight outside
growing compact zero windows tends to zero.
-/
theorem tendsto_norm_completedZetaNormalizedZeroWeight_zetaZeroWindowTail_of_horizontalStripDecay_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum
            (fun rho : ZetaZeroSubtype =>
              norm (completedZetaNormalizedZeroWeight system f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype =>
              norm (completedZetaNormalizedZeroWeight system f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable
        (fun rho : ZetaZeroSubtype =>
          norm (completedZetaNormalizedZeroWeight system f rho)) :=
    summable_norm_completedZetaNormalizedZeroWeight_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype =>
              norm (completedZetaNormalizedZeroWeight system f rho)))
        Filter.atTop
        (nhds
          (tsum
            (fun rho : ZetaZeroSubtype =>
              norm (completedZetaNormalizedZeroWeight system f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum
            (fun rho : ZetaZeroSubtype =>
              norm (completedZetaNormalizedZeroWeight system f rho)))
        Filter.atTop
        (nhds
          (tsum
            (fun rho : ZetaZeroSubtype =>
              norm (completedZetaNormalizedZeroWeight system f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the completed-zeta normalized absolute norm tail
is eventually below that tolerance.
-/
theorem eventually_norm_completedZetaNormalizedZeroWeight_zetaZeroWindowTail_lt_of_horizontalStripDecay_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum
            (fun rho : ZetaZeroSubtype =>
              norm (completedZetaNormalizedZeroWeight system f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype =>
                norm (completedZetaNormalizedZeroWeight system f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_completedZetaNormalizedZeroWeight_zetaZeroWindowTail_of_horizontalStripDecay_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le counting counting_cutoff_eq
      growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

end CompletedZetaNormalizedZeroWeightWindowEndpoints

/--
Corrected project-side zero-locus weighted decay from horizontal strip decay
and completed-zeta trivial-zero normalization.

The nontrivial zero arguments already lie in the closed horizontal strip.  The
trivial zero arguments contribute zero in this normalization, so no separate
positive-imaginary-axis tail theorem is required.
-/
theorem zeroArgument_weighted_norm_le_of_horizontalStripDecayAndTrivialVanishing
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (trivial_zeroArgument_extension_eq_zero :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      constant f := by
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · rw [trivial_zeroArgument_extension_eq_zero f rho htrivial]
    simpa using constant_nonneg f
  · have hstrip :=
      riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
        (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
    exact
      horizontal_strip_weighted_norm_le f
        (riemannWeilZeroArgument (rho : Complex)) hstrip.1 hstrip.2

/--
Exact-denominator zero-locus decay for the corrected horizontal-strip route.
-/
theorem zeroArgument_norm_le_of_horizontalStripDecayAndTrivialVanishing
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (trivial_zeroArgument_extension_eq_zero :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      constant f *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  have hweighted :
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        constant f :=
    zeroArgument_weighted_norm_le_of_horizontalStripDecayAndTrivialVanishing
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero f rho
  simpa using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension f (riemannWeilZeroArgument (rho : Complex)))
      (zeroArgument := riemannWeilZeroArgument (rho : Complex))
      (k := k) (bound := constant f) hweighted

/--
Corrected horizontal-strip route to the closed-ball cutoff-1 p-series shell
bound for the actual project-side `system.weight`.
-/
theorem weight_norm_le_closedBall_cutoffOneShellBound_of_horizontalStripDecayAndTrivialVanishing
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (trivial_zeroArgument_extension_eq_zero :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      constant f *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  have hzero :
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        constant f *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) :=
    zeroArgument_norm_le_of_horizontalStripDecayAndTrivialVanishing
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero f rho
  simpa using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) f rho (constant f) k (constant_nonneg f) hzero

/--
Horizontal strip decay plus trivial-zero vanishing and cutoff-1 closed-ball
polynomial counting give absolute summability of the actual project-side zero
weight.
-/
theorem summable_norm_weight_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (trivial_zeroArgument_extension_eq_zero :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  let projectConstant : Real := constant f
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    simpa [projectConstant] using constant_nonneg f
  let projectWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight f rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := projectWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
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
        simpa [projectWeight, projectConstant] using
          weight_norm_le_closedBall_cutoffOneShellBound_of_horizontalStripDecayAndTrivialVanishing
            (system := system) constant constant_nonneg k
            horizontal_strip_weighted_norm_le
            trivial_zeroArgument_extension_eq_zero f rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, projectWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The corrected horizontal-strip route makes the signed project-side
`system.weight` series summable.
-/
theorem summable_weight_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (constant : SchwartzLineTestFunction -> Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (k : Nat)
    (horizontal_strip_weighted_norm_le :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
              constant f)
    (trivial_zeroArgument_extension_eq_zero :
      forall f : SchwartzLineTestFunction,
        forall rho : ZetaZeroSubtype,
          IsTrivialZetaZero (rho : Complex) ->
            system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  have hnorm :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero
      counting counting_cutoff_eq growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

section HorizontalStripProjectWeightWindowEndpoints

variable {system : SchwartzRiemannWeilExtensionSystem}
variable (constant : SchwartzLineTestFunction -> Real)
variable (constant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= constant f)
variable (k : Nat)
variable (horizontal_strip_weighted_norm_le :
  forall (f : SchwartzLineTestFunction) (z : Complex),
    -(1 / 2 : Real) <= z.im ->
      z.im <= (1 / 2 : Real) ->
        norm (system.extension f z) * (norm z + 2) ^ (k : Real) <=
          constant f)
variable (trivial_zeroArgument_extension_eq_zero :
  forall f : SchwartzLineTestFunction,
    forall rho : ZetaZeroSubtype,
      IsTrivialZetaZero (rho : Complex) ->
        system.extension f (riemannWeilZeroArgument (rho : Complex)) = 0)
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include constant constant_nonneg k horizontal_strip_weighted_norm_le
  trivial_zeroArgument_extension_eq_zero counting counting_cutoff_eq
  growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the corrected horizontal-strip project
`system.weight` series converge to the signed infinite zero-side series.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat => windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_weight_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero
      counting counting_cutoff_eq growth_add_one_lt_k f)

/-- The corrected horizontal-strip signed finite-window error norm tends to zero. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_weight_zetaZeroWindowSum_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/--
For every positive tolerance, the corrected horizontal-strip signed
finite-window error is eventually below that tolerance.
-/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
              windowExhaustion.zetaZeroWindowSum n (system.weight f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_weight_zetaZeroWindowErrorNorm_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the corrected horizontal-strip project
`system.weight` series outside growing compact zero windows tends to zero.
-/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero
      counting counting_cutoff_eq growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the corrected horizontal-strip absolute norm tail
is eventually below that tolerance.
-/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_weight_zetaZeroWindowTail_of_horizontalStripDecayAndTrivialVanishing_closedBallPolynomialCounting
      (system := system) constant constant_nonneg k
      horizontal_strip_weighted_norm_le
      trivial_zeroArgument_extension_eq_zero
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

end HorizontalStripProjectWeightWindowEndpoints

/--
Direct zero-locus weighted decay from a real-radius strip envelope plus an
indexed finite-prefix/tail trivial-axis estimate.

This avoids asking the source proof for a uniform positive-imaginary-axis
bound at every height. It is enough to bound exactly the project-known trivial
zero sequence, with finite exceptional heights separated from the tail.
-/
theorem zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisPrefixTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant prefixAxisConstant tailAxisConstant :
      SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (prefixAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixAxisConstant f)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (prefix_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          n < cutoff ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              prefixAxisConstant f)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * stripConstant f +
        (prefixAxisConstant f + tailAxisConstant f) := by
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have haxis :=
      trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisPrefixTail
        (system := system) prefixAxisConstant tailAxisConstant
        prefixAxisConstant_nonneg tailAxisConstant_nonneg cutoff k
        prefix_trivialAxis_weighted_norm_le
        tail_trivialAxis_weighted_norm_le f rho htrivial
    exact haxis.trans (by
      have hstrip_nonneg :
          0 <= (2 : Real) ^ k * stripConstant f := by
        exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (stripConstant_nonneg f)
      linarith)
  · have hstrip :=
      nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (system := system) stripConstant k
        strip_extension_weighted_norm_le_realRadius f rho htrivial
    exact hstrip.trans (by
      have haxis_nonneg :
          0 <= prefixAxisConstant f + tailAxisConstant f := by
        exact add_nonneg (prefixAxisConstant_nonneg f)
          (tailAxisConstant_nonneg f)
      linarith)

/--
Sharp direct zero-locus weighted decay from a real-radius strip envelope plus
an indexed finite-prefix/tail trivial-axis estimate.

This is the same split strip/tail theorem, but the nontrivial-zero strip side
uses the actual closed-strip geometry and pays `(5 / 4)^k` instead of `2^k`.
-/
theorem zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisPrefixTail_sharpStrip
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant prefixAxisConstant tailAxisConstant :
      SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (prefixAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixAxisConstant f)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (prefix_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          n < cutoff ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              prefixAxisConstant f)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k * stripConstant f +
        (prefixAxisConstant f + tailAxisConstant f) := by
  by_cases htrivial : IsTrivialZetaZero (rho : Complex)
  · have haxis :=
      trivialZeroArgument_weighted_norm_le_of_indexedTrivialAxisPrefixTail
        (system := system) prefixAxisConstant tailAxisConstant
        prefixAxisConstant_nonneg tailAxisConstant_nonneg cutoff k
        prefix_trivialAxis_weighted_norm_le
        tail_trivialAxis_weighted_norm_le f rho htrivial
    exact haxis.trans (by
      have hstrip_nonneg :
          0 <= ((5 : Real) / 4) ^ k * stripConstant f := by
        exact mul_nonneg
          (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          (stripConstant_nonneg f)
      linarith)
  · have hstrip :=
      nontrivialZeroArgument_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast_sharp
        (system := system) stripConstant k
        strip_extension_weighted_norm_le_realRadius f rho htrivial
    exact hstrip.trans (by
      have haxis_nonneg :
          0 <= prefixAxisConstant f + tailAxisConstant f := by
        exact add_nonneg (prefixAxisConstant_nonneg f)
          (tailAxisConstant_nonneg f)
      linarith)

/--
Exact-norm zero-locus decay with the p-series denominator, derived from a
real-radius strip envelope and indexed finite-prefix/tail control of the
project-known trivial zero sequence.
-/
theorem zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisPrefixTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant prefixAxisConstant tailAxisConstant :
      SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (prefixAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixAxisConstant f)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (prefix_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          n < cutoff ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              prefixAxisConstant f)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k * stripConstant f +
          (prefixAxisConstant f + tailAxisConstant f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let radiusPower : Real := (norm zeroArgument + 2) ^ (k : Real)
  have hbase_pos : 0 < norm zeroArgument + 2 := by
    have hnorm_nonneg : 0 <= norm zeroArgument := norm_nonneg zeroArgument
    linarith
  have hradiusPower_pos : 0 < radiusPower := by
    dsimp [radiusPower]
    exact Real.rpow_pos_of_pos hbase_pos (k : Real)
  have hweighted :
      norm (system.extension f zeroArgument) * radiusPower <=
        (2 : Real) ^ k * stripConstant f +
          (prefixAxisConstant f + tailAxisConstant f) := by
    simpa [zeroArgument, radiusPower] using
      zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisPrefixTail
        (system := system) stripConstant prefixAxisConstant tailAxisConstant
        stripConstant_nonneg prefixAxisConstant_nonneg tailAxisConstant_nonneg
        cutoff k strip_extension_weighted_norm_le_realRadius
        prefix_trivialAxis_weighted_norm_le
        tail_trivialAxis_weighted_norm_le f rho
  have hdiv :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower <=
        ((2 : Real) ^ k * stripConstant f +
          (prefixAxisConstant f + tailAxisConstant f)) / radiusPower :=
    div_le_div_of_nonneg_right hweighted (le_of_lt hradiusPower_pos)
  have hleft :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower =
        norm (system.extension f zeroArgument) := by
    field_simp [hradiusPower_pos.ne']
  have hright :
      ((2 : Real) ^ k * stripConstant f +
        (prefixAxisConstant f + tailAxisConstant f)) / radiusPower =
        ((2 : Real) ^ k * stripConstant f +
          (prefixAxisConstant f + tailAxisConstant f)) * (1 / radiusPower) := by
    ring
  calc
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex)))
        = norm (system.extension f zeroArgument) := by
          rfl
    _ = norm (system.extension f zeroArgument) * radiusPower / radiusPower := by
      rw [hleft]
    _ <= ((2 : Real) ^ k * stripConstant f +
          (prefixAxisConstant f + tailAxisConstant f)) / radiusPower := hdiv
    _ = ((2 : Real) ^ k * stripConstant f +
          (prefixAxisConstant f + tailAxisConstant f)) *
        (1 / radiusPower) := hright
    _ = ((2 : Real) ^ k * stripConstant f +
          (prefixAxisConstant f + tailAxisConstant f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
      rfl

/--
Weighted zero-locus decay from a strip envelope and a tail estimate on the
indexed trivial-zero sequence.

The finite prefix is absorbed by
`riemannWeilIndexedTrivialAxisPrefixSumConstant`, so the only trivial-axis
analytic input left is the tail estimate for `cutoff <= n`.
-/
theorem zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant tailAxisConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * stripConstant f +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          tailAxisConstant f) := by
  exact
    zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisPrefixTail
      (system := system) stripConstant
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k)
      tailAxisConstant stripConstant_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k)
      tailAxisConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
        (system := system) cutoff k)
      tail_trivialAxis_weighted_norm_le f rho

/--
Weighted zero-locus decay from a sharp strip envelope and a tail estimate on
the indexed trivial-zero sequence.

The finite prefix is bounded by the concrete prefix-sum constant, while the
nontrivial strip side pays the sharper `(5 / 4)^k` closed-strip geometry.
-/
theorem zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisTail_sharpStrip
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant tailAxisConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k * stripConstant f +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          tailAxisConstant f) := by
  exact
    zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisPrefixTail_sharpStrip
      (system := system) stripConstant
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k)
      tailAxisConstant stripConstant_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k)
      tailAxisConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
        (system := system) cutoff k)
      tail_trivialAxis_weighted_norm_le f rho

/--
Finite-component indexed one-add tail route with both checked geometric
sharpenings.

The nontrivial strip side uses the closed-strip `(5 / 4)^k` radius comparison,
and the indexed trivial-zero tail uses the actual-height `(9 / 7)^k`
one-add-to-shifted conversion.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      ((5 : Real) / 4) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          ((9 : Real) / 7) ^ k *
            (Finset.univ.sum fun i : Index =>
              axisComponentConstant i f)) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let axisConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => axisComponentConstant i f
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have haxis_tail_nonneg :
      forall f : SchwartzLineTestFunction,
        0 <= ((9 : Real) / 7) ^ k * axisConstant f := by
    intro f
    exact mul_nonneg
      (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
      (Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f)
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have htail :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              ((9 : Real) / 7) ^ k * axisConstant f := by
    intro f n hn
    let height : Real := riemannWeilTrivialZeroArgumentHeight n
    let axisPoint : Complex := (height : Complex) * Complex.I
    let shiftedPower : Real := (norm axisPoint + 2) ^ (k : Real)
    have hbase_pos : 0 < norm axisPoint + 2 := by
      have hnorm_nonneg : 0 <= norm axisPoint := norm_nonneg _
      linarith
    have hshiftedPower_nonneg : 0 <= shiftedPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f axisPoint) <=
          Finset.univ.sum fun i : Index =>
            norm (component i f axisPoint) := by
      dsimp [axisPoint, height]
      rw [tail_axis_extension_eq_component_sum f n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        component i f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    have htail_at_height :
        norm (system.extension f axisPoint) * shiftedPower <=
          ((9 : Real) / 7) ^ k * axisConstant f := by
      calc
        norm (system.extension f axisPoint) * shiftedPower
            <= (Finset.univ.sum fun i : Index =>
                norm (component i f axisPoint)) * shiftedPower :=
          mul_le_mul_of_nonneg_right hnorm hshiftedPower_nonneg
        _ = Finset.univ.sum fun i : Index =>
              norm (component i f axisPoint) * shiftedPower := by
          simp [Finset.sum_mul, shiftedPower]
        _ <= Finset.univ.sum fun i : Index =>
              ((9 : Real) / 7) ^ k * axisComponentConstant i f :=
          Finset.sum_le_sum fun i _ => by
            have honeAdd :
                norm (component i f axisPoint) *
                    (1 + height) ^ (k : Real) <=
                  axisComponentConstant i f := by
              dsimp [axisPoint, height]
              simpa using
                component_tail_axis_oneAdd_weighted_norm_le i f n hn
            simpa [axisPoint, shiftedPower] using
              fixedImaginaryAxis_shiftedNorm_weighted_norm_le_of_oneAdd_at_trivialZeroHeight
                (fun z : Complex => component i f z)
                (axisComponentConstant i f) k n honeAdd
        _ = ((9 : Real) / 7) ^ k * axisConstant f := by
          dsimp [axisConstant]
          rw [← Finset.mul_sum]
    simpa [height, axisPoint, shiftedPower] using htail_at_height
  simpa [stripConstant, axisConstant] using
    zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisTail_sharpStrip
      (system := system) stripConstant
      (fun f => ((9 : Real) / 7) ^ k * axisConstant f)
      hstrip_nonneg haxis_tail_nonneg cutoff k hstrip htail f rho

/--
Finite-component indexed one-add estimates give the combined-sharp direct
closed-ball p-series shell bound for the actual project-side real zero weight.

The strip side keeps the checked `(5 / 4)^k` closed-horizontal-strip constant,
while the indexed trivial-zero tail keeps the checked `(9 / 7)^k` actual-height
one-add conversion constant.
-/
theorem weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      (((5 : Real) / 4) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            ((9 : Real) / 7) ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => stripComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => axisComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
    simpa [bound] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  have hweighted :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        bound := by
    simpa [bound] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
        (system := system) component stripComponentConstant axisComponentConstant
        stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_oneAdd_weighted_norm_le f rho
  have hzero :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
        (value := system.extension f
          (riemannWeilZeroArgument (rho : Complex)))
        (zeroArgument := riemannWeilZeroArgument (rho : Complex))
        (k := k) (bound := bound) hweighted
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) f rho bound k hbound_nonneg hzero

/--
Eventual finite-component indexed one-add estimates give an extracted-cutoff
combined-sharp shell bound for the actual project-side real zero weight.
-/
theorem exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight f rho) <=
          (((5 : Real) / 4) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripComponentConstant i f) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k f +
                ((9 : Real) / 7) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisComponentConstant i f))) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventually-valid combined-sharp shell bound for the actual project-side real
zero weight from finite-component indexed one-add estimates.
-/
theorem eventually_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight f rho) <=
            (((5 : Real) / 4) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    stripComponentConstant i f) +
                (riemannWeilIndexedTrivialAxisPrefixSumConstant
                    (system := system) cutoff k f +
                  ((9 : Real) / 7) ^ k *
                    (Finset.univ.sum fun i : Index =>
                      axisComponentConstant i f))) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  exact htail_eventually.mono fun cutoff hcutoff rho =>
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventual finite-component indexed one-add estimates plus cutoff-1 closed-ball
polynomial counting give absolute summability of the actual project-side zero
weight with both checked geometric constants.
-/
theorem summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  rcases
    exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually f with
  ⟨cutoff, hshell⟩
  let projectConstant : Real :=
    ((5 : Real) / 4) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => stripComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => axisComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
    simpa [projectConstant] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (5 / 4)) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  let projectWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight f rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := projectWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
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
        simpa [projectWeight, projectConstant] using hshell rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, projectWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The same combined-sharp project-side indexed one-add hypotheses make the signed
`system.weight` series summable.
-/
theorem summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  have hnorm :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

/--
Finite compact-exhaustion windows of the combined-sharp project-side
`system.weight` series converge to the signed infinite zero-side series.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat => windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f)

/-- The combined-sharp signed finite-window project-side error norm tends to zero. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/-- The combined-sharp signed finite-window error is eventually below any positive tolerance. -/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
              windowExhaustion.zetaZeroWindowSum n (system.weight f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/-- The combined-sharp absolute norm tail outside compact zero windows tends to zero. -/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/-- The combined-sharp absolute norm tail is eventually below any positive tolerance. -/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharpStrip_sharpTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
Finite-component indexed one-add estimates give the sharp-tail direct
closed-ball p-series shell bound for the actual project-side real zero weight.

This keeps the ordinary `2^k` strip conversion while preserving the indexed
trivial-zero tail improvement `(9 / 7)^k`.
-/
theorem weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            ((9 : Real) / 7) ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => stripComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => axisComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
    simpa [bound] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  have hweighted :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        bound := by
    simpa [bound] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
        (system := system) component stripComponentConstant axisComponentConstant
        stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_oneAdd_weighted_norm_le f rho
  have hzero :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
        (value := system.extension f
          (riemannWeilZeroArgument (rho : Complex)))
        (zeroArgument := riemannWeilZeroArgument (rho : Complex))
        (k := k) (bound := bound) hweighted
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) f rho bound k hbound_nonneg hzero

/--
Eventual finite-component indexed one-add estimates give an extracted-cutoff
sharp-tail shell bound for the actual project-side real zero weight.
-/
theorem exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight f rho) <=
          ((2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripComponentConstant i f) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k f +
                ((9 : Real) / 7) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisComponentConstant i f))) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventually-valid sharp-tail shell bound for the actual project-side real zero
weight from finite-component indexed one-add estimates.
-/
theorem eventually_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight f rho) <=
            ((2 : Real) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    stripComponentConstant i f) +
                (riemannWeilIndexedTrivialAxisPrefixSumConstant
                    (system := system) cutoff k f +
                  ((9 : Real) / 7) ^ k *
                    (Finset.univ.sum fun i : Index =>
                      axisComponentConstant i f))) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  exact htail_eventually.mono fun cutoff hcutoff rho =>
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventual finite-component indexed one-add estimates plus cutoff-1 closed-ball
polynomial counting give absolute summability of the actual project-side zero
weight with the sharp indexed-tail constant.
-/
theorem summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  rcases
    exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually f with
  ⟨cutoff, hshell⟩
  let projectConstant : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        ((9 : Real) / 7) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => stripComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => axisComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
    simpa [projectConstant] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= (9 / 7)) k)
            haxis_sum_nonneg))
  let projectWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight f rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := projectWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
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
        simpa [projectWeight, projectConstant] using hshell rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, projectWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The same sharp-tail project-side indexed one-add hypotheses make the signed
`system.weight` series summable.
-/
theorem summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  have hnorm :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

/--
Finite compact-exhaustion windows of the sharp-tail project-side `system.weight`
series converge to the signed infinite zero-side series.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat => windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f)

/-- The sharp-tail signed finite-window project-side error norm tends to zero. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/-- The sharp-tail signed finite-window error is eventually below any positive tolerance. -/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
              windowExhaustion.zetaZeroWindowSum n (system.weight f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/-- The sharp-tail absolute norm tail outside compact zero windows tends to zero. -/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/-- The sharp-tail absolute norm tail is eventually below any positive tolerance. -/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting_sharp
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
Exact-norm zero-locus p-series decay from a strip envelope and a tail estimate
on the indexed trivial-zero sequence, with the finite prefix bounded by an
explicit nonnegative finite sum.
-/
theorem zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant tailAxisConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (tailAxisConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= tailAxisConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (tail_trivialAxis_weighted_norm_le :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) *
                (norm
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) + 2) ^ (k : Real) <=
              tailAxisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k * stripConstant f +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            tailAxisConstant f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  exact
    zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisPrefixTail
      (system := system) stripConstant
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
        (system := system) cutoff k)
      tailAxisConstant stripConstant_nonneg
      (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k)
      tailAxisConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (riemannWeilIndexedTrivialAxis_weighted_norm_le_prefixSumConstant
        (system := system) cutoff k)
      tail_trivialAxis_weighted_norm_le f rho

/--
Weighted zero-locus decay from a strip envelope and tail domination of the
trivial-axis extension by real-axis Schwartz values.

The finite trivial-zero prefix is still absorbed by
`riemannWeilIndexedTrivialAxisPrefixSumConstant`; the tail constant is the
explicit real-axis Schwartz seminorm bound scaled by `comparisonConstant`.
-/
theorem zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) <=
              comparisonConstant f *
                ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k * stripConstant f +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          comparisonConstant f *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  exact
    zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisTail
      (system := system) stripConstant
      (fun f => comparisonConstant f *
        schwartzLineRealAxisShiftedSeminormConstant k f)
      stripConstant_nonneg
      (by
        intro f
        exact mul_nonneg (comparisonConstant_nonneg f)
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
      cutoff k strip_extension_weighted_norm_le_realRadius
      (riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_realHeightComparison
        (system := system) comparisonConstant comparisonConstant_nonneg
        cutoff k trivialAxis_norm_le_realHeight)
      f rho

/--
Exact-norm zero-locus p-series decay from a strip envelope plus tail
real-height domination on the explicit trivial-zero sequence.
-/
theorem zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) <=
              comparisonConstant f *
                ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k * stripConstant f +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            comparisonConstant f *
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  exact
    zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisTail
      (system := system) stripConstant
      (fun f => comparisonConstant f *
        schwartzLineRealAxisShiftedSeminormConstant k f)
      stripConstant_nonneg
      (by
        intro f
        exact mul_nonneg (comparisonConstant_nonneg f)
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
      cutoff k strip_extension_weighted_norm_le_realRadius
      (riemannWeilIndexedTrivialAxis_tail_weighted_norm_le_of_realHeightComparison
        (system := system) comparisonConstant comparisonConstant_nonneg
        cutoff k trivialAxis_norm_le_realHeight)
      f rho

/--
Eventual-tail exact-denominator version of the single-component real-radius
route.

This is the analytic-facing form when the extension itself satisfies the strip
real-radius envelope and the indexed trivial-axis real-height domination only
eventually.
-/
theorem exists_cutoff_zeroArgument_norm_le_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k * stripConstant f +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              comparisonConstant f *
                schwartzLineRealAxisShiftedSeminormConstant k f)) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
  rw [Filter.eventually_atTop] at trivialAxis_norm_le_realHeight_eventually
  rcases trivialAxis_norm_le_realHeight_eventually with
    ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
    zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (fun f n hn => hcutoff n hn f) f rho

/--
Eventual-tail weighted version of the single-component real-radius route.

Lean extracts the eventual indexed-tail cutoff and returns the shifted-radius
weighted zero-locus estimate with the concrete finite-prefix term.
-/
theorem exists_cutoff_zeroArgument_weighted_norm_le_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k * stripConstant f +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            comparisonConstant f *
              schwartzLineRealAxisShiftedSeminormConstant k f) := by
  rcases
    exists_cutoff_zeroArgument_norm_le_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually f rho with
  ⟨cutoff, hnorm⟩
  refine ⟨cutoff, ?_⟩
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k * stripConstant f +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        comparisonConstant f *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hnorm' :
      norm (system.extension f zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using hnorm
  simpa [zeroArgument, bound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hnorm'

/--
Eventually-valid exact-denominator single-component real-radius indexed-tail
estimate.

Once real-height domination holds eventually on the indexed trivial-axis tail,
the exact zero-locus decay estimate is valid for every sufficiently large
finite-prefix cutoff.
-/
theorem eventually_zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k * stripConstant f +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              comparisonConstant f *
                schwartzLineRealAxisShiftedSeminormConstant k f)) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
  exact trivialAxis_norm_le_realHeight_eventually.mono fun cutoff hcutoff =>
    zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (fun f n hn => hcutoff n hn f) f rho

/--
Eventually-valid weighted single-component real-radius indexed-tail estimate.

This is the weighted companion to
`eventually_zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail`.
-/
theorem eventually_zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k * stripConstant f +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            comparisonConstant f *
              schwartzLineRealAxisShiftedSeminormConstant k f) := by
  exact trivialAxis_norm_le_realHeight_eventually.mono fun cutoff hcutoff =>
    zeroArgument_weighted_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (fun f n hn => hcutoff n hn f) f rho

/--
Single-component real-radius indexed-tail estimates give a direct closed-ball
p-series shell bound for the actual real zero-side weight.

This is the direct-weight consequence of the analytic strip envelope plus
indexed trivial-axis real-height domination, before any polynomial counting is
used.
-/
theorem weight_norm_le_closedBall_cutoffOneShellBound_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (cutoff k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) <=
              comparisonConstant f *
                ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      ((2 : Real) ^ k * stripConstant f +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            comparisonConstant f *
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    (2 : Real) ^ k * stripConstant f +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        comparisonConstant f *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hbound_nonneg : 0 <= bound := by
    have hstrip_nonneg :
        0 <= (2 : Real) ^ k * stripConstant f := by
      exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (stripConstant_nonneg f)
    have hprefix_nonneg :
        0 <=
          riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f :=
      riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f
    have htail_nonneg :
        0 <= comparisonConstant f *
          schwartzLineRealAxisShiftedSeminormConstant k f := by
      exact mul_nonneg (comparisonConstant_nonneg f)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)
    simpa [bound] using
      add_nonneg hstrip_nonneg (add_nonneg hprefix_nonneg htail_nonneg)
  have hzero :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) stripConstant comparisonConstant
        stripConstant_nonneg comparisonConstant_nonneg cutoff k
        strip_extension_weighted_norm_le_realRadius
        trivialAxis_norm_le_realHeight f rho
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) f rho bound k hbound_nonneg hzero

/--
Eventual single-component real-height tail control gives an extracted-cutoff
closed-ball shell bound for the actual real zero-side weight.
-/
theorem exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight f rho) <=
          ((2 : Real) ^ k * stripConstant f +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k f +
                comparisonConstant f *
                  schwartzLineRealAxisShiftedSeminormConstant k f)) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  rw [Filter.eventually_atTop] at trivialAxis_norm_le_realHeight_eventually
  rcases trivialAxis_norm_le_realHeight_eventually with
    ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    weight_norm_le_closedBall_cutoffOneShellBound_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (fun f n hn => hcutoff n hn f) f rho

/--
Eventually-valid single-component real-height-tail shell bound for the actual
real zero-side weight.

The direct closed-ball `system.weight` estimate remains valid for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_weight_norm_le_closedBall_cutoffOneShellBound_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      forall rho : ZetaZeroSubtype,
        norm (system.weight f rho) <=
          ((2 : Real) ^ k * stripConstant f +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k f +
                comparisonConstant f *
                  schwartzLineRealAxisShiftedSeminormConstant k f)) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  exact trivialAxis_norm_le_realHeight_eventually.mono fun cutoff hcutoff rho =>
    weight_norm_le_closedBall_cutoffOneShellBound_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg cutoff k
      strip_extension_weighted_norm_le_realRadius
      (fun f n hn => hcutoff n hn f) f rho

/--
Eventual single-component real-radius indexed-tail estimates plus cutoff-1
closed-ball polynomial counting give absolute summability of the actual
project-side zero weight.

This is the p-series consequence of the direct single-component shell estimate:
the strip envelope, finite trivial-axis prefix, and real-height tail constant
remain visible in the polynomial decay constant.
-/
theorem summable_norm_weight_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  rcases
    exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually f with
  ⟨cutoff, hshell⟩
  let projectConstant : Real :=
    (2 : Real) ^ k * stripConstant f +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        comparisonConstant f *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    have hstrip_nonneg :
        0 <= (2 : Real) ^ k * stripConstant f := by
      exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (stripConstant_nonneg f)
    have hprefix_nonneg :
        0 <=
          riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f :=
      riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
        (system := system) cutoff k f
    have htail_nonneg :
        0 <= comparisonConstant f *
          schwartzLineRealAxisShiftedSeminormConstant k f := by
      exact mul_nonneg (comparisonConstant_nonneg f)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)
    simpa [projectConstant] using
      add_nonneg hstrip_nonneg (add_nonneg hprefix_nonneg htail_nonneg)
  let projectWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight f rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := projectWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
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
        simpa [projectWeight, projectConstant] using hshell rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, projectWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The same single-component real-radius indexed-tail hypotheses make the signed
project-side `system.weight` series summable.
-/
theorem summable_weight_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    {system : SchwartzRiemannWeilExtensionSystem}
    (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
    (stripConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
    (comparisonConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
    (k : Nat)
    (strip_extension_weighted_norm_le_realRadius :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f)
    (trivialAxis_norm_le_realHeight_eventually :
      ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
        forall n : Nat,
          cutoff <= n ->
            forall f : SchwartzLineTestFunction,
              norm
                  (system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonConstant f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  have hnorm :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

section RealPartEnvelopeProjectWeightWindowEndpoints

variable {system : SchwartzRiemannWeilExtensionSystem}
variable (stripConstant comparisonConstant : SchwartzLineTestFunction -> Real)
variable (stripConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= stripConstant f)
variable (comparisonConstant_nonneg :
  forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f)
variable (k : Nat)
variable (strip_extension_weighted_norm_le_realRadius :
  forall (f : SchwartzLineTestFunction) (z : Complex),
    -(1 / 2 : Real) <= z.im ->
      z.im <= (1 / 2 : Real) ->
        norm (system.extension f z) *
            (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
          stripConstant f)
variable (trivialAxis_norm_le_realHeight_eventually :
  ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
    forall n : Nat,
      cutoff <= n ->
        forall f : SchwartzLineTestFunction,
          norm
              (system.extension f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) <=
            comparisonConstant f *
              norm (f (riemannWeilTrivialZeroArgumentHeight n)))
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include stripConstant comparisonConstant stripConstant_nonneg
  comparisonConstant_nonneg k strip_extension_weighted_norm_le_realRadius
  trivialAxis_norm_le_realHeight_eventually counting counting_cutoff_eq
  growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the project-side `system.weight` series
converge to the signed infinite zero-side series under single-component
real-radius eventual-tail hypotheses and cutoff-1 closed-ball counting.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat => windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_weight_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f)

/-- The signed finite-window project-side single-component error norm tends to zero. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_weight_zetaZeroWindowSum_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/--
For every positive tolerance, the signed project-side single-component
finite-window error is eventually below that tolerance.
-/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
              windowExhaustion.zetaZeroWindowSum n (system.weight f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_weight_zetaZeroWindowErrorNorm_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the project-side single-component `system.weight`
series outside growing compact zero windows tends to zero.
-/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the absolute norm tail of the project-side
single-component `system.weight` series is eventually below that tolerance.
-/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_weight_zetaZeroWindowTail_of_realPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) stripConstant comparisonConstant
      stripConstant_nonneg comparisonConstant_nonneg k
      strip_extension_weighted_norm_le_realRadius
      trivialAxis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

end RealPartEnvelopeProjectWeightWindowEndpoints

/--
Exact-norm zero-locus decay with the p-series denominator, derived directly
from the real-radius strip envelope and the positive-imaginary-axis estimate.
-/
theorem zeroArgument_norm_le_of_realPartEnvelopeAndOneAddImaginaryAxisControl
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
              axisConstant f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k * stripConstant f +
          (2 : Real) ^ k * axisConstant f) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let radiusPower : Real := (norm zeroArgument + 2) ^ (k : Real)
  have hbase_pos : 0 < norm zeroArgument + 2 := by
    have hnorm_nonneg : 0 <= norm zeroArgument := norm_nonneg zeroArgument
    linarith
  have hradiusPower_pos : 0 < radiusPower := by
    dsimp [radiusPower]
    exact Real.rpow_pos_of_pos hbase_pos (k : Real)
  have hweighted :
      norm (system.extension f zeroArgument) * radiusPower <=
        (2 : Real) ^ k * stripConstant f +
          (2 : Real) ^ k * axisConstant f := by
    simpa [zeroArgument, radiusPower] using
      zeroArgument_weighted_norm_le_of_realPartEnvelopeAndOneAddImaginaryAxisControl
        (system := system) stripConstant axisConstant stripConstant_nonneg
        axisConstant_nonneg k strip_extension_weighted_norm_le_realRadius
        imaginaryAxis_oneAdd_weighted_norm_le f rho
  have hdiv :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower <=
        ((2 : Real) ^ k * stripConstant f +
          (2 : Real) ^ k * axisConstant f) / radiusPower :=
    div_le_div_of_nonneg_right hweighted (le_of_lt hradiusPower_pos)
  have hleft :
      norm (system.extension f zeroArgument) * radiusPower / radiusPower =
        norm (system.extension f zeroArgument) := by
    field_simp [hradiusPower_pos.ne']
  have hright :
      ((2 : Real) ^ k * stripConstant f +
        (2 : Real) ^ k * axisConstant f) / radiusPower =
        ((2 : Real) ^ k * stripConstant f +
          (2 : Real) ^ k * axisConstant f) * (1 / radiusPower) := by
    ring
  calc
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex)))
        = norm (system.extension f zeroArgument) := by
          rfl
    _ = norm (system.extension f zeroArgument) * radiusPower / radiusPower := by
      rw [hleft]
    _ <= ((2 : Real) ^ k * stripConstant f +
          (2 : Real) ^ k * axisConstant f) / radiusPower := hdiv
    _ = ((2 : Real) ^ k * stripConstant f +
          (2 : Real) ^ k * axisConstant f) * (1 / radiusPower) := hright
    _ = ((2 : Real) ^ k * stripConstant f +
          (2 : Real) ^ k * axisConstant f) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
      rfl

/--
Finite-component version of the repaired zero-locus p-series bound.

This is the componentwise analytic shape expected from a Guinand-Weil
decomposition: prove the real-radius strip envelope and the positive
imaginary-axis estimate for each finite component, together with the finite
sum identity on the two relevant loci. Lean then supplies the combined
exact-norm zero-locus p-series denominator.
-/
theorem zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndOneAddImaginaryAxisControl
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
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
          (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => axisComponentConstant i f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let axisConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => axisComponentConstant i f
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have haxis_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= axisConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have haxis :
      forall f : SchwartzLineTestFunction,
        forall y : Real,
          0 <= y ->
            norm (system.extension f ((y : Complex) * Complex.I)) *
                (1 + y) ^ (k : Real) <=
              axisConstant f := by
    intro f y hy
    let radiusPower : Real := (1 + y) ^ (k : Real)
    have hbase_pos : 0 < 1 + y := by linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f ((y : Complex) * Complex.I)) <=
          (Finset.univ.sum fun i : Index =>
            norm (component i f ((y : Complex) * Complex.I))) := by
      rw [axis_extension_eq_component_sum f y hy]
      exact norm_sum_le Finset.univ
        (fun i : Index => component i f ((y : Complex) * Complex.I))
    calc
      norm (system.extension f ((y : Complex) * Complex.I)) * radiusPower
          <= (Finset.univ.sum fun i : Index =>
              norm (component i f ((y : Complex) * Complex.I))) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f ((y : Complex) * Complex.I)) *
              radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => axisComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_axis_oneAdd_weighted_norm_le i f y hy
  simpa [stripConstant, axisConstant] using
    zeroArgument_norm_le_of_realPartEnvelopeAndOneAddImaginaryAxisControl
      (system := system) stripConstant axisConstant hstrip_nonneg
      haxis_nonneg k hstrip haxis f rho

/--
Finite-component version of the indexed real-height-tail p-series route.

This is the componentwise shape expected from a Guinand-Weil decomposition
when the positive-axis estimate is replaced by tail control on the explicit
trivial-zero sequence. The finite prefix is still the concrete system-level
sum `riemannWeilIndexedTrivialAxisPrefixSumConstant`; the component work is
only the strip envelope and tail domination by `‖f height‖`.
-/
theorem zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i f *
                  ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (Finset.univ.sum fun i : Index =>
                comparisonComponentConstant i f) *
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let stripConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => stripComponentConstant i f
  let comparisonConstant : SchwartzLineTestFunction -> Real :=
    fun f => Finset.univ.sum fun i : Index => comparisonComponentConstant i f
  have hstrip_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= stripConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
  have hcomparison_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= comparisonConstant f := by
    intro f
    exact Finset.sum_nonneg fun i _ => comparisonComponentConstant_nonneg i f
  have hstrip :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) *
                (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
              stripConstant f := by
    intro f z hlow hhigh
    let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
    have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
      have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : Index => norm (component i f z)) := by
      rw [strip_extension_eq_component_sum f z hlow hhigh]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z)
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : Index => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : Index =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : Index => stripComponentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using
            component_strip_weighted_norm_le_realRadius i f z hlow hhigh
  have htail :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
            norm
                (system.extension f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) <=
              comparisonConstant f *
                ‖f (riemannWeilTrivialZeroArgumentHeight n)‖ := by
    intro f n hn
    have hnorm :
        norm
            (system.extension f
              ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                Complex.I)) <=
          Finset.univ.sum fun i : Index =>
            norm
              (component i f
                ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                  Complex.I)) := by
      rw [tail_axis_extension_eq_component_sum f n hn]
      exact norm_sum_le Finset.univ fun i : Index =>
        component i f
          ((riemannWeilTrivialZeroArgumentHeight n : Complex) * Complex.I)
    calc
      norm
          (system.extension f
            ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
              Complex.I))
          <= Finset.univ.sum fun i : Index =>
              norm
                (component i f
                  ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                    Complex.I)) := hnorm
      _ <= Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f *
              ‖f (riemannWeilTrivialZeroArgumentHeight n)‖ :=
        Finset.sum_le_sum fun i _ => by
          exact component_tail_axis_norm_le_realHeight i f n hn
      _ = (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) *
          ‖f (riemannWeilTrivialZeroArgumentHeight n)‖ := by
        simp [Finset.sum_mul]
  simpa [stripConstant, comparisonConstant] using
    zeroArgument_norm_le_of_realPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) stripConstant comparisonConstant hstrip_nonneg
      hcomparison_nonneg cutoff k hstrip htail f rho

/--
Finite-component weighted zero-locus decay from a real-radius strip envelope
and indexed trivial-axis real-height tail domination.

This is the weighted companion to
`zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail`:
it keeps the same finite prefix and tail seminorm constant, but returns the
closedness-friendly weighted inequality directly.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff k f +
          (Finset.univ.sum fun i : Index =>
              comparisonComponentConstant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hnorm :
      norm (system.extension f zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using
      zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripComponentConstant
        comparisonComponentConstant stripComponentConstant_nonneg
        comparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_norm_le_realHeight f rho
  simpa [zeroArgument, bound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hnorm

/--
The real-radius indexed-tail weighted estimate survives enlarging the finite
prefix cutoff.

This is the cutoff-alignment form used when several eventual hypotheses are
combined: prove the analytic tail estimate at `cutoff`, then freely enlarge the
explicit finite prefix to any `cutoff'`.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff
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
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          (Finset.univ.sum fun i : Index =>
              comparisonComponentConstant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hbase :=
    zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight f rho
  have hmono :=
    finiteComponentRealIndexedTailMajorant_mono_cutoff
      (system := system) stripComponentConstant comparisonComponentConstant
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff f
  exact hbase.trans hmono

/--
The real-radius indexed-tail exact-denominator estimate survives enlarging the
finite prefix cutoff.

This is the exact p-series denominator companion to
`zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff`.
-/
theorem zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff
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
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff' k f +
            (Finset.univ.sum fun i : Index =>
                comparisonComponentConstant i f) *
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k f +
        (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hweighted :
      norm (system.extension f zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff
        (system := system) component stripComponentConstant
        comparisonComponentConstant stripComponentConstant_nonneg
        comparisonComponentConstant_nonneg hcutoff
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_norm_le_realHeight f rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hweighted

/--
Eventual-tail version of the finite-component real-radius envelope route.

This is the nondegenerate replacement for the pointwise real/Fourier component
comparison. It keeps the strip side as a genuine weighted real-radius envelope
for each component, while allowing the indexed trivial-zero decomposition and
real-height domination to hold only eventually.
-/
theorem exists_cutoff_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
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
                    ‖f (riemannWeilTrivialZeroArgumentHeight n)‖)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripComponentConstant i f) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              (Finset.univ.sum fun i : Index =>
                  comparisonComponentConstant i f) *
                schwartzLineRealAxisShiftedSeminormConstant k f)) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
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
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
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
Eventual-tail weighted version of the finite-component real-radius route.

Lean extracts a cutoff from the eventual indexed trivial-axis decomposition
and tail domination hypotheses, then returns the weighted zero-locus estimate
with the extracted finite prefix and shifted real-axis tail seminorm.
-/
theorem exists_cutoff_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
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
                    norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (Finset.univ.sum fun i : Index =>
                comparisonComponentConstant i f) *
              schwartzLineRealAxisShiftedSeminormConstant k f) := by
  rcases
    exists_cutoff_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually f rho with
  ⟨cutoff, hnorm⟩
  refine ⟨cutoff, ?_⟩
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hnorm' :
      norm (system.extension f zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using hnorm
  simpa [zeroArgument, bound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hnorm'

/--
Eventually-valid exact-denominator real-radius indexed-tail estimate.

Once the indexed trivial-axis decomposition and real-height domination hold
eventually, the exact zero-locus decay estimate holds for every sufficiently
large finite-prefix cutoff.
-/
theorem eventually_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
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
                    norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripComponentConstant i f) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              (Finset.univ.sum fun i : Index =>
                  comparisonComponentConstant i f) *
                schwartzLineRealAxisShiftedSeminormConstant k f)) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
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
  exact htail_eventually.mono fun cutoff hcutoff =>
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
Eventually-valid weighted real-radius indexed-tail estimate.

This is stronger than the existential cutoff form: once the tail decomposition
and real-height domination hold eventually, the weighted zero-locus estimate
holds for every sufficiently large finite-prefix cutoff.
-/
theorem eventually_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
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
                    norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
        (2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (Finset.univ.sum fun i : Index =>
                comparisonComponentConstant i f) *
              schwartzLineRealAxisShiftedSeminormConstant k f) := by
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
  exact htail_eventually.mono fun cutoff hcutoff =>
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
Finite-component real-radius indexed-tail estimates give a direct closed-ball
p-series shell bound for the actual real zero-side weight.

This is the project-side direct-weight companion to
`zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail`.
It keeps the component strip/tail hypotheses visible while moving the estimate
onto `system.weight`, the quantity consumed by the direct p-series route.
-/
theorem weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (Finset.univ.sum fun i : Index =>
                comparisonComponentConstant i f) *
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hbound_nonneg : 0 <= bound := by
    simpa [bound] using
      finiteComponentRealIndexedTailMajorant_nonneg
        (system := system) stripComponentConstant comparisonComponentConstant
        stripComponentConstant_nonneg comparisonComponentConstant_nonneg cutoff k f
  have hzero :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripComponentConstant
        comparisonComponentConstant stripComponentConstant_nonneg
        comparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_norm_le_realHeight f rho
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) f rho bound k hbound_nonneg hzero

/--
Eventual finite-component real-height tail control gives an extracted-cutoff
closed-ball shell bound for the actual real zero-side weight.
-/
theorem exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_norm_le_realHeight_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    comparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight f rho) <=
          ((2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripComponentConstant i f) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k f +
                (Finset.univ.sum fun i : Index =>
                    comparisonComponentConstant i f) *
                  schwartzLineRealAxisShiftedSeminormConstant k f)) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    comparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n))))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_norm_le_realHeight_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventually-valid finite-component real-height-tail shell bound for the actual
real zero-side weight.

The direct closed-ball `system.weight` estimate remains valid for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_norm_le_realHeight_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    comparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight f rho) <=
            ((2 : Real) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    stripComponentConstant i f) +
                (riemannWeilIndexedTrivialAxisPrefixSumConstant
                    (system := system) cutoff k f +
                  (Finset.univ.sum fun i : Index =>
                      comparisonComponentConstant i f) *
                    schwartzLineRealAxisShiftedSeminormConstant k f)) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    comparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n))))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff rho =>
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventual finite-component real-radius indexed-tail estimates plus cutoff-1
closed-ball polynomial counting give absolute summability of the actual
project-side zero weight.

This is the p-series consequence of the direct shell estimate above: the
analytic strip/tail hypotheses provide the shell decay constant, while the
counting package supplies the polynomial shell cardinality bound.
-/
theorem summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_norm_le_realHeight_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    comparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  rcases
    exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually f with
  ⟨cutoff, hshell⟩
  let projectConstant : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (Finset.univ.sum fun i : Index =>
            comparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    simpa [projectConstant] using
      finiteComponentRealIndexedTailMajorant_nonneg
        (system := system) stripComponentConstant comparisonComponentConstant
        stripComponentConstant_nonneg comparisonComponentConstant_nonneg cutoff k f
  let projectWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight f rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := projectWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
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
        simpa [projectWeight, projectConstant] using hshell rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, projectWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The same finite-component real-radius indexed-tail hypotheses make the signed
project-side `system.weight` series summable.
-/
theorem summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_norm_le_realHeight_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    comparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  have hnorm :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

section FiniteComponentRealPartEnvelopeProjectWeightWindowEndpoints

variable {Index : Type*} [Fintype Index]
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
variable (stripComponentConstant comparisonComponentConstant :
  Index -> SchwartzLineTestFunction -> Real)
variable (stripComponentConstant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= stripComponentConstant i f)
variable (comparisonComponentConstant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= comparisonComponentConstant i f)
variable (k : Nat)
variable (strip_extension_eq_component_sum :
  forall (f : SchwartzLineTestFunction) (z : Complex),
    -(1 / 2 : Real) <= z.im ->
      z.im <= (1 / 2 : Real) ->
        system.extension f z =
          Finset.univ.sum fun i : Index => component i f z)
variable (tail_axis_extension_eq_component_sum_eventually :
  Filter.Eventually
    (fun cutoff : Nat =>
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
    (Filter.atTop : Filter Nat))
variable (component_strip_weighted_norm_le_realRadius :
  forall i : Index,
    forall (f : SchwartzLineTestFunction) (z : Complex),
      -(1 / 2 : Real) <= z.im ->
        z.im <= (1 / 2 : Real) ->
          norm (component i f z) *
              (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
            stripComponentConstant i f)
variable (component_tail_axis_norm_le_realHeight_eventually :
  Filter.Eventually
    (fun cutoff : Nat =>
      forall n : Nat,
        cutoff <= n ->
          forall i : Index,
            forall f : SchwartzLineTestFunction,
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                comparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (Filter.atTop : Filter Nat))
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include component stripComponentConstant comparisonComponentConstant
  stripComponentConstant_nonneg comparisonComponentConstant_nonneg k
  strip_extension_eq_component_sum tail_axis_extension_eq_component_sum_eventually
  component_strip_weighted_norm_le_realRadius
  component_tail_axis_norm_le_realHeight_eventually counting counting_cutoff_eq
  growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the project-side `system.weight` series
converge to the signed infinite zero-side series under finite-component
real-radius eventual-tail hypotheses and cutoff-1 closed-ball counting.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat => windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f)

/-- The signed finite-window project-side error norm tends to zero. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/--
For every positive tolerance, the signed project-side finite-window error is
eventually below that tolerance.
-/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
              windowExhaustion.zetaZeroWindowSum n (system.weight f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the project-side `system.weight` series outside
growing compact zero windows tends to zero.
-/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the absolute norm tail of the project-side
`system.weight` series is eventually below that tolerance.
-/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant
      comparisonComponentConstant stripComponentConstant_nonneg
      comparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

end FiniteComponentRealPartEnvelopeProjectWeightWindowEndpoints

/--
Eventually-valid exact-denominator indexed one-add tail estimate.

Once the indexed trivial-axis decomposition and component `(1 + y)^k` tail
estimates hold eventually, the exact zero-locus decay estimate holds for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    Filter.Eventually
      (fun cutoff : Nat =>
        norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
          ((2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripComponentConstant i f) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k f +
                (2 : Real) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisComponentConstant i f))) *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)))
      (Filter.atTop : Filter Nat) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventually-valid weighted indexed one-add tail estimate.

This is the weighted companion to
`eventually_zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail`.
-/
theorem eventually_zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    Filter.Eventually
      (fun cutoff : Nat =>
        norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                stripComponentConstant i f) +
            (riemannWeilIndexedTrivialAxisPrefixSumConstant
                (system := system) cutoff k f +
              (2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  axisComponentConstant i f)))
      (Filter.atTop : Filter Nat) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
                          Complex.I)) *
                    (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                      (k : Real) <=
                  axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  exact htail_eventually.mono fun cutoff hcutoff =>
    zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Finite-component indexed one-add estimates give a direct closed-ball p-series
shell bound for the actual project-side real zero weight.

This is the project-side `system.weight` consequence of the one-add route: the
component strip envelopes and indexed `(1 + y)^k` tail estimates control the
zero-argument extension, and the closed-ball first-entry comparison converts
that shifted-radius denominator into the direct p-series shell denominator.
-/
theorem weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_oneAdd_weighted_norm_le :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripComponentConstant i f) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff k f +
            (2 : Real) ^ k *
              (Finset.univ.sum fun i : Index =>
                axisComponentConstant i f))) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hbound_nonneg : 0 <= bound := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => stripComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => axisComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
    simpa [bound] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            haxis_sum_nonneg))
  have hzero :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
        (system := system) component stripComponentConstant axisComponentConstant
        stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_weighted_norm_le_realRadius
        component_tail_axis_oneAdd_weighted_norm_le f rho
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) f rho bound k hbound_nonneg hzero

/--
Eventual finite-component indexed one-add estimates give an extracted-cutoff
closed-ball shell bound for the actual project-side real zero weight.
-/
theorem exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight f rho) <=
          ((2 : Real) ^ k *
                (Finset.univ.sum fun i : Index =>
                  stripComponentConstant i f) +
              (riemannWeilIndexedTrivialAxisPrefixSumConstant
                  (system := system) cutoff k f +
                (2 : Real) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    axisComponentConstant i f))) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventually-valid finite-component indexed one-add shell bound for the actual
project-side real zero weight.
-/
theorem eventually_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight f rho) <=
            ((2 : Real) ^ k *
                  (Finset.univ.sum fun i : Index =>
                    stripComponentConstant i f) +
                (riemannWeilIndexedTrivialAxisPrefixSumConstant
                    (system := system) cutoff k f +
                  (2 : Real) ^ k *
                    (Finset.univ.sum fun i : Index =>
                      axisComponentConstant i f))) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_oneAdd_weighted_norm_le_eventually
  exact htail_eventually.mono fun cutoff hcutoff rho =>
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_weighted_norm_le_realRadius
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventual finite-component indexed one-add estimates plus cutoff-1 closed-ball
polynomial counting give absolute summability of the actual project-side zero
weight.
-/
theorem summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  rcases
    exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually f with
  ⟨cutoff, hshell⟩
  let projectConstant : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index => stripComponentConstant i f) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff k f +
        (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index => axisComponentConstant i f))
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    have hstrip_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => stripComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => stripComponentConstant_nonneg i f
    have haxis_sum_nonneg :
        0 <=
          Finset.univ.sum fun i : Index => axisComponentConstant i f := by
      exact Finset.sum_nonneg fun i _ => axisComponentConstant_nonneg i f
    simpa [projectConstant] using
      add_nonneg
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          hstrip_sum_nonneg)
        (add_nonneg
          (riemannWeilIndexedTrivialAxisPrefixSumConstant_nonneg
            (system := system) cutoff k f)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            haxis_sum_nonneg))
  let projectWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight f rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := projectWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
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
        simpa [projectWeight, projectConstant] using hshell rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, projectWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The same project-side indexed one-add hypotheses make the signed
`system.weight` series summable.
-/
theorem summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
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
    (tail_axis_extension_eq_component_sum_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
    (component_strip_weighted_norm_le_realRadius :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) *
                  (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                stripComponentConstant i f)
    (component_tail_axis_oneAdd_weighted_norm_le_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) *
                      (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                        (k : Real) <=
                    axisComponentConstant i f)
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  have hnorm :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

section FiniteComponentOneAddProjectWeightWindowEndpoints

variable {Index : Type*} [Fintype Index]
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
variable (stripComponentConstant axisComponentConstant :
  Index -> SchwartzLineTestFunction -> Real)
variable (stripComponentConstant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= stripComponentConstant i f)
variable (axisComponentConstant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= axisComponentConstant i f)
variable (k : Nat)
variable (strip_extension_eq_component_sum :
  forall (f : SchwartzLineTestFunction) (z : Complex),
    -(1 / 2 : Real) <= z.im ->
      z.im <= (1 / 2 : Real) ->
        system.extension f z =
          Finset.univ.sum fun i : Index => component i f z)
variable (tail_axis_extension_eq_component_sum_eventually :
  Filter.Eventually
    (fun cutoff : Nat =>
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
    (Filter.atTop : Filter Nat))
variable (component_strip_weighted_norm_le_realRadius :
  forall i : Index,
    forall (f : SchwartzLineTestFunction) (z : Complex),
      -(1 / 2 : Real) <= z.im ->
        z.im <= (1 / 2 : Real) ->
          norm (component i f z) *
              (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
            stripComponentConstant i f)
variable (component_tail_axis_oneAdd_weighted_norm_le_eventually :
  Filter.Eventually
    (fun cutoff : Nat =>
      forall n : Nat,
        cutoff <= n ->
          forall i : Index,
            forall f : SchwartzLineTestFunction,
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) *
                  (1 + riemannWeilTrivialZeroArgumentHeight n) ^
                    (k : Real) <=
                axisComponentConstant i f)
    (Filter.atTop : Filter Nat))
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include component stripComponentConstant axisComponentConstant
  stripComponentConstant_nonneg axisComponentConstant_nonneg k
  strip_extension_eq_component_sum tail_axis_extension_eq_component_sum_eventually
  component_strip_weighted_norm_le_realRadius
  component_tail_axis_oneAdd_weighted_norm_le_eventually counting
  counting_cutoff_eq growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the project-side `system.weight` series
converge to the signed infinite zero-side series under finite-component
indexed one-add hypotheses and cutoff-1 closed-ball counting.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat => windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f)

/-- The signed finite-window project-side one-add error norm tends to zero. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/--
For every positive tolerance, the signed project-side one-add finite-window
error is eventually below that tolerance.
-/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
              windowExhaustion.zetaZeroWindowSum n (system.weight f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the project-side one-add `system.weight` series
outside growing compact zero windows tends to zero.
-/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the absolute norm tail of the project-side
one-add `system.weight` series is eventually below that tolerance.
-/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealPartEnvelopeAndEventuallyIndexedTrivialAxisOneAddTail_closedBallPolynomialCounting
      (system := system) component stripComponentConstant axisComponentConstant
      stripComponentConstant_nonneg axisComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_weighted_norm_le_realRadius
      component_tail_axis_oneAdd_weighted_norm_le_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

end FiniteComponentOneAddProjectWeightWindowEndpoints

/--
Finite-component p-series route where each strip component is controlled by
two real-line Schwartz profiles: the test function and its Fourier transform.

This avoids making the strip target depend only on `‖f z.re‖`, while still
letting Lean obtain the real-radius polynomial decay from checked Schwartz
decay on the real line.
-/
theorem zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                tailComparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
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
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let stripComponentConstant :
      Index -> SchwartzLineTestFunction -> Real :=
    fun i f =>
      stripRealComparisonConstant i f *
          schwartzLineRealAxisShiftedSeminormConstant k f +
        stripFourierComparisonConstant i f *
          schwartzLineRealAxisShiftedSeminormConstant k
            (SchwartzLineTestFunction.fourier f)
  have hstripComponent_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= stripComponentConstant i f := by
    intro i f
    exact add_nonneg
      (mul_nonneg (stripRealComparisonConstant_nonneg i f)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
      (mul_nonneg (stripFourierComparisonConstant_nonneg i f)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k
          (SchwartzLineTestFunction.fourier f)))
  have hcomponent_strip :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
                  norm (component i f z) *
                      (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
                    stripComponentConstant i f := by
    intro i f z hlow hhigh
    have hnorm := component_strip_norm_le_real_fourier i f z hlow hhigh
    simpa [stripComponentConstant] using
      realFourierProfile_bound_weighted_norm_le_shiftedSeminormMajorant
        k f z (component i f z) (stripRealComparisonConstant i f)
        (stripFourierComparisonConstant i f)
        (stripRealComparisonConstant_nonneg i f)
        (stripFourierComparisonConstant_nonneg i f) hnorm
  simpa [stripComponentConstant] using
    zeroArgument_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail
      (system := system) component stripComponentConstant
      tailComparisonComponentConstant hstripComponent_nonneg
      tailComparisonComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
      hcomponent_strip component_tail_axis_norm_le_realHeight f rho

/--
Finite-component weighted zero-locus decay from two real-line Schwartz
profiles.

This is the project-level weighted companion to
`zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail`.
Each strip component is controlled by the real profile of `f` and of
`Fourier f`; Lean keeps the indexed trivial-axis finite prefix and real-axis
tail seminorm explicit in the weighted estimate.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                tailComparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
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
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
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
  have hnorm :
      norm (system.extension f zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using
      zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_norm_le_real_fourier
        component_tail_axis_norm_le_realHeight f rho
  simpa [zeroArgument, bound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hnorm

/--
The real/Fourier indexed-tail weighted estimate survives enlarging the finite
prefix cutoff.

This is the two-profile counterpart of
`zeroArgument_weighted_norm_le_of_finiteComponentRealPartEnvelopeAndIndexedTrivialAxisRealHeightTail_mono_cutoff`.
-/
theorem zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_mono_cutoff
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
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                tailComparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^ (k : Real) <=
      (2 : Real) ^ k *
          (Finset.univ.sum fun i : Index =>
            stripRealComparisonConstant i f *
                schwartzLineRealAxisShiftedSeminormConstant k f +
              stripFourierComparisonConstant i f *
                schwartzLineRealAxisShiftedSeminormConstant k
                  (SchwartzLineTestFunction.fourier f)) +
        (riemannWeilIndexedTrivialAxisPrefixSumConstant
            (system := system) cutoff' k f +
          (Finset.univ.sum fun i : Index =>
              tailComparisonComponentConstant i f) *
            schwartzLineRealAxisShiftedSeminormConstant k f) := by
  have hbase :=
    zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight f rho
  have hmono :=
    finiteComponentRealFourierIndexedTailMajorant_mono_cutoff
      (system := system) stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      (cutoff := cutoff) (cutoff' := cutoff') (k := k) hcutoff f
  exact hbase.trans hmono

/--
The real/Fourier indexed-tail exact-denominator estimate survives enlarging
the finite prefix cutoff.

This is the exact p-series denominator companion to
`zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_mono_cutoff`.
-/
theorem zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_mono_cutoff
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
    {cutoff cutoff' k : Nat}
    (hcutoff : cutoff <= cutoff')
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                tailComparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
      ((2 : Real) ^ k *
            (Finset.univ.sum fun i : Index =>
              stripRealComparisonConstant i f *
                  schwartzLineRealAxisShiftedSeminormConstant k f +
                stripFourierComparisonConstant i f *
                  schwartzLineRealAxisShiftedSeminormConstant k
                    (SchwartzLineTestFunction.fourier f)) +
          (riemannWeilIndexedTrivialAxisPrefixSumConstant
              (system := system) cutoff' k f +
            (Finset.univ.sum fun i : Index =>
                tailComparisonComponentConstant i f) *
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real)) := by
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
    (2 : Real) ^ k *
        (Finset.univ.sum fun i : Index =>
          stripRealComparisonConstant i f *
              schwartzLineRealAxisShiftedSeminormConstant k f +
            stripFourierComparisonConstant i f *
              schwartzLineRealAxisShiftedSeminormConstant k
                (SchwartzLineTestFunction.fourier f)) +
      (riemannWeilIndexedTrivialAxisPrefixSumConstant
          (system := system) cutoff' k f +
        (Finset.univ.sum fun i : Index =>
            tailComparisonComponentConstant i f) *
          schwartzLineRealAxisShiftedSeminormConstant k f)
  have hweighted :
      norm (system.extension f zeroArgument) *
          (norm zeroArgument + 2) ^ (k : Real) <= bound := by
    simpa [zeroArgument, bound] using
      zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail_mono_cutoff
        (system := system) component stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg hcutoff
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_norm_le_real_fourier
        component_tail_axis_norm_le_realHeight f rho
  simpa [zeroArgument, bound] using
    norm_le_mul_inv_shiftedRadius_of_weighted_norm_le
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hweighted

/--
Eventual-tail version of the two-channel componentwise p-series route.

Source estimates are often stated as holding for all sufficiently large
trivial-zero indices. This theorem extracts a cutoff from eventual component
tail decomposition and eventual component real-height domination, then applies
the checked exact-norm p-series route with the automatic finite prefix.
-/
theorem exists_cutoff_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
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
                norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
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
                schwartzLineRealAxisShiftedSeminormConstant k f)) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
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
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  exact
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

/--
Eventual-tail weighted version of the two-channel componentwise p-series route.

The indexed trivial-axis decomposition and tail domination may hold only
eventually. Lean extracts a cutoff and returns the corresponding weighted
zero-locus estimate with the finite prefix, real profile, Fourier profile, and
tail seminorm constants all visible.
-/
theorem exists_cutoff_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
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
                norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    exists cutoff : Nat,
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
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
              schwartzLineRealAxisShiftedSeminormConstant k f) := by
  rcases
    exists_cutoff_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually f rho with
  ⟨cutoff, hnorm⟩
  refine ⟨cutoff, ?_⟩
  let zeroArgument := riemannWeilZeroArgument (rho : Complex)
  let bound : Real :=
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
  have hnorm' :
      norm (system.extension f zeroArgument) <=
        bound * (1 / (norm zeroArgument + 2) ^ (k : Real)) := by
    simpa [zeroArgument, bound] using hnorm
  simpa [zeroArgument, bound] using
    weighted_norm_le_of_norm_le_mul_inv_shiftedRadius
      (value := system.extension f zeroArgument) (zeroArgument := zeroArgument)
      (k := k) (bound := bound) hnorm'

/--
Eventually-valid exact-denominator real/Fourier indexed-tail estimate.

Once the indexed trivial-axis decomposition and real-height domination hold
eventually, the exact two-profile zero-locus decay estimate holds for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
                    norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        ((2 : Real) ^ k *
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
                schwartzLineRealAxisShiftedSeminormConstant k f)) *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
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
  exact htail_eventually.mono fun cutoff hcutoff =>
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

/--
Eventually-valid weighted real/Fourier indexed-tail estimate.

Once the indexed trivial-axis decomposition and real-height domination hold
eventually, the weighted two-profile zero-locus estimate holds for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_zeroArgument_weighted_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
                    norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    ∀ᶠ cutoff : Nat in (Filter.atTop : Filter Nat),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            (k : Real) <=
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
              schwartzLineRealAxisShiftedSeminormConstant k f) := by
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
  exact htail_eventually.mono fun cutoff hcutoff =>
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

/--
Finite-component real/Fourier strip comparison plus indexed real-height tail
estimates give a direct closed-ball p-series shell bound for the actual real
zero-side weight.

This is the project-side direct-weight companion to
`zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail`.
It keeps the two real-line strip profiles and indexed trivial-axis tail
constant visible while moving the estimate onto `system.weight`.
-/
theorem weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
    (cutoff k : Nat)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (tail_axis_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        forall n : Nat,
          cutoff <= n ->
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
    (component_tail_axis_norm_le_realHeight :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          forall n : Nat,
            cutoff <= n ->
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                tailComparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    norm (system.weight f rho) <=
      ((2 : Real) ^ k *
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
              schwartzLineRealAxisShiftedSeminormConstant k f)) *
        (1 /
          |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
              rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  let bound : Real :=
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
  have hbound_nonneg : 0 <= bound := by
    simpa [bound] using
      finiteComponentRealFourierIndexedTailMajorant_nonneg
        (system := system) stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg cutoff k f
  have hzero :
      norm
          (system.extension f
            (riemannWeilZeroArgument (rho : Complex))) <=
        bound *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    simpa [bound] using
      zeroArgument_norm_le_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
        (system := system) component stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg cutoff k
        strip_extension_eq_component_sum tail_axis_extension_eq_component_sum
        component_strip_norm_le_real_fourier
        component_tail_axis_norm_le_realHeight f rho
  simpa [bound] using
    norm_weight_le_closedBall_cutoffOneShellBound_of_zeroArgument_norm_le
      (system := system) f rho bound k hbound_nonneg hzero

/--
Eventual finite-component real/Fourier strip comparison plus real-height tail
control gives an extracted-cutoff closed-ball shell bound for the actual real
zero-side weight.
-/
theorem exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
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
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    tailComparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    exists cutoff : Nat,
      forall rho : ZetaZeroSubtype,
        norm (system.weight f rho) <=
          ((2 : Real) ^ k *
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
                  schwartzLineRealAxisShiftedSeminormConstant k f)) *
            (1 /
              |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                  rho - 1 : Nat) : Real) + 1)| ^ (k : Real)) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    tailComparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n))))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_norm_le_realHeight_eventually
  rw [Filter.eventually_atTop] at htail_eventually
  rcases htail_eventually with ⟨cutoff, hcutoff_all⟩
  have hcutoff := hcutoff_all cutoff le_rfl
  refine ⟨cutoff, ?_⟩
  intro rho
  exact
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_norm_le_real_fourier
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventually-valid finite-component real/Fourier shell bound for the actual real
zero-side weight.

The direct closed-ball `system.weight` estimate remains valid for every
sufficiently large finite-prefix cutoff.
-/
theorem eventually_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
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
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    tailComparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (f : SchwartzLineTestFunction) :
    Filter.Eventually
      (fun cutoff : Nat =>
        forall rho : ZetaZeroSubtype,
          norm (system.weight f rho) <=
            ((2 : Real) ^ k *
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
                    schwartzLineRealAxisShiftedSeminormConstant k f)) *
              (1 /
                |(((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex
                    rho - 1 : Nat) : Real) + 1)| ^ (k : Real)))
      (Filter.atTop : Filter Nat) := by
  have htail_eventually :
      Filter.Eventually
        (fun cutoff : Nat =>
          (forall n : Nat,
            cutoff <= n ->
              forall f : SchwartzLineTestFunction,
                system.extension f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I) =
                  Finset.univ.sum fun i : Index =>
                    component i f
                      ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                        Complex.I)) /\
          (forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    tailComparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n))))
        (Filter.atTop : Filter Nat) :=
    tail_axis_extension_eq_component_sum_eventually.and
      component_tail_axis_norm_le_realHeight_eventually
  exact htail_eventually.mono fun cutoff hcutoff rho =>
    weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndIndexedTrivialAxisRealHeightTail
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg cutoff k
      strip_extension_eq_component_sum
      (fun f n hn => hcutoff.1 n hn f)
      component_strip_norm_le_real_fourier
      (fun i f n hn => hcutoff.2 n hn i f)
      f rho

/--
Eventual finite-component real/Fourier strip comparison plus indexed
real-height tail estimates and cutoff-1 closed-ball polynomial counting give
absolute summability of the actual project-side zero weight.

This is the p-series consequence of the direct two-profile shell estimate:
the real-line and Fourier strip constants, finite trivial-axis prefix, and
real-height tail constant stay visible in the polynomial decay constant.
-/
theorem summable_norm_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
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
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    tailComparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) := by
  rcases
    exists_cutoff_weight_norm_le_closedBall_cutoffOneShellBound_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually f with
  ⟨cutoff, hshell⟩
  let projectConstant : Real :=
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
  have hprojectConstant_nonneg : 0 <= projectConstant := by
    simpa [projectConstant] using
      finiteComponentRealFourierIndexedTailMajorant_nonneg
        (system := system) stripRealComparisonConstant
        stripFourierComparisonConstant tailComparisonComponentConstant
        stripRealComparisonConstant_nonneg
        stripFourierComparisonConstant_nonneg
        tailComparisonComponentConstant_nonneg cutoff k f
  let projectWeight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real :=
    fun _f rho => system.weight f rho
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
        ComplexCompactExhaustion.closedBallZero :=
    { weight := projectWeight
      cutoff := 1
      shellBound := fun _f n =>
        projectConstant *
          (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
      zeroConstant := fun _f => projectConstant
      decayExponent := fun _f => (k : Real)
      zeroConstant_nonneg := fun _f => hprojectConstant_nonneg
      shellBound_nonneg := by
        intro _f n
        exact mul_nonneg hprojectConstant_nonneg
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
        simpa [projectWeight, projectConstant] using hshell rho }
  simpa [SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay,
    decay, projectWeight] using
    (SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate.ofCountingAndDecay
      counting decay
      (by
        simpa [decay] using counting_cutoff_eq)
      (fun _f => by
        simpa [decay] using growth_add_one_lt_k)).summable_norm_weight f

/--
The same finite-component real/Fourier indexed-tail hypotheses make the signed
project-side `system.weight` series summable.
-/
theorem summable_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
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
      Filter.Eventually
        (fun cutoff : Nat =>
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
        (Filter.atTop : Filter Nat))
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
      Filter.Eventually
        (fun cutoff : Nat =>
          forall n : Nat,
            cutoff <= n ->
              forall i : Index,
                forall f : SchwartzLineTestFunction,
                  norm
                      (component i f
                        ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                          Complex.I)) <=
                    tailComparisonComponentConstant i f *
                      norm (f (riemannWeilTrivialZeroArgumentHeight n)))
        (Filter.atTop : Filter Nat))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_k : counting.growth + 1 < (k : Real))
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  have hnorm :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  exact hnorm.of_norm_bounded (fun _rho => le_rfl)

section FiniteComponentRealFourierProjectWeightWindowEndpoints

variable {Index : Type*} [Fintype Index]
variable {system : SchwartzRiemannWeilExtensionSystem}
variable (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
variable (stripRealComparisonConstant stripFourierComparisonConstant
  tailComparisonComponentConstant :
  Index -> SchwartzLineTestFunction -> Real)
variable (stripRealComparisonConstant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= stripRealComparisonConstant i f)
variable (stripFourierComparisonConstant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= stripFourierComparisonConstant i f)
variable (tailComparisonComponentConstant_nonneg :
  forall i : Index, forall f : SchwartzLineTestFunction,
    0 <= tailComparisonComponentConstant i f)
variable (k : Nat)
variable (strip_extension_eq_component_sum :
  forall (f : SchwartzLineTestFunction) (z : Complex),
    -(1 / 2 : Real) <= z.im ->
      z.im <= (1 / 2 : Real) ->
        system.extension f z =
          Finset.univ.sum fun i : Index => component i f z)
variable (tail_axis_extension_eq_component_sum_eventually :
  Filter.Eventually
    (fun cutoff : Nat =>
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
    (Filter.atTop : Filter Nat))
variable (component_strip_norm_le_real_fourier :
  forall i : Index,
    forall (f : SchwartzLineTestFunction) (z : Complex),
      -(1 / 2 : Real) <= z.im ->
        z.im <= (1 / 2 : Real) ->
          norm (component i f z) <=
            stripRealComparisonConstant i f * norm (f z.re) +
              stripFourierComparisonConstant i f *
                norm ((SchwartzLineTestFunction.fourier f) z.re))
variable (component_tail_axis_norm_le_realHeight_eventually :
  Filter.Eventually
    (fun cutoff : Nat =>
      forall n : Nat,
        cutoff <= n ->
          forall i : Index,
            forall f : SchwartzLineTestFunction,
              norm
                  (component i f
                    ((riemannWeilTrivialZeroArgumentHeight n : Complex) *
                      Complex.I)) <=
                tailComparisonComponentConstant i f *
                  norm (f (riemannWeilTrivialZeroArgumentHeight n)))
    (Filter.atTop : Filter Nat))
variable (counting :
  SchwartzRiemannWeilPolynomialZeroCountingEstimate
    ComplexCompactExhaustion.closedBallZero)
variable (counting_cutoff_eq : counting.cutoff = 1)
variable (growth_add_one_lt_k : counting.growth + 1 < (k : Real))

include component stripRealComparisonConstant stripFourierComparisonConstant
  tailComparisonComponentConstant stripRealComparisonConstant_nonneg
  stripFourierComparisonConstant_nonneg tailComparisonComponentConstant_nonneg
  k strip_extension_eq_component_sum tail_axis_extension_eq_component_sum_eventually
  component_strip_norm_le_real_fourier
  component_tail_axis_norm_le_realHeight_eventually counting counting_cutoff_eq
  growth_add_one_lt_k

/--
Finite compact-exhaustion windows of the project-side `system.weight` series
converge to the signed infinite zero-side series under finite-component
real/Fourier eventual-tail hypotheses and cutoff-1 closed-ball counting.
-/
theorem tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat => windowExhaustion.zetaZeroWindowSum n (system.weight f))
      Filter.atTop
      (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
  windowExhaustion.tendsto_zetaZeroWindowSum
    (summable_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f)

/-- The signed finite-window project-side real/Fourier error norm tends to zero. -/
theorem tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        norm
          (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
            windowExhaustion.zetaZeroWindowSum n (system.weight f)))
      Filter.atTop
      (nhds 0) := by
  have hwindow :=
    tendsto_weight_zetaZeroWindowSum_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f
  have hconst :
      Filter.Tendsto
        (fun _ : Nat => tsum (fun rho : ZetaZeroSubtype => system.weight f rho))
        Filter.atTop
        (nhds (tsum (fun rho : ZetaZeroSubtype => system.weight f rho))) :=
    tendsto_const_nhds
  simpa using (hconst.sub hwindow).norm

/--
For every positive tolerance, the signed project-side real/Fourier finite-window
error is eventually below that tolerance.
-/
theorem eventually_weight_zetaZeroWindowErrorNorm_lt_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        norm
            (tsum (fun rho : ZetaZeroSubtype => system.weight f rho) -
              windowExhaustion.zetaZeroWindowSum n (system.weight f)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_weight_zetaZeroWindowErrorNorm_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

/--
The absolute norm tail of the project-side real/Fourier `system.weight` series
outside growing compact zero windows tends to zero.
-/
theorem tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Filter.Tendsto
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
      Filter.atTop
      (nhds 0) := by
  have hsummable :
      Summable (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) :=
    summable_norm_weight_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k f
  have hwindow :
      Filter.Tendsto
        (fun n : Nat =>
          windowExhaustion.zetaZeroWindowSum n
            (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    windowExhaustion.tendsto_zetaZeroWindowSum hsummable
  have hconst :
      Filter.Tendsto
        (fun _ : Nat =>
          tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))
        Filter.atTop
        (nhds (tsum
          (fun rho : ZetaZeroSubtype => norm (system.weight f rho)))) :=
    tendsto_const_nhds
  simpa using hconst.sub hwindow

/--
For every positive tolerance, the absolute norm tail of the project-side
real/Fourier `system.weight` series is eventually below that tolerance.
-/
theorem eventually_norm_weight_zetaZeroWindowTail_lt_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction)
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    Filter.Eventually
      (fun n : Nat =>
        tsum (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) -
            windowExhaustion.zetaZeroWindowSum n
              (fun rho : ZetaZeroSubtype => norm (system.weight f rho)) <
          epsilon)
      Filter.atTop := by
  simpa using
    (tendsto_norm_weight_zetaZeroWindowTail_of_finiteComponentRealFourierStripComparisonAndEventuallyIndexedTrivialAxisRealHeightTail_closedBallPolynomialCounting
      (system := system) component stripRealComparisonConstant
      stripFourierComparisonConstant tailComparisonComponentConstant
      stripRealComparisonConstant_nonneg stripFourierComparisonConstant_nonneg
      tailComparisonComponentConstant_nonneg k
      strip_extension_eq_component_sum
      tail_axis_extension_eq_component_sum_eventually
      component_strip_norm_le_real_fourier
      component_tail_axis_norm_le_realHeight_eventually
      counting counting_cutoff_eq growth_add_one_lt_k windowExhaustion f).eventually
      (Iio_mem_nhds hepsilon)

end FiniteComponentRealFourierProjectWeightWindowEndpoints

end RiemannHypothesisProject
