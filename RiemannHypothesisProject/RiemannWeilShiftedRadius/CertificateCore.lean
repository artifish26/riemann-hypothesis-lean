import RiemannHypothesisProject.RiemannWeilShiftedRadius.ProjectWeightEndpoints

/-!
# Shifted-radius certificate core

This module contains the reusable shifted-radius certificate records, critical-
line core estimates, global certificate handoffs, zero-argument certificate
records, and split zero-locus input constructors.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion
open MeasureTheory
open scoped Topology

/--
A weighted shifted-radius decay certificate for an extension system.

The remaining analytic work for a concrete extension is the field
`weighted_norm_le`: prove that `||F_f(z)|| * (||z|| + 2)^q` is uniformly
bounded by `constant f`.
-/
structure RiemannWeilShiftedRadiusDecayCertificate
    (system : SchwartzRiemannWeilExtensionSystem) where
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  weighted_norm_le :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      norm (system.extension f z) * (norm z + 2) ^ decayExponent <=
        constant f

/--
Critical-line zero arguments satisfy the project weighted zero-locus estimate
with the concrete shifted real-axis Schwartz seminorm constant.

This is the direct source-side inequality used by the p-series closedness
route: once `rho = 1/2 + i t`, the Riemann-Weil zero argument is the real
height `t`, so the extension value is controlled by ordinary Schwartz decay on
the real line.
-/
theorem criticalLine_zeroArgument_extension_weighted_norm_le
    (system : SchwartzRiemannWeilExtensionSystem)
    (k : Nat)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (t : Real)
    (hrho : (rho : Complex) = criticalLinePoint t) :
    norm
        (system.extension f
          (riemannWeilZeroArgument (rho : Complex))) *
        (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
          (k : Real) <=
      schwartzLineRealAxisShiftedSeminormConstant k f := by
  have harg :
      riemannWeilZeroArgument (rho : Complex) = (t : Complex) := by
    rw [hrho, riemannWeilZeroArgument_criticalLinePoint]
  have hvalue_real :
      system.extension f (t : Complex) = f t :=
    system.extension_restricts f t
  have hreal :=
    schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast
      k f t
  simpa [harg, hvalue_real] using hreal

/--
Critical-line zero values satisfy the closed-ball first-entry p-series bound
coming from ordinary real-axis Schwartz decay.

This is a genuine estimate, not a new route assumption: once a zero is
identified as `rho = 1/2 + i t`, the extension value at the Riemann-Weil
zero argument is `f t`, and the checked closed-ball shell geometry compares
the first-entry index with `‖t‖`.
-/
theorem criticalLine_zeroValue_le_closedBallFirstEntryIndex_pseries
    (system : SchwartzRiemannWeilExtensionSystem)
    (k : Nat)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype)
    (t : Real)
    (hrho : (rho : Complex) = criticalLinePoint t) :
    norm (system.zeroValue f rho) <=
      schwartzLineRealAxisShiftedSeminormConstant k f *
        (1 /
          |((ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho -
              1 : Nat) : Real) + 1| ^ (k : Real)) := by
  let n := ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho
  have hconstant_nonneg :
      0 <= schwartzLineRealAxisShiftedSeminormConstant k f :=
    schwartzLineRealAxisShiftedSeminormConstant_nonneg k f
  have hzeroValue : system.zeroValue f rho = f t :=
    system.zeroValue_of_criticalLinePoint f t hrho
  have harg :
      norm (riemannWeilZeroArgument (rho : Complex)) =
        norm ((t : Complex)) := by
    rw [hrho, riemannWeilZeroArgument_criticalLinePoint]
  have hshifted :
      norm (system.zeroValue f rho) <=
        schwartzLineRealAxisShiftedSeminormConstant k f *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) := by
    have hmul :=
      schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast
        k f t
    have hden_pos :
        0 < (norm ((t : Complex)) + 2) ^ (k : Real) :=
      Real.rpow_pos_of_pos (by positivity) (k : Real)
    have hle :
        norm (f t) <=
          schwartzLineRealAxisShiftedSeminormConstant k f /
            (norm ((t : Complex)) + 2) ^ (k : Real) :=
      (le_div_iff₀ hden_pos).mpr hmul
    simpa [hzeroValue, harg, one_div, div_eq_mul_inv] using hle
  by_cases hn : 1 <= n
  · have hindex : (n - 1) + 1 = n := Nat.sub_add_cancel hn
    have hlower :
        ComplexCompactExhaustion.closedBallZeroArgumentShellLowerBound
            ((n - 1) + 1) <
          norm (riemannWeilZeroArgument (rho : Complex)) := by
      simpa [n, hindex] using
        ComplexCompactExhaustion.closedBallZero_firstEntryIndex_argumentShellLowerBound_lt
          rho
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) <=
          (1 / |((n - 1 : Nat) : Real) + 1| ^ (k : Real)) :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_tailFactor_of_succ_argumentShellLowerBound
        (n - 1) (by positivity) hlower
    exact hshifted.trans
      (mul_le_mul_of_nonneg_left hfactor hconstant_nonneg)
  · have hn_zero : n = 0 := by omega
    have hfactor :
        (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real)) <= 1 :=
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_one_of_nonneg_radius
        (norm_nonneg (riemannWeilZeroArgument (rho : Complex)))
        (by positivity)
    have hprefix :
        schwartzLineRealAxisShiftedSeminormConstant k f *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                (k : Real)) <=
          schwartzLineRealAxisShiftedSeminormConstant k f :=
      (mul_le_mul_of_nonneg_left hfactor hconstant_nonneg).trans_eq
        (mul_one (schwartzLineRealAxisShiftedSeminormConstant k f))
    refine hshifted.trans ?_
    simpa [n, hn_zero] using hprefix

/--
Under an explicit critical-line height realization for every zero, ordinary
real-axis Schwartz decay supplies a cutoff-1 closed-ball polynomial zero-decay
estimate.

The cutoff is `1` because shell `n + 1` is compared with the p-series term
`1 / (n + 1)^k`; shell `0` is absorbed by the finite prefix.
-/
noncomputable def criticalLinePolynomialZeroDecayEstimate
    (system : SchwartzRiemannWeilExtensionSystem)
    (k : Nat)
    (criticalLineHeight : ZetaZeroSubtype -> Real)
    (criticalLineHeight_spec :
      forall rho : ZetaZeroSubtype,
        (rho : Complex) = criticalLinePoint (criticalLineHeight rho)) :
    SchwartzRiemannWeilPolynomialZeroDecayEstimate
      ComplexCompactExhaustion.closedBallZero system where
  cutoff := 1
  shellBound := fun f n =>
    schwartzLineRealAxisShiftedSeminormConstant k f *
      (1 / |(((n - 1 : Nat) : Real) + 1)| ^ (k : Real))
  zeroConstant := fun f => schwartzLineRealAxisShiftedSeminormConstant k f
  decayExponent := fun _ => (k : Real)
  zeroConstant_nonneg := fun f =>
    schwartzLineRealAxisShiftedSeminormConstant_nonneg k f
  shellBound_nonneg := by
    intro f n
    exact
      mul_nonneg
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)
        (one_div_nonneg.mpr
          (Real.rpow_nonneg
            (abs_nonneg ((((n - 1 : Nat) : Real) + 1)))
            (k : Real)))
  tail_shellBound_le := by
    intro f n
    simp
  norm_zeroValue_le_shellBound := by
    intro f rho
    simpa using
      criticalLine_zeroValue_le_closedBallFirstEntryIndex_pseries
        system k f rho (criticalLineHeight rho)
        (criticalLineHeight_spec rho)

namespace RiemannWeilShiftedRadiusDecayCertificate

/--
The weighted seminorm form implies the shifted-radius exact-norm estimate used
by the p-series route.
-/
theorem extension_norm_le_shiftedRadialBound
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : RiemannWeilShiftedRadiusDecayCertificate system) :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      norm (system.extension f z) <=
        certificate.constant f *
          (1 / (norm z + 2) ^ certificate.decayExponent) := by
  intro f z
  let radiusPower : Real := (norm z + 2) ^ certificate.decayExponent
  have hbase_pos : 0 < norm z + 2 := by
    have hnorm_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hradiusPower_pos : 0 < radiusPower := by
    dsimp [radiusPower]
    exact Real.rpow_pos_of_pos hbase_pos certificate.decayExponent
  have hweighted :
      norm (system.extension f z) * radiusPower <= certificate.constant f := by
    simpa [radiusPower] using certificate.weighted_norm_le f z
  have hdiv :
      norm (system.extension f z) * radiusPower / radiusPower <=
        certificate.constant f / radiusPower :=
    div_le_div_of_nonneg_right hweighted (le_of_lt hradiusPower_pos)
  have hleft :
      norm (system.extension f z) * radiusPower / radiusPower =
        norm (system.extension f z) := by
    field_simp [hradiusPower_pos.ne']
  have hright :
      certificate.constant f / radiusPower =
        certificate.constant f * (1 / radiusPower) := by
    ring
  calc
    norm (system.extension f z)
        = norm (system.extension f z) * radiusPower / radiusPower := by
          rw [hleft]
    _ <= certificate.constant f / radiusPower := hdiv
    _ = certificate.constant f * (1 / radiusPower) := hright

/--
The current global all-plane shifted-radius decay certificate is analytically
very strong: since the exponent is nonnegative, it makes each entire extension
bounded, hence constant by Liouville's theorem.

This checked obstruction says that a nontrivial p-series route cannot ask for
polynomial decay of an entire extension in every complex direction.  The
eventual target must be weakened to the actual zero-argument locus, a strip,
or another non-global domain/envelope.
-/
theorem extension_range_isBounded
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : RiemannWeilShiftedRadiusDecayCertificate system)
    (f : SchwartzLineTestFunction) :
    Bornology.IsBounded (Set.range (system.extension f)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨certificate.constant f, ?_⟩
  intro value hvalue
  rcases hvalue with ⟨z, rfl⟩
  let radiusPower : Real := (norm z + 2) ^ certificate.decayExponent
  have hbase_one : 1 <= norm z + 2 := by
    have hnorm_nonneg : 0 <= norm z := norm_nonneg z
    linarith
  have hradiusPower_one : 1 <= radiusPower := by
    dsimp [radiusPower]
    exact Real.one_le_rpow hbase_one certificate.decayExponent_nonneg
  have hnorm_le_weighted :
      norm (system.extension f z) <=
        norm (system.extension f z) * radiusPower := by
    calc
      norm (system.extension f z)
          = norm (system.extension f z) * 1 := by ring
      _ <= norm (system.extension f z) * radiusPower := by
        exact mul_le_mul_of_nonneg_left hradiusPower_one
          (norm_nonneg (system.extension f z))
  exact hnorm_le_weighted.trans (by
    simpa [radiusPower] using certificate.weighted_norm_le f z)

/--
Liouville consequence of `extension_range_isBounded`: a global all-plane
shifted-radius certificate forces every candidate extension to be constant.
-/
theorem extension_apply_eq_apply_of_global_decay
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : RiemannWeilShiftedRadiusDecayCertificate system)
    (f : SchwartzLineTestFunction) (z w : Complex) :
    system.extension f z = system.extension f w :=
  (system.extension_differentiable f).apply_eq_apply_of_bounded
    (certificate.extension_range_isBounded f) z w

/--
Consequently, the current global certificate shape would force every project
Schwartz test function to be constant on the real line.
-/
theorem realLine_apply_eq_apply_of_global_decay
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : RiemannWeilShiftedRadiusDecayCertificate system)
    (f : SchwartzLineTestFunction) (t u : Real) :
    f t = f u := by
  calc
    f t = system.extension f (t : Complex) := by
      exact (system.extension_restricts f t).symm
    _ = system.extension f (u : Complex) :=
      certificate.extension_apply_eq_apply_of_global_decay f (t : Complex) (u : Complex)
    _ = f u := system.extension_restricts f u

/--
Every global shifted-radius certificate restricts to the expected real-axis
decay estimate for the original Schwartz test function.
-/
theorem realAxis_weighted_norm_le
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : RiemannWeilShiftedRadiusDecayCertificate system)
    (f : SchwartzLineTestFunction) (t : Real) :
    ‖f t‖ * (norm ((t : Complex)) + 2) ^ certificate.decayExponent <=
      certificate.constant f := by
  simpa [system.extension_restricts f t] using
    certificate.weighted_norm_le f (t : Complex)

/--
The weighted seminorm certificate feeds the existing cutoff-2 exact-norm
automatic-prefix p-series target.
-/
noncomputable def toCutoffTwoClosedBallAutomaticPrefixTarget
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : RiemannWeilShiftedRadiusDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  RiemannWeilAutomaticPrefixRadialPSeriesTarget.ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    system certificate.constant certificate.decayExponent
    certificate.constant_nonneg certificate.decayExponent_nonneg
    certificate.extension_norm_le_shiftedRadialBound counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
The same certificate also feeds the cutoff-1 shifted-radius zero-data route
directly when the counting input has cutoff `1`.
-/
noncomputable def toCutoffOneClosedBallZeroData
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate : RiemannWeilShiftedRadiusDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData.ofClosedBallShiftedRadiusExactNormCutoffOneSelf
    system certificate.constant certificate.decayExponent
    certificate.constant_nonneg certificate.decayExponent_nonneg
    certificate.extension_norm_le_shiftedRadialBound counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
If an admissible Guinand-Weil source class covers every project Schwartz test
function, then a weighted decay estimate proved on admissible source tests gives
the global shifted-radius decay certificate.

This is the p-series analogue of the source-formula coverage bridge: it keeps
the real analytic work on the source class while producing the global
`SchwartzLineTestFunction` certificate required by the exact-norm route.
-/
noncomputable def ofSourceCoverageWeightedDecay
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (coversSchwartz :
      forall f : SchwartzLineTestFunction,
        exists g : testData.SourceTestFunction,
          testData.admissible g /\ testData.toSchwartz g = f)
    (source_weighted_norm_le :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            norm (system.extension (testData.toSchwartz g) z) *
                (norm z + 2) ^ decayExponent <=
              constant (testData.toSchwartz g)) :
    RiemannWeilShiftedRadiusDecayCertificate system where
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  weighted_norm_le := by
    classical
    intro f z
    let g := Classical.choose (coversSchwartz f)
    have hgpair := Classical.choose_spec (coversSchwartz f)
    have hg : testData.admissible g := hgpair.1
    have hgf : testData.toSchwartz g = f := hgpair.2
    simpa [g, hgf] using source_weighted_norm_le g hg z

/--
Finite-component weighted decay certificate.

This is the proof shape expected for a concrete Guinand-Weil extension written
as a finite sum of analytically controlled pieces.  The analytic work is now
split into two explicit obligations:

* the extension norm is bounded by the sum of component norms;
* each component has the required shifted weighted decay.

The resulting certificate feeds the same exact-norm p-series constructors as a
single global weighted estimate.
-/
noncomputable def ofFiniteComponentWeightedDecay
    {ι : Type*} [Fintype ι]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : ι -> SchwartzLineTestFunction -> Complex -> Complex)
    (componentConstant : ι -> SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (componentConstant_nonneg :
      forall i : ι, forall f : SchwartzLineTestFunction,
        0 <= componentConstant i f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : ι => norm (component i f z)))
    (component_weighted_norm_le :
      forall i : ι,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          norm (component i f z) * (norm z + 2) ^ decayExponent <=
            componentConstant i f) :
    RiemannWeilShiftedRadiusDecayCertificate system where
  constant := fun f => Finset.univ.sum fun i : ι => componentConstant i f
  decayExponent := decayExponent
  constant_nonneg := by
    intro f
    exact Finset.sum_nonneg fun i _ => componentConstant_nonneg i f
  decayExponent_nonneg := decayExponent_nonneg
  weighted_norm_le := by
    intro f z
    let radiusPower : Real := (norm z + 2) ^ decayExponent
    have hbase_pos : 0 < norm z + 2 := by
      have hnorm_nonneg : 0 <= norm z := norm_nonneg z
      linarith
    have hradiusPower_nonneg : 0 <= radiusPower := by
      exact le_of_lt (Real.rpow_pos_of_pos hbase_pos decayExponent)
    have hnorm :
        norm (system.extension f z) <=
          (Finset.univ.sum fun i : ι => norm (component i f z)) :=
      extension_norm_le_component_sum f z
    calc
      norm (system.extension f z) * radiusPower
          <= (Finset.univ.sum fun i : ι => norm (component i f z)) *
              radiusPower :=
        mul_le_mul_of_nonneg_right hnorm hradiusPower_nonneg
      _ = Finset.univ.sum fun i : ι =>
            norm (component i f z) * radiusPower := by
        simp [Finset.sum_mul, radiusPower]
      _ <= Finset.univ.sum fun i : ι => componentConstant i f :=
        Finset.sum_le_sum fun i _ => by
          simpa [radiusPower] using component_weighted_norm_le i f z

/--
Finite-sum component weighted decay certificate.

When the concrete extension is literally a finite sum of controlled analytic
components, the triangle inequality supplies the component norm majorization
required by `ofFiniteComponentWeightedDecay`.  The remaining analytic fields are
the finite decomposition identity and the componentwise shifted weighted decay.
-/
noncomputable def ofFiniteComponentSumWeightedDecay
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (componentConstant : Index -> SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (componentConstant_nonneg :
      forall i : Index, forall f : SchwartzLineTestFunction,
        0 <= componentConstant i f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        system.extension f z =
          Finset.univ.sum fun i : Index => component i f z)
    (component_weighted_norm_le :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          norm (component i f z) * (norm z + 2) ^ decayExponent <=
            componentConstant i f) :
    RiemannWeilShiftedRadiusDecayCertificate system :=
  ofFiniteComponentWeightedDecay component componentConstant decayExponent
    componentConstant_nonneg decayExponent_nonneg
    (by
      intro f z
      rw [extension_eq_component_sum f z]
      exact norm_sum_le Finset.univ (fun i : Index => component i f z))
    component_weighted_norm_le

end RiemannWeilShiftedRadiusDecayCertificate

/--
Zero-argument shifted-radius decay certificate.

Unlike `RiemannWeilShiftedRadiusDecayCertificate`, this certificate only asks
for the exact-norm bound at the complex arguments that actually occur in the
Riemann-Weil zero side.  This avoids the Liouville obstruction for all-plane
polynomial decay of an entire extension.
-/
structure RiemannWeilZeroArgumentShiftedRadiusDecayCertificate
    (system : SchwartzRiemannWeilExtensionSystem) where
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  zeroArgument_norm_le_shiftedRadialBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) <=
        constant f *
          (1 /
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              decayExponent)


namespace RiemannWeilZeroArgumentShiftedRadiusDecayCertificate

/--
The zero-argument shifted-radius certificate feeds the same cutoff-1
closed-ball p-series zero-data route as the former global certificate, but only
uses decay at actual zeta-zero arguments.
-/
noncomputable def toCutoffOneClosedBallZeroData
    {system : SchwartzRiemannWeilExtensionSystem}
    (certificate :
      RiemannWeilZeroArgumentShiftedRadiusDecayCertificate system)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate
        ComplexCompactExhaustion.closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < certificate.decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData where
  exhaustion := ComplexCompactExhaustion.closedBallZero
  system := system
  growthBound := SchwartzRiemannWeilExtensionGrowthBound.exactNorm system
  cutoff := 1
  prefixBound := fun f _ => certificate.constant f
  zeroConstant := certificate.constant
  decayExponent := fun _ => certificate.decayExponent
  zeroConstant_nonneg := certificate.constant_nonneg
  prefixBound_nonneg := fun f _ => certificate.constant_nonneg f
  pseriesBound_nonneg :=
    fun f n =>
      pseriesEnvelopeTerm_nonneg
        (zeroConstant := certificate.constant)
        (decayExponent := fun _ => certificate.decayExponent)
        certificate.constant_nonneg f n
  envelope_zeroArgument_le_eventualPSeries := by
    intro f rho
    let n := ComplexCompactExhaustion.closedBallZero.zetaZeroFirstEntryIndex rho
    have hdecay :
        (SchwartzRiemannWeilExtensionGrowthBound.exactNorm system).envelope
          f (riemannWeilZeroArgument (rho : Complex)) <=
          certificate.constant f *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                certificate.decayExponent) := by
      simpa [SchwartzRiemannWeilExtensionGrowthBound.exactNorm] using
        certificate.zeroArgument_norm_le_shiftedRadialBound f rho
    refine hdecay.trans ?_
    dsimp [SchwartzRiemannWeilExtensionShellDecayEstimate.eventualPSeriesShellBound]
    by_cases hn : 1 <= n
    · have hindex : (n - 1) + 1 = n := Nat.sub_add_cancel hn
      have hlower :
          closedBallZeroArgumentShellLowerBound ((n - 1) + 1) <
            norm (riemannWeilZeroArgument (rho : Complex)) := by
        simpa [n, hindex] using
          closedBallZero_firstEntryIndex_argumentShellLowerBound_lt rho
      have hfactor :
          (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                certificate.decayExponent) <=
            (1 / |((n - 1 : Nat) : Real) + 1| ^
              certificate.decayExponent) :=
        RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_tailFactor_of_succ_argumentShellLowerBound
          (n - 1) certificate.decayExponent_nonneg hlower
      simpa [n, hn] using
        mul_le_mul_of_nonneg_left hfactor (certificate.constant_nonneg f)
    · have hfactor :
          (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                certificate.decayExponent) <= 1 :=
        RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_one_of_nonneg_radius
          (norm_nonneg (riemannWeilZeroArgument (rho : Complex)))
          certificate.decayExponent_nonneg
      have hprefix :
          certificate.constant f *
              (1 /
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  certificate.decayExponent) <=
            certificate.constant f :=
        (mul_le_mul_of_nonneg_left hfactor (certificate.constant_nonneg f)).trans_eq
          (mul_one (certificate.constant f))
      simpa [n, hn] using hprefix
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := fun _ => growth_add_one_lt_decay

end RiemannWeilZeroArgumentShiftedRadiusDecayCertificate

/--
Weighted zero-argument shifted-radius decay certificate.

This is the zero-locus analogue of
`RiemannWeilShiftedRadiusDecayCertificate`: it asks for the analytically natural
weighted estimate only at Riemann-Weil zero arguments, avoiding the all-plane
Liouville obstruction while preserving the p-series denominator.
-/
structure RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate
    (system : SchwartzRiemannWeilExtensionSystem) where
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  zeroArgument_weighted_norm_le :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
          (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
            decayExponent <=
        constant f

/--
Split analytic input for proving the actual all-zero-locus weighted decay
certificate.

The zeta-zero subtype contains the project-known trivial zeroes, whose
Riemann-Weil arguments run up the imaginary axis. Therefore a horizontal-strip
decay theorem alone cannot prove decay on the whole subtype. This package
separates the real analytic obligations into:

* a weighted extension estimate on the checked nontrivial-zero horizontal strip;
* separate control of project-known trivial zero arguments.
-/
structure RiemannWeilSplitZeroLocusWeightedDecayInput
    (system : SchwartzRiemannWeilExtensionSystem) where
  constant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  constant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= constant f
  decayExponent_nonneg : 0 <= decayExponent
  strip_weighted_norm_le :
    forall (f : SchwartzLineTestFunction) (z : Complex),
      -(1 / 2 : Real) <= z.im ->
        z.im <= (1 / 2 : Real) ->
          norm (system.extension f z) * (norm z + 2) ^ decayExponent <=
            constant f
  trivial_zeroArgument_weighted_norm_le :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      IsTrivialZetaZero (rho : Complex) ->
        norm
            (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              decayExponent <=
          constant f

namespace RiemannWeilSplitZeroLocusWeightedDecayInput

/--
The split strip/trivial-axis analytic input proves the preferred weighted
zero-locus certificate.
-/
noncomputable def toZeroArgumentShiftedRadiusWeightedDecayCertificate
    {system : SchwartzRiemannWeilExtensionSystem}
    (input : RiemannWeilSplitZeroLocusWeightedDecayInput system) :
    RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate system where
  constant := input.constant
  decayExponent := input.decayExponent
  constant_nonneg := input.constant_nonneg
  decayExponent_nonneg := input.decayExponent_nonneg
  zeroArgument_weighted_norm_le := by
    intro f rho
    by_cases htrivial : IsTrivialZetaZero (rho : Complex)
    · exact input.trivial_zeroArgument_weighted_norm_le f rho htrivial
    · have hstrip :=
        riemannWeilZeroArgument_mem_closedHorizontalStrip_of_re_nonneg rho
          (zetaZeroSubtype_re_nonneg_of_not_trivial rho htrivial)
      exact input.strip_weighted_norm_le f
        (riemannWeilZeroArgument (rho : Complex)) hstrip.1 hstrip.2

/--
If trivial zero arguments vanish in the zero contribution, the split input only
needs strip decay plus trivial-zero vanishing.
-/
noncomputable def ofStripDecayAndTrivialVanishing
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
    RiemannWeilSplitZeroLocusWeightedDecayInput system where
  constant := constant
  decayExponent := decayExponent
  constant_nonneg := constant_nonneg
  decayExponent_nonneg := decayExponent_nonneg
  strip_weighted_norm_le := strip_weighted_norm_le
  trivial_zeroArgument_weighted_norm_le := by
    intro f rho htrivial
    rw [trivial_zeroArgument_extension_eq_zero f rho htrivial]
    simpa using constant_nonneg f

/--
Concrete horizontal-strip route from a vertical real-part comparison estimate.

The remaining analytic theorem for a chosen extension can now be stated as:
on the critical horizontal strip, `system.extension f z` is dominated by a
nonnegative multiple of the real-axis value `f z.re`. The checked real-axis
Schwartz decay and strip-radius geometry then produce the full weighted
zero-locus input, provided the trivial-zero arguments vanish in this
normalization.
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
    RiemannWeilSplitZeroLocusWeightedDecayInput system where
  constant := fun f =>
    comparisonConstant f *
      ((2 : Real) ^ k * schwartzLineRealAxisShiftedSeminormConstant k f)
  decayExponent := k
  constant_nonneg := by
    intro f
    exact mul_nonneg (comparisonConstant_nonneg f)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
  decayExponent_nonneg := by positivity
  strip_weighted_norm_le := by
    intro f z hlow hhigh
    exact
      horizontalStrip_weighted_norm_le_of_realPartComparison_rpow_natCast
        comparisonConstant comparisonConstant_nonneg
        strip_extension_norm_le_realAxis k f z hlow hhigh
  trivial_zeroArgument_weighted_norm_le := by
    intro f rho htrivial
    rw [trivial_zeroArgument_extension_eq_zero f rho htrivial]
    exact by
      simpa using
        mul_nonneg (comparisonConstant_nonneg f)
          (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
            (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))

/--
Concrete route from vertical real-part comparison plus an indexed
trivial-axis estimate.

This removes the last opaque part of the split p-series target: trivial zeroes
are now controlled by proving a one-dimensional estimate along the explicit
sequence `(2 * (n + 1) + 1 / 2) * I`.
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
    RiemannWeilSplitZeroLocusWeightedDecayInput system where
  constant := fun f =>
    comparisonConstant f *
      ((2 : Real) ^ k * schwartzLineRealAxisShiftedSeminormConstant k f)
  decayExponent := k
  constant_nonneg := by
    intro f
    exact mul_nonneg (comparisonConstant_nonneg f)
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
  decayExponent_nonneg := by positivity
  strip_weighted_norm_le := by
    intro f z hlow hhigh
    exact
      horizontalStrip_weighted_norm_le_of_realPartComparison_rpow_natCast
        comparisonConstant comparisonConstant_nonneg
        strip_extension_norm_le_realAxis k f z hlow hhigh
  trivial_zeroArgument_weighted_norm_le := by
    intro f rho htrivial
    rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
        (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    have haxis := trivialAxis_weighted_norm_le f n
    have hheight_abs :
        |riemannWeilTrivialZeroArgumentHeight n| =
          riemannWeilTrivialZeroArgumentHeight n := by
      exact abs_of_nonneg
        (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
    simpa [harg, norm_trivialZeroArgumentHeight_mul_I n, hheight_abs]
      using haxis

/--
Concrete route from vertical real-part comparison plus uniform positive
imaginary-axis control.

Compared with `ofRealPartComparisonAndTrivialAxisControl`, this removes the
indexed trivial-axis obligation. The remaining real analytic tasks are now:

* prove vertical real-part domination on the checked critical strip;
* prove a one-dimensional weighted estimate on the positive imaginary axis.
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
    RiemannWeilSplitZeroLocusWeightedDecayInput system where
  constant := fun f =>
    comparisonConstant f *
        ((2 : Real) ^ k * schwartzLineRealAxisShiftedSeminormConstant k f) +
      axisConstant f
  decayExponent := k
  constant_nonneg := by
    intro f
    exact add_nonneg
      (mul_nonneg (comparisonConstant_nonneg f)
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f)))
      (axisConstant_nonneg f)
  decayExponent_nonneg := by positivity
  strip_weighted_norm_le := by
    intro f z hlow hhigh
    have hstrip :=
      horizontalStrip_weighted_norm_le_of_realPartComparison_rpow_natCast
        comparisonConstant comparisonConstant_nonneg
        strip_extension_norm_le_realAxis k f z hlow hhigh
    exact hstrip.trans (by
      have haxis_nonneg := axisConstant_nonneg f
      linarith)
  trivial_zeroArgument_weighted_norm_le := by
    intro f rho htrivial
    rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
        (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    have haxis :=
      trivialAxis_weighted_norm_le_of_imaginaryAxis_nonnegative_height_bound
        (system := system) axisConstant k imaginaryAxis_weighted_norm_le f n
    have hheight_abs :
        |riemannWeilTrivialZeroArgumentHeight n| =
          riemannWeilTrivialZeroArgumentHeight n := by
      exact abs_of_nonneg
        (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
    have hcomparison_nonneg :
        0 <= comparisonConstant f *
          ((2 : Real) ^ k * schwartzLineRealAxisShiftedSeminormConstant k f) := by
      exact mul_nonneg (comparisonConstant_nonneg f)
        (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (schwartzLineRealAxisShiftedSeminormConstant_nonneg k f))
    have haxis_zeroArgument :
        norm
            (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          axisConstant f := by
      simpa [harg, norm_trivialZeroArgumentHeight_mul_I n, hheight_abs]
        using haxis
    exact haxis_zeroArgument.trans (by
      linarith)

/--
Variant of `ofRealPartComparisonAndImaginaryAxisControl` whose imaginary-axis
input uses the standard `(1 + y)^k` weight. The constructor pays the explicit
factor `2^k` to match the shifted-radius p-series normalization.
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
    RiemannWeilSplitZeroLocusWeightedDecayInput system :=
  RiemannWeilSplitZeroLocusWeightedDecayInput.ofRealPartComparisonAndImaginaryAxisControl
    comparisonConstant
    (fun f => (2 : Real) ^ k * axisConstant f)
    comparisonConstant_nonneg
    (by
      intro f
      exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (axisConstant_nonneg f))
    k
    strip_extension_norm_le_realAxis
    (by
      intro f y hy
      exact
        imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_rpow_natCast
          (system := system) axisConstant k
          imaginaryAxis_oneAdd_weighted_norm_le f y hy)

/--
Preferred replacement for pointwise real-value domination.

The strip input is a nonvanishing real-radius envelope
`norm (extension f z) * (norm (z.re) + 2)^k <= stripConstant f`; this avoids
the real-zero obstruction of `norm (f z.re)` while still giving the shifted
complex-radius p-series weight by checked geometry. The trivial-zero ray is
handled by the standard `(1 + y)^k` positive-imaginary-axis estimate.
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
    RiemannWeilSplitZeroLocusWeightedDecayInput system where
  constant := fun f =>
    (2 : Real) ^ k * stripConstant f +
      (2 : Real) ^ k * axisConstant f
  decayExponent := k
  constant_nonneg := by
    intro f
    exact add_nonneg
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (stripConstant_nonneg f))
      (mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (axisConstant_nonneg f))
  decayExponent_nonneg := by positivity
  strip_weighted_norm_le := by
    intro f z hlow hhigh
    have hstrip :=
      horizontalStrip_weighted_norm_le_of_realPartShiftedEnvelope_rpow_natCast
        (system := system) stripConstant k
        strip_extension_weighted_norm_le_realRadius f z hlow hhigh
    exact hstrip.trans (by
      have haxis_nonneg :
          0 <= (2 : Real) ^ k * axisConstant f :=
        mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
          (axisConstant_nonneg f)
      linarith)
  trivial_zeroArgument_weighted_norm_le := by
    intro f rho htrivial
    rcases exists_riemannWeilZeroArgument_eq_trivialZeroHeight_mul_I
        (s := (rho : Complex)) htrivial with ⟨n, harg⟩
    have haxis :=
      trivialAxis_weighted_norm_le_of_imaginaryAxis_nonnegative_height_bound
        (system := system)
        (fun f => (2 : Real) ^ k * axisConstant f) k
        (by
          intro f y hy
          exact
            imaginaryAxis_shifted_weighted_norm_le_of_oneAdd_weighted_norm_le_rpow_natCast
              (system := system) axisConstant k
              imaginaryAxis_oneAdd_weighted_norm_le f y hy)
        f n
    have hheight_abs :
        |riemannWeilTrivialZeroArgumentHeight n| =
          riemannWeilTrivialZeroArgumentHeight n := by
      exact abs_of_nonneg
        (le_of_lt (riemannWeilTrivialZeroArgumentHeight_pos n))
    have hstrip_nonneg :
        0 <= (2 : Real) ^ k * stripConstant f :=
      mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
        (stripConstant_nonneg f)
    have haxis_zeroArgument :
        norm
            (system.extension f (riemannWeilZeroArgument (rho : Complex))) *
            (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
              (k : Real) <=
          (2 : Real) ^ k * axisConstant f := by
      simpa [harg, norm_trivialZeroArgumentHeight_mul_I n, hheight_abs]
        using haxis
    exact haxis_zeroArgument.trans (by
      linarith)

end RiemannWeilSplitZeroLocusWeightedDecayInput
end RiemannHypothesisProject
