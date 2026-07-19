import RiemannHypothesisProject.RiemannWeilAntitoneRadialPSeriesBridge

/-!
# Split antitone radial p-series bridge

`RiemannWeilAntitoneRadialPSeriesBridge` asks for one theorem bounding the
radial majorant at the checked shell lower bound by the eventual p-series shell
bound.

Analytically, that theorem naturally splits into two parts:

* a finite-prefix bound for `n < cutoff`;
* a p-series tail bound for `cutoff <= n`.

This file checks that split once and converts the resulting package back to the
existing antitone radial p-series route.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion

namespace RiemannWeilAntitoneRadialPSeriesEnvelopeData

/--
Finite-prefix and tail estimates imply the single eventual p-series bound used
by the antitone radial route.
-/
theorem lowerBound_le_eventualConstantPSeries_of_split
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < cutoff ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        cutoff <= n ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            zeroConstant f *
              (1 / |((n - cutoff : Nat) : Real) + 1| ^ decayExponent))
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    radialBound f (closedBallZeroArgumentShellLowerBound n) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        cutoff prefixBound zeroConstant decayExponent f n := by
  by_cases hcutoff : cutoff <= n
  · simpa [SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound,
      hcutoff] using tail_radialBound_lowerBound_le f n hcutoff
  · have hn : n < cutoff := Nat.lt_of_not_ge hcutoff
    simpa [SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound,
      hcutoff] using prefix_radialBound_lowerBound_le f n hn

/--
A tail estimate stated in the natural coordinate `m` after the cutoff gives the
absolute-index tail field used by the split package.
-/
theorem tail_radialBound_lowerBound_le_of_tailCoordinate
    (cutoff : Nat)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (tail_radialBound_lowerBound_le_tail :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (closedBallZeroArgumentShellLowerBound (m + cutoff)) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hcutoff : cutoff <= n) :
    radialBound f (closedBallZeroArgumentShellLowerBound n) <=
      zeroConstant f *
        (1 / |((n - cutoff : Nat) : Real) + 1| ^ decayExponent) := by
  have hindex : (n - cutoff) + cutoff = n := Nat.sub_add_cancel hcutoff
  simpa [hindex] using tail_radialBound_lowerBound_le_tail f (n - cutoff)

/--
If the shell lower bound for `m + cutoff` dominates the plain radius `m`, then
an antitone radial majorant only needs to be bounded at radius `m`.
-/
theorem tailCoordinate_lowerBound_le_of_natRadius_tail
    (cutoff : Nat)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (f : SchwartzLineTestFunction)
    (m : Nat) :
    radialBound f (closedBallZeroArgumentShellLowerBound (m + cutoff)) <=
      zeroConstant f *
        (1 / |(m : Real) + 1| ^ decayExponent) :=
  ((radialBound_antitone f) (tail_radius_le_lowerBound m)).trans
    (tail_radialBound_natRadius_le f m)

/-- The natural p-series tail base `|m + 1|` is at least `1`. -/
theorem one_le_abs_natCast_add_one (m : Nat) :
    (1 : Real) <= |(m : Real) + 1| := by
  have hm : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
  have hnonneg : 0 <= (m : Real) + 1 := by linarith
  have hone : (1 : Real) <= (m : Real) + 1 := by linarith
  rw [abs_of_nonneg hnonneg]
  exact hone

/--
A stronger p-series decay exponent may be weakened to a smaller exponent on
the natural tail coordinate.
-/
theorem pseriesTailFactor_le_of_decayExponent_le
    (m : Nat)
    {decayExponent strongDecayExponent : Real}
    (hdecay_le_strong : decayExponent <= strongDecayExponent) :
    (1 / |(m : Real) + 1| ^ strongDecayExponent) <=
      (1 / |(m : Real) + 1| ^ decayExponent) := by
  have hbase_one : (1 : Real) <= |(m : Real) + 1| :=
    one_le_abs_natCast_add_one m
  have hbase_pos : 0 < |(m : Real) + 1| := zero_lt_one.trans_le hbase_one
  have hpow_le :
      |(m : Real) + 1| ^ decayExponent <=
        |(m : Real) + 1| ^ strongDecayExponent :=
    Real.rpow_le_rpow_of_exponent_le hbase_one hdecay_le_strong
  exact
    one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hbase_pos decayExponent)
      hpow_le

/-- The natural p-series tail factor is nonnegative. -/
theorem pseriesTailFactor_nonneg
    (m : Nat)
    (decayExponent : Real) :
    0 <= (1 / |(m : Real) + 1| ^ decayExponent) :=
  one_div_nonneg.mpr
    (Real.rpow_nonneg (abs_nonneg ((m : Real) + 1)) decayExponent)

/--
If a source tail has both a smaller leading constant and a stronger exponent,
it is bounded by the weaker target tail used by the p-series package.
-/
theorem sourceConstant_mul_strongTailFactor_le_target
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    {decayExponent strongDecayExponent : Real}
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (f : SchwartzLineTestFunction)
    (m : Nat) :
    sourceConstant f * (1 / |(m : Real) + 1| ^ strongDecayExponent) <=
      zeroConstant f * (1 / |(m : Real) + 1| ^ decayExponent) :=
  (mul_le_mul_of_nonneg_left
      (pseriesTailFactor_le_of_decayExponent_le m hdecay_le_strong)
      (sourceConstant_nonneg f)).trans
    (mul_le_mul_of_nonneg_right
      (sourceConstant_le_zeroConstant f)
      (pseriesTailFactor_nonneg m decayExponent))

/--
A nonnegative source constant bounded by the target constant gives the target
constant nonnegative, so source-shaped constructors need not ask for that field
again.
-/
theorem targetZeroConstant_nonneg_of_sourceConstant_le
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (f : SchwartzLineTestFunction) :
    0 <= zeroConstant f :=
  (sourceConstant_nonneg f).trans (sourceConstant_le_zeroConstant f)

/--
If the analytic tail estimate has a stronger decay exponent, it can feed a
package using any smaller exponent.  This is the common shape when the chosen
exponent is set by the zero-counting margin rather than by the sharpest decay
available for the extension.
-/
theorem tail_radialBound_natRadius_le_of_strongDecay
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    {decayExponent strongDecayExponent : Real}
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_strong :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (f : SchwartzLineTestFunction)
    (m : Nat) :
    radialBound f (m : Real) <=
      zeroConstant f *
        (1 / |(m : Real) + 1| ^ decayExponent) :=
  (tail_radialBound_natRadius_le_strong f m).trans
    (mul_le_mul_of_nonneg_left
      (pseriesTailFactor_le_of_decayExponent_le m hdecay_le_strong)
      (zeroConstant_nonneg f))

/--
If the analytic tail estimate uses a source-native leading constant and a
stronger decay exponent, it can feed a package whose target constant dominates
the source constant and whose exponent is weaker.
-/
theorem tail_radialBound_natRadius_le_of_sourceConstantStrongDecay
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    {decayExponent strongDecayExponent : Real}
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (f : SchwartzLineTestFunction)
    (m : Nat) :
    radialBound f (m : Real) <=
      zeroConstant f *
        (1 / |(m : Real) + 1| ^ decayExponent) :=
  (tail_radialBound_natRadius_le_source f m).trans
    (sourceConstant_mul_strongTailFactor_le_target sourceConstant zeroConstant
      sourceConstant_nonneg sourceConstant_le_zeroConstant
      hdecay_le_strong f m)

/--
Prefix bound specialized to cutoff `2`.  Future finite-prefix estimates only
need to supply the two shell values that can actually occur before the tail.
-/
noncomputable def cutoffTwoPrefixBound
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (f : SchwartzLineTestFunction)
    (n : Nat) : Real :=
  if n = 0 then prefixZero f else if n = 1 then prefixOne f else 0

/-- Nonnegativity of the cutoff-2 prefix bound follows from the two shell values. -/
theorem cutoffTwoPrefixBound_nonneg
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (prefixZero_nonneg : forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg : forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    0 <= cutoffTwoPrefixBound prefixZero prefixOne f n := by
  unfold cutoffTwoPrefixBound
  by_cases hn0 : n = 0
  · simpa [hn0] using prefixZero_nonneg f
  · by_cases hn1 : n = 1
    · simpa [hn0, hn1] using prefixOne_nonneg f
    · simp [hn0, hn1]

/--
For cutoff `2`, proving the finite-prefix radial estimate at shells `0` and
`1` proves the whole `n < 2` prefix obligation.
-/
theorem prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hn : n < 2) :
    radialBound f (closedBallZeroArgumentShellLowerBound n) <=
      cutoffTwoPrefixBound prefixZero prefixOne f n := by
  cases n with
  | zero =>
      simpa [cutoffTwoPrefixBound] using prefixZero_bound f
  | succ n =>
      cases n with
      | zero =>
          simpa [cutoffTwoPrefixBound] using prefixOne_bound f
      | succ n =>
          have htwo : 2 <= Nat.succ (Nat.succ n) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
          exact (not_lt_of_ge htwo hn).elim

/-- A source prefix bound dominated by the target prefix bound gives target nonnegativity. -/
theorem targetPrefix_nonneg_of_sourcePrefix_le
    (sourcePrefix targetPrefix : SchwartzLineTestFunction -> Real)
    (sourcePrefix_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefix f)
    (sourcePrefix_le_prefix :
      forall f : SchwartzLineTestFunction, sourcePrefix f <= targetPrefix f)
    (f : SchwartzLineTestFunction) :
    0 <= targetPrefix f :=
  (sourcePrefix_nonneg f).trans (sourcePrefix_le_prefix f)

/--
For cutoff `2`, source-native finite-prefix shell constants may be weakened to
the target prefix constants used by the p-series package.
-/
theorem prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound_of_sourceBounds
    (sourcePrefixZero sourcePrefixOne
      prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourcePrefixZero_le_prefixZero :
      forall f : SchwartzLineTestFunction, sourcePrefixZero f <= prefixZero f)
    (sourcePrefixOne_le_prefixOne :
      forall f : SchwartzLineTestFunction, sourcePrefixOne f <= prefixOne f)
    (prefixZero_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          sourcePrefixZero f)
    (prefixOne_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          sourcePrefixOne f)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hn : n < 2) :
    radialBound f (closedBallZeroArgumentShellLowerBound n) <=
      cutoffTwoPrefixBound prefixZero prefixOne f n :=
  prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound
    prefixZero prefixOne radialBound
    (fun f => (prefixZero_source_bound f).trans
      (sourcePrefixZero_le_prefixZero f))
    (fun f => (prefixOne_source_bound f).trans
      (sourcePrefixOne_le_prefixOne f))
    f n hn

/--
Automatic nonnegative prefix value for shell `0`: it is just the radial
majorant at the shell lower bound, clipped below by `0`.
-/
noncomputable def cutoffTwoMaxPrefixZero
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction) : Real :=
  max 0 (radialBound f (closedBallZeroArgumentShellLowerBound 0))

/--
Automatic nonnegative prefix value for shell `1`: it is just the radial
majorant at the shell lower bound, clipped below by `0`.
-/
noncomputable def cutoffTwoMaxPrefixOne
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction) : Real :=
  max 0 (radialBound f (closedBallZeroArgumentShellLowerBound 1))

/-- The automatic shell-`0` prefix value is nonnegative. -/
theorem cutoffTwoMaxPrefixZero_nonneg
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction) :
    0 <= cutoffTwoMaxPrefixZero radialBound f := by
  unfold cutoffTwoMaxPrefixZero
  exact le_max_left 0 (radialBound f (closedBallZeroArgumentShellLowerBound 0))

/-- The automatic shell-`1` prefix value is nonnegative. -/
theorem cutoffTwoMaxPrefixOne_nonneg
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction) :
    0 <= cutoffTwoMaxPrefixOne radialBound f := by
  unfold cutoffTwoMaxPrefixOne
  exact le_max_left 0 (radialBound f (closedBallZeroArgumentShellLowerBound 1))

/-- The radial shell-`0` value is bounded by its automatic prefix value. -/
theorem radialBound_lowerBound_zero_le_cutoffTwoMaxPrefixZero
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction) :
    radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
      cutoffTwoMaxPrefixZero radialBound f := by
  unfold cutoffTwoMaxPrefixZero
  exact le_max_right 0 (radialBound f (closedBallZeroArgumentShellLowerBound 0))

/-- The radial shell-`1` value is bounded by its automatic prefix value. -/
theorem radialBound_lowerBound_one_le_cutoffTwoMaxPrefixOne
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction) :
    radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
      cutoffTwoMaxPrefixOne radialBound f := by
  unfold cutoffTwoMaxPrefixOne
  exact le_max_right 0 (radialBound f (closedBallZeroArgumentShellLowerBound 1))

/--
For cutoff `2`, the automatic max-prefix values discharge the finite-prefix
radial estimate for both shells before the tail.
-/
theorem prefix_radialBound_lowerBound_le_cutoffTwoMaxPrefixBound
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction)
    (n : Nat)
    (hn : n < 2) :
    radialBound f (closedBallZeroArgumentShellLowerBound n) <=
      cutoffTwoPrefixBound
        (cutoffTwoMaxPrefixZero radialBound)
        (cutoffTwoMaxPrefixOne radialBound) f n :=
  prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound
    (cutoffTwoMaxPrefixZero radialBound)
    (cutoffTwoMaxPrefixOne radialBound)
    radialBound
    (radialBound_lowerBound_zero_le_cutoffTwoMaxPrefixZero radialBound)
    (radialBound_lowerBound_one_le_cutoffTwoMaxPrefixOne radialBound)
    f n hn

/--
Automatic nonnegative finite-prefix value for any shell: it is the radial
majorant at that shell lower bound, clipped below by `0`.
-/
noncomputable def automaticPrefixBound
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction)
    (n : Nat) : Real :=
  max 0 (radialBound f (closedBallZeroArgumentShellLowerBound n))

/-- The automatic finite-prefix value is nonnegative. -/
theorem automaticPrefixBound_nonneg
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    0 <= automaticPrefixBound radialBound f n := by
  unfold automaticPrefixBound
  exact le_max_left 0 (radialBound f (closedBallZeroArgumentShellLowerBound n))

/--
The radial value at a shell lower bound is bounded by its automatic
finite-prefix value.
-/
theorem radialBound_lowerBound_le_automaticPrefixBound
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    radialBound f (closedBallZeroArgumentShellLowerBound n) <=
      automaticPrefixBound radialBound f n := by
  unfold automaticPrefixBound
  exact le_max_right 0 (radialBound f (closedBallZeroArgumentShellLowerBound n))

/--
A concrete radial p-series majorant.  The clipped radius `max 1 r + 1` makes
the model antitone on all real radii, while agreeing with the natural
p-series scale up to a harmless strengthening on natural radii.
-/
noncomputable def clippedPSeriesRadialBound
    (sourceConstant : SchwartzLineTestFunction -> Real)
    (strongDecayExponent : Real)
    (f : SchwartzLineTestFunction)
    (r : Real) : Real :=
  sourceConstant f *
    (1 / (max (1 : Real) r + 1) ^ strongDecayExponent)

/-- The clipped p-series denominator is positive. -/
theorem clippedPSeriesRadius_pos (r : Real) :
    0 < max (1 : Real) r + 1 := by
  have hbase : (1 : Real) <= max (1 : Real) r := le_max_left 1 r
  linarith

/-- The clipped p-series denominator is monotone in the radius. -/
theorem clippedPSeriesRadius_monotone :
    Monotone (fun r : Real => max (1 : Real) r + 1) := by
  intro r s hrs
  simpa [add_comm] using
    add_le_add_right (max_le_max le_rfl hrs) (1 : Real)

/-- The clipped p-series radial bound is antitone in the radius. -/
theorem clippedPSeriesRadialBound_antitone
    (sourceConstant : SchwartzLineTestFunction -> Real)
    {strongDecayExponent : Real}
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (f : SchwartzLineTestFunction) :
    Antitone (clippedPSeriesRadialBound sourceConstant strongDecayExponent f) := by
  intro r s hrs
  unfold clippedPSeriesRadialBound
  have hbase_le :
      max (1 : Real) r + 1 <= max (1 : Real) s + 1 :=
    clippedPSeriesRadius_monotone hrs
  have hpow_le :
      (max (1 : Real) r + 1) ^ strongDecayExponent <=
        (max (1 : Real) s + 1) ^ strongDecayExponent :=
    Real.rpow_le_rpow (le_of_lt (clippedPSeriesRadius_pos r))
      hbase_le strongDecayExponent_nonneg
  exact
    mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le
        (Real.rpow_pos_of_pos (clippedPSeriesRadius_pos r)
          strongDecayExponent)
        hpow_le)
      (sourceConstant_nonneg f)

/--
On natural radii, the clipped radial p-series model is bounded by the standard
tail factor `1 / |m + 1|^q`.
-/
theorem clippedPSeriesRadialBound_natRadius_le_source
    (sourceConstant : SchwartzLineTestFunction -> Real)
    {strongDecayExponent : Real}
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (f : SchwartzLineTestFunction)
    (m : Nat) :
    clippedPSeriesRadialBound sourceConstant strongDecayExponent f (m : Real) <=
      sourceConstant f *
        (1 / |(m : Real) + 1| ^ strongDecayExponent) := by
  unfold clippedPSeriesRadialBound
  have hnat_nonneg : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
  have hbase_nonneg : 0 <= (m : Real) + 1 := by linarith
  have hbase_le :
      |(m : Real) + 1| <= max (1 : Real) (m : Real) + 1 := by
    rw [abs_of_nonneg hbase_nonneg]
    simpa [add_comm] using
      add_le_add_right (le_max_right (1 : Real) (m : Real)) (1 : Real)
  have hbase_pos : 0 < |(m : Real) + 1| :=
    zero_lt_one.trans_le (one_le_abs_natCast_add_one m)
  have hpow_le :
      |(m : Real) + 1| ^ strongDecayExponent <=
        (max (1 : Real) (m : Real) + 1) ^ strongDecayExponent :=
    Real.rpow_le_rpow (abs_nonneg ((m : Real) + 1)) hbase_le
      strongDecayExponent_nonneg
  exact
    mul_le_mul_of_nonneg_left
      (one_div_le_one_div_of_le
        (Real.rpow_pos_of_pos hbase_pos strongDecayExponent)
        hpow_le)
      (sourceConstant_nonneg f)

/--
The shifted denominator `r + 2` is a stronger p-series denominator than the
clipped denominator `max 1 r + 1` on nonnegative radii.
-/
theorem shiftedPSeriesFactor_le_clippedPSeriesFactor
    {r strongDecayExponent : Real}
    (hr_nonneg : 0 <= r)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent) :
    (1 / (r + 2) ^ strongDecayExponent) <=
      (1 / (max (1 : Real) r + 1) ^ strongDecayExponent) := by
  have hclipped_pos : 0 < max (1 : Real) r + 1 :=
    clippedPSeriesRadius_pos r
  have hclipped_le_shift : max (1 : Real) r + 1 <= r + 2 := by
    have hmax_le : max (1 : Real) r <= r + 1 := by
      exact max_le (by linarith) (by linarith)
    linarith
  have hpow_le :
      (max (1 : Real) r + 1) ^ strongDecayExponent <=
        (r + 2) ^ strongDecayExponent :=
    Real.rpow_le_rpow (le_of_lt hclipped_pos) hclipped_le_shift
      strongDecayExponent_nonneg
  exact
    one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos hclipped_pos strongDecayExponent)
      hpow_le

/--
A shifted-radius p-series radial estimate implies the clipped radial estimate
used by the automatic-prefix package.
-/
theorem shiftedPSeriesRadialBound_le_clippedPSeriesRadialBound
    (sourceConstant : SchwartzLineTestFunction -> Real)
    {strongDecayExponent r : Real}
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (hr_nonneg : 0 <= r)
    (f : SchwartzLineTestFunction) :
    sourceConstant f * (1 / (r + 2) ^ strongDecayExponent) <=
      clippedPSeriesRadialBound sourceConstant strongDecayExponent f r := by
  unfold clippedPSeriesRadialBound
  exact
    mul_le_mul_of_nonneg_left
      (shiftedPSeriesFactor_le_clippedPSeriesFactor hr_nonneg
        strongDecayExponent_nonneg)
      (sourceConstant_nonneg f)

/--
On nonnegative radii, the shifted p-series factor is bounded by the first
p-series term. This discharges the shell `0` prefix in the cutoff-1 route.
-/
theorem shiftedPSeriesFactor_le_one_of_nonneg_radius
    {r strongDecayExponent : Real}
    (hr_nonneg : 0 <= r)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent) :
    (1 / (r + 2) ^ strongDecayExponent) <= 1 := by
  have hbase_one : (1 : Real) <= r + 2 := by linarith
  have hpow_one :
      (1 : Real) <= (r + 2) ^ strongDecayExponent := by
    have hpow_le :
        (1 : Real) ^ strongDecayExponent <=
          (r + 2) ^ strongDecayExponent :=
      Real.rpow_le_rpow zero_le_one hbase_one strongDecayExponent_nonneg
    simpa using hpow_le
  simpa using one_div_le_one_div_of_le zero_lt_one hpow_one

/--
For successor closed-ball shells, the shifted denominator `r + 2` dominates the
cutoff-1 p-series tail denominator as soon as `r` is past the checked
Riemann-Weil zero-argument shell lower bound.
-/
theorem shiftedPSeriesFactor_le_tailFactor_of_succ_argumentShellLowerBound
    (m : Nat)
    {r strongDecayExponent : Real}
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (hlower :
      closedBallZeroArgumentShellLowerBound (m + 1) < r) :
    (1 / (r + 2) ^ strongDecayExponent) <=
      (1 / |(m : Real) + 1| ^ strongDecayExponent) := by
  unfold closedBallZeroArgumentShellLowerBound at hlower
  have hhalf : norm (1 / 2 : Complex) <= (1 : Real) :=
    norm_half_complex_le_one
  have hm_nonneg : (0 : Real) <= (m : Real) := Nat.cast_nonneg m
  have htail_nonneg : 0 <= (m : Real) + 1 := by linarith
  have htail_le : |(m : Real) + 1| <= r + 2 := by
    rw [abs_of_nonneg htail_nonneg]
    linarith
  have htail_pos : 0 < |(m : Real) + 1| :=
    zero_lt_one.trans_le (one_le_abs_natCast_add_one m)
  have hpow_le :
      |(m : Real) + 1| ^ strongDecayExponent <=
        (r + 2) ^ strongDecayExponent :=
    Real.rpow_le_rpow (abs_nonneg ((m : Real) + 1))
      htail_le strongDecayExponent_nonneg
  exact
    one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos htail_pos strongDecayExponent)
      hpow_le

end RiemannWeilAntitoneRadialPSeriesEnvelopeData

namespace SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData

/--
Cutoff-1 closed-ball zero data from a global shifted-radius exact-norm
estimate.  The shell `0` contribution is kept as the one-term prefix
`constant f`; every successor shell uses the checked Riemann-Weil
zero-argument lower bound to compare `‖z‖ + 2` with the cutoff-1 p-series
tail coordinate.

The remaining analytic inputs are exactly the shifted-radius decay theorem, a
cutoff-1 zero-counting estimate, and the p-series margin.
-/
noncomputable def ofClosedBallShiftedRadiusExactNormCutoffOneSelf
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 1)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData where
  exhaustion := closedBallZero
  system := system
  growthBound := SchwartzRiemannWeilExtensionGrowthBound.exactNorm system
  cutoff := 1
  prefixBound := fun f _ => constant f
  zeroConstant := constant
  decayExponent := fun _ => decayExponent
  zeroConstant_nonneg := constant_nonneg
  prefixBound_nonneg := fun f _ => constant_nonneg f
  pseriesBound_nonneg :=
    fun f n =>
      pseriesEnvelopeTerm_nonneg
        (zeroConstant := constant)
        (decayExponent := fun _ => decayExponent)
        constant_nonneg f n
  envelope_zeroArgument_le_eventualPSeries := by
    intro f rho
    let n := closedBallZero.zetaZeroFirstEntryIndex rho
    have hdecay :
        (SchwartzRiemannWeilExtensionGrowthBound.exactNorm system).envelope
          f (riemannWeilZeroArgument (rho : Complex)) <=
          constant f *
            (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                decayExponent) := by
      simpa [SchwartzRiemannWeilExtensionGrowthBound.exactNorm] using
        extension_norm_le_shiftedRadialBound f
          (riemannWeilZeroArgument (rho : Complex))
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
                decayExponent) <=
            (1 / |((n - 1 : Nat) : Real) + 1| ^ decayExponent) :=
        RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_tailFactor_of_succ_argumentShellLowerBound
          (n - 1) decayExponent_nonneg hlower
      simpa [n, hn] using
        mul_le_mul_of_nonneg_left hfactor (constant_nonneg f)
    · have hfactor :
          (1 /
              (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                decayExponent) <= 1 :=
        RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesFactor_le_one_of_nonneg_radius
          (norm_nonneg (riemannWeilZeroArgument (rho : Complex)))
          decayExponent_nonneg
      have hprefix :
          constant f *
              (1 /
                (norm (riemannWeilZeroArgument (rho : Complex)) + 2) ^
                  decayExponent) <=
            constant f :=
        (mul_le_mul_of_nonneg_left hfactor (constant_nonneg f)).trans_eq
          (mul_one (constant f))
      simpa [n, hn] using hprefix
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := fun _ => growth_add_one_lt_decay

end SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData

/--
Antitone radial p-series data with the checked shell-lower-bound estimate split
into finite-prefix and tail pieces.
-/
structure RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData where
  system : SchwartzRiemannWeilExtensionSystem
  growthBound : SchwartzRiemannWeilExtensionGrowthBound system
  cutoff : Nat
  prefixBound : SchwartzLineTestFunction -> Nat -> Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  radialBound : SchwartzLineTestFunction -> Real -> Real
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  prefixBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n
  envelope_le_radialBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
        radialBound f ‖riemannWeilZeroArgument (rho : Complex)‖
  radialBound_antitone :
    forall f : SchwartzLineTestFunction, Antitone (radialBound f)
  prefix_radialBound_lowerBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      n < cutoff ->
        radialBound f (closedBallZeroArgumentShellLowerBound n) <=
          prefixBound f n
  tail_radialBound_lowerBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      cutoff <= n ->
        radialBound f (closedBallZeroArgumentShellLowerBound n) <=
          zeroConstant f *
            (1 / |((n - cutoff : Nat) : Real) + 1| ^ decayExponent)
  counting :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero
  counting_cutoff_eq : counting.cutoff = cutoff
  growth_add_one_lt_decay :
    counting.growth + 1 < decayExponent

namespace RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData

/--
Constructor for split p-series data when the tail estimate is proved in the
natural post-cutoff coordinate `m`, i.e. on shells `m + cutoff`.
-/
noncomputable def ofTailCoordinateBounds
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < cutoff ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radialBound_lowerBound_le_tail :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (closedBallZeroArgumentShellLowerBound (m + cutoff)) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData where
  system := system
  growthBound := growthBound
  cutoff := cutoff
  prefixBound := prefixBound
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  radialBound := radialBound
  zeroConstant_nonneg := zeroConstant_nonneg
  prefixBound_nonneg := prefixBound_nonneg
  envelope_le_radialBound := envelope_le_radialBound
  radialBound_antitone := radialBound_antitone
  prefix_radialBound_lowerBound_le := prefix_radialBound_lowerBound_le
  tail_radialBound_lowerBound_le :=
    RiemannWeilAntitoneRadialPSeriesEnvelopeData.tail_radialBound_lowerBound_le_of_tailCoordinate
      cutoff zeroConstant decayExponent radialBound
      tail_radialBound_lowerBound_le_tail
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Constructor for split p-series data when the tail estimate is proved at the
plain radius `m`, and a separate shell-geometry lemma proves
`m <= lowerBound (m + cutoff)`.
-/
noncomputable def ofNatRadiusTailBounds
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < cutoff ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofTailCoordinateBounds system growthBound cutoff prefixBound zeroConstant
    decayExponent radialBound zeroConstant_nonneg prefixBound_nonneg
    envelope_le_radialBound radialBound_antitone
    prefix_radialBound_lowerBound_le
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.tailCoordinate_lowerBound_le_of_natRadius_tail
      cutoff zeroConstant decayExponent radialBound radialBound_antitone
      tail_radius_le_lowerBound tail_radialBound_natRadius_le)
    counting counting_cutoff_eq growth_add_one_lt_decay

/--
Constructor for split p-series data where the finite-prefix constants are
chosen automatically from the radial majorant at each shell lower bound.
-/
noncomputable def ofNatRadiusTailBoundsAutomaticPrefix
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBounds system growthBound cutoff
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.automaticPrefixBound
      radialBound)
    zeroConstant decayExponent radialBound zeroConstant_nonneg
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.automaticPrefixBound_nonneg
      radialBound)
    envelope_le_radialBound radialBound_antitone
    (fun f n _ =>
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.radialBound_lowerBound_le_automaticPrefixBound
        radialBound f n)
    tail_radius_le_lowerBound tail_radialBound_natRadius_le counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
Variant of `ofNatRadiusTailBounds` for source estimates with a stronger tail
decay exponent than the one chosen for the p-series/counting margin.
-/
noncomputable def ofNatRadiusTailBoundsOfStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < cutoff ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_strong :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBounds system growthBound cutoff prefixBound zeroConstant
    decayExponent radialBound zeroConstant_nonneg prefixBound_nonneg
    envelope_le_radialBound radialBound_antitone
    prefix_radialBound_lowerBound_le tail_radius_le_lowerBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.tail_radialBound_natRadius_le_of_strongDecay
      zeroConstant radialBound zeroConstant_nonneg hdecay_le_strong
      tail_radialBound_natRadius_le_strong)
    counting counting_cutoff_eq growth_add_one_lt_decay

/--
Variant of `ofNatRadiusTailBoundsAutomaticPrefix` for source estimates with a
stronger tail decay exponent than the one chosen for the p-series margin.
-/
noncomputable def ofNatRadiusTailBoundsAutomaticPrefixOfStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_strong :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsOfStrongDecay system growthBound cutoff
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.automaticPrefixBound
      radialBound)
    zeroConstant decayExponent strongDecayExponent radialBound
    zeroConstant_nonneg
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.automaticPrefixBound_nonneg
      radialBound)
    envelope_le_radialBound radialBound_antitone
    (fun f n _ =>
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.radialBound_lowerBound_le_automaticPrefixBound
        radialBound f n)
    tail_radius_le_lowerBound hdecay_le_strong
    tail_radialBound_natRadius_le_strong counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Variant of `ofNatRadiusTailBounds` for source estimates whose leading constant
and decay exponent are both source-native.  A source constant dominated by the
package constant, together with a stronger source exponent, is weakened to the
target tail bound automatically.
-/
noncomputable def ofNatRadiusTailBoundsOfSourceConstantStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < cutoff ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBounds system growthBound cutoff prefixBound zeroConstant
    decayExponent radialBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.targetZeroConstant_nonneg_of_sourceConstant_le
      sourceConstant zeroConstant sourceConstant_nonneg
      sourceConstant_le_zeroConstant)
    prefixBound_nonneg envelope_le_radialBound radialBound_antitone
    prefix_radialBound_lowerBound_le tail_radius_le_lowerBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.tail_radialBound_natRadius_le_of_sourceConstantStrongDecay
      sourceConstant zeroConstant radialBound sourceConstant_nonneg
      sourceConstant_le_zeroConstant hdecay_le_strong
      tail_radialBound_natRadius_le_source)
    counting counting_cutoff_eq growth_add_one_lt_decay

/--
Variant of `ofNatRadiusTailBoundsAutomaticPrefix` for source-native tail
constants and stronger source decay exponents.
-/
noncomputable def ofNatRadiusTailBoundsAutomaticPrefixOfSourceConstantStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsOfSourceConstantStrongDecay system growthBound cutoff
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.automaticPrefixBound
      radialBound)
    sourceConstant zeroConstant decayExponent strongDecayExponent radialBound
    sourceConstant_nonneg sourceConstant_le_zeroConstant
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.automaticPrefixBound_nonneg
      radialBound)
    envelope_le_radialBound radialBound_antitone
    (fun f n _ =>
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.radialBound_lowerBound_le_automaticPrefixBound
        radialBound f n)
    tail_radius_le_lowerBound hdecay_le_strong
    tail_radialBound_natRadius_le_source counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 specialization of `ofNatRadiusTailBounds`, using the checked
closed-ball shell geometry `m <= lowerBound (m + 2)`.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwo
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < 2 ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBounds system growthBound 2 prefixBound zeroConstant
    decayExponent radialBound zeroConstant_nonneg prefixBound_nonneg
    envelope_le_radialBound radialBound_antitone
    prefix_radialBound_lowerBound_le
    nat_le_closedBallZeroArgumentShellLowerBound_add_two
    tail_radialBound_natRadius_le counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 specialization where the source tail estimate has a stronger decay
exponent than the exponent used by the final p-series package.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoOfStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < 2 ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_strong :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsOfStrongDecay system growthBound 2 prefixBound
    zeroConstant decayExponent strongDecayExponent radialBound
    zeroConstant_nonneg prefixBound_nonneg envelope_le_radialBound
    radialBound_antitone prefix_radialBound_lowerBound_le
    nat_le_closedBallZeroArgumentShellLowerBound_add_two hdecay_le_strong
    tail_radialBound_natRadius_le_strong counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 source-constant/strong-decay specialization, using the checked
closed-ball shell geometry for the plain-radius tail comparison.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoOfSourceConstantStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixBound : SchwartzLineTestFunction -> Nat -> Real)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (prefixBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= prefixBound f n)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefix_radialBound_lowerBound_le :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        n < 2 ->
          radialBound f (closedBallZeroArgumentShellLowerBound n) <=
            prefixBound f n)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsOfSourceConstantStrongDecay system growthBound 2
    prefixBound sourceConstant zeroConstant decayExponent strongDecayExponent
    radialBound sourceConstant_nonneg sourceConstant_le_zeroConstant
    prefixBound_nonneg envelope_le_radialBound radialBound_antitone
    prefix_radialBound_lowerBound_le
    nat_le_closedBallZeroArgumentShellLowerBound_add_two hdecay_le_strong
    tail_radialBound_natRadius_le_source counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 specialization where the finite-prefix estimate is supplied only by
the two shell values before the tail.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoPrefixValues
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsCutoffTwo system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
      prefixZero prefixOne)
    zeroConstant decayExponent radialBound zeroConstant_nonneg
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound_nonneg
      prefixZero prefixOne prefixZero_nonneg prefixOne_nonneg)
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound
      prefixZero prefixOne radialBound prefixZero_bound prefixOne_bound)
    tail_radialBound_natRadius_le counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 prefix-value specialization for a source tail estimate with stronger
decay than the final p-series exponent.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_strong :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsCutoffTwoOfStrongDecay system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
      prefixZero prefixOne)
    zeroConstant decayExponent strongDecayExponent radialBound
    zeroConstant_nonneg
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound_nonneg
      prefixZero prefixOne prefixZero_nonneg prefixOne_nonneg)
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound
      prefixZero prefixOne radialBound prefixZero_bound prefixOne_bound)
    hdecay_le_strong tail_radialBound_natRadius_le_strong counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
Cutoff-2 prefix-value specialization for source-native constants and stronger
source exponents in the tail estimate.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceConstantStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsCutoffTwoOfSourceConstantStrongDecay system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
      prefixZero prefixOne)
    sourceConstant zeroConstant decayExponent strongDecayExponent radialBound
    sourceConstant_nonneg sourceConstant_le_zeroConstant
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound_nonneg
      prefixZero prefixOne prefixZero_nonneg prefixOne_nonneg)
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound
      prefixZero prefixOne radialBound prefixZero_bound prefixOne_bound)
    hdecay_le_strong tail_radialBound_natRadius_le_source counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
Cutoff-2 source-tail specialization with automatic finite-prefix constants.
The two prefix constants are chosen as `max 0` of the radial majorant at shells
`0` and `1`, so no separate finite-prefix estimates are needed.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoAutomaticPrefixOfSourceConstantStrongDecay
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceConstantStrongDecay
    system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixZero
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixOne
      radialBound)
    sourceConstant zeroConstant decayExponent strongDecayExponent radialBound
    sourceConstant_nonneg sourceConstant_le_zeroConstant
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixZero_nonneg
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoMaxPrefixOne_nonneg
      radialBound)
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.radialBound_lowerBound_zero_le_cutoffTwoMaxPrefixZero
      radialBound)
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.radialBound_lowerBound_one_le_cutoffTwoMaxPrefixOne
      radialBound)
    hdecay_le_strong tail_radialBound_natRadius_le_source counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
Cutoff-2 source-bound specialization for the fully source-shaped split radial
input: source constants for the two finite-prefix shells, a source leading
constant for the tail, and a stronger source decay exponent.  Each source
quantity is weakened to the corresponding package quantity by explicit
dominance hypotheses.
-/
noncomputable def ofNatRadiusTailBoundsCutoffTwoPrefixValuesOfSourceBounds
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourcePrefixZero sourcePrefixOne
      prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourcePrefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixZero f)
    (sourcePrefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourcePrefixOne f)
    (sourcePrefixZero_le_prefixZero :
      forall f : SchwartzLineTestFunction, sourcePrefixZero f <= prefixZero f)
    (sourcePrefixOne_le_prefixOne :
      forall f : SchwartzLineTestFunction, sourcePrefixOne f <= prefixOne f)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          sourcePrefixZero f)
    (prefixOne_source_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          sourcePrefixOne f)
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  ofNatRadiusTailBoundsCutoffTwoOfSourceConstantStrongDecay system growthBound
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
      prefixZero prefixOne)
    sourceConstant zeroConstant decayExponent strongDecayExponent radialBound
    sourceConstant_nonneg sourceConstant_le_zeroConstant
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound_nonneg
      prefixZero prefixOne
      (RiemannWeilAntitoneRadialPSeriesEnvelopeData.targetPrefix_nonneg_of_sourcePrefix_le
        sourcePrefixZero prefixZero sourcePrefixZero_nonneg
        sourcePrefixZero_le_prefixZero)
      (RiemannWeilAntitoneRadialPSeriesEnvelopeData.targetPrefix_nonneg_of_sourcePrefix_le
        sourcePrefixOne prefixOne sourcePrefixOne_nonneg
        sourcePrefixOne_le_prefixOne))
    envelope_le_radialBound radialBound_antitone
    (RiemannWeilAntitoneRadialPSeriesEnvelopeData.prefix_radialBound_lowerBound_le_cutoffTwoPrefixBound_of_sourceBounds
      sourcePrefixZero sourcePrefixOne prefixZero prefixOne radialBound
      sourcePrefixZero_le_prefixZero sourcePrefixOne_le_prefixOne
      prefixZero_source_bound prefixOne_source_bound)
    hdecay_le_strong tail_radialBound_natRadius_le_source counting
    counting_cutoff_eq growth_add_one_lt_decay

/-- The cutoff-2 prefix-values constructor has cutoff exactly `2`. -/
theorem ofNatRadiusTailBoundsCutoffTwoPrefixValues_cutoff
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    (ofNatRadiusTailBoundsCutoffTwoPrefixValues system growthBound
      prefixZero prefixOne zeroConstant decayExponent radialBound
      zeroConstant_nonneg prefixZero_nonneg prefixOne_nonneg
      envelope_le_radialBound radialBound_antitone prefixZero_bound
      prefixOne_bound tail_radialBound_natRadius_le counting
      counting_cutoff_eq growth_add_one_lt_decay).cutoff = 2 := by
  rfl

/-- The cutoff-2 prefix-values constructor uses exactly the two-value prefix bound. -/
theorem ofNatRadiusTailBoundsCutoffTwoPrefixValues_prefixBound
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (prefixZero prefixOne : SchwartzLineTestFunction -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (prefixZero_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixZero f)
    (prefixOne_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= prefixOne f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (prefixZero_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 0) <=
          prefixZero f)
    (prefixOne_bound :
      forall f : SchwartzLineTestFunction,
        radialBound f (closedBallZeroArgumentShellLowerBound 1) <=
          prefixOne f)
    (tail_radialBound_natRadius_le :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          zeroConstant f *
            (1 / |(m : Real) + 1| ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    (ofNatRadiusTailBoundsCutoffTwoPrefixValues system growthBound
      prefixZero prefixOne zeroConstant decayExponent radialBound
      zeroConstant_nonneg prefixZero_nonneg prefixOne_nonneg
      envelope_le_radialBound radialBound_antitone prefixZero_bound
      prefixOne_bound tail_radialBound_natRadius_le counting
      counting_cutoff_eq growth_add_one_lt_decay).prefixBound =
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.cutoffTwoPrefixBound
        prefixZero prefixOne := by
  rfl

/-- The split finite-prefix/tail estimates imply the original lower-bound field. -/
theorem radialBound_lowerBound_le_eventualPSeries
    (data : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    data.radialBound f (closedBallZeroArgumentShellLowerBound n) <=
      SchwartzRiemannWeilExtensionShellDecayEstimate.eventualConstantPSeriesShellBound
        data.cutoff data.prefixBound data.zeroConstant data.decayExponent f n :=
  RiemannWeilAntitoneRadialPSeriesEnvelopeData.lowerBound_le_eventualConstantPSeries_of_split
      data.cutoff data.prefixBound data.zeroConstant data.decayExponent
      data.radialBound data.prefix_radialBound_lowerBound_le
      data.tail_radialBound_lowerBound_le f n

/-- Convert split antitone radial data to the existing antitone radial package. -/
noncomputable def toAntitoneRadialPSeriesEnvelopeData
    (data : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData) :
    RiemannWeilAntitoneRadialPSeriesEnvelopeData where
  system := data.system
  growthBound := data.growthBound
  cutoff := data.cutoff
  prefixBound := data.prefixBound
  zeroConstant := data.zeroConstant
  decayExponent := data.decayExponent
  radialBound := data.radialBound
  zeroConstant_nonneg := data.zeroConstant_nonneg
  prefixBound_nonneg := data.prefixBound_nonneg
  envelope_le_radialBound := data.envelope_le_radialBound
  radialBound_antitone := data.radialBound_antitone
  radialBound_lowerBound_le_eventualPSeries :=
    data.radialBound_lowerBound_le_eventualPSeries
  counting := data.counting
  counting_cutoff_eq := data.counting_cutoff_eq
  growth_add_one_lt_decay := data.growth_add_one_lt_decay

/-- The split package gives eventual p-series zero data. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    (data : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  data.toAntitoneRadialPSeriesEnvelopeData.toEventualPSeriesEnvelopeZeroData

/-- The split package gives the induced zero side. -/
noncomputable def zeroSide
    (data : RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData) :
    SchwartzRiemannWeilZeroSide :=
  data.toEventualPSeriesEnvelopeZeroData.zeroSide

end RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData

/--
Analytic target for the automatic-prefix antitone radial p-series route.

The finite-prefix bounds are not fields: they are chosen automatically as
`max 0` of the radial majorant at each shell lower bound.  The remaining
analytic work is the radial envelope domination, radial antitonicity, a
plain-radius source-tail estimate, and zero counting with a compatible growth
margin.
-/
structure RiemannWeilAutomaticPrefixRadialPSeriesTarget where
  system : SchwartzRiemannWeilExtensionSystem
  growthBound : SchwartzRiemannWeilExtensionGrowthBound system
  cutoff : Nat
  sourceConstant : SchwartzLineTestFunction -> Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : Real
  strongDecayExponent : Real
  radialBound : SchwartzLineTestFunction -> Real -> Real
  sourceConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= sourceConstant f
  sourceConstant_le_zeroConstant :
    forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f
  envelope_le_radialBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
        radialBound f (norm (riemannWeilZeroArgument (rho : Complex)))
  radialBound_antitone :
    forall f : SchwartzLineTestFunction, Antitone (radialBound f)
  tail_radius_le_lowerBound :
    forall m : Nat,
      (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff)
  hdecay_le_strong : decayExponent <= strongDecayExponent
  tail_radialBound_natRadius_le_source :
    forall (f : SchwartzLineTestFunction) (m : Nat),
      radialBound f (m : Real) <=
        sourceConstant f *
          (1 / |(m : Real) + 1| ^ strongDecayExponent)
  counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero
  counting_cutoff_eq : counting.cutoff = cutoff
  growth_add_one_lt_decay : counting.growth + 1 < decayExponent

namespace RiemannWeilAutomaticPrefixRadialPSeriesTarget

/--
Build the checked split p-series package from the automatic-prefix radial
target.
-/
noncomputable def toSplitPSeriesEnvelopeData
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget) :
    RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData :=
  RiemannWeilAntitoneRadialSplitPSeriesEnvelopeData.ofNatRadiusTailBoundsAutomaticPrefixOfSourceConstantStrongDecay
    target.system target.growthBound target.cutoff target.sourceConstant
    target.zeroConstant target.decayExponent target.strongDecayExponent
    target.radialBound target.sourceConstant_nonneg
    target.sourceConstant_le_zeroConstant target.envelope_le_radialBound
    target.radialBound_antitone target.tail_radius_le_lowerBound
    target.hdecay_le_strong target.tail_radialBound_natRadius_le_source
    target.counting target.counting_cutoff_eq
    target.growth_add_one_lt_decay

/-- The generated split package uses the target cutoff. -/
theorem toSplitPSeriesEnvelopeData_cutoff
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget) :
    target.toSplitPSeriesEnvelopeData.cutoff = target.cutoff := by
  rfl

/-- The generated split package uses the automatic finite-prefix bound. -/
theorem toSplitPSeriesEnvelopeData_prefixBound
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget) :
    target.toSplitPSeriesEnvelopeData.prefixBound =
      RiemannWeilAntitoneRadialPSeriesEnvelopeData.automaticPrefixBound
        target.radialBound := by
  rfl

/-- The automatic-prefix radial target gives eventual p-series zero data. -/
noncomputable def toEventualPSeriesEnvelopeZeroData
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget) :
    SchwartzRiemannWeilEventualPSeriesEnvelopeZeroData :=
  target.toSplitPSeriesEnvelopeData.toEventualPSeriesEnvelopeZeroData

/-- The automatic-prefix radial target gives the induced zero side. -/
noncomputable def zeroSide
    (target : RiemannWeilAutomaticPrefixRadialPSeriesTarget) :
    SchwartzRiemannWeilZeroSide :=
  target.toEventualPSeriesEnvelopeZeroData.zeroSide

/--
Cutoff-2 constructor for the standard closed-ball route.  The checked shell
geometry supplies the plain-radius-to-shell comparison, leaving only the real
radial majorant and counting inputs.
-/
noncomputable def ofCutoffTwoClosedBallGeometry
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget where
  system := system
  growthBound := growthBound
  cutoff := 2
  sourceConstant := sourceConstant
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  strongDecayExponent := strongDecayExponent
  radialBound := radialBound
  sourceConstant_nonneg := sourceConstant_nonneg
  sourceConstant_le_zeroConstant := sourceConstant_le_zeroConstant
  envelope_le_radialBound := envelope_le_radialBound
  radialBound_antitone := radialBound_antitone
  tail_radius_le_lowerBound :=
    nat_le_closedBallZeroArgumentShellLowerBound_add_two
  hdecay_le_strong := hdecay_le_strong
  tail_radialBound_natRadius_le_source :=
    tail_radialBound_natRadius_le_source
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Constructor for the automatic-prefix route from cumulative-window zero
counting.  Analytic `N(T)` estimates usually bound cumulative windows first;
this adapter performs the checked conversion to first-entry shell counting at
the target boundary.
-/
noncomputable def ofCumulativeWindowCounting
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget where
  system := system
  growthBound := growthBound
  cutoff := cutoff
  sourceConstant := sourceConstant
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  strongDecayExponent := strongDecayExponent
  radialBound := radialBound
  sourceConstant_nonneg := sourceConstant_nonneg
  sourceConstant_le_zeroConstant := sourceConstant_le_zeroConstant
  envelope_le_radialBound := envelope_le_radialBound
  radialBound_antitone := radialBound_antitone
  tail_radius_le_lowerBound := tail_radius_le_lowerBound
  hdecay_le_strong := hdecay_le_strong
  tail_radialBound_natRadius_le_source :=
    tail_radialBound_natRadius_le_source
  counting := counting.toPolynomialZeroCountingEstimate
  counting_cutoff_eq := by
    simpa [SchwartzRiemannWeilCumulativeWindowCountingEstimate.toPolynomialZeroCountingEstimate]
      using counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Cutoff-2 closed-ball cumulative-window constructor.  This is the direct
automatic-prefix p-series target for a cumulative `N(T)`-style count plus the
checked closed-ball zero-argument shell geometry.
-/
noncomputable def ofCutoffTwoClosedBallGeometryOfCumulativeWindowCounting
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (radialBound : SchwartzLineTestFunction -> Real -> Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (envelope_le_radialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          radialBound f (norm (riemannWeilZeroArgument (rho : Complex))))
    (radialBound_antitone :
      forall f : SchwartzLineTestFunction, Antitone (radialBound f))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (tail_radialBound_natRadius_le_source :
      forall (f : SchwartzLineTestFunction) (m : Nat),
        radialBound f (m : Real) <=
          sourceConstant f *
            (1 / |(m : Real) + 1| ^ strongDecayExponent))
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofCumulativeWindowCounting system growthBound 2 sourceConstant zeroConstant
    decayExponent strongDecayExponent radialBound sourceConstant_nonneg
    sourceConstant_le_zeroConstant envelope_le_radialBound
    radialBound_antitone nat_le_closedBallZeroArgumentShellLowerBound_add_two
    hdecay_le_strong tail_radialBound_natRadius_le_source counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
Constructor using the concrete clipped p-series radial majorant.  Its
antitonicity and natural-radius tail estimate are checked here, so the
remaining radial analytic input is only the envelope domination by this
majorant.
-/
noncomputable def ofClippedPSeriesRadialMajorant
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (envelope_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            sourceConstant strongDecayExponent f
              (norm (riemannWeilZeroArgument (rho : Complex))))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget where
  system := system
  growthBound := growthBound
  cutoff := cutoff
  sourceConstant := sourceConstant
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  strongDecayExponent := strongDecayExponent
  radialBound :=
    RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
      sourceConstant strongDecayExponent
  sourceConstant_nonneg := sourceConstant_nonneg
  sourceConstant_le_zeroConstant := sourceConstant_le_zeroConstant
  envelope_le_radialBound := envelope_le_clippedRadialBound
  radialBound_antitone :=
    RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound_antitone
      sourceConstant sourceConstant_nonneg strongDecayExponent_nonneg
  tail_radius_le_lowerBound := tail_radius_le_lowerBound
  hdecay_le_strong := hdecay_le_strong
  tail_radialBound_natRadius_le_source :=
    RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound_natRadius_le_source
      sourceConstant sourceConstant_nonneg strongDecayExponent_nonneg
  counting := counting
  counting_cutoff_eq := counting_cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Cutoff-2 closed-ball constructor using the concrete clipped p-series radial
majorant.  The checked shell geometry supplies the plain-radius-to-shell
comparison automatically.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorant
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (envelope_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            sourceConstant strongDecayExponent f
              (norm (riemannWeilZeroArgument (rho : Complex))))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorant system growthBound 2 sourceConstant
    zeroConstant decayExponent strongDecayExponent sourceConstant_nonneg
    sourceConstant_le_zeroConstant strongDecayExponent_nonneg
    envelope_le_clippedRadialBound
    nat_le_closedBallZeroArgumentShellLowerBound_add_two hdecay_le_strong
    counting counting_cutoff_eq growth_add_one_lt_decay

/--
Exact-norm version of `ofClippedPSeriesRadialMajorant`.  This is the most
natural analytic input when the extension itself is proved to decay like the
clipped p-series radial majorant for every complex argument; Lean then uses the
exact norm envelope and specializes the bound to zeta-zero arguments.
-/
noncomputable def ofClippedPSeriesRadialMajorantExactNorm
    (system : SchwartzRiemannWeilExtensionSystem)
    (cutoff : Nat)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            sourceConstant strongDecayExponent f (norm z))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorant system
    (SchwartzRiemannWeilExtensionGrowthBound.exactNorm system) cutoff
    sourceConstant zeroConstant decayExponent strongDecayExponent
    sourceConstant_nonneg sourceConstant_le_zeroConstant
    strongDecayExponent_nonneg
    (fun f rho => by
      simpa [SchwartzRiemannWeilExtensionGrowthBound.exactNorm] using
        extension_norm_le_clippedRadialBound f
          (riemannWeilZeroArgument (rho : Complex)))
    tail_radius_le_lowerBound hdecay_le_strong counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 closed-ball exact-norm constructor for the clipped p-series radial
majorant.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNorm
    (system : SchwartzRiemannWeilExtensionSystem)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            sourceConstant strongDecayExponent f (norm z))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantExactNorm system 2 sourceConstant
    zeroConstant decayExponent strongDecayExponent sourceConstant_nonneg
    sourceConstant_le_zeroConstant strongDecayExponent_nonneg
    extension_norm_le_clippedRadialBound
    nat_le_closedBallZeroArgumentShellLowerBound_add_two hdecay_le_strong
    counting counting_cutoff_eq growth_add_one_lt_decay

/--
Exact-norm clipped constructor fed by the smoother shifted-radius estimate
`C_f / (‖z‖ + 2)^q`.  The shifted estimate is stronger than the clipped one on
complex norms, so the remaining analytic input can use the more standard
denominator.
-/
noncomputable def ofClippedPSeriesRadialMajorantExactNormOfShiftedRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (cutoff : Nat)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          sourceConstant f *
            (1 / (norm z + 2) ^ strongDecayExponent))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantExactNorm system cutoff sourceConstant
    zeroConstant decayExponent strongDecayExponent sourceConstant_nonneg
    sourceConstant_le_zeroConstant strongDecayExponent_nonneg
    (fun f z =>
      (extension_norm_le_shiftedRadialBound f z).trans
        (RiemannWeilAntitoneRadialPSeriesEnvelopeData.shiftedPSeriesRadialBound_le_clippedPSeriesRadialBound
          sourceConstant sourceConstant_nonneg strongDecayExponent_nonneg
          (norm_nonneg z) f))
    tail_radius_le_lowerBound hdecay_le_strong counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 closed-ball exact-norm clipped constructor fed by a shifted-radius
estimate `C_f / (‖z‖ + 2)^q`.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormOfShiftedRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (sourceConstant zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent strongDecayExponent : Real)
    (sourceConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= sourceConstant f)
    (sourceConstant_le_zeroConstant :
      forall f : SchwartzLineTestFunction, sourceConstant f <= zeroConstant f)
    (strongDecayExponent_nonneg : 0 <= strongDecayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          sourceConstant f *
            (1 / (norm z + 2) ^ strongDecayExponent))
    (hdecay_le_strong : decayExponent <= strongDecayExponent)
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantExactNormOfShiftedRadius system 2
    sourceConstant zeroConstant decayExponent strongDecayExponent
    sourceConstant_nonneg sourceConstant_le_zeroConstant
    strongDecayExponent_nonneg extension_norm_le_shiftedRadialBound
    nat_le_closedBallZeroArgumentShellLowerBound_add_two hdecay_le_strong
    counting counting_cutoff_eq growth_add_one_lt_decay

/--
Exact-norm clipped constructor when the same constant and exponent are used for
the source tail and final p-series package.
-/
noncomputable def ofClippedPSeriesRadialMajorantExactNormSelf
    (system : SchwartzRiemannWeilExtensionSystem)
    (cutoff : Nat)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            constant decayExponent f (norm z))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantExactNorm system cutoff constant constant
    decayExponent decayExponent constant_nonneg (fun _ => le_rfl)
    decayExponent_nonneg extension_norm_le_clippedRadialBound
    tail_radius_le_lowerBound le_rfl counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 closed-ball exact-norm clipped constructor with matching source and
package constants/exponents.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelf
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            constant decayExponent f (norm z))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantExactNormSelf system 2 constant
    decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_clippedRadialBound
    nat_le_closedBallZeroArgumentShellLowerBound_add_two counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
Exact-norm clipped self-constructor fed by a shifted-radius estimate
`C_f / (‖z‖ + 2)^q`.
-/
noncomputable def ofClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (cutoff : Nat)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantExactNormOfShiftedRadius system cutoff
    constant constant decayExponent decayExponent constant_nonneg
    (fun _ => le_rfl) decayExponent_nonneg
    extension_norm_le_shiftedRadialBound tail_radius_le_lowerBound le_rfl
    counting counting_cutoff_eq growth_add_one_lt_decay

/--
Cutoff-2 closed-ball exact-norm clipped self-constructor fed by a shifted-radius
estimate `C_f / (‖z‖ + 2)^q`.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius system 2
    constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    nat_le_closedBallZeroArgumentShellLowerBound_add_two counting
    counting_cutoff_eq growth_add_one_lt_decay

/--
Cutoff-2 closed-ball exact-norm shifted-radius self-constructor from
cumulative-window counting.  This is the cumulative `N(T)` version of the
preferred shifted-radius p-series target.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadiusOfCumulativeWindowCounting
    (system : SchwartzRiemannWeilExtensionSystem)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (extension_norm_le_shiftedRadialBound :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        norm (system.extension f z) <=
          constant f * (1 / (norm z + 2) ^ decayExponent))
    (counting :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofCutoffTwoClosedBallClippedPSeriesRadialMajorantExactNormSelfOfShiftedRadius
    system constant decayExponent constant_nonneg decayExponent_nonneg
    extension_norm_le_shiftedRadialBound
    counting.toPolynomialZeroCountingEstimate
    (by
      simpa [SchwartzRiemannWeilCumulativeWindowCountingEstimate.toPolynomialZeroCountingEstimate]
        using counting_cutoff_eq)
    growth_add_one_lt_decay

/--
Constructor using the clipped p-series radial majorant when the same constant
and exponent are used for the source tail and final p-series package.
-/
noncomputable def ofClippedPSeriesRadialMajorantSelf
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (cutoff : Nat)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (envelope_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            constant decayExponent f
              (norm (riemannWeilZeroArgument (rho : Complex))))
    (tail_radius_le_lowerBound :
      forall m : Nat,
        (m : Real) <= closedBallZeroArgumentShellLowerBound (m + cutoff))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = cutoff)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorant system growthBound cutoff constant constant
    decayExponent decayExponent constant_nonneg (fun _ => le_rfl)
    decayExponent_nonneg envelope_le_clippedRadialBound
    tail_radius_le_lowerBound le_rfl counting counting_cutoff_eq
    growth_add_one_lt_decay

/--
Cutoff-2 closed-ball constructor using the clipped p-series radial majorant
with the same constant and exponent on the source and package sides.
-/
noncomputable def ofCutoffTwoClosedBallClippedPSeriesRadialMajorantSelf
    (system : SchwartzRiemannWeilExtensionSystem)
    (growthBound : SchwartzRiemannWeilExtensionGrowthBound system)
    (constant : SchwartzLineTestFunction -> Real)
    (decayExponent : Real)
    (constant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= constant f)
    (decayExponent_nonneg : 0 <= decayExponent)
    (envelope_le_clippedRadialBound :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        growthBound.envelope f (riemannWeilZeroArgument (rho : Complex)) <=
          RiemannWeilAntitoneRadialPSeriesEnvelopeData.clippedPSeriesRadialBound
            constant decayExponent f
              (norm (riemannWeilZeroArgument (rho : Complex))))
    (counting :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero)
    (counting_cutoff_eq : counting.cutoff = 2)
    (growth_add_one_lt_decay :
      counting.growth + 1 < decayExponent) :
    RiemannWeilAutomaticPrefixRadialPSeriesTarget :=
  ofClippedPSeriesRadialMajorantSelf system growthBound 2 constant
    decayExponent constant_nonneg decayExponent_nonneg
    envelope_le_clippedRadialBound
    nat_le_closedBallZeroArgumentShellLowerBound_add_two counting
    counting_cutoff_eq growth_add_one_lt_decay

end RiemannWeilAutomaticPrefixRadialPSeriesTarget

end RiemannHypothesisProject
