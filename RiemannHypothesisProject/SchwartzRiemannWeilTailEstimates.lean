import RiemannHypothesisProject.SchwartzRiemannWeilWeight

/-!
# Separated Riemann-Weil tail estimates

This module separates the eventual polynomial tail estimate for the candidate
Riemann-Weil zero contribution into two independently reusable analytic inputs:

* a zero-counting estimate for first-entry shells of a compact exhaustion; and
* a test-function-dependent decay estimate for the complex zero contribution.

If the decay exponent beats the zero-counting growth exponent by more than one,
Lean recombines those two inputs into the existing checked
`SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant` interface. From
there all previously proved summability, zero-side, and compact-exhaustion
convergence machinery applies.
-/

namespace RiemannHypothesisProject

open Filter

/--
A polynomial zero-counting estimate for first-entry shells of a compact
exhaustion.

The field `shellCardBound` may include arbitrary finite-prefix behavior. The
eventual bound only starts after `cutoff`, where the shell cardinalities are
controlled by `shellCardConstant * |n + 1| ^ growth`.
-/
structure SchwartzRiemannWeilPolynomialZeroCountingEstimate
    (exhaustion : ComplexCompactExhaustion) where
  cutoff : Nat
  shellCardBound : Nat -> Real
  shellCardConstant : Real
  growth : Real
  shellCardConstant_nonneg : 0 <= shellCardConstant
  shellCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <= shellCardBound n
  tail_shellCardBound_le :
    forall n : Nat,
      shellCardBound (n + cutoff) <=
        shellCardConstant * |(n : Real) + 1| ^ growth

namespace SchwartzRiemannWeilPolynomialZeroCountingEstimate

/-- A first-entry shell is contained in its compact-exhaustion window. -/
theorem firstEntryShell_subset_window
    (exhaustion : ComplexCompactExhaustion) (n : Nat) :
    exhaustion.zetaZeroFirstEntryShell n ⊆
      exhaustion.zetaZeroSubtypeFinset n := by
  intro rho hrho
  exact ((exhaustion.mem_zetaZeroFirstEntryShell_iff n).mp hrho).1

/-- The first-entry shell cardinality is bounded by the cumulative window count. -/
theorem firstEntryShell_card_le_window_card
    (exhaustion : ComplexCompactExhaustion) (n : Nat) :
    ((exhaustion.zetaZeroFirstEntryShell n).card : Real) <=
      ((exhaustion.zetaZeroSubtypeFinset n).card : Real) := by
  exact_mod_cast
    Finset.card_le_card (firstEntryShell_subset_window exhaustion n)

/--
Build a polynomial zero-counting estimate using the exact shell cardinalities
as the shell-cardinality bound.
-/
noncomputable def ofExactShellCardPolynomialBound
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat)
    (shellCardConstant growth : Real)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_shellCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroFirstEntryShell (n + cutoff)).card : Real) <=
          shellCardConstant * |(n : Real) + 1| ^ growth) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion where
  cutoff := cutoff
  shellCardBound := fun n =>
    ((exhaustion.zetaZeroFirstEntryShell n).card : Real)
  shellCardConstant := shellCardConstant
  growth := growth
  shellCardConstant_nonneg := shellCardConstant_nonneg
  shellCard_le := fun _n => le_rfl
  tail_shellCardBound_le := tail_shellCard_le

/--
Build a polynomial zero-counting estimate from a uniform tail bound on shell
cardinalities. This is the growth-zero special case.
-/
noncomputable def ofUniformTailShellCardBound
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat)
    (shellCardConstant : Real)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_shellCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroFirstEntryShell (n + cutoff)).card : Real) <=
          shellCardConstant) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion :=
  ofExactShellCardPolynomialBound exhaustion cutoff shellCardConstant 0
    shellCardConstant_nonneg <| fun n => by
      simpa using tail_shellCard_le n

/--
Build a polynomial zero-counting estimate from a polynomial bound on cumulative
compact-window zero counts.  Since each first-entry shell is contained in its
window, this is often the most natural analytic zero-counting input.
-/
noncomputable def ofWindowCardPolynomialBound
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat)
    (shellCardConstant growth : Real)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          shellCardConstant * |(n : Real) + 1| ^ growth) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion :=
  ofExactShellCardPolynomialBound exhaustion cutoff shellCardConstant growth
    shellCardConstant_nonneg <| fun n => by
      exact le_trans
        (firstEntryShell_card_le_window_card exhaustion (n + cutoff))
        (tail_windowCard_le n)

/--
Build a polynomial zero-counting estimate from a uniform tail bound on
cumulative compact-window zero counts. This is the growth-zero cumulative
window special case.
-/
noncomputable def ofUniformTailWindowCardBound
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat)
    (shellCardConstant : Real)
    (shellCardConstant_nonneg : 0 <= shellCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          shellCardConstant) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion :=
  ofWindowCardPolynomialBound exhaustion cutoff shellCardConstant 0
    shellCardConstant_nonneg <| fun n => by
      simpa using tail_windowCard_le n

/--
The natural polynomial tail factor is monotone along successor indices when
the growth exponent is nonnegative.
-/
theorem polynomialTailFactor_le_successor
    {growth : Real}
    (growth_nonneg : 0 <= growth)
    (n : Nat) :
    |(n : Real) + 1| ^ growth <=
      |((n + 1 : Nat) : Real) + 1| ^ growth := by
  have hn_nonneg : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  have hleft_nonneg : 0 <= (n : Real) + 1 := by linarith
  have hright_nonneg : 0 <= ((n + 1 : Nat) : Real) + 1 := by
    have hsucc_nonneg : (0 : Real) <= ((n + 1 : Nat) : Real) :=
      Nat.cast_nonneg (n + 1)
    linarith
  have hbase_le :
      |(n : Real) + 1| <= |((n + 1 : Nat) : Real) + 1| := by
    rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
    have hcast : ((n + 1 : Nat) : Real) = (n : Real) + 1 := by
      norm_num
    linarith
  exact
    Real.rpow_le_rpow (abs_nonneg ((n : Real) + 1)) hbase_le
      growth_nonneg

/--
Lower a cutoff-2 first-entry shell counting estimate to cutoff `1`.

The new estimate reuses the old shell-cardinality bound.  The only extra
finite-prefix information needed is a bound for shell `1`; from shell `2`
onward, the old cutoff-2 tail bound applies and monotonicity of the polynomial
tail factor lets the new tail use the successor coordinate.
-/
noncomputable def lowerCutoffTwoToOne
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (cutoff_eq_two : estimate.cutoff = 2)
    (newShellCardConstant : Real)
    (newShellCardConstant_nonneg : 0 <= newShellCardConstant)
    (oldConstant_le_new :
      estimate.shellCardConstant <= newShellCardConstant)
    (growth_nonneg : 0 <= estimate.growth)
    (shell_one_le :
      estimate.shellCardBound 1 <= newShellCardConstant) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion where
  cutoff := 1
  shellCardBound := estimate.shellCardBound
  shellCardConstant := newShellCardConstant
  growth := estimate.growth
  shellCardConstant_nonneg := newShellCardConstant_nonneg
  shellCard_le := estimate.shellCard_le
  tail_shellCardBound_le := by
    intro n
    cases n with
    | zero =>
        simpa using shell_one_le
    | succ k =>
        have hold :
            estimate.shellCardBound (k + estimate.cutoff) <=
              estimate.shellCardConstant *
                |(k : Real) + 1| ^ estimate.growth :=
          estimate.tail_shellCardBound_le k
        have hold' :
            estimate.shellCardBound ((k + 1) + 1) <=
              estimate.shellCardConstant *
                |(k : Real) + 1| ^ estimate.growth := by
          simpa [cutoff_eq_two, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hold
        have hfactor_nonneg :
            0 <= |(k : Real) + 1| ^ estimate.growth :=
          Real.rpow_nonneg (abs_nonneg ((k : Real) + 1)) estimate.growth
        have hconst :
            estimate.shellCardConstant *
                |(k : Real) + 1| ^ estimate.growth <=
              newShellCardConstant *
                |(k : Real) + 1| ^ estimate.growth :=
          mul_le_mul_of_nonneg_right oldConstant_le_new hfactor_nonneg
        have hfactor :
            |(k : Real) + 1| ^ estimate.growth <=
              |((k + 1 : Nat) : Real) + 1| ^ estimate.growth :=
          polynomialTailFactor_le_successor growth_nonneg k
        have hsucc :
            newShellCardConstant *
                |(k : Real) + 1| ^ estimate.growth <=
              newShellCardConstant *
                |((k + 1 : Nat) : Real) + 1| ^ estimate.growth :=
          mul_le_mul_of_nonneg_left hfactor newShellCardConstant_nonneg
        exact hold'.trans (hconst.trans hsucc)

end SchwartzRiemannWeilPolynomialZeroCountingEstimate

/--
A polynomial cumulative zero-counting estimate for compact exhaustion windows.

This is the form closest to many analytic zero-counting statements: instead of
bounding first-entry shells directly, it bounds the total number of zeta zeroes
in each compact window.  The conversion to first-entry shell counting is
checked below using the containment of each shell in its window.
-/
structure SchwartzRiemannWeilCumulativeWindowCountingEstimate
    (exhaustion : ComplexCompactExhaustion) where
  cutoff : Nat
  windowCardBound : Nat -> Real
  windowCardConstant : Real
  growth : Real
  windowCardConstant_nonneg : 0 <= windowCardConstant
  windowCard_le :
    forall n : Nat,
      ((exhaustion.zetaZeroSubtypeFinset n).card : Real) <= windowCardBound n
  tail_windowCardBound_le :
    forall n : Nat,
      windowCardBound (n + cutoff) <=
        windowCardConstant * |(n : Real) + 1| ^ growth

namespace SchwartzRiemannWeilCumulativeWindowCountingEstimate

/-- Build a cumulative estimate using exact compact-window cardinalities. -/
noncomputable def ofExactWindowCardPolynomialBound
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat)
    (windowCardConstant growth : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          windowCardConstant * |(n : Real) + 1| ^ growth) :
    SchwartzRiemannWeilCumulativeWindowCountingEstimate exhaustion where
  cutoff := cutoff
  windowCardBound := fun n =>
    ((exhaustion.zetaZeroSubtypeFinset n).card : Real)
  windowCardConstant := windowCardConstant
  growth := growth
  windowCardConstant_nonneg := windowCardConstant_nonneg
  windowCard_le := fun _n => le_rfl
  tail_windowCardBound_le := tail_windowCard_le

/--
Build a cumulative estimate from a uniform tail bound on compact-window zero
counts. This is the growth-zero cumulative-window special case.
-/
noncomputable def ofUniformTailWindowCardBound
    (exhaustion : ComplexCompactExhaustion)
    (cutoff : Nat)
    (windowCardConstant : Real)
    (windowCardConstant_nonneg : 0 <= windowCardConstant)
    (tail_windowCard_le :
      forall n : Nat,
        ((exhaustion.zetaZeroSubtypeFinset (n + cutoff)).card : Real) <=
          windowCardConstant) :
    SchwartzRiemannWeilCumulativeWindowCountingEstimate exhaustion :=
  ofExactWindowCardPolynomialBound exhaustion cutoff windowCardConstant 0
    windowCardConstant_nonneg <| fun n => by
      simpa using tail_windowCard_le n

/--
Convert cumulative compact-window counting into first-entry shell counting.
-/
noncomputable def toPolynomialZeroCountingEstimate
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate exhaustion) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion where
  cutoff := estimate.cutoff
  shellCardBound := estimate.windowCardBound
  shellCardConstant := estimate.windowCardConstant
  growth := estimate.growth
  shellCardConstant_nonneg := estimate.windowCardConstant_nonneg
  shellCard_le := fun n =>
    le_trans
      (SchwartzRiemannWeilPolynomialZeroCountingEstimate.firstEntryShell_card_le_window_card
        exhaustion n)
      (estimate.windowCard_le n)
  tail_shellCardBound_le := estimate.tail_windowCardBound_le

/--
Lower a cutoff-2 cumulative-window counting estimate to cutoff `1`.

This is the cumulative-window analogue of
`SchwartzRiemannWeilPolynomialZeroCountingEstimate.lowerCutoffTwoToOne`.
It is useful when an analytic `N(T)` theorem naturally supplies cumulative
window bounds rather than first-entry shell bounds.  The only new finite
input is the bound at window `1`; from window `2` onward, the old cutoff-2
tail applies and the polynomial tail factor is monotone.
-/
noncomputable def lowerCutoffTwoToOne
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilCumulativeWindowCountingEstimate exhaustion)
    (cutoff_eq_two : estimate.cutoff = 2)
    (newWindowCardConstant : Real)
    (newWindowCardConstant_nonneg : 0 <= newWindowCardConstant)
    (oldConstant_le_new :
      estimate.windowCardConstant <= newWindowCardConstant)
    (growth_nonneg : 0 <= estimate.growth)
    (window_one_le :
      estimate.windowCardBound 1 <= newWindowCardConstant) :
    SchwartzRiemannWeilCumulativeWindowCountingEstimate exhaustion where
  cutoff := 1
  windowCardBound := estimate.windowCardBound
  windowCardConstant := newWindowCardConstant
  growth := estimate.growth
  windowCardConstant_nonneg := newWindowCardConstant_nonneg
  windowCard_le := estimate.windowCard_le
  tail_windowCardBound_le := by
    intro n
    cases n with
    | zero =>
        simpa using window_one_le
    | succ k =>
        have hold :
            estimate.windowCardBound (k + estimate.cutoff) <=
              estimate.windowCardConstant *
                |(k : Real) + 1| ^ estimate.growth :=
          estimate.tail_windowCardBound_le k
        have hold' :
            estimate.windowCardBound ((k + 1) + 1) <=
              estimate.windowCardConstant *
                |(k : Real) + 1| ^ estimate.growth := by
          simpa [cutoff_eq_two, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hold
        have hfactor_nonneg :
            0 <= |(k : Real) + 1| ^ estimate.growth :=
          Real.rpow_nonneg (abs_nonneg ((k : Real) + 1)) estimate.growth
        have hconst :
            estimate.windowCardConstant *
                |(k : Real) + 1| ^ estimate.growth <=
              newWindowCardConstant *
                |(k : Real) + 1| ^ estimate.growth :=
          mul_le_mul_of_nonneg_right oldConstant_le_new hfactor_nonneg
        have hfactor :
            |(k : Real) + 1| ^ estimate.growth <=
              |((k + 1 : Nat) : Real) + 1| ^ estimate.growth :=
          SchwartzRiemannWeilPolynomialZeroCountingEstimate.polynomialTailFactor_le_successor
            growth_nonneg k
        have hsucc :
            newWindowCardConstant *
                |(k : Real) + 1| ^ estimate.growth <=
              newWindowCardConstant *
                |((k + 1 : Nat) : Real) + 1| ^ estimate.growth :=
          mul_le_mul_of_nonneg_left hfactor newWindowCardConstant_nonneg
        exact hold'.trans (hconst.trans hsucc)

end SchwartzRiemannWeilCumulativeWindowCountingEstimate

/--
A polynomial decay estimate for the complex zero contribution on first-entry
shells.

For each Schwartz test function, `shellBound f n` bounds the norm of the
complex zero contribution for zeroes whose first compact-exhaustion entry index
is `n`. After `cutoff`, those bounds decay like a shifted p-series with
test-function-dependent constant and exponent.
-/
structure SchwartzRiemannWeilPolynomialZeroDecayEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  cutoff : Nat
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : SchwartzLineTestFunction -> Real
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)
  norm_zeroValue_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (system.zeroValue f rho) <=
        shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilPolynomialZeroDecayEstimate

/-- A zero-value p-series term is nonnegative when its leading constant is. -/
theorem pseriesZeroValueTerm_nonneg
    {zeroConstant decayExponent : SchwartzLineTestFunction -> Real}
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    0 <=
      zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f) :=
  mul_nonneg (zeroConstant_nonneg f)
    (one_div_nonneg.mpr
      (Real.rpow_nonneg (abs_nonneg ((n : Real) + 1))
        (decayExponent f)))

/--
Build a zero-decay estimate from a direct global p-series bound on the zero
contribution at each first-entry shell index. This is the cutoff-zero case.
-/
noncomputable def ofGlobalPSeriesZeroValueBound
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (pseriesBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= zeroConstant f *
          (1 / |(n : Real) + 1| ^ decayExponent f))
    (norm_zeroValue_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (system.zeroValue f rho) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f)) :
    SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system where
  cutoff := 0
  shellBound := fun f n =>
    zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  zeroConstant_nonneg := zeroConstant_nonneg
  shellBound_nonneg := pseriesBound_nonneg
  tail_shellBound_le := fun _f _n => le_rfl
  norm_zeroValue_le_shellBound := norm_zeroValue_le_pseries

/--
Build a zero-decay estimate from a direct global p-series bound, deriving
p-series nonnegativity from `zeroConstant_nonneg`.
-/
noncomputable def ofGlobalPSeriesZeroValueBoundOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (norm_zeroValue_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (system.zeroValue f rho) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f)) :
    SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system :=
  ofGlobalPSeriesZeroValueBound zeroConstant decayExponent
    zeroConstant_nonneg
    (fun f n => pseriesZeroValueTerm_nonneg zeroConstant_nonneg f n)
    norm_zeroValue_le_pseries

end SchwartzRiemannWeilPolynomialZeroDecayEstimate

/--
Separated polynomial count-and-decay data.

This is the practical target for analytic work: prove zero counting once, prove
Schwartz-decay estimates separately, check that both estimates use the same
eventual cutoff, and show the decay exponent leaves more than one power after
subtracting the counting growth.
-/
structure SchwartzRiemannWeilSeparatedPolynomialDecayEstimate
    (exhaustion : ComplexCompactExhaustion)
    (system : SchwartzRiemannWeilExtensionSystem) where
  counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion
  decay : SchwartzRiemannWeilPolynomialZeroDecayEstimate exhaustion system
  cutoff_eq : counting.cutoff = decay.cutoff
  growth_add_one_lt_decay :
    forall f : SchwartzLineTestFunction,
      counting.growth + 1 < decay.decayExponent f

namespace SchwartzRiemannWeilSeparatedPolynomialDecayEstimate

/--
Separated polynomial zero-counting and zero-decay estimates produce the
combined decay-margin tail majorant.
-/
noncomputable def toEventualPolynomialCardDecayTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilEventualPolynomialCardDecayTailMajorant
      exhaustion system where
  cutoff := estimate.counting.cutoff
  shellCardBound := estimate.counting.shellCardBound
  shellBound := estimate.decay.shellBound
  shellCardConstant := estimate.counting.shellCardConstant
  growth := estimate.counting.growth
  zeroConstant := estimate.decay.zeroConstant
  decayExponent := estimate.decay.decayExponent
  shellCardConstant_nonneg := estimate.counting.shellCardConstant_nonneg
  zeroConstant_nonneg := estimate.decay.zeroConstant_nonneg
  growth_add_one_lt_decay := estimate.growth_add_one_lt_decay
  shellBound_nonneg := estimate.decay.shellBound_nonneg
  shellCard_le := estimate.counting.shellCard_le
  tail_shellCardBound_le := estimate.counting.tail_shellCardBound_le
  tail_shellBound_le := fun f n => by
    simpa [estimate.cutoff_eq] using estimate.decay.tail_shellBound_le f n
  norm_zeroValue_le_shellBound := estimate.decay.norm_zeroValue_le_shellBound

/-- Separated polynomial estimates produce the p-series tail certificate. -/
noncomputable def toEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilEventualPSeriesTailMajorant exhaustion system :=
  estimate.toEventualPolynomialCardDecayTailMajorant.toEventualPSeriesTailMajorant

/-- Separated polynomial estimates produce the summable-tail certificate. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilEventualSummableTailMajorant exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toEventualSummableTailMajorant

/-- Separated polynomial estimates produce the named shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilFirstEntryShellEstimate exhaustion system :=
  estimate.toEventualPSeriesTailMajorant.toFirstEntryShellEstimate

/-- Separated polynomial estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilFiniteShellMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toFiniteShellMajorant

/-- Separated polynomial estimates induce the norm-majorant interface. -/
noncomputable def toNormMajorant
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilNormMajorant system :=
  estimate.toEventualPSeriesTailMajorant.toNormMajorant

/-- Separated polynomial estimates make all shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.counting.shellCardBound n * estimate.decay.shellBound f n) := by
  simpa [toEventualPolynomialCardDecayTailMajorant] using
    estimate.toEventualPolynomialCardDecayTailMajorant.summable_boundTotal f

/-- Separated polynomial estimates make the complex zero-value norms summable. -/
theorem summable_norm_zeroValue
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (system.zeroValue f rho)) := by
  simpa [toEventualPolynomialCardDecayTailMajorant] using
    estimate.toEventualPolynomialCardDecayTailMajorant.summable_norm_zeroValue f

/-- Separated polynomial estimates give absolute convergence. -/
noncomputable def toAbsoluteConvergence
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilAbsoluteConvergence system :=
  estimate.toEventualPSeriesTailMajorant.toAbsoluteConvergence

/-- Separated polynomial estimates give real-weight summability. -/
noncomputable def toWeightSummability
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilWeightSummability system :=
  estimate.toEventualPSeriesTailMajorant.toWeightSummability

/-- Separated polynomial estimates make the extension-induced weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (f : SchwartzLineTestFunction) :
    Summable (system.weight f) := by
  simpa [toEventualPolynomialCardDecayTailMajorant] using
    estimate.toEventualPolynomialCardDecayTailMajorant.summable_weight f

/-- Separated polynomial estimates turn the candidate weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toWeightSummability.toZeroSide

/-- The zero side induced by separated polynomial estimates has the candidate weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = system.weight f rho :=
  rfl

/-- Compact-exhaustion sums for separated polynomial estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

/--
Separated polynomial estimates whose zero side is identified with a formula
residual side have compact-window sums converging to that residual side.
-/
theorem tendsto_windowZeroSide_formulaResidualSide
    {exhaustion : ComplexCompactExhaustion}
    {system : SchwartzRiemannWeilExtensionSystem}
    (estimate :
      SchwartzRiemannWeilSeparatedPolynomialDecayEstimate exhaustion system)
    (formulaResidualSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        estimate.toZeroSide.zeroSide f = formulaResidualSide f)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (formulaResidualSide f)) := by
  rw [← explicitFormula f]
  exact estimate.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilSeparatedPolynomialDecayEstimate

/--
A polynomial decay estimate for a directly supplied real-valued zero-side
weight on first-entry shells.

This is the abstract analogue of `SchwartzRiemannWeilPolynomialZeroDecayEstimate`.
It keeps the restricted-source p-series route independent of a global
`SchwartzRiemannWeilExtensionSystem`.
-/
structure SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate
    (exhaustion : ComplexCompactExhaustion) where
  weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real
  cutoff : Nat
  shellBound : SchwartzLineTestFunction -> Nat -> Real
  zeroConstant : SchwartzLineTestFunction -> Real
  decayExponent : SchwartzLineTestFunction -> Real
  zeroConstant_nonneg :
    forall f : SchwartzLineTestFunction, 0 <= zeroConstant f
  shellBound_nonneg :
    forall (f : SchwartzLineTestFunction) (n : Nat), 0 <= shellBound f n
  tail_shellBound_le :
    forall (f : SchwartzLineTestFunction) (n : Nat),
      shellBound f (n + cutoff) <=
        zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)
  norm_weight_le_shellBound :
    forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
      norm (weight f rho) <= shellBound f (exhaustion.zetaZeroFirstEntryIndex rho)

namespace SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate

/-- A direct-weight p-series term is nonnegative when its leading constant is. -/
theorem pseriesWeightTerm_nonneg
    {zeroConstant decayExponent : SchwartzLineTestFunction -> Real}
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (f : SchwartzLineTestFunction)
    (n : Nat) :
    0 <=
      zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f) :=
  mul_nonneg (zeroConstant_nonneg f)
    (one_div_nonneg.mpr
      (Real.rpow_nonneg (abs_nonneg ((n : Real) + 1))
        (decayExponent f)))

/--
Build an abstract zero-decay estimate from a direct global p-series bound on the
supplied zero-side weight. This is the cutoff-zero case.
-/
noncomputable def ofGlobalPSeriesWeightBound
    {exhaustion : ComplexCompactExhaustion}
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (pseriesBound_nonneg :
      forall (f : SchwartzLineTestFunction) (n : Nat),
        0 <= zeroConstant f *
          (1 / |(n : Real) + 1| ^ decayExponent f))
    (norm_weight_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f)) :
    SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate exhaustion where
  weight := weight
  cutoff := 0
  shellBound := fun f n =>
    zeroConstant f * (1 / |(n : Real) + 1| ^ decayExponent f)
  zeroConstant := zeroConstant
  decayExponent := decayExponent
  zeroConstant_nonneg := zeroConstant_nonneg
  shellBound_nonneg := pseriesBound_nonneg
  tail_shellBound_le := fun _f _n => le_rfl
  norm_weight_le_shellBound := norm_weight_le_pseries

/--
Build an abstract zero-decay estimate from a direct global p-series bound,
deriving p-series nonnegativity from `zeroConstant_nonneg`.
-/
noncomputable def ofGlobalPSeriesWeightBoundOfNonnegConstant
    {exhaustion : ComplexCompactExhaustion}
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (norm_weight_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f)) :
    SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate exhaustion :=
  ofGlobalPSeriesWeightBound weight zeroConstant decayExponent
    zeroConstant_nonneg
    (fun f n => pseriesWeightTerm_nonneg zeroConstant_nonneg f n)
    norm_weight_le_pseries

end SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate

/--
Separated polynomial count-and-decay data for a directly supplied abstract
zero-side weight.

This is the practical direct-weight p-series target: prove zero counting once,
prove real-valued shell decay for the intended weight, check both estimates use
the same eventual cutoff, and show the decay exponent beats the counting growth
by more than one.
-/
structure SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate
    (exhaustion : ComplexCompactExhaustion) where
  counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion
  decay : SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate exhaustion
  cutoff_eq : counting.cutoff = decay.cutoff
  growth_add_one_lt_decay :
    forall f : SchwartzLineTestFunction,
      counting.growth + 1 < decay.decayExponent f

namespace SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate

/-- Bundle abstract zero-counting and zero-decay estimates into a separated estimate. -/
def ofCountingAndDecay
    {exhaustion : ComplexCompactExhaustion}
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (decay : SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate exhaustion)
    (cutoff_eq : counting.cutoff = decay.cutoff)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decay.decayExponent f) :
    SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion where
  counting := counting
  decay := decay
  cutoff_eq := cutoff_eq
  growth_add_one_lt_decay := growth_add_one_lt_decay

/--
Build the direct separated target from packaged counting and a cutoff-zero
global p-series weight bound, deriving p-series nonnegativity automatically.
-/
noncomputable def ofCountingAndGlobalPSeriesWeightBound
    {exhaustion : ComplexCompactExhaustion}
    (weight : SchwartzLineTestFunction -> ZetaZeroSubtype -> Real)
    (zeroConstant : SchwartzLineTestFunction -> Real)
    (decayExponent : SchwartzLineTestFunction -> Real)
    (zeroConstant_nonneg :
      forall f : SchwartzLineTestFunction, 0 <= zeroConstant f)
    (norm_weight_le_pseries :
      forall (f : SchwartzLineTestFunction) (rho : ZetaZeroSubtype),
        norm (weight f rho) <=
          zeroConstant f *
            (1 /
              |(exhaustion.zetaZeroFirstEntryIndex rho : Real) + 1| ^
                decayExponent f))
    (counting : SchwartzRiemannWeilPolynomialZeroCountingEstimate exhaustion)
    (counting_cutoff_eq_zero : counting.cutoff = 0)
    (growth_add_one_lt_decay :
      forall f : SchwartzLineTestFunction,
        counting.growth + 1 < decayExponent f) :
    SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion := by
  let decay :
      SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate exhaustion :=
    SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate.ofGlobalPSeriesWeightBoundOfNonnegConstant
      weight zeroConstant decayExponent zeroConstant_nonneg
      norm_weight_le_pseries
  exact ofCountingAndDecay counting decay
    (by
      simpa [decay,
        SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate.ofGlobalPSeriesWeightBoundOfNonnegConstant,
        SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate.ofGlobalPSeriesWeightBound]
        using counting_cutoff_eq_zero)
    (fun f => by
      simpa [decay,
        SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate.ofGlobalPSeriesWeightBoundOfNonnegConstant,
        SchwartzRiemannWeilAbstractPolynomialZeroDecayEstimate.ofGlobalPSeriesWeightBound]
        using growth_add_one_lt_decay f)

/--
Separated abstract polynomial zero-counting and zero-decay estimates produce
the direct polynomial-cardinality decay-margin tail majorant.
-/
noncomputable def toEventualPolynomialCardDecayTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion) :
    SchwartzRiemannWeilAbstractEventualPolynomialCardDecayTailMajorant
      exhaustion where
  weight := estimate.decay.weight
  cutoff := estimate.counting.cutoff
  shellCardBound := estimate.counting.shellCardBound
  shellBound := estimate.decay.shellBound
  shellCardConstant := estimate.counting.shellCardConstant
  growth := estimate.counting.growth
  zeroConstant := estimate.decay.zeroConstant
  decayExponent := estimate.decay.decayExponent
  shellCardConstant_nonneg := estimate.counting.shellCardConstant_nonneg
  zeroConstant_nonneg := estimate.decay.zeroConstant_nonneg
  growth_add_one_lt_decay := estimate.growth_add_one_lt_decay
  shellBound_nonneg := estimate.decay.shellBound_nonneg
  shellCard_le := estimate.counting.shellCard_le
  tail_shellCardBound_le := estimate.counting.tail_shellCardBound_le
  tail_shellBound_le := fun f n => by
    simpa [estimate.cutoff_eq] using estimate.decay.tail_shellBound_le f n
  norm_weight_le_shellBound := estimate.decay.norm_weight_le_shellBound

/-- Separated abstract polynomial estimates produce the p-series tail certificate. -/
noncomputable def toEventualPSeriesTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion) :
    SchwartzRiemannWeilAbstractEventualPSeriesTailMajorant exhaustion :=
  estimate.toEventualPolynomialCardDecayTailMajorant.toEventualPSeriesTailMajorant

/-- Separated abstract polynomial estimates produce the summable-tail certificate. -/
noncomputable def toEventualSummableTailMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion) :
    SchwartzRiemannWeilAbstractEventualSummableTailMajorant exhaustion :=
  estimate.toEventualPSeriesTailMajorant.toEventualSummableTailMajorant

/-- Separated abstract polynomial estimates produce the named shell estimate. -/
noncomputable def toFirstEntryShellEstimate
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion) :
    SchwartzRiemannWeilAbstractFirstEntryShellEstimate exhaustion :=
  estimate.toEventualPSeriesTailMajorant.toFirstEntryShellEstimate

/-- Separated abstract polynomial estimates produce a finite-shell majorant. -/
noncomputable def toFiniteShellMajorant
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion) :
    SchwartzRiemannWeilAbstractFiniteShellMajorant :=
  estimate.toEventualPSeriesTailMajorant.toFiniteShellMajorant

/-- Separated abstract polynomial estimates make all shell totals summable. -/
theorem summable_boundTotal
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      estimate.counting.shellCardBound n * estimate.decay.shellBound f n) := by
  simpa [toEventualPolynomialCardDecayTailMajorant] using
    estimate.toEventualPolynomialCardDecayTailMajorant.summable_boundTotal f

/-- Separated abstract polynomial estimates give absolute summability of the supplied weight. -/
theorem summable_norm_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (fun rho : ZetaZeroSubtype => norm (estimate.decay.weight f rho)) := by
  simpa [toEventualPolynomialCardDecayTailMajorant] using
    estimate.toEventualPolynomialCardDecayTailMajorant.summable_norm_weight f

/-- Separated abstract polynomial estimates make the supplied zero-side weight summable. -/
theorem summable_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion)
    (f : SchwartzLineTestFunction) :
    Summable (estimate.decay.weight f) := by
  simpa [toEventualPolynomialCardDecayTailMajorant] using
    estimate.toEventualPolynomialCardDecayTailMajorant.summable_weight f

/-- Separated abstract polynomial estimates turn the supplied weight into the zero side. -/
noncomputable def toZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion) :
    SchwartzRiemannWeilZeroSide :=
  estimate.toEventualPSeriesTailMajorant.toZeroSide

/-- The zero side induced by separated abstract estimates has the supplied weight. -/
theorem toZeroSide_weight
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion)
    (f : SchwartzLineTestFunction)
    (rho : ZetaZeroSubtype) :
    estimate.toZeroSide.weight f rho = estimate.decay.weight f rho :=
  rfl

/-- Compact-exhaustion sums for separated abstract polynomial estimates converge globally. -/
theorem tendsto_windowZeroSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (estimate.toZeroSide.zeroSide f)) :=
  estimate.toZeroSide.tendsto_windowZeroSide windowExhaustion f

/--
Separated abstract polynomial estimates whose direct zero side is identified
with a formula residual side have compact-window sums converging to that
residual side.
-/
theorem tendsto_windowZeroSide_formulaResidualSide
    {exhaustion : ComplexCompactExhaustion}
    (estimate :
      SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate exhaustion)
    (formulaResidualSide : SchwartzLineTestFunction -> Real)
    (explicitFormula :
      forall f : SchwartzLineTestFunction,
        estimate.toZeroSide.zeroSide f = formulaResidualSide f)
    (windowExhaustion : ComplexCompactExhaustion)
    (f : SchwartzLineTestFunction) :
    Tendsto
      (fun n : Nat => estimate.toZeroSide.windowZeroSide windowExhaustion n f)
      atTop (nhds (formulaResidualSide f)) := by
  rw [← explicitFormula f]
  exact estimate.tendsto_windowZeroSide windowExhaustion f

end SchwartzRiemannWeilAbstractSeparatedPolynomialDecayEstimate

end RiemannHypothesisProject
