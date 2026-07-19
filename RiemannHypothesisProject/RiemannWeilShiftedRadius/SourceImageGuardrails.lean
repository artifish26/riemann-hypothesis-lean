import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Distribution.TestFunction
import RiemannHypothesisProject.GuinandWeilDensityFormulaBridge
import RiemannHypothesisProject.GuinandWeilTestFunctionTarget
import RiemannHypothesisProject.SchwartzRiemannWeilWeight
import RiemannHypothesisProject.RiemannWeilShiftedRadius.CutoffApproximation

/-!
# Source-image guardrails for shifted-radius certificates

This module contains obstruction and no-go lemmas that constrain source-image
and shared-zero comparison targets for the shifted-radius p-series route.
-/

namespace RiemannHypothesisProject

open ComplexCompactExhaustion
open MeasureTheory
open scoped Topology

/--
Pointwise vertical domination by the real-axis value is too rigid at real
zeroes: over any real zero of `f`, it forces the whole vertical strip segment
of the extension to vanish.

This is an obstruction lemma for the old target
`norm (system.extension f z) <= A f * norm (f z.re)`. For a global Schwartz
class, the replacement target should use a nonvanishing seminorm/envelope
majorant rather than the point value `norm (f z.re)`.
-/
theorem realPartComparison_forces_verticalLine_zero_of_real_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (f : SchwartzLineTestFunction)
    (t y : Real)
    (hf_zero : f t = 0)
    (hy_low : -(1 / 2 : Real) <= y)
    (hy_high : y <= (1 / 2 : Real)) :
    system.extension f ((t : Complex) + (y : Complex) * Complex.I) = 0 := by
  let z : Complex := (t : Complex) + (y : Complex) * Complex.I
  have hz_re : z.re = t := by
    simp [z]
  have hz_im : z.im = y := by
    simp [z]
  have hdom := strip_extension_norm_le_realAxis f z
    (by simpa [hz_im] using hy_low)
    (by simpa [hz_im] using hy_high)
  have hrhs_zero : comparisonConstant f * ‖f z.re‖ = 0 := by
    simp [hz_re, hf_zero]
  have hnorm_le_zero : norm (system.extension f z) <= 0 := by
    simpa [hrhs_zero] using hdom
  have hnorm_zero : norm (system.extension f z) = 0 :=
    le_antisymm hnorm_le_zero (norm_nonneg _)
  exact norm_eq_zero.mp hnorm_zero

/--
Analytic-continuation obstruction for the project extension system: if an
entire extension has zeroes accumulating at any point, the whole extension is
zero.

This is the continuation step behind the real-zero warning for pointwise
real-value domination. The separate vertical-line lemma supplies many zeroes;
this theorem records the exact analytic continuation consequence.
-/
theorem extension_eq_zero_of_frequently_zero_near
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (z0 : Complex)
    (hfreq :
      ∃ᶠ z in 𝓝[≠] z0, system.extension f z = 0) :
    system.extension f = 0 := by
  have hanalytic :
      AnalyticOnNhd Complex (system.extension f) Set.univ := by
    intro z _hz
    exact (system.extension_differentiable f).analyticAt z
  have hzero :
      AnalyticOnNhd Complex (fun _ : Complex => (0 : Complex)) Set.univ :=
    analyticOnNhd_const
  exact AnalyticOnNhd.eq_of_frequently_eq hanalytic hzero hfreq

/--
Generic analytic-continuation form used by the source-class obstruction:
a complex-differentiable function with zeroes accumulating at a punctured
neighborhood is identically zero.
-/
theorem differentiableFunction_eq_zero_of_frequently_zero_near
    {F : Complex -> Complex}
    (hF : Differentiable Complex F)
    (z0 : Complex)
    (hfreq : ∃ᶠ z in 𝓝[≠] z0, F z = 0) :
    F = 0 := by
  have hanalytic : AnalyticOnNhd Complex F Set.univ := by
    intro z _hz
    exact hF.analyticAt z
  have hzero :
      AnalyticOnNhd Complex (fun _ : Complex => (0 : Complex)) Set.univ :=
    analyticOnNhd_const
  exact AnalyticOnNhd.eq_of_frequently_eq hanalytic hzero hfreq

/--
If a project extension has accumulating zeroes, its real-line Schwartz
restriction is the zero function.
-/
theorem realLine_eq_zero_of_extension_frequently_zero_near
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (z0 : Complex)
    (hfreq :
      ∃ᶠ z in 𝓝[≠] z0, system.extension f z = 0)
    (t : Real) :
    f t = 0 := by
  have hglobal :=
    extension_eq_zero_of_frequently_zero_near
      (system := system) f z0 hfreq
  have hvalue : system.extension f (t : Complex) = 0 := by
    simpa using congrFun hglobal (t : Complex)
  simpa [system.extension_restricts f t] using hvalue

/--
The pointwise real-value domination target is globally degenerate for any
test function with a real zero: the vertical segment of forced zeroes
accumulates, so analytic continuation makes the whole extension vanish.
-/
theorem realPartComparison_forces_extension_eq_zero_of_real_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (f : SchwartzLineTestFunction)
    (t : Real)
    (hf_zero : f t = 0) :
    system.extension f = 0 := by
  let verticalPath : Real -> Complex :=
    fun y => (t : Complex) + (y : Complex) * Complex.I
  have hvertical_zero :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        system.extension f (verticalPath y) = 0 := by
    have hupper :
        {y : Real | y < (1 / 2 : Real)} ∈ 𝓝[>] (0 : Real) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hupper] with y hy_pos hy_upper
    have hy_pos' : 0 < y := hy_pos
    exact
      realPartComparison_forces_verticalLine_zero_of_real_zero
        comparisonConstant strip_extension_norm_le_realAxis f t y hf_zero
        (by linarith) (le_of_lt hy_upper)
  have hvertical_tendsto_nhds :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝 (t : Complex)) := by
    have hofReal :
        Filter.Tendsto (fun y : Real => (y : Complex))
          (𝓝 (0 : Real)) (𝓝 (0 : Complex)) :=
      Complex.continuous_ofReal.tendsto 0
    have hfull :
        Filter.Tendsto verticalPath (𝓝 (0 : Real)) (𝓝 (t : Complex)) := by
      simpa [verticalPath] using
        (tendsto_const_nhds.add (hofReal.mul tendsto_const_nhds))
    exact tendsto_nhdsWithin_of_tendsto_nhds hfull
  have hvertical_eventually_ne :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        verticalPath y ∈ ({z : Complex | z ≠ (t : Complex)} : Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with y hy_pos
    intro h_eq
    have him :
        (verticalPath y).im = ((t : Complex)).im := by
      rw [h_eq]
    have hy_zero : y = 0 := by
      simpa [verticalPath] using him
    have hy_pos' : 0 < y := hy_pos
    linarith
  have hvertical_tendsto_ne :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝[≠] (t : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      verticalPath hvertical_tendsto_nhds hvertical_eventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] (t : Complex), system.extension f z = 0 :=
    hvertical_tendsto_ne.frequently hvertical_zero.frequently
  exact extension_eq_zero_of_frequently_zero_near
    (system := system) f (t : Complex) hfreq

/--
Consequently, under pointwise real-value domination, any real zero forces the
original real-line test function itself to vanish everywhere.
-/
theorem realPartComparison_forces_realLine_eq_zero_of_real_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (comparisonConstant : SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_realAxis :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant f * ‖f z.re‖)
    (f : SchwartzLineTestFunction)
    (t : Real)
    (hf_zero : f t = 0)
    (u : Real) :
    f u = 0 := by
  have hglobal :=
    realPartComparison_forces_extension_eq_zero_of_real_zero
      comparisonConstant strip_extension_norm_le_realAxis f t hf_zero
  have hvalue : system.extension f (u : Complex) = 0 := by
    simpa using congrFun hglobal (u : Complex)
  simpa [system.extension_restricts f u] using hvalue

/--
Fixed-test no-go form for the one-profile real-value comparison: one test with
a real zero and a nonzero value elsewhere contradicts the pointwise real-axis
strip domination for that test.
-/
theorem fixedRealPartComparison_inconsistent_of_real_zero_nonzero
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (comparisonConstant : Real)
    (strip_extension_norm_le_realAxis :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              comparisonConstant * ‖f z.re‖)
    (t u : Real)
    (hf_zero : f t = 0)
    (hf_nonzero : f u ≠ 0) :
    False := by
  let verticalPath : Real -> Complex :=
    fun y => (t : Complex) + (y : Complex) * Complex.I
  have hvertical_zero :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        system.extension f (verticalPath y) = 0 := by
    have hupper :
        {y : Real | y < (1 / 2 : Real)} ∈ 𝓝[>] (0 : Real) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hupper] with y hy_pos hy_upper
    let z : Complex := verticalPath y
    have hz_re : z.re = t := by
      simp [z, verticalPath]
    have hz_im : z.im = y := by
      simp [z, verticalPath]
    have hdom := strip_extension_norm_le_realAxis z
      (by
        have hy_pos' : 0 < y := hy_pos
        simpa [hz_im] using (by linarith : -(1 / 2 : Real) <= y))
      (by simpa [hz_im] using le_of_lt hy_upper)
    have hrhs_zero : comparisonConstant * ‖f z.re‖ = 0 := by
      simp [hz_re, hf_zero]
    have hnorm_le_zero : norm (system.extension f z) <= 0 := by
      simpa [hrhs_zero] using hdom
    have hnorm_zero : norm (system.extension f z) = 0 :=
      le_antisymm hnorm_le_zero (norm_nonneg _)
    exact norm_eq_zero.mp hnorm_zero
  have hvertical_tendsto_nhds :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝 (t : Complex)) := by
    have hofReal :
        Filter.Tendsto (fun y : Real => (y : Complex))
          (𝓝 (0 : Real)) (𝓝 (0 : Complex)) :=
      Complex.continuous_ofReal.tendsto 0
    have hfull :
        Filter.Tendsto verticalPath (𝓝 (0 : Real)) (𝓝 (t : Complex)) := by
      simpa [verticalPath] using
        (tendsto_const_nhds.add (hofReal.mul tendsto_const_nhds))
    exact tendsto_nhdsWithin_of_tendsto_nhds hfull
  have hvertical_eventually_ne :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        verticalPath y ∈ ({z : Complex | z ≠ (t : Complex)} : Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with y hy_pos
    intro h_eq
    have him :
        (verticalPath y).im = ((t : Complex)).im := by
      rw [h_eq]
    have hy_zero : y = 0 := by
      simpa [verticalPath] using him
    have hy_pos' : 0 < y := hy_pos
    linarith
  have hvertical_tendsto_ne :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝[≠] (t : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      verticalPath hvertical_tendsto_nhds hvertical_eventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] (t : Complex), system.extension f z = 0 :=
    hvertical_tendsto_ne.frequently hvertical_zero.frequently
  have hglobal :=
    extension_eq_zero_of_frequently_zero_near
      (system := system) f (t : Complex) hfreq
  have hvalue : system.extension f (u : Complex) = 0 := by
    simpa using congrFun hglobal (u : Complex)
  exact hf_nonzero (by simpa [system.extension_restricts f u] using hvalue)

/--
Source-class one-profile no-go form. If an admissible Guinand-Weil source test
maps to any Schwartz test with a real zero and a nonzero value elsewhere, then
source-side pointwise real-value strip domination is inconsistent for that
source class.
-/
theorem sourceRealPartComparison_inconsistent_of_mapsTo_real_zero_nonzero
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (target : SchwartzLineTestFunction)
    (t u : Real)
    (htarget_zero : target t = 0)
    (htarget_nonzero : target u ≠ 0)
    (g0 : testData.SourceTestFunction)
    (hg0 : testData.admissible g0)
    (hg0_toSchwartz : testData.toSchwartz g0 = target)
    (comparisonConstant : testData.SourceTestFunction -> Real)
    (strip_extension_norm_le_realAxis :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (system.extension (testData.toSchwartz g) z) <=
                  comparisonConstant g * ‖(testData.toSchwartz g) z.re‖) :
    False := by
  have hf_zero : testData.toSchwartz g0 t = 0 := by
    simpa [hg0_toSchwartz] using htarget_zero
  have hf_nonzero :
      testData.toSchwartz g0 u ≠ 0 := by
    simpa [hg0_toSchwartz] using htarget_nonzero
  exact
    fixedRealPartComparison_inconsistent_of_real_zero_nonzero
      (system := system)
      (testData.toSchwartz g0)
      (comparisonConstant g0)
      (fun z hlow hhigh =>
        strip_extension_norm_le_realAxis g0 hg0 z hlow hhigh)
      t u hf_zero hf_nonzero

/--
Source-coverage one-profile no-go form. A source class that covers every
project Schwartz test cannot support pointwise real-value strip domination:
coverage supplies a source representative of any requested real-zero/nonzero
Schwartz witness.
-/
theorem sourceCoverageRealPartComparison_inconsistent_of_real_zero_nonzero
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (target : SchwartzLineTestFunction)
    (t u : Real)
    (htarget_zero : target t = 0)
    (htarget_nonzero : target u ≠ 0)
    (coversSchwartz :
      forall f : SchwartzLineTestFunction,
        exists g : testData.SourceTestFunction,
          testData.admissible g /\ testData.toSchwartz g = f)
    (comparisonConstant : testData.SourceTestFunction -> Real)
    (strip_extension_norm_le_realAxis :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (system.extension (testData.toSchwartz g) z) <=
                  comparisonConstant g * ‖(testData.toSchwartz g) z.re‖) :
    False := by
  classical
  let g0 : testData.SourceTestFunction :=
    Classical.choose (coversSchwartz target)
  have hg0_pair := Classical.choose_spec (coversSchwartz target)
  exact
    sourceRealPartComparison_inconsistent_of_mapsTo_real_zero_nonzero
      (system := system)
      testData target t u htarget_zero htarget_nonzero
      g0 hg0_pair.1 hg0_pair.2 comparisonConstant
      strip_extension_norm_le_realAxis

/--
The two-profile pointwise strip comparison has the same rigidity problem as
the one-profile real-axis comparison: if `f` and its Fourier transform share a
real zero, the whole vertical strip segment over that real point is forced to
vanish.

This is a checked obstruction for the tempting target
`norm F_f(z) <= A f * norm (f z.re) + B f * norm (Fourier f z.re)` on the full
Schwartz class. A genuine source proof must either restrict the source class
to avoid shared real/Fourier zeroes or replace these point values by a
nonvanishing seminorm/envelope majorant.
-/
theorem realFourierProfileComparison_forces_verticalLine_zero_of_shared_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (realProfileConstant fourierProfileConstant :
      SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_real_fourier :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant f * ‖f z.re‖ +
                fourierProfileConstant f *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t y : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (hy_low : -(1 / 2 : Real) <= y)
    (hy_high : y <= (1 / 2 : Real)) :
    system.extension f ((t : Complex) + (y : Complex) * Complex.I) = 0 := by
  let z : Complex := (t : Complex) + (y : Complex) * Complex.I
  have hz_re : z.re = t := by
    simp [z]
  have hz_im : z.im = y := by
    simp [z]
  have hdom := strip_extension_norm_le_real_fourier f z
    (by simpa [hz_im] using hy_low)
    (by simpa [hz_im] using hy_high)
  have hrhs_zero :
      realProfileConstant f * ‖f z.re‖ +
          fourierProfileConstant f *
            ‖(SchwartzLineTestFunction.fourier f) z.re‖ = 0 := by
    simp [hz_re, hf_zero, hfourier_zero]
  have hnorm_le_zero : norm (system.extension f z) <= 0 := by
    simpa [hrhs_zero] using hdom
  have hnorm_zero : norm (system.extension f z) = 0 :=
    le_antisymm hnorm_le_zero (norm_nonneg _)
  exact norm_eq_zero.mp hnorm_zero

/--
Analytic-continuation form of the two-profile obstruction: under pointwise
real/Fourier profile domination, one shared real zero of `f` and `Fourier f`
forces the entire extension to be zero.
-/
theorem realFourierProfileComparison_forces_extension_eq_zero_of_shared_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (realProfileConstant fourierProfileConstant :
      SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_real_fourier :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant f * ‖f z.re‖ +
                fourierProfileConstant f *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0) :
    system.extension f = 0 := by
  let verticalPath : Real -> Complex :=
    fun y => (t : Complex) + (y : Complex) * Complex.I
  have hvertical_zero :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        system.extension f (verticalPath y) = 0 := by
    have hupper :
        {y : Real | y < (1 / 2 : Real)} ∈ 𝓝[>] (0 : Real) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hupper] with y hy_pos hy_upper
    exact
      realFourierProfileComparison_forces_verticalLine_zero_of_shared_zero
        realProfileConstant fourierProfileConstant
        strip_extension_norm_le_real_fourier f t y hf_zero hfourier_zero
        (by
          have hy_pos' : 0 < y := hy_pos
          linarith)
        (le_of_lt hy_upper)
  have hvertical_tendsto_nhds :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝 (t : Complex)) := by
    have hofReal :
        Filter.Tendsto (fun y : Real => (y : Complex))
          (𝓝 (0 : Real)) (𝓝 (0 : Complex)) :=
      Complex.continuous_ofReal.tendsto 0
    have hfull :
        Filter.Tendsto verticalPath (𝓝 (0 : Real)) (𝓝 (t : Complex)) := by
      simpa [verticalPath] using
        (tendsto_const_nhds.add (hofReal.mul tendsto_const_nhds))
    exact tendsto_nhdsWithin_of_tendsto_nhds hfull
  have hvertical_eventually_ne :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        verticalPath y ∈ ({z : Complex | z ≠ (t : Complex)} : Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with y hy_pos
    intro h_eq
    have him :
        (verticalPath y).im = ((t : Complex)).im := by
      rw [h_eq]
    have hy_zero : y = 0 := by
      simpa [verticalPath] using him
    have hy_pos' : 0 < y := hy_pos
    linarith
  have hvertical_tendsto_ne :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝[≠] (t : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      verticalPath hvertical_tendsto_nhds hvertical_eventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] (t : Complex), system.extension f z = 0 :=
    hvertical_tendsto_ne.frequently hvertical_zero.frequently
  exact extension_eq_zero_of_frequently_zero_near
    (system := system) f (t : Complex) hfreq

/--
Consequently, a full-class two-profile pointwise strip comparison would make
any source test with a shared real/Fourier zero vanish identically on the real
line.
-/
theorem realFourierProfileComparison_forces_realLine_eq_zero_of_shared_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (realProfileConstant fourierProfileConstant :
      SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_real_fourier :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant f * ‖f z.re‖ +
                fourierProfileConstant f *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (u : Real) :
    f u = 0 := by
  have hglobal :=
    realFourierProfileComparison_forces_extension_eq_zero_of_shared_zero
      realProfileConstant fourierProfileConstant
      strip_extension_norm_le_real_fourier f t hf_zero hfourier_zero
  have hvalue : system.extension f (u : Complex) = 0 := by
    simpa using congrFun hglobal (u : Complex)
  simpa [system.extension_restricts f u] using hvalue

/--
Fixed-test version of the two-profile obstruction. This is the form needed for
restricted source classes: it only assumes the pointwise profile comparison for
one chosen test function.
-/
theorem fixedRealFourierProfileComparison_forces_verticalLine_zero_of_shared_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (realProfileConstant fourierProfileConstant : Real)
    (strip_extension_norm_le_real_fourier :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant * ‖f z.re‖ +
                fourierProfileConstant *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (t y : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (hy_low : -(1 / 2 : Real) <= y)
    (hy_high : y <= (1 / 2 : Real)) :
    system.extension f ((t : Complex) + (y : Complex) * Complex.I) = 0 := by
  let z : Complex := (t : Complex) + (y : Complex) * Complex.I
  have hz_re : z.re = t := by
    simp [z]
  have hz_im : z.im = y := by
    simp [z]
  have hdom := strip_extension_norm_le_real_fourier z
    (by simpa [hz_im] using hy_low)
    (by simpa [hz_im] using hy_high)
  have hrhs_zero :
      realProfileConstant * ‖f z.re‖ +
          fourierProfileConstant *
            ‖(SchwartzLineTestFunction.fourier f) z.re‖ = 0 := by
    simp [hz_re, hf_zero, hfourier_zero]
  have hnorm_le_zero : norm (system.extension f z) <= 0 := by
    simpa [hrhs_zero] using hdom
  have hnorm_zero : norm (system.extension f z) = 0 :=
    le_antisymm hnorm_le_zero (norm_nonneg _)
  exact norm_eq_zero.mp hnorm_zero

/--
Fixed-test analytic-continuation form of the two-profile obstruction.
-/
theorem fixedRealFourierProfileComparison_forces_extension_eq_zero_of_shared_zero
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (realProfileConstant fourierProfileConstant : Real)
    (strip_extension_norm_le_real_fourier :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant * ‖f z.re‖ +
                fourierProfileConstant *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (t : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0) :
    system.extension f = 0 := by
  let verticalPath : Real -> Complex :=
    fun y => (t : Complex) + (y : Complex) * Complex.I
  have hvertical_zero :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        system.extension f (verticalPath y) = 0 := by
    have hupper :
        {y : Real | y < (1 / 2 : Real)} ∈ 𝓝[>] (0 : Real) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hupper] with y hy_pos hy_upper
    exact
      fixedRealFourierProfileComparison_forces_verticalLine_zero_of_shared_zero
        f realProfileConstant fourierProfileConstant
        strip_extension_norm_le_real_fourier t y hf_zero hfourier_zero
        (by
          have hy_pos' : 0 < y := hy_pos
          linarith)
        (le_of_lt hy_upper)
  have hvertical_tendsto_nhds :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝 (t : Complex)) := by
    have hofReal :
        Filter.Tendsto (fun y : Real => (y : Complex))
          (𝓝 (0 : Real)) (𝓝 (0 : Complex)) :=
      Complex.continuous_ofReal.tendsto 0
    have hfull :
        Filter.Tendsto verticalPath (𝓝 (0 : Real)) (𝓝 (t : Complex)) := by
      simpa [verticalPath] using
        (tendsto_const_nhds.add (hofReal.mul tendsto_const_nhds))
    exact tendsto_nhdsWithin_of_tendsto_nhds hfull
  have hvertical_eventually_ne :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        verticalPath y ∈ ({z : Complex | z ≠ (t : Complex)} : Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with y hy_pos
    intro h_eq
    have him :
        (verticalPath y).im = ((t : Complex)).im := by
      rw [h_eq]
    have hy_zero : y = 0 := by
      simpa [verticalPath] using him
    have hy_pos' : 0 < y := hy_pos
    linarith
  have hvertical_tendsto_ne :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝[≠] (t : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      verticalPath hvertical_tendsto_nhds hvertical_eventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] (t : Complex), system.extension f z = 0 :=
    hvertical_tendsto_ne.frequently hvertical_zero.frequently
  exact extension_eq_zero_of_frequently_zero_near
    (system := system) f (t : Complex) hfreq

/--
Fixed-test no-go form: one admissible test with a shared real/Fourier zero and
a nonzero value elsewhere contradicts the pointwise profile comparison for
that test.
-/
theorem fixedRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (realProfileConstant fourierProfileConstant : Real)
    (strip_extension_norm_le_real_fourier :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant * ‖f z.re‖ +
                fourierProfileConstant *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (t u : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (hf_nonzero : f u ≠ 0) :
    False := by
  have hglobal :=
    fixedRealFourierProfileComparison_forces_extension_eq_zero_of_shared_zero
      f realProfileConstant fourierProfileConstant
      strip_extension_norm_le_real_fourier t hf_zero hfourier_zero
  have hvalue : system.extension f (u : Complex) = 0 := by
    simpa using congrFun hglobal (u : Complex)
  exact hf_nonzero (by simpa [system.extension_restricts f u] using hvalue)

/--
No-go form of the two-profile obstruction: a full-class pointwise
real/Fourier profile comparison is inconsistent with the existence of a test
function that has a shared real/Fourier zero but is nonzero somewhere else.
-/
theorem realFourierProfileComparison_inconsistent_of_shared_zero_nonzero
    {system : SchwartzRiemannWeilExtensionSystem}
    (realProfileConstant fourierProfileConstant :
      SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_real_fourier :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant f * ‖f z.re‖ +
                fourierProfileConstant f *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t u : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (hf_nonzero : f u ≠ 0) :
    False := by
  exact hf_nonzero
    (realFourierProfileComparison_forces_realLine_eq_zero_of_shared_zero
      realProfileConstant fourierProfileConstant
      strip_extension_norm_le_real_fourier f t hf_zero hfourier_zero u)

/--
A concrete witness that the pointwise two-profile strip target is impossible on
the full Schwartz class.

The intended analytic instance is an odd compactly supported smooth function,
for example a difference of two equal bumps centered at `1` and `-1`: it
vanishes at `0`, its Fourier transform vanishes at `0` because its integral is
zero, and it is nonzero near one bump center.
-/
structure SchwartzSharedRealFourierZeroNonzeroWitness where
  test : SchwartzLineTestFunction
  sharedZero : Real
  nonzeroPoint : Real
  test_sharedZero_eq_zero : test sharedZero = 0
  fourier_sharedZero_eq_zero :
    (SchwartzLineTestFunction.fourier test) sharedZero = 0
  test_nonzero : test nonzeroPoint ≠ 0

namespace SchwartzSharedRealFourierZeroNonzeroWitness

/--
Build the shared-zero obstruction witness from a nonzero Schwartz test that
vanishes at the origin and has zero integral.  The Fourier zero is no longer an
extra analytic obligation: it follows from the checked frequency-zero Fourier
identity.
-/
def of_zero_value_integral_and_nonzero
    (f : SchwartzLineTestFunction)
    (nonzeroPoint : Real)
    (hf_zero : f (0 : Real) = 0)
    (h_integral_zero : (∫ x : Real, f x) = 0)
    (hf_nonzero : f nonzeroPoint ≠ 0) :
    SchwartzSharedRealFourierZeroNonzeroWitness where
  test := f
  sharedZero := 0
  nonzeroPoint := nonzeroPoint
  test_sharedZero_eq_zero := hf_zero
  fourier_sharedZero_eq_zero :=
    SchwartzLineTestFunction.fourier_zero_eq_zero_of_integral_eq_zero
      f h_integral_zero
  test_nonzero := hf_nonzero

noncomputable section

/-- A fixed smooth bump on the real line, equal to `1` near `0` and supported in `(-1, 1)`. -/
def centeredUnitBump : ContDiffBump (0 : Real) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The fixed centered bump, viewed as a real-valued Schwartz function. -/
def centeredUnitBumpRealSchwartz : SchwartzMap Real Real :=
  centeredUnitBump.hasCompactSupport.toSchwartzMap centeredUnitBump.contDiff

/-- The fixed centered bump, viewed as a complex-valued Schwartz test function. -/
def centeredUnitBumpSchwartz : SchwartzLineTestFunction :=
  centeredUnitBumpRealSchwartz.postcompCLM Complex.ofRealCLM

@[simp]
theorem centeredUnitBumpRealSchwartz_apply (x : Real) :
    centeredUnitBumpRealSchwartz x = centeredUnitBump x :=
  rfl

@[simp]
theorem centeredUnitBumpSchwartz_apply (x : Real) :
    centeredUnitBumpSchwartz x = (centeredUnitBump x : Complex) := by
  rfl

/-- The explicit centered bump is compactly supported as a project Schwartz test. -/
theorem centeredUnitBumpSchwartz_hasCompactSupport :
    HasCompactSupport centeredUnitBumpSchwartz := by
  change HasCompactSupport (fun x : Real => (centeredUnitBump x : Complex))
  exact centeredUnitBump.hasCompactSupport.comp_left
    (show ((0 : Real) : Complex) = 0 by norm_num)

@[simp]
theorem centeredUnitBump_zero :
    centeredUnitBump (0 : Real) = 1 := by
  exact centeredUnitBump.one_of_mem_closedBall (by simp [centeredUnitBump])

@[simp]
theorem centeredUnitBump_one :
    centeredUnitBump (1 : Real) = 0 := by
  exact centeredUnitBump.zero_of_le_dist (by simp [centeredUnitBump])

@[simp]
theorem centeredUnitBump_neg_one :
    centeredUnitBump (-1 : Real) = 0 := by
  simpa using centeredUnitBump.neg (1 : Real)

@[simp]
theorem centeredUnitBump_two :
    centeredUnitBump (2 : Real) = 0 := by
  exact centeredUnitBump.zero_of_le_dist (by norm_num [centeredUnitBump, Real.dist_eq])

/--
An explicit odd-type Schwartz bump difference. It is the difference of two
equal compactly supported smooth bumps centered at `1` and `-1`.
-/
def oddTranslatedBumpDifference : SchwartzLineTestFunction :=
  centeredUnitBumpSchwartz.compSubConstCLM Complex (1 : Real) -
    centeredUnitBumpSchwartz.compSubConstCLM Complex (-1 : Real)

@[simp]
theorem oddTranslatedBumpDifference_zero :
    oddTranslatedBumpDifference (0 : Real) = 0 := by
  simp [oddTranslatedBumpDifference]

@[simp]
theorem oddTranslatedBumpDifference_one :
    oddTranslatedBumpDifference (1 : Real) = 1 := by
  simp [oddTranslatedBumpDifference,
    show (1 : Real) - (-1) = 2 by norm_num]

theorem oddTranslatedBumpDifference_one_ne_zero :
    oddTranslatedBumpDifference (1 : Real) ≠ 0 := by
  simp

theorem oddTranslatedBumpDifference_eq_zero_of_three_lt
    {x : Real} (hx : 3 < x) :
    oddTranslatedBumpDifference x = 0 := by
  have hleft : centeredUnitBump (x - 1) = 0 := by
    exact centeredUnitBump.zero_of_le_dist (by
      rw [Real.dist_eq]
      have hnonneg : 0 <= x - 1 - 0 := by linarith
      rw [abs_of_nonneg hnonneg]
      norm_num [centeredUnitBump]
      linarith)
  have hright : centeredUnitBump (x + 1) = 0 := by
    exact centeredUnitBump.zero_of_le_dist (by
      rw [Real.dist_eq]
      have hnonneg : 0 <= x + 1 - 0 := by linarith
      rw [abs_of_nonneg hnonneg]
      norm_num [centeredUnitBump]
      linarith)
  simp [oddTranslatedBumpDifference, hleft, hright]

theorem oddTranslatedBumpDifference_integral_eq_zero :
    (∫ x : Real, oddTranslatedBumpDifference x) = 0 := by
  have hleft :
      (∫ x : Real,
          (centeredUnitBumpSchwartz.compSubConstCLM Complex (1 : Real)) x) =
        ∫ x : Real, centeredUnitBumpSchwartz x := by
    simpa [sub_eq_add_neg] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := volume)
        (fun x : Real => centeredUnitBumpSchwartz x)
        (-(1 : Real)))
  have hright :
      (∫ x : Real,
          (centeredUnitBumpSchwartz.compSubConstCLM Complex (-1 : Real)) x) =
        ∫ x : Real, centeredUnitBumpSchwartz x := by
    simpa [sub_eq_add_neg] using
      (MeasureTheory.integral_add_right_eq_self
        (μ := volume)
        (fun x : Real => centeredUnitBumpSchwartz x)
        (1 : Real))
  change
    (∫ x : Real,
        (centeredUnitBumpSchwartz.compSubConstCLM Complex (1 : Real)) x -
          (centeredUnitBumpSchwartz.compSubConstCLM Complex (-1 : Real)) x) = 0
  rw [integral_sub
    (centeredUnitBumpSchwartz.compSubConstCLM Complex (1 : Real)).integrable
    (centeredUnitBumpSchwartz.compSubConstCLM Complex (-1 : Real)).integrable]
  rw [hleft, hright, sub_self]

/--
The explicit shared-zero, nonzero Schwartz witness. This closes the no-go
instance for the full-Schwartz pointwise real/Fourier two-profile route.
-/
def oddTranslatedBumpDifferenceSharedZeroWitness :
    SchwartzSharedRealFourierZeroNonzeroWitness :=
  of_zero_value_integral_and_nonzero
    oddTranslatedBumpDifference
    (1 : Real)
    oddTranslatedBumpDifference_zero
    oddTranslatedBumpDifference_integral_eq_zero
    oddTranslatedBumpDifference_one_ne_zero

end

/--
Foundational obstruction: a `SchwartzRiemannWeilExtensionSystem` over all
project Schwartz test functions cannot exist.

The explicit compactly supported two-bump Schwartz test is zero on a real
right-neighborhood of `3` but nonzero at `1`. Any entire extension agreeing
with it on the real axis would vanish identically by analytic continuation,
contradicting the nonzero value at `1`.
-/
theorem no_global_schwartzRiemannWeilExtensionSystem
    (system : SchwartzRiemannWeilExtensionSystem) :
    False := by
  let f :=
    SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference
  have hreal_zero :
      ∀ᶠ x in (𝓝[>] (3 : Real) : Filter Real),
        system.extension f (((x : Real) : Complex)) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hf :
        f x = 0 :=
      SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference_eq_zero_of_three_lt hx
    simpa [system.extension_restricts f x] using hf
  have htendsto_nhds :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[>] (3 : Real) : Filter Real) (𝓝 ((3 : Real) : Complex)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (Complex.continuous_ofReal.tendsto 3)
  have heventually_ne :
      ∀ᶠ x in (𝓝[>] (3 : Real) : Filter Real),
        (((x : Real) : Complex)) ∈
          ({z : Complex | z ≠ ((3 : Real) : Complex)} :
          Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro h_eq
    have hx_eq : x = 3 := Complex.ofReal_injective h_eq
    have hx_gt : 3 < x := hx
    linarith
  have htendsto_ne :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[>] (3 : Real) : Filter Real) (𝓝[≠] ((3 : Real) : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun x : Real => (x : Complex)) htendsto_nhds heventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] ((3 : Real) : Complex), system.extension f z = 0 :=
    htendsto_ne.frequently hreal_zero.frequently
  have hglobal :
      system.extension f = 0 :=
    extension_eq_zero_of_frequently_zero_near
      (system := system) f ((3 : Real) : Complex) hfreq
  have hvalue : system.extension f ((1 : Real) : Complex) = 0 := by
    simpa using congrFun hglobal ((1 : Real) : Complex)
  have hf_one_zero : f (1 : Real) = 0 := by
    rw [← system.extension_restricts f (1 : Real)]
    exact hvalue
  have hf_one_zero_explicit :
      SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference
          (1 : Real) = 0 := by
    exact hf_one_zero
  exact
    SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference_one_ne_zero
      hf_one_zero_explicit

/--
Restricted source-extension data for Guinand-Weil admissible tests.

Unlike `SchwartzRiemannWeilExtensionSystem`, this does not claim that every
project Schwartz function has an entire extension. It only packages an entire
extension for tests admitted by a chosen source class.
-/
structure GuinandWeilSourceExtensionSystem
    (testData : GuinandWeilSourceTestFunctionClass) where
  extension : testData.SourceTestFunction -> Complex -> Complex
  extension_restricts :
    forall g : testData.SourceTestFunction,
      testData.admissible g ->
        forall t : Real, extension g (t : Complex) = testData.toSchwartz g t
  extension_differentiable :
    forall g : testData.SourceTestFunction,
      testData.admissible g -> Differentiable Complex (extension g)

/--
Exact coverage of all project Schwartz tests is incompatible with an admissible
source class whose tests have entire source extensions.

This is the source-level version of
`no_global_schwartzRiemannWeilExtensionSystem`: the compactly supported
two-bump Schwartz witness cannot be the real-line restriction of any entire
admissible source extension.
-/
theorem sourceExtension_exactSchwartzCoverage_inconsistent
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem : GuinandWeilSourceExtensionSystem testData)
    (coversSchwartz :
      forall f : SchwartzLineTestFunction,
        exists g : testData.SourceTestFunction,
          testData.admissible g /\ testData.toSchwartz g = f) :
    False := by
  let f :=
    SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference
  rcases coversSchwartz f with ⟨g, hg, hgf⟩
  have hreal_zero :
      ∀ᶠ x in (𝓝[>] (3 : Real) : Filter Real),
        sourceSystem.extension g (((x : Real) : Complex)) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hf :
        f x = 0 :=
      SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference_eq_zero_of_three_lt hx
    calc
      sourceSystem.extension g (((x : Real) : Complex)) =
          testData.toSchwartz g x :=
        sourceSystem.extension_restricts g hg x
      _ = f x := by
        simp [hgf]
      _ = 0 := hf
  have htendsto_nhds :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[>] (3 : Real) : Filter Real) (𝓝 ((3 : Real) : Complex)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (Complex.continuous_ofReal.tendsto 3)
  have heventually_ne :
      ∀ᶠ x in (𝓝[>] (3 : Real) : Filter Real),
        (((x : Real) : Complex)) ∈
          ({z : Complex | z ≠ ((3 : Real) : Complex)} :
          Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro h_eq
    have hx_eq : x = 3 := Complex.ofReal_injective h_eq
    have hx_gt : 3 < x := hx
    linarith
  have htendsto_ne :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[>] (3 : Real) : Filter Real) (𝓝[≠] ((3 : Real) : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun x : Real => (x : Complex)) htendsto_nhds heventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] ((3 : Real) : Complex),
        sourceSystem.extension g z = 0 :=
    htendsto_ne.frequently hreal_zero.frequently
  have hglobal :
      sourceSystem.extension g = 0 :=
    differentiableFunction_eq_zero_of_frequently_zero_near
      (sourceSystem.extension_differentiable g hg)
      ((3 : Real) : Complex) hfreq
  have hvalue : sourceSystem.extension g ((1 : Real) : Complex) = 0 := by
    simpa using congrFun hglobal ((1 : Real) : Complex)
  have hf_one_zero : f (1 : Real) = 0 := by
    calc
      f (1 : Real) = testData.toSchwartz g (1 : Real) :=
        by simp [hgf]
      _ = sourceSystem.extension g ((1 : Real) : Complex) :=
        (sourceSystem.extension_restricts g hg (1 : Real)).symm
      _ = 0 := hvalue
  exact
    SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference_one_ne_zero
      hf_one_zero

/--
The witness immediately contradicts a full-class pointwise real/Fourier profile
comparison for a nontrivial extension system.
-/
theorem contradicts_realFourierProfileComparison
    {system : SchwartzRiemannWeilExtensionSystem}
    (witness : SchwartzSharedRealFourierZeroNonzeroWitness)
    (realProfileConstant fourierProfileConstant :
      SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_real_fourier :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant f * ‖f z.re‖ +
                fourierProfileConstant f *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖) :
    False :=
  realFourierProfileComparison_inconsistent_of_shared_zero_nonzero
    realProfileConstant fourierProfileConstant
    strip_extension_norm_le_real_fourier witness.test witness.sharedZero
    witness.nonzeroPoint witness.test_sharedZero_eq_zero
    witness.fourier_sharedZero_eq_zero witness.test_nonzero

/--
The explicit bump-difference witness contradicts any full-class pointwise
real/Fourier profile comparison.
-/
theorem oddTranslatedBumpDifference_contradicts_realFourierProfileComparison
    {system : SchwartzRiemannWeilExtensionSystem}
    (realProfileConstant fourierProfileConstant :
      SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_real_fourier :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            norm (system.extension f z) <=
              realProfileConstant f * ‖f z.re‖ +
                fourierProfileConstant f *
                  ‖(SchwartzLineTestFunction.fourier f) z.re‖) :
    False :=
  oddTranslatedBumpDifferenceSharedZeroWitness.contradicts_realFourierProfileComparison
    realProfileConstant fourierProfileConstant
    strip_extension_norm_le_real_fourier

end SchwartzSharedRealFourierZeroNonzeroWitness

/--
Restricted-source no-go form. If a restricted source class admits the explicit
two-bump witness, then even a pointwise real/Fourier profile comparison stated
only for admissible tests is inconsistent.
-/
theorem restrictedRealFourierProfileComparison_inconsistent_of_admits_oddTranslatedBumpDifference
    {system : SchwartzRiemannWeilExtensionSystem}
    (admissible : SchwartzLineTestFunction -> Prop)
    (hadmissible :
      admissible
        SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference)
    (realProfileConstant fourierProfileConstant :
      SchwartzLineTestFunction -> Real)
    (strip_extension_norm_le_real_fourier :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                norm (system.extension f z) <=
                  realProfileConstant f * ‖f z.re‖ +
                    fourierProfileConstant f *
                      ‖(SchwartzLineTestFunction.fourier f) z.re‖) :
    False := by
  let witness :=
    SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifferenceSharedZeroWitness
  exact
    fixedRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
      witness.test
      (realProfileConstant witness.test)
      (fourierProfileConstant witness.test)
      (fun z hlow hhigh =>
        strip_extension_norm_le_real_fourier witness.test hadmissible z hlow hhigh)
      witness.sharedZero witness.nonzeroPoint
      witness.test_sharedZero_eq_zero witness.fourier_sharedZero_eq_zero
      witness.test_nonzero

/--
Fixed-test finite-component no-go form. It converts componentwise pointwise
real/Fourier bounds for one test into the fixed-test profile contradiction.
-/
theorem fixedFiniteComponentRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (f : SchwartzLineTestFunction)
    (component : Index -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant : Index -> Real)
    (strip_extension_eq_component_sum :
      forall z : Complex,
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall z : Complex,
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i z) <=
                realProfileConstant i * ‖f z.re‖ +
                  fourierProfileConstant i *
                    ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (t u : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (hf_nonzero : f u ≠ 0) :
    False := by
  refine
    fixedRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
      (system := system)
      f (Finset.univ.sum realProfileConstant)
      (Finset.univ.sum fourierProfileConstant) ?_ t u
      hf_zero hfourier_zero hf_nonzero
  intro z hlow hhigh
  have hnorm :
      norm (system.extension f z) <=
        Finset.univ.sum fun i : Index => norm (component i z) := by
    rw [strip_extension_eq_component_sum z hlow hhigh]
    exact norm_sum_le Finset.univ (fun i : Index => component i z)
  have hsum :
      (Finset.univ.sum fun i : Index => norm (component i z)) <=
        Finset.univ.sum fun i : Index =>
          realProfileConstant i * ‖f z.re‖ +
            fourierProfileConstant i *
              ‖(SchwartzLineTestFunction.fourier f) z.re‖ :=
    Finset.sum_le_sum fun i _ =>
      component_strip_norm_le_real_fourier i z hlow hhigh
  calc
    norm (system.extension f z)
        <= Finset.univ.sum fun i : Index => norm (component i z) := hnorm
    _ <= Finset.univ.sum fun i : Index =>
          realProfileConstant i * ‖f z.re‖ +
            fourierProfileConstant i *
              ‖(SchwartzLineTestFunction.fourier f) z.re‖ := hsum
    _ = (Finset.univ.sum realProfileConstant) * ‖f z.re‖ +
          (Finset.univ.sum fourierProfileConstant) *
            ‖(SchwartzLineTestFunction.fourier f) z.re‖ := by
      rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]

/--
Restricted-source finite-component no-go form. If a restricted source class
admits the explicit two-bump witness, then the componentwise pointwise
real/Fourier p-series source shape is inconsistent on that class.
-/
theorem restrictedFiniteComponentRealFourierProfileComparison_inconsistent_of_admits_oddTranslatedBumpDifference
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (admissible : SchwartzLineTestFunction -> Prop)
    (hadmissible :
      admissible
        SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference)
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall f : SchwartzLineTestFunction,
        admissible f ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension f z =
                  Finset.univ.sum fun i : Index => component i f z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall f : SchwartzLineTestFunction,
          admissible f ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (component i f z) <=
                    realProfileConstant i f * ‖f z.re‖ +
                      fourierProfileConstant i f *
                        ‖(SchwartzLineTestFunction.fourier f) z.re‖) :
    False := by
  let witness :=
    SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifferenceSharedZeroWitness
  exact
    fixedFiniteComponentRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
      (system := system)
      witness.test
      (fun i z => component i witness.test z)
      (fun i => realProfileConstant i witness.test)
      (fun i => fourierProfileConstant i witness.test)
      (fun z hlow hhigh =>
        strip_extension_eq_component_sum witness.test hadmissible z hlow hhigh)
      (fun i z hlow hhigh =>
        component_strip_norm_le_real_fourier i witness.test hadmissible z hlow hhigh)
      witness.sharedZero witness.nonzeroPoint
      witness.test_sharedZero_eq_zero witness.fourier_sharedZero_eq_zero
      witness.test_nonzero

/--
Source-class finite-component no-go form. If an admissible Guinand-Weil source
test maps to the explicit two-bump Schwartz witness, then source-side
componentwise pointwise real/Fourier strip bounds are inconsistent for that
source class.
-/
theorem sourceFiniteComponentRealFourierProfileComparison_inconsistent_of_mapsTo_oddTranslatedBumpDifference
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (g0 : testData.SourceTestFunction)
    (hg0 : testData.admissible g0)
    (hg0_toSchwartz :
      testData.toSchwartz g0 =
        SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference)
    (component : Index -> testData.SourceTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> testData.SourceTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => component i g z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (component i g z) <=
                    realProfileConstant i g * ‖(testData.toSchwartz g) z.re‖ +
                      fourierProfileConstant i g *
                        ‖(SchwartzLineTestFunction.fourier
                            (testData.toSchwartz g)) z.re‖) :
    False := by
  have hf_zero : testData.toSchwartz g0 (0 : Real) = 0 := by
    simp [hg0_toSchwartz]
  have hfourier_zero :
      (SchwartzLineTestFunction.fourier (testData.toSchwartz g0))
          (0 : Real) = 0 := by
    simpa [hg0_toSchwartz] using
      SchwartzLineTestFunction.fourier_zero_eq_zero_of_integral_eq_zero
        SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference
        SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference_integral_eq_zero
  have hf_nonzero :
      testData.toSchwartz g0 (1 : Real) ≠ 0 := by
    simp [hg0_toSchwartz]
  exact
    fixedFiniteComponentRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
      (system := system)
      (testData.toSchwartz g0)
      (fun i z => component i g0 z)
      (fun i => realProfileConstant i g0)
      (fun i => fourierProfileConstant i g0)
      (fun z hlow hhigh =>
        strip_extension_eq_component_sum g0 hg0 z hlow hhigh)
      (fun i z hlow hhigh =>
        component_strip_norm_le_real_fourier i g0 hg0 z hlow hhigh)
      (0 : Real) (1 : Real)
      hf_zero hfourier_zero hf_nonzero

/--
Source-coverage no-go form. A source class that covers every project Schwartz
test cannot support a finite-component pointwise real/Fourier strip comparison:
coverage supplies a source representative of the explicit two-bump witness.
-/
theorem sourceCoverageFiniteComponentRealFourierProfileComparison_inconsistent
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (testData : GuinandWeilSourceTestFunctionClass)
    (coversSchwartz :
      forall f : SchwartzLineTestFunction,
        exists g : testData.SourceTestFunction,
          testData.admissible g /\ testData.toSchwartz g = f)
    (component : Index -> testData.SourceTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> testData.SourceTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall z : Complex,
            -(1 / 2 : Real) <= z.im ->
              z.im <= (1 / 2 : Real) ->
                system.extension (testData.toSchwartz g) z =
                  Finset.univ.sum fun i : Index => component i g z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall g : testData.SourceTestFunction,
          testData.admissible g ->
            forall z : Complex,
              -(1 / 2 : Real) <= z.im ->
                z.im <= (1 / 2 : Real) ->
                  norm (component i g z) <=
                    realProfileConstant i g * ‖(testData.toSchwartz g) z.re‖ +
                      fourierProfileConstant i g *
                        ‖(SchwartzLineTestFunction.fourier
                            (testData.toSchwartz g)) z.re‖) :
    False := by
  classical
  let witnessTest :=
    SchwartzSharedRealFourierZeroNonzeroWitness.oddTranslatedBumpDifference
  let g0 : testData.SourceTestFunction :=
    Classical.choose (coversSchwartz witnessTest)
  have hg0_pair := Classical.choose_spec (coversSchwartz witnessTest)
  exact
    sourceFiniteComponentRealFourierProfileComparison_inconsistent_of_mapsTo_oddTranslatedBumpDifference
      (system := system)
      testData g0 hg0_pair.1 hg0_pair.2
      component realProfileConstant fourierProfileConstant
      strip_extension_eq_component_sum component_strip_norm_le_real_fourier

/--
Finite-component version of the two-profile obstruction.

This attacks the componentwise p-series target directly: if every component is
pointwise controlled by the two values `f z.re` and `Fourier f z.re`, and the
extension is the finite sum of those components on the horizontal strip, then a
shared real zero of `f` and `Fourier f` forces the whole vertical strip segment
of the extension to vanish.
-/
theorem finiteComponentRealFourierProfileComparison_forces_verticalLine_zero_of_shared_zero
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) <=
                realProfileConstant i f * ‖f z.re‖ +
                  fourierProfileConstant i f *
                    ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t y : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (hy_low : -(1 / 2 : Real) <= y)
    (hy_high : y <= (1 / 2 : Real)) :
    system.extension f ((t : Complex) + (y : Complex) * Complex.I) = 0 := by
  let z : Complex := (t : Complex) + (y : Complex) * Complex.I
  have hz_re : z.re = t := by
    simp [z]
  have hz_im : z.im = y := by
    simp [z]
  have hcomponent_zero :
      forall i : Index, component i f z = 0 := by
    intro i
    have hdom := component_strip_norm_le_real_fourier i f z
      (by simpa [hz_im] using hy_low)
      (by simpa [hz_im] using hy_high)
    have hrhs_zero :
        realProfileConstant i f * ‖f z.re‖ +
            fourierProfileConstant i f *
              ‖(SchwartzLineTestFunction.fourier f) z.re‖ = 0 := by
      simp [hz_re, hf_zero, hfourier_zero]
    have hnorm_le_zero : norm (component i f z) <= 0 := by
      simpa [hrhs_zero] using hdom
    have hnorm_zero : norm (component i f z) = 0 :=
      le_antisymm hnorm_le_zero (norm_nonneg _)
    exact norm_eq_zero.mp hnorm_zero
  have hsum_zero :
      (Finset.univ.sum fun i : Index => component i f z) = 0 := by
    exact Finset.sum_eq_zero fun i _ => hcomponent_zero i
  have hsum := strip_extension_eq_component_sum f z
    (by simpa [hz_im] using hy_low)
    (by simpa [hz_im] using hy_high)
  simpa [z] using hsum.trans hsum_zero

/--
Analytic-continuation form of the finite-component obstruction: the
componentwise real/Fourier pointwise strip target is degenerate on any test
with a shared real zero of `f` and `Fourier f`.
-/
theorem finiteComponentRealFourierProfileComparison_forces_extension_eq_zero_of_shared_zero
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) <=
                realProfileConstant i f * ‖f z.re‖ +
                  fourierProfileConstant i f *
                    ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0) :
    system.extension f = 0 := by
  let verticalPath : Real -> Complex :=
    fun y => (t : Complex) + (y : Complex) * Complex.I
  have hvertical_zero :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        system.extension f (verticalPath y) = 0 := by
    have hupper :
        {y : Real | y < (1 / 2 : Real)} ∈ 𝓝[>] (0 : Real) :=
      mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (by norm_num : (0 : Real) < 1 / 2))
    filter_upwards [self_mem_nhdsWithin, hupper] with y hy_pos hy_upper
    exact
      finiteComponentRealFourierProfileComparison_forces_verticalLine_zero_of_shared_zero
        component realProfileConstant fourierProfileConstant
        strip_extension_eq_component_sum component_strip_norm_le_real_fourier
        f t y hf_zero hfourier_zero
        (by
          have hy_pos' : 0 < y := hy_pos
          linarith)
        (le_of_lt hy_upper)
  have hvertical_tendsto_nhds :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝 (t : Complex)) := by
    have hofReal :
        Filter.Tendsto (fun y : Real => (y : Complex))
          (𝓝 (0 : Real)) (𝓝 (0 : Complex)) :=
      Complex.continuous_ofReal.tendsto 0
    have hfull :
        Filter.Tendsto verticalPath (𝓝 (0 : Real)) (𝓝 (t : Complex)) := by
      simpa [verticalPath] using
        (tendsto_const_nhds.add (hofReal.mul tendsto_const_nhds))
    exact tendsto_nhdsWithin_of_tendsto_nhds hfull
  have hvertical_eventually_ne :
      ∀ᶠ y in 𝓝[>] (0 : Real),
        verticalPath y ∈ ({z : Complex | z ≠ (t : Complex)} : Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with y hy_pos
    intro h_eq
    have him :
        (verticalPath y).im = ((t : Complex)).im := by
      rw [h_eq]
    have hy_zero : y = 0 := by
      simpa [verticalPath] using him
    have hy_pos' : 0 < y := hy_pos
    linarith
  have hvertical_tendsto_ne :
      Filter.Tendsto verticalPath (𝓝[>] (0 : Real)) (𝓝[≠] (t : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      verticalPath hvertical_tendsto_nhds hvertical_eventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] (t : Complex), system.extension f z = 0 :=
    hvertical_tendsto_ne.frequently hvertical_zero.frequently
  exact extension_eq_zero_of_frequently_zero_near
    (system := system) f (t : Complex) hfreq

/--
Real-line consequence of the finite-component two-profile obstruction.
-/
theorem finiteComponentRealFourierProfileComparison_forces_realLine_eq_zero_of_shared_zero
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) <=
                realProfileConstant i f * ‖f z.re‖ +
                  fourierProfileConstant i f *
                    ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (u : Real) :
    f u = 0 := by
  have hglobal :=
    finiteComponentRealFourierProfileComparison_forces_extension_eq_zero_of_shared_zero
      component realProfileConstant fourierProfileConstant
      strip_extension_eq_component_sum component_strip_norm_le_real_fourier
      f t hf_zero hfourier_zero
  have hvalue : system.extension f (u : Complex) = 0 := by
    simpa using congrFun hglobal (u : Complex)
  simpa [system.extension_restricts f u] using hvalue

/--
No-go form of the finite-component obstruction. It is the theorem-facing
version of the warning in the blocker plan: the full-class pointwise
componentwise `f`/`Fourier f` strip estimate cannot coexist with a nonzero
Schwartz test that has a shared real/Fourier zero.
-/
theorem finiteComponentRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) <=
                realProfileConstant i f * ‖f z.re‖ +
                  fourierProfileConstant i f *
                    ‖(SchwartzLineTestFunction.fourier f) z.re‖)
    (f : SchwartzLineTestFunction)
    (t u : Real)
    (hf_zero : f t = 0)
    (hfourier_zero : (SchwartzLineTestFunction.fourier f) t = 0)
    (hf_nonzero : f u ≠ 0) :
    False := by
  exact hf_nonzero
    (finiteComponentRealFourierProfileComparison_forces_realLine_eq_zero_of_shared_zero
      component realProfileConstant fourierProfileConstant
      strip_extension_eq_component_sum component_strip_norm_le_real_fourier
      f t hf_zero hfourier_zero u)

namespace SchwartzSharedRealFourierZeroNonzeroWitness

/--
The same witness contradicts the full-class finite-component pointwise
real/Fourier profile comparison.
-/
theorem contradicts_finiteComponentRealFourierProfileComparison
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (witness : SchwartzSharedRealFourierZeroNonzeroWitness)
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) <=
                realProfileConstant i f * ‖f z.re‖ +
                  fourierProfileConstant i f *
                    ‖(SchwartzLineTestFunction.fourier f) z.re‖) :
    False :=
  finiteComponentRealFourierProfileComparison_inconsistent_of_shared_zero_nonzero
    component realProfileConstant fourierProfileConstant
    strip_extension_eq_component_sum component_strip_norm_le_real_fourier
    witness.test witness.sharedZero witness.nonzeroPoint
    witness.test_sharedZero_eq_zero witness.fourier_sharedZero_eq_zero
    witness.test_nonzero

/--
The explicit bump-difference witness contradicts any full-class
finite-component pointwise real/Fourier profile comparison.
-/
theorem oddTranslatedBumpDifference_contradicts_finiteComponentRealFourierProfileComparison
    {Index : Type*} [Fintype Index]
    {system : SchwartzRiemannWeilExtensionSystem}
    (component : Index -> SchwartzLineTestFunction -> Complex -> Complex)
    (realProfileConstant fourierProfileConstant :
      Index -> SchwartzLineTestFunction -> Real)
    (strip_extension_eq_component_sum :
      forall (f : SchwartzLineTestFunction) (z : Complex),
        -(1 / 2 : Real) <= z.im ->
          z.im <= (1 / 2 : Real) ->
            system.extension f z =
              Finset.univ.sum fun i : Index => component i f z)
    (component_strip_norm_le_real_fourier :
      forall i : Index,
        forall (f : SchwartzLineTestFunction) (z : Complex),
          -(1 / 2 : Real) <= z.im ->
            z.im <= (1 / 2 : Real) ->
              norm (component i f z) <=
                realProfileConstant i f * ‖f z.re‖ +
                  fourierProfileConstant i f *
                    ‖(SchwartzLineTestFunction.fourier f) z.re‖) :
    False :=
  oddTranslatedBumpDifferenceSharedZeroWitness
    |>.contradicts_finiteComponentRealFourierProfileComparison
      component realProfileConstant fourierProfileConstant
      strip_extension_eq_component_sum component_strip_norm_le_real_fourier

end SchwartzSharedRealFourierZeroNonzeroWitness

namespace RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate

/--
An admissible source test whose project Schwartz image has real zeroes
accumulating at a real point must be the zero test under an entire
source-extension system.

This is the quasianalyticity obstruction behind the cutoff no-go: a nonzero
source image for an entire restriction cannot have an accumulating real zero
set.
-/
theorem sourceExtension_toSchwartz_eq_zero_of_frequently_zero_near_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (t : Real)
    (hfreq_real :
      ∃ᶠ x in 𝓝[≠] t, testData.toSchwartz g x = 0) :
    testData.toSchwartz g = 0 := by
  let f : SchwartzLineTestFunction := testData.toSchwartz g
  have hsource_zero :
      ∃ᶠ x in 𝓝[≠] t,
        sourceSystem.extension g (((x : Real) : Complex)) = 0 :=
    hfreq_real.mono fun x hx_zero => by
      calc
        sourceSystem.extension g (((x : Real) : Complex)) =
            testData.toSchwartz g x :=
          sourceSystem.extension_restricts g hg x
        _ = 0 := hx_zero
  have htendsto_nhds :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[≠] t : Filter Real) (𝓝 ((t : Real) : Complex)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (Complex.continuous_ofReal.tendsto t)
  have heventually_ne :
      ∀ᶠ x in (𝓝[≠] t : Filter Real),
        (((x : Real) : Complex)) ∈
          ({z : Complex | z ≠ ((t : Real) : Complex)} :
          Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro h_eq
    exact hx (Complex.ofReal_injective h_eq)
  have htendsto_ne :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[≠] t : Filter Real) (𝓝[≠] ((t : Real) : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun x : Real => (x : Complex)) htendsto_nhds heventually_ne
  have hfreq_complex :
      ∃ᶠ z in 𝓝[≠] ((t : Real) : Complex),
        sourceSystem.extension g z = 0 :=
    htendsto_ne.frequently hsource_zero
  have hglobal :
      sourceSystem.extension g = 0 :=
    differentiableFunction_eq_zero_of_frequently_zero_near
      (sourceSystem.extension_differentiable g hg)
      ((t : Real) : Complex) hfreq_complex
  ext x
  have hvalue : sourceSystem.extension g ((x : Real) : Complex) = 0 := by
    simpa using congrFun hglobal ((x : Real) : Complex)
  have hrestrict :=
    sourceSystem.extension_restricts g hg x
  rw [hrestrict] at hvalue
  simpa [f] using hvalue

/--
A nonzero admissible source image for an entire source-extension system has no
real zeroes frequent in a punctured neighborhood of any real point.

This is the contrapositive form needed when choosing the actual 80% source
class: every nonzero admitted real-axis restriction must avoid accumulating
real zeroes.
-/
theorem sourceExtension_toSchwartz_ne_zero_not_frequently_zero_near_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hne : testData.toSchwartz g ≠ 0)
    (t : Real) :
    ¬ (∃ᶠ x in 𝓝[≠] t, testData.toSchwartz g x = 0) := by
  intro hfreq_real
  exact hne
    (sourceExtension_toSchwartz_eq_zero_of_frequently_zero_near_real
      testData sourceSystem g hg t hfreq_real)

/--
An admissible source test whose project Schwartz image vanishes on a real set
that is frequent in a punctured neighborhood of a real point must be the zero
test under an entire source-extension system.

This is the set form of the quasianalyticity obstruction. It packages intervals,
zero sequences, and other accumulating real zero sets behind the same
neighborhood-filter hypothesis.
-/
theorem sourceExtension_toSchwartz_eq_zero_of_zero_on_frequently_near_real_set
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (s : Set Real)
    (t : Real)
    (hs_frequently :
      ∃ᶠ x in 𝓝[≠] t, x ∈ s)
    (hzero_on :
      forall x : Real, x ∈ s -> testData.toSchwartz g x = 0) :
    testData.toSchwartz g = 0 := by
  have hfreq_real :
      ∃ᶠ x in 𝓝[≠] t, testData.toSchwartz g x = 0 :=
    hs_frequently.mono fun x hx => hzero_on x hx
  exact
    sourceExtension_toSchwartz_eq_zero_of_frequently_zero_near_real
      testData sourceSystem g hg t hfreq_real

/--
A nonzero admissible source image for an entire source-extension system cannot
vanish on any real set frequent in a punctured real neighborhood.

This rules out source normalizations whose nonzero members acquire a real
zero set with a real accumulation point, including intervals and convergent
zero sequences.
-/
theorem sourceExtension_toSchwartz_ne_zero_no_frequent_real_zero_set
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hne : testData.toSchwartz g ≠ 0)
    (s : Set Real)
    (t : Real)
    (hzero_on :
      forall x : Real, x ∈ s -> testData.toSchwartz g x = 0) :
    ¬ (∃ᶠ x in 𝓝[≠] t, x ∈ s) := by
  intro hs_frequently
  exact hne
    (sourceExtension_toSchwartz_eq_zero_of_zero_on_frequently_near_real_set
      testData sourceSystem g hg s t hs_frequently hzero_on)

/--
An admissible source test whose project Schwartz image vanishes along a real
sequence accumulating at a real point must be the zero test under an entire
source-extension system.

This is the sequence form of the quasianalyticity obstruction: a nonzero real
restriction of an entire source function cannot have a convergent sequence of
distinct real zeroes.
-/
theorem sourceExtension_toSchwartz_eq_zero_of_zero_sequence_tendsto_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (u : Nat -> Real)
    (t : Real)
    (hu_tendsto : Filter.Tendsto u Filter.atTop (𝓝 t))
    (hu_ne :
      ∀ᶠ n in Filter.atTop, u n ≠ t)
    (hzero_seq :
      ∀ᶠ n in Filter.atTop, testData.toSchwartz g (u n) = 0) :
    testData.toSchwartz g = 0 := by
  have hu_tendsto_ne :
      Filter.Tendsto u Filter.atTop (𝓝[≠] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      u hu_tendsto (by simpa using hu_ne)
  have hfreq_real :
      ∃ᶠ x in 𝓝[≠] t, testData.toSchwartz g x = 0 :=
    hu_tendsto_ne.frequently hzero_seq.frequently
  exact
    sourceExtension_toSchwartz_eq_zero_of_frequently_zero_near_real
      testData sourceSystem g hg t hfreq_real

/--
A nonzero admissible source image for an entire source-extension system cannot
vanish eventually along a sequence of real points tending to a distinct real
limit.
-/
theorem sourceExtension_toSchwartz_ne_zero_no_zero_sequence_tendsto_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hne : testData.toSchwartz g ≠ 0)
    (u : Nat -> Real)
    (t : Real)
    (hu_tendsto : Filter.Tendsto u Filter.atTop (𝓝 t))
    (hu_ne :
      ∀ᶠ n in Filter.atTop, u n ≠ t)
    (hzero_seq :
      ∀ᶠ n in Filter.atTop, testData.toSchwartz g (u n) = 0) :
    False := by
  exact hne
    (sourceExtension_toSchwartz_eq_zero_of_zero_sequence_tendsto_real
      testData sourceSystem g hg u t hu_tendsto hu_ne hzero_seq)

/--
An admissible source test whose project Schwartz image vanishes on a nonempty
real interval must be the zero test under an entire source-extension system.

This is the no-gap form of the quasianalyticity obstruction: a nonzero real
restriction of an entire source function cannot have an open interval of
vanishing.
-/
theorem sourceExtension_toSchwartz_eq_zero_of_eq_zero_on_Ioo
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    {a b : Real}
    (hab : a < b)
    (hzero_Ioo :
      forall x : Real, x ∈ Set.Ioo a b -> testData.toSchwartz g x = 0) :
    testData.toSchwartz g = 0 := by
  have hzero_right :
      ∀ᶠ x in (𝓝[>] a : Filter Real), testData.toSchwartz g x = 0 := by
    have hupper :
        {x : Real | x < b} ∈ (𝓝[>] a : Filter Real) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hab)
    filter_upwards [self_mem_nhdsWithin, hupper] with x hx_gt hx_lt
    exact hzero_Ioo x ⟨hx_gt, hx_lt⟩
  have htendsto_nhds :
      Filter.Tendsto (fun x : Real => x)
        (𝓝[>] a : Filter Real) (𝓝 a) :=
    tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto a)
  have heventually_ne :
      ∀ᶠ x in (𝓝[>] a : Filter Real),
        x ∈ ({x : Real | x ≠ a} : Set Real) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ne_of_gt hx
  have htendsto_ne :
      Filter.Tendsto (fun x : Real => x)
        (𝓝[>] a : Filter Real) (𝓝[≠] a) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun x : Real => x) htendsto_nhds heventually_ne
  have hfreq_real :
      ∃ᶠ x in 𝓝[≠] a, testData.toSchwartz g x = 0 :=
    htendsto_ne.frequently hzero_right.frequently
  exact
    sourceExtension_toSchwartz_eq_zero_of_frequently_zero_near_real
      testData sourceSystem g hg a hfreq_real

/--
A nonzero admissible source image for an entire source-extension system cannot
vanish on a nonempty open real interval.
-/
theorem sourceExtension_toSchwartz_ne_zero_no_eq_zero_on_Ioo
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hne : testData.toSchwartz g ≠ 0)
    {a b : Real}
    (hab : a < b)
    (hzero_Ioo :
      forall x : Real, x ∈ Set.Ioo a b -> testData.toSchwartz g x = 0) :
    False := by
  exact hne
    (sourceExtension_toSchwartz_eq_zero_of_eq_zero_on_Ioo
      testData sourceSystem g hg hab hzero_Ioo)

/--
An admissible source test whose project Schwartz image is eventually zero on
the positive real ray must be the zero test under an entire source-extension
system.

The reason is exact, not asymptotic: a real ray of zeroes accumulates at a real
point from within the complex plane, hence analytic continuation forces the
entire extension to vanish everywhere, and the real-axis restriction forces the
source image itself to vanish.
-/
theorem sourceExtension_toSchwartz_eq_zero_of_eventually_zero_atTop
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hzero_atTop :
      ∀ᶠ x in Filter.atTop, testData.toSchwartz g x = 0) :
    testData.toSchwartz g = 0 := by
  let f : SchwartzLineTestFunction := testData.toSchwartz g
  have hzero_atTop_eventually :
      ∀ᶠ x in Filter.atTop, f x = 0 := by
    simpa [f] using hzero_atTop
  rw [Filter.eventually_atTop] at hzero_atTop_eventually
  obtain ⟨R, hR⟩ := hzero_atTop_eventually
  have hreal_zero :
      ∀ᶠ x in (𝓝[>] R : Filter Real),
        sourceSystem.extension g (((x : Real) : Complex)) = 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx_ge : R <= x := le_of_lt hx
    have hf_zero : f x = 0 := hR x hx_ge
    calc
      sourceSystem.extension g (((x : Real) : Complex)) =
          testData.toSchwartz g x :=
        sourceSystem.extension_restricts g hg x
      _ = f x := rfl
      _ = 0 := hf_zero
  have htendsto_nhds :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[>] R : Filter Real) (𝓝 ((R : Real) : Complex)) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds
      (Complex.continuous_ofReal.tendsto R)
  have heventually_ne :
      ∀ᶠ x in (𝓝[>] R : Filter Real),
        (((x : Real) : Complex)) ∈
          ({z : Complex | z ≠ ((R : Real) : Complex)} :
          Set Complex) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    intro h_eq
    have hx_eq : x = R := Complex.ofReal_injective h_eq
    have hx_gt : R < x := hx
    linarith
  have htendsto_ne :
      Filter.Tendsto (fun x : Real => (x : Complex))
        (𝓝[>] R : Filter Real) (𝓝[≠] ((R : Real) : Complex)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (fun x : Real => (x : Complex)) htendsto_nhds heventually_ne
  have hfreq :
      ∃ᶠ z in 𝓝[≠] ((R : Real) : Complex),
        sourceSystem.extension g z = 0 :=
    htendsto_ne.frequently hreal_zero.frequently
  have hglobal :
      sourceSystem.extension g = 0 :=
    differentiableFunction_eq_zero_of_frequently_zero_near
      (sourceSystem.extension_differentiable g hg)
      ((R : Real) : Complex) hfreq
  ext x
  have hvalue : sourceSystem.extension g ((x : Real) : Complex) = 0 := by
    simpa using congrFun hglobal ((x : Real) : Complex)
  have hrestrict :=
    sourceSystem.extension_restricts g hg x
  rw [hrestrict] at hvalue
  simpa [f] using hvalue

/--
An admissible source test whose project Schwartz image is compactly supported
must be the zero test under an entire source-extension system.

Compact support supplies eventual zeroes on the positive real ray, so this is
the compact-support corollary of the one-sided real-ray obstruction.
-/
theorem sourceExtension_toSchwartz_eq_zero_of_hasCompactSupport
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hcompact : HasCompactSupport (testData.toSchwartz g)) :
    testData.toSchwartz g = 0 := by
  let f : SchwartzLineTestFunction := testData.toSchwartz g
  have hzero_cocompact :
      f =ᶠ[Filter.cocompact Real] 0 := by
    have hzero_coclosed :
        f =ᶠ[Filter.coclosedCompact Real] 0 :=
      hasCompactSupport_iff_eventuallyEq.mp hcompact
    simpa [f, Filter.coclosedCompact_eq_cocompact] using hzero_coclosed
  have hzero_atTop_f :
      f =ᶠ[Filter.atTop] 0 :=
    hzero_cocompact.filter_mono atTop_le_cocompact
  have hzero_atTop :
      ∀ᶠ x in Filter.atTop, testData.toSchwartz g x = 0 := by
    filter_upwards [hzero_atTop_f] with x hx
    simpa [f] using hx
  exact
    sourceExtension_toSchwartz_eq_zero_of_eventually_zero_atTop
      testData sourceSystem g hg hzero_atTop

/--
A nonzero admissible source image for an entire source-extension system cannot
be eventually zero on the positive real ray.
-/
theorem sourceExtension_toSchwartz_ne_zero_no_eventually_zero_atTop
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hne : testData.toSchwartz g ≠ 0)
    (hzero_atTop :
      ∀ᶠ x in Filter.atTop, testData.toSchwartz g x = 0) :
    False := by
  exact hne
    (sourceExtension_toSchwartz_eq_zero_of_eventually_zero_atTop
      testData sourceSystem g hg hzero_atTop)

/--
A nonzero admissible source image for an entire source-extension system cannot
be compactly supported on the real line.
-/
theorem sourceExtension_toSchwartz_ne_zero_no_hasCompactSupport
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (g : testData.SourceTestFunction)
    (hg : testData.admissible g)
    (hne : testData.toSchwartz g ≠ 0)
    (hcompact : HasCompactSupport (testData.toSchwartz g)) :
    False := by
  exact hne
    (sourceExtension_toSchwartz_eq_zero_of_hasCompactSupport
      testData sourceSystem g hg hcompact)

/--
A dense admissible source image cannot lie in the kernel of a nonzero
continuous complex-linear map.

This packages the closed-hyperplane obstruction behind many candidate source
conditions: pointwise values, moments, finite jets, vector-valued constraint
bundles, and similar continuous linear tests cannot vanish on a dense
admissible source image unless the test operator itself is zero.
-/
theorem no_dense_sourceImage_continuousLinearMap_kernel
    {ConstraintSpace : Type*}
    [NormedAddCommGroup ConstraintSpace]
    [NormedSpace Complex ConstraintSpace]
    (testData : GuinandWeilSourceTestFunctionClass)
    (operator : SchwartzLineTestFunction →L[Complex] ConstraintSpace)
    (operator_ne_zero : operator ≠ 0)
    (admissible_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> operator (testData.toSchwartz g) = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  have himage_subset_kernel :
      guinandWeilAdmissibleSchwartzImage testData ⊆
        {f : SchwartzLineTestFunction | operator f = 0} := by
    intro f hf
    rcases hf with ⟨g, hg, hgf⟩
    rw [← hgf]
    exact admissible_zero g hg
  have hkernel_closed :
      IsClosed {f : SchwartzLineTestFunction | operator f = 0} := by
    simpa using
      isClosed_eq operator.continuous continuous_const
  have hclosure_subset_kernel :
      closure (guinandWeilAdmissibleSchwartzImage testData) ⊆
        {f : SchwartzLineTestFunction | operator f = 0} :=
    closure_minimal himage_subset_kernel hkernel_closed
  have hoperator_zero : operator = 0 := by
    ext f
    have hf_closure :
        f ∈ closure (guinandWeilAdmissibleSchwartzImage testData) := by
      rw [dense_admissible_image]
      exact Set.mem_univ f
    simpa using hclosure_subset_kernel hf_closure
  exact operator_ne_zero hoperator_zero

/--
A dense admissible source image cannot lie in a fixed affine level set of a
nonzero continuous complex-linear map.

This is the fixed-normalization version of the closed-hyperplane obstruction:
requiring every admissible test to have the same nonzero value under a
continuous linear observable is already incompatible with density in the full
Schwartz space.
-/
theorem no_dense_sourceImage_continuousLinearMap_constant
    {ConstraintSpace : Type*}
    [NormedAddCommGroup ConstraintSpace]
    [NormedSpace Complex ConstraintSpace]
    (testData : GuinandWeilSourceTestFunctionClass)
    (operator : SchwartzLineTestFunction →L[Complex] ConstraintSpace)
    (operator_ne_zero : operator ≠ 0)
    (constant : ConstraintSpace)
    (admissible_constant :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> operator (testData.toSchwartz g) = constant)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  have himage_subset_level :
      guinandWeilAdmissibleSchwartzImage testData ⊆
        {f : SchwartzLineTestFunction | operator f = constant} := by
    intro f hf
    rcases hf with ⟨g, hg, hgf⟩
    rw [← hgf]
    exact admissible_constant g hg
  have hlevel_closed :
      IsClosed {f : SchwartzLineTestFunction | operator f = constant} := by
    simpa using
      isClosed_eq operator.continuous continuous_const
  have hclosure_subset_level :
      closure (guinandWeilAdmissibleSchwartzImage testData) ⊆
        {f : SchwartzLineTestFunction | operator f = constant} :=
    closure_minimal himage_subset_level hlevel_closed
  have hoperator_constant :
      forall f : SchwartzLineTestFunction, operator f = constant := by
    intro f
    have hf_closure :
        f ∈ closure (guinandWeilAdmissibleSchwartzImage testData) := by
      rw [dense_admissible_image]
      exact Set.mem_univ f
    exact hclosure_subset_level hf_closure
  have hconstant_zero : constant = 0 := by
    have hzero :
        operator (0 : SchwartzLineTestFunction) = constant :=
      hoperator_constant 0
    simpa using hzero.symm
  have hoperator_zero : operator = 0 := by
    ext f
    exact (hoperator_constant f).trans hconstant_zero
  exact operator_ne_zero hoperator_zero

/--
A dense admissible source image cannot lie in the kernel of a nonzero
continuous complex-linear functional.
-/
theorem no_dense_sourceImage_linearFunctional_vanishes
    (testData : GuinandWeilSourceTestFunctionClass)
    (functional : SchwartzLineTestFunction →L[Complex] Complex)
    (functional_ne_zero : functional ≠ 0)
    (admissible_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> functional (testData.toSchwartz g) = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_continuousLinearMap_kernel testData functional
    functional_ne_zero admissible_zero dense_admissible_image

/--
A dense admissible source image cannot force a nonzero continuous complex-linear
functional to take one fixed value on every admissible source test.
-/
theorem no_dense_sourceImage_linearFunctional_constant
    (testData : GuinandWeilSourceTestFunctionClass)
    (functional : SchwartzLineTestFunction →L[Complex] Complex)
    (functional_ne_zero : functional ≠ 0)
    (constant : Complex)
    (admissible_constant :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> functional (testData.toSchwartz g) = constant)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_continuousLinearMap_constant testData functional
    functional_ne_zero constant admissible_constant dense_admissible_image

/-- Fixed real-point evaluation is a nonzero continuous linear functional. -/
theorem schwartzLineEvaluationCLM_ne_zero (t : Real) :
    schwartzLineEvaluationCLM t ≠ 0 := by
  intro hzero
  let witness :=
    SchwartzSharedRealFourierZeroNonzeroWitness.centeredUnitBumpSchwartz.compSubConstCLM
      Complex t
  have hwitness_one_at_t : witness t = 1 := by
    simp [witness]
  have hwitness_zero_at_t : witness t = 0 := by
    have hfunctional_zero : schwartzLineEvaluationCLM t witness = 0 := by
      rw [hzero]
      rfl
    simpa using hfunctional_zero
  exact one_ne_zero
    (hwitness_one_at_t.symm.trans hwitness_zero_at_t)

/--
A dense admissible source image cannot force every admissible test to have the
same fixed value at a fixed real point.
-/
theorem no_dense_sourceImage_has_fixed_value_at_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (t : Real)
    (constant : Complex)
    (admissible_value :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> testData.toSchwartz g t = constant)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_linearFunctional_constant testData
    (schwartzLineEvaluationCLM t) (schwartzLineEvaluationCLM_ne_zero t)
    constant
    (by
      intro g hg
      simpa using admissible_value g hg)
    dense_admissible_image

/-- Fixed real-frequency Fourier evaluation is a nonzero continuous linear
functional. -/
theorem schwartzLineFourierEvaluationCLM_ne_zero (t : Real) :
    schwartzLineFourierEvaluationCLM t ≠ 0 := by
  intro hzero
  let witness :=
    SchwartzLineTestFunction.fourierInv
      (SchwartzSharedRealFourierZeroNonzeroWitness.centeredUnitBumpSchwartz.compSubConstCLM
        Complex t)
  have hwitness_one_at_t :
      (SchwartzLineTestFunction.fourier witness) t = 1 := by
    simp [witness, SchwartzLineTestFunction.fourier,
      SchwartzLineTestFunction.fourierInv]
  have hwitness_zero_at_t :
      (SchwartzLineTestFunction.fourier witness) t = 0 := by
    have hfunctional_zero :
        schwartzLineFourierEvaluationCLM t witness = 0 := by
      rw [hzero]
      rfl
    simpa using hfunctional_zero
  exact one_ne_zero
    (hwitness_one_at_t.symm.trans hwitness_zero_at_t)

/--
A dense admissible source image cannot force every admissible test to have the
same fixed Fourier value at a fixed real frequency.
-/
theorem no_dense_sourceImage_fourier_has_fixed_value_at_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (t : Real)
    (constant : Complex)
    (admissible_fourier_value :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          (SchwartzLineTestFunction.fourier (testData.toSchwartz g)) t =
            constant)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_linearFunctional_constant testData
    (schwartzLineFourierEvaluationCLM t)
    (schwartzLineFourierEvaluationCLM_ne_zero t) constant
    (by
      intro g hg
      simpa using admissible_fourier_value g hg)
    dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to vanish at
any fixed real point.

This is a basic density obstruction for candidate 80% source classes: any
common real-line vanishing condition defines a closed proper evaluation
hyperplane, so it cannot contain a dense source image.
-/
theorem no_dense_sourceImage_vanishes_at_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (t : Real)
    (admissible_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> testData.toSchwartz g t = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_linearFunctional_vanishes testData
    (schwartzLineEvaluationCLM t) (schwartzLineEvaluationCLM_ne_zero t)
    (by
      intro g hg
      simpa using admissible_zero g hg)
    dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to vanish at
the real origin.
-/
theorem no_dense_sourceImage_vanishes_at_zero
    (testData : GuinandWeilSourceTestFunctionClass)
    (admissible_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> testData.toSchwartz g (0 : Real) = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_vanishes_at_real testData (0 : Real)
    admissible_zero dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to have the
same fixed value on a nonempty open real interval.

This rules out common flat real-line bands as dense full-Schwartz source
classes, including the zero-value/gap case below.
-/
theorem no_dense_sourceImage_has_fixed_value_on_real_Ioo
    (testData : GuinandWeilSourceTestFunctionClass)
    {a b : Real} (hab : a < b)
    (constant : Complex)
    (admissible_value :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall t : Real, t ∈ Set.Ioo a b ->
            testData.toSchwartz g t = constant)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  let mid : Real := (a + b) / 2
  have hmid : mid ∈ Set.Ioo a b := by
    have htwo_pos : (0 : Real) < 2 := by norm_num
    constructor <;> dsimp [mid] <;> linarith
  exact
    no_dense_sourceImage_has_fixed_value_at_real testData mid constant
      (by
        intro g hg
        exact admissible_value g hg mid hmid)
      dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to vanish on
a common nonempty open real interval.
-/
theorem no_dense_sourceImage_vanishes_on_real_Ioo
    (testData : GuinandWeilSourceTestFunctionClass)
    {a b : Real} (hab : a < b)
    (admissible_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall t : Real, t ∈ Set.Ioo a b -> testData.toSchwartz g t = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_has_fixed_value_on_real_Ioo testData hab 0
    admissible_zero dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to have a
Fourier zero at any fixed real frequency.

This is the Fourier-side closed-hyperplane obstruction for candidate 80%
source classes: imposing a common Fourier-frequency zero on all admissible
source images is incompatible with density in the project Schwartz space.
-/
theorem no_dense_sourceImage_fourier_vanishes_at_real
    (testData : GuinandWeilSourceTestFunctionClass)
    (t : Real)
    (admissible_fourier_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          (SchwartzLineTestFunction.fourier (testData.toSchwartz g)) t = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_linearFunctional_vanishes testData
    (schwartzLineFourierEvaluationCLM t)
    (schwartzLineFourierEvaluationCLM_ne_zero t)
    (by
      intro g hg
      simpa using admissible_fourier_zero g hg)
    dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to have a
Fourier zero at the origin.
-/
theorem no_dense_sourceImage_fourier_vanishes_at_zero
    (testData : GuinandWeilSourceTestFunctionClass)
    (admissible_fourier_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          (SchwartzLineTestFunction.fourier (testData.toSchwartz g))
            (0 : Real) = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_fourier_vanishes_at_real testData (0 : Real)
    admissible_fourier_zero dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to have the
same fixed Fourier value on a nonempty open real-frequency interval.

This rules out common flat Fourier bands as dense full-Schwartz source classes,
including the band-gap case below.
-/
theorem no_dense_sourceImage_fourier_has_fixed_value_on_real_Ioo
    (testData : GuinandWeilSourceTestFunctionClass)
    {a b : Real} (hab : a < b)
    (constant : Complex)
    (admissible_fourier_value :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall t : Real, t ∈ Set.Ioo a b ->
            (SchwartzLineTestFunction.fourier (testData.toSchwartz g)) t =
              constant)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  let mid : Real := (a + b) / 2
  have hmid : mid ∈ Set.Ioo a b := by
    have htwo_pos : (0 : Real) < 2 := by norm_num
    constructor <;> dsimp [mid] <;> linarith
  exact
    no_dense_sourceImage_fourier_has_fixed_value_at_real testData mid constant
      (by
        intro g hg
        exact admissible_fourier_value g hg mid hmid)
      dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to have a
common Fourier gap on a nonempty open real-frequency interval.
-/
theorem no_dense_sourceImage_fourier_vanishes_on_real_Ioo
    (testData : GuinandWeilSourceTestFunctionClass)
    {a b : Real} (hab : a < b)
    (admissible_fourier_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          forall t : Real, t ∈ Set.Ioo a b ->
            (SchwartzLineTestFunction.fourier (testData.toSchwartz g)) t = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_fourier_has_fixed_value_on_real_Ioo testData hab 0
    admissible_fourier_zero dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to have the
same fixed integral.

This catches fixed-mean source normalizations, including nonzero normalizations,
by converting the integral to Fourier evaluation at the origin.
-/
theorem no_dense_sourceImage_integral_has_fixed_value
    (testData : GuinandWeilSourceTestFunctionClass)
    (constant : Complex)
    (admissible_integral_constant :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          (∫ x : Real, testData.toSchwartz g x) = constant)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_fourier_has_fixed_value_at_real testData (0 : Real)
    constant
    (by
      intro g hg
      rw [SchwartzLineTestFunction.fourier_zero_eq_integral]
      exact admissible_integral_constant g hg)
    dense_admissible_image

/--
A dense admissible source image cannot force every admissible test to have zero
integral.

Equivalently, this is the Fourier-origin closed-hyperplane obstruction written
in the source normalization most often used for mean-zero candidate source
classes.
-/
theorem no_dense_sourceImage_integral_vanishes
    (testData : GuinandWeilSourceTestFunctionClass)
    (admissible_integral_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          (∫ x : Real, testData.toSchwartz g x) = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False :=
  no_dense_sourceImage_fourier_vanishes_at_zero testData
    (by
      intro g hg
      exact
        SchwartzLineTestFunction.fourier_zero_eq_zero_of_integral_eq_zero
          (testData.toSchwartz g) (admissible_integral_zero g hg))
    dense_admissible_image

/--
A dense admissible source image cannot consist entirely of real-line
restrictions with zeroes accumulating at some real point if the source tests
carry entire extensions.

This is the quasianalyticity form of the 80% source-choice obstruction:
nonzero admissible source images for an entire restriction must have no
accumulating real zero set.
-/
theorem no_dense_accumulatingRealZeroSourceImage_with_sourceExtensionSystem
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (admissible_accumulating_real_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          exists t : Real,
            ∃ᶠ x in 𝓝[≠] t, testData.toSchwartz g x = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  exact
    no_dense_sourceImage_vanishes_at_zero testData
      (by
        intro g hg
        rcases admissible_accumulating_real_zero g hg with
          ⟨t, hfreq_real⟩
        have hzero :
            testData.toSchwartz g = 0 :=
          sourceExtension_toSchwartz_eq_zero_of_frequently_zero_near_real
            testData sourceSystem g hg t hfreq_real
        simp [hzero])
      dense_admissible_image

/--
A dense admissible source image cannot consist entirely of real-line
restrictions that vanish on a zero set frequent in some punctured real
neighborhood if the source tests carry entire extensions.

This is the set/filter form of the 80% quasianalyticity source-choice
obstruction. It captures interval gaps, convergent zero sequences, and other
accumulating real zero sets in one dense-source no-go.
-/
theorem no_dense_frequentZeroSetSourceImage_with_sourceExtensionSystem
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (admissible_frequent_zero_set :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          exists s : Set Real,
            exists t : Real,
              (∃ᶠ x in 𝓝[≠] t, x ∈ s) ∧
                forall x : Real,
                  x ∈ s -> testData.toSchwartz g x = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  exact
    no_dense_sourceImage_vanishes_at_zero testData
      (by
        intro g hg
        rcases admissible_frequent_zero_set g hg with
          ⟨s, t, hs_frequently, hzero_on⟩
        have hzero :
            testData.toSchwartz g = 0 :=
          sourceExtension_toSchwartz_eq_zero_of_zero_on_frequently_near_real_set
            testData sourceSystem g hg s t hs_frequently hzero_on
        simp [hzero])
      dense_admissible_image

/--
A dense admissible source image cannot consist entirely of real-line
restrictions with a convergent sequence of distinct real zeroes if the source
tests carry entire extensions.

This is the sequential form of the quasianalyticity obstruction, useful when
the analytic source condition naturally produces a zero sequence rather than a
neighborhood-filter statement.
-/
theorem no_dense_zeroSequenceSourceImage_with_sourceExtensionSystem
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (admissible_zero_sequence :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          exists u : Nat -> Real,
            exists t : Real,
              Filter.Tendsto u Filter.atTop (𝓝 t) ∧
                (∀ᶠ n in Filter.atTop, u n ≠ t) ∧
                  (∀ᶠ n in Filter.atTop,
                    testData.toSchwartz g (u n) = 0))
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  exact
    no_dense_sourceImage_vanishes_at_zero testData
      (by
        intro g hg
        rcases admissible_zero_sequence g hg with
          ⟨u, t, hu_tendsto, hu_ne, hzero_seq⟩
        have hzero :
            testData.toSchwartz g = 0 :=
          sourceExtension_toSchwartz_eq_zero_of_zero_sequence_tendsto_real
            testData sourceSystem g hg u t hu_tendsto hu_ne hzero_seq
        simp [hzero])
      dense_admissible_image

/--
A dense admissible source image cannot consist entirely of real-line
restrictions with a nonempty open interval of vanishing if the source tests
carry entire extensions.

This rules out dense source designs built from functions with real gaps: for
an entire source restriction, any such gap forces the whole source image to be
zero.
-/
theorem no_dense_openIntervalZeroSourceImage_with_sourceExtensionSystem
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (admissible_interval_zero :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          exists a b : Real,
            a < b ∧
              forall x : Real,
                x ∈ Set.Ioo a b -> testData.toSchwartz g x = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  exact
    no_dense_sourceImage_vanishes_at_zero testData
      (by
        intro g hg
        rcases admissible_interval_zero g hg with ⟨a, b, hab, hzero_Ioo⟩
        have hzero :
            testData.toSchwartz g = 0 :=
          sourceExtension_toSchwartz_eq_zero_of_eq_zero_on_Ioo
            testData sourceSystem g hg hab hzero_Ioo
        simp [hzero])
      dense_admissible_image

/--
A dense admissible source image cannot consist entirely of real-line
restrictions that are eventually zero on the positive ray if the source tests
carry entire extensions.

This is a broader source-choice obstruction than compact support: one-sided
cutoffs already force every admissible source image to vanish by analytic
continuation, so a dense source image cannot be built from them.
-/
theorem no_dense_eventuallyZeroAtTopSourceImage_with_sourceExtensionSystem
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (admissible_eventually_zero_atTop :
      forall g : testData.SourceTestFunction,
        testData.admissible g ->
          ∀ᶠ x in Filter.atTop, testData.toSchwartz g x = 0)
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  exact
    no_dense_sourceImage_vanishes_at_zero testData
      (by
        intro g hg
        have hzero :
            testData.toSchwartz g = 0 :=
          sourceExtension_toSchwartz_eq_zero_of_eventually_zero_atTop
            testData sourceSystem g hg
            (admissible_eventually_zero_atTop g hg)
        simp [hzero])
      dense_admissible_image

/--
A dense admissible source image cannot consist entirely of compactly supported
real-line restrictions if the source tests carry entire extensions.

This is the structural form of the compact-source 80% no-go: compactly
previous theorem forces every source image to vanish, hence to vanish at the
origin.  The zero-at-origin locus is closed by evaluation continuity, but it
does not contain the explicit compact bump.
-/
theorem no_dense_compactSupportedSourceImage_with_sourceExtensionSystem
    (testData : GuinandWeilSourceTestFunctionClass)
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        testData)
    (admissible_compact :
      forall g : testData.SourceTestFunction,
        testData.admissible g -> HasCompactSupport (testData.toSchwartz g))
    (dense_admissible_image :
      closure (guinandWeilAdmissibleSchwartzImage testData) = Set.univ) :
    False := by
  exact
    no_dense_eventuallyZeroAtTopSourceImage_with_sourceExtensionSystem
      testData sourceSystem
      (by
        intro g hg
        let f : SchwartzLineTestFunction := testData.toSchwartz g
        have hzero_cocompact :
            f =ᶠ[Filter.cocompact Real] 0 := by
          have hzero_coclosed :
              f =ᶠ[Filter.coclosedCompact Real] 0 :=
            hasCompactSupport_iff_eventuallyEq.mp (admissible_compact g hg)
          simpa [f, Filter.coclosedCompact_eq_cocompact] using
            hzero_coclosed
        have hzero_atTop_f :
            f =ᶠ[Filter.atTop] 0 :=
          hzero_cocompact.filter_mono atTop_le_cocompact
        filter_upwards [hzero_atTop_f] with x hx
        simpa [f] using hx)
      dense_admissible_image

/--
The compactly supported smooth source class cannot itself carry an entire
source-extension system.

This is the analytic-continuation obstruction behind the 80% source choice:
compactly supported smooth tests are excellent dense approximants, but an
entire function that agrees with a nonzero compactly supported real-line test
would vanish on a real interval and hence everywhere.  Thus the actual
Guinand-Weil source class for off-real zero estimates must be a different
restricted analytic class, not the compact-support proxy used for density.
-/
theorem no_compactlySupportedSmoothLineSourceExtensionSystem
    (sourceSystem :
      SchwartzSharedRealFourierZeroNonzeroWitness.GuinandWeilSourceExtensionSystem
        compactlySupportedSmoothLineSource) :
    False := by
  let f :=
    SchwartzSharedRealFourierZeroNonzeroWitness.centeredUnitBumpSchwartz
  let hf :
      HasCompactSupport f :=
    SchwartzSharedRealFourierZeroNonzeroWitness.centeredUnitBumpSchwartz_hasCompactSupport
  let g : compactlySupportedSmoothLineSource.SourceTestFunction :=
    compactlySupportedSchwartzLineToSource f hf
  have hg_admissible : compactlySupportedSmoothLineSource.admissible g := by
    trivial
  have hg_toSchwartz :
      compactlySupportedSmoothLineSource.toSchwartz g = f := by
    simp [g]
  have hf_zero_at_origin : f (0 : Real) = 0 := by
    have hg_zero :
        compactlySupportedSmoothLineSource.toSchwartz g = 0 :=
      sourceExtension_toSchwartz_eq_zero_of_hasCompactSupport
        compactlySupportedSmoothLineSource sourceSystem g hg_admissible
        (by simpa [hg_toSchwartz] using hf)
    have hzero_eval :
        compactlySupportedSmoothLineSource.toSchwartz g (0 : Real) = 0 := by
      simp [hg_zero]
    simpa [hg_toSchwartz] using hzero_eval
  have hf_one_at_origin : f (0 : Real) = 1 := by
    simp [f]
  exact one_ne_zero (hf_one_at_origin.symm.trans hf_zero_at_origin)


end RiemannWeilZeroArgumentShiftedRadiusWeightedDecayCertificate

end RiemannHypothesisProject
