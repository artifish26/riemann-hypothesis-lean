import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaPrimitiveCoreDensity
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceClosure
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierL1L2Bridge

/-!
# Boundary-cutoff source sequence for B2S

This module fixes the shrinking smooth boundary-layer sequence used in
Suzuki's Section 3.2 argument. It proves unconditionally that the resulting
compactly supported smooth modes converge to the periodic endpoint modes in
both the physical and logarithmically weighted Fourier `L²` coordinates, and
thereby supplies the B2S form-core source proposition.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiBoundaryCutoffFiniteMeasure (r : Real) :
    IsFiniteMeasure (volume : Measure (SuzukiFiniteInterval r)) :=
  { measure_univ_lt_top := by
      rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
      exact measure_Icc_lt_top }

/-- The normalized endpoint exponential multiplied by the canonical
shrinking smooth boundary-layer cutoff. -/
def suzukiYoshidaBoundaryCutoffModeSmoothCore
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) : SuzukiSmoothCore r := by
  let f : Real → Complex := fun x =>
    (suzukiQuantitativeIntervalCutoff r k x : Complex) *
      suzukiIntervalExponentialCore r mode x
  have hsupport : Function.support f ⊆ Ioo (-r) r := by
    intro x hx
    apply support_suzukiQuantitativeIntervalCutoff_subset hr k
    change suzukiQuantitativeIntervalCutoff r k x ≠ 0
    intro hzero
    apply hx
    simp [f, hzero]
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hne
    have hopen := hsupport hne
    exact hx ⟨hopen.1.le, hopen.2.le⟩
  have hcutoff : ContDiff Real (⊤ : ℕ∞)
      (fun x : Real => (suzukiQuantitativeIntervalCutoff r k x : Complex)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_suzukiBoundaryLayerCutoff r
        (suzukiBoundaryLayerWidth r k))
  refine ⟨hfCompact.toSchwartzMap
      (hcutoff.mul (contDiff_suzukiIntervalExponentialCore r mode)), ?_⟩
  exact hsupport

@[simp]
theorem suzukiYoshidaBoundaryCutoffModeSmoothCore_apply
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) (x : Real) :
    (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 x =
      (suzukiQuantitativeIntervalCutoff r k x : Complex) *
        suzukiIntervalExponentialCore r mode x := by
  rfl

/-- The derivative of the boundary cutoff is confined to the two strips of
width `delta` adjacent to the interval endpoints.  This is the support fact
that turns the pointwise inverse-width estimate into a uniform `L1` bound. -/
theorem deriv_suzukiBoundaryLayerCutoff_ne_zero_mem_boundaryStrips
    {r delta x : Real} (hdelta : 0 < delta)
    (hx : deriv (suzukiBoundaryLayerCutoff r delta) x ≠ 0) :
    x ∈ Icc (-r) (-r + delta) ∪ Icc (r - delta) r := by
  have hsupport :
      Function.support (suzukiBoundaryLayerCutoff r delta) ⊆ Ioo (-r) r :=
    support_suzukiBoundaryLayerCutoff_subset hdelta
  have htopSupport :
      tsupport (suzukiBoundaryLayerCutoff r delta) ⊆ Icc (-r) r := by
    exact closure_minimal (hsupport.trans Ioo_subset_Icc_self) isClosed_Icc
  have hxInterval : x ∈ Icc (-r) r :=
    htopSupport (support_deriv_subset hx)
  have hxNotInterior : x ∉ Ioo (-r + delta) (r - delta) := by
    intro hxInterior
    exact hx (deriv_suzukiBoundaryLayerCutoff_eq_zero_of_mem_Ioo
      hdelta hxInterior)
  simp only [mem_Ioo, not_and_or, not_lt] at hxNotInterior
  rcases hxNotInterior with hxLeft | hxRight
  · exact Or.inl ⟨hxInterval.1, hxLeft⟩
  · exact Or.inr ⟨hxRight, hxInterval.2⟩

/-- The total variation of the canonical boundary cutoff is bounded
independently of the boundary width.  The coarse constant `4 * C` is enough
for the uniform Fourier-tail estimate used in the B2S source limit. -/
theorem integral_abs_deriv_suzukiBoundaryLayerCutoff_le
    {r delta : Real} (hdelta : 0 < delta) :
    (∫ x : Real, |deriv (suzukiBoundaryLayerCutoff r delta) x|) ≤
      4 * suzukiSmoothTransitionDerivativeBound := by
  let boundaryStrips : Set Real :=
    Icc (-r) (-r + delta) ∪ Icc (r - delta) r
  let derivativeBound : Real :=
    2 * suzukiSmoothTransitionDerivativeBound / delta
  have hcutoffCompact :
      HasCompactSupport (suzukiBoundaryLayerCutoff r delta) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hne
    have hopen := support_suzukiBoundaryLayerCutoff_subset hdelta hne
    exact hx ⟨hopen.1.le, hopen.2.le⟩
  have hderivContinuous :
      Continuous (deriv (suzukiBoundaryLayerCutoff r delta)) :=
    (contDiff_suzukiBoundaryLayerCutoff r delta).continuous_deriv (by norm_num)
  have hderivIntegrable :
      Integrable (fun x : Real =>
        |deriv (suzukiBoundaryLayerCutoff r delta) x|) :=
    hderivContinuous.abs.integrable_of_hasCompactSupport
      hcutoffCompact.deriv.abs
  have hboundaryMeasurable : MeasurableSet boundaryStrips :=
    measurableSet_Icc.union measurableSet_Icc
  have hboundaryFinite : (volume : Measure Real) boundaryStrips ≠ ∞ := by
    apply (measure_union_lt_top measure_Icc_lt_top measure_Icc_lt_top).ne
  have hmajorIntegrable : Integrable
      (boundaryStrips.indicator (fun _ : Real => derivativeBound)) :=
    (integrableOn_const hboundaryFinite).integrable_indicator hboundaryMeasurable
  have hderivativeBoundNonneg : 0 ≤ derivativeBound := by
    exact div_nonneg
      (mul_nonneg (by norm_num) suzukiSmoothTransitionDerivativeBound_nonneg)
      hdelta.le
  have hpointwise : ∀ x : Real,
      |deriv (suzukiBoundaryLayerCutoff r delta) x| ≤
        boundaryStrips.indicator (fun _ : Real => derivativeBound) x := by
    intro x
    by_cases hx : deriv (suzukiBoundaryLayerCutoff r delta) x = 0
    · by_cases hxStrips : x ∈ boundaryStrips
      · simp [hx, hxStrips, hderivativeBoundNonneg]
      · simp [hx, hxStrips]
    · have hxStrips : x ∈ boundaryStrips :=
        deriv_suzukiBoundaryLayerCutoff_ne_zero_mem_boundaryStrips hdelta hx
      rw [Set.indicator_of_mem hxStrips]
      exact abs_deriv_suzukiBoundaryLayerCutoff_le hdelta
  have hintegral :
      (∫ x : Real, |deriv (suzukiBoundaryLayerCutoff r delta) x|) ≤
        (volume : Measure Real).real boundaryStrips * derivativeBound := by
    calc
      (∫ x : Real, |deriv (suzukiBoundaryLayerCutoff r delta) x|) ≤
          ∫ x : Real,
            boundaryStrips.indicator (fun _ : Real => derivativeBound) x :=
        integral_mono hderivIntegrable hmajorIntegrable hpointwise
      _ = (volume : Measure Real).real boundaryStrips * derivativeBound := by
        rw [integral_indicator_const derivativeBound hboundaryMeasurable]
        simp only [smul_eq_mul]
  have hmeasure :
      (volume : Measure Real).real boundaryStrips ≤ 2 * delta := by
    calc
      (volume : Measure Real).real boundaryStrips ≤
          (volume : Measure Real).real (Icc (-r) (-r + delta)) +
            (volume : Measure Real).real (Icc (r - delta) r) :=
        measureReal_union_le _ _
      _ = delta + delta := by
        rw [Real.volume_real_Icc_of_le (by linarith),
          Real.volume_real_Icc_of_le (by linarith)]
        ring
      _ = 2 * delta := by ring
  calc
    (∫ x : Real, |deriv (suzukiBoundaryLayerCutoff r delta) x|) ≤
        (volume : Measure Real).real boundaryStrips * derivativeBound := hintegral
    _ ≤ (2 * delta) * derivativeBound :=
      mul_le_mul_of_nonneg_right hmeasure hderivativeBoundNonneg
    _ = 4 * suzukiSmoothTransitionDerivativeBound := by
      dsimp only [derivativeBound]
      field_simp
      ring

theorem hasDerivAt_suzukiIntervalExponentialCore_mode
    (r : Real) (mode : Int) (x : Real) :
    HasDerivAt (suzukiIntervalExponentialCore r mode)
      (suzukiIntervalExponentialCore r mode x *
        suzukiIntervalModeFrequency r mode) x := by
  let frequency : Complex := suzukiIntervalModeFrequency r mode
  have hlinear : HasDerivAt
      (fun y : Real => frequency * (y : Complex)) frequency x := by
    simpa using
      (((hasDerivAt_id (x : Complex)).const_mul frequency).comp_ofReal)
  have hexponential : HasDerivAt
      (fun y : Real => Complex.exp (frequency * (y : Complex)))
      (Complex.exp (frequency * (x : Complex)) * frequency) x :=
    (Complex.hasDerivAt_exp (frequency * (x : Complex))).comp x hlinear
  have hscaled := hexponential.const_mul
    (((Real.sqrt (2 * r))⁻¹ : Real) : Complex)
  unfold suzukiIntervalExponentialCore
  change HasDerivAt
    (fun y : Real => (((Real.sqrt (2 * r))⁻¹ : Real) : Complex) *
      Complex.exp (frequency * (y : Complex)))
    (((((Real.sqrt (2 * r))⁻¹ : Real) : Complex) *
      Complex.exp (frequency * (x : Complex))) * frequency) x
  simpa only [mul_assoc] using hscaled

/-- Exact product derivative for a boundary-cutoff endpoint mode. -/
theorem deriv_suzukiYoshidaBoundaryCutoffMode
    {r delta : Real} (hdelta : 0 < delta) (mode : Int) (x : Real) :
    deriv (fun y : Real =>
      (suzukiBoundaryLayerCutoff r delta y : Complex) *
        suzukiIntervalExponentialCore r mode y) x =
      ((deriv (suzukiBoundaryLayerCutoff r delta) x : Real) : Complex) *
          suzukiIntervalExponentialCore r mode x +
        (suzukiBoundaryLayerCutoff r delta x : Complex) *
          (suzukiIntervalExponentialCore r mode x *
            suzukiIntervalModeFrequency r mode) := by
  have hcutoff : HasDerivAt
      (fun y : Real => (suzukiBoundaryLayerCutoff r delta y : Complex))
      ((deriv (suzukiBoundaryLayerCutoff r delta) x : Real) : Complex) x := by
    simpa only [deriv_suzukiBoundaryLayerCutoff hdelta.ne'] using
      (hasDerivAt_suzukiBoundaryLayerCutoff
        (a := r) (δ := delta) (x := x) hdelta.ne').ofReal_comp
  exact (hcutoff.mul
    (hasDerivAt_suzukiIntervalExponentialCore_mode r mode x)).deriv

/-- Pointwise derivative majorant separating cutoff variation from the fixed
mode frequency. -/
theorem norm_deriv_suzukiYoshidaBoundaryCutoffMode_le
    {r delta : Real} (hdelta : 0 < delta) (mode : Int) (x : Real) :
    ‖deriv (fun y : Real =>
      (suzukiBoundaryLayerCutoff r delta y : Complex) *
        suzukiIntervalExponentialCore r mode y) x‖ ≤
      (suzukiIntervalModeAmplitude r : Real) *
        (|deriv (suzukiBoundaryLayerCutoff r delta) x| +
          ‖suzukiIntervalModeFrequency r mode‖) := by
  rw [deriv_suzukiYoshidaBoundaryCutoffMode hdelta mode x]
  calc
    ‖((deriv (suzukiBoundaryLayerCutoff r delta) x : Real) : Complex) *
          suzukiIntervalExponentialCore r mode x +
        (suzukiBoundaryLayerCutoff r delta x : Complex) *
          (suzukiIntervalExponentialCore r mode x *
            suzukiIntervalModeFrequency r mode)‖ ≤
        ‖((deriv (suzukiBoundaryLayerCutoff r delta) x : Real) : Complex) *
          suzukiIntervalExponentialCore r mode x‖ +
        ‖(suzukiBoundaryLayerCutoff r delta x : Complex) *
          (suzukiIntervalExponentialCore r mode x *
            suzukiIntervalModeFrequency r mode)‖ := norm_add_le _ _
    _ = |deriv (suzukiBoundaryLayerCutoff r delta) x| *
          (suzukiIntervalModeAmplitude r : Real) +
        |suzukiBoundaryLayerCutoff r delta x| *
          ((suzukiIntervalModeAmplitude r : Real) *
            ‖suzukiIntervalModeFrequency r mode‖) := by
      rw [norm_mul, norm_mul, norm_mul,
        norm_suzukiIntervalExponentialCore,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs]
    _ ≤ 1 * ((suzukiIntervalModeAmplitude r : Real) *
          ‖suzukiIntervalModeFrequency r mode‖) +
        |deriv (suzukiBoundaryLayerCutoff r delta) x| *
          (suzukiIntervalModeAmplitude r : Real) := by
      rw [add_comm]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right
          (by
            rw [abs_of_nonneg
              (suzukiBoundaryLayerCutoff_nonneg r delta x)]
            exact suzukiBoundaryLayerCutoff_le_one r delta x)
          (mul_nonneg (suzukiIntervalModeAmplitude r).2 (norm_nonneg _))
      · exact le_rfl
    _ = (suzukiIntervalModeAmplitude r : Real) *
        (|deriv (suzukiBoundaryLayerCutoff r delta) x| +
          ‖suzukiIntervalModeFrequency r mode‖) := by ring

/-- Integrable pointwise majorant for the boundary-cutoff mode derivative.
The fixed-frequency contribution is restricted to the physical interval. -/
theorem norm_deriv_suzukiYoshidaBoundaryCutoffMode_le_indicator
    {r delta : Real} (hdelta : 0 < delta) (mode : Int) (x : Real) :
    ‖deriv (fun y : Real =>
      (suzukiBoundaryLayerCutoff r delta y : Complex) *
        suzukiIntervalExponentialCore r mode y) x‖ ≤
      (suzukiIntervalModeAmplitude r : Real) *
        (|deriv (suzukiBoundaryLayerCutoff r delta) x| +
          (Icc (-r) r).indicator
            (fun _ : Real => ‖suzukiIntervalModeFrequency r mode‖) x) := by
  by_cases hx : x ∈ Icc (-r) r
  · rw [Set.indicator_of_mem hx]
    exact norm_deriv_suzukiYoshidaBoundaryCutoffMode_le hdelta mode x
  · have hcutoff : suzukiBoundaryLayerCutoff r delta x = 0 := by
      by_contra hne
      have hopen := support_suzukiBoundaryLayerCutoff_subset hdelta hne
      exact hx ⟨hopen.1.le, hopen.2.le⟩
    have hderiv : deriv (suzukiBoundaryLayerCutoff r delta) x = 0 := by
      by_contra hne
      have hsupport :
          Function.support (suzukiBoundaryLayerCutoff r delta) ⊆ Ioo (-r) r :=
        support_suzukiBoundaryLayerCutoff_subset hdelta
      have htopSupport :
          tsupport (suzukiBoundaryLayerCutoff r delta) ⊆ Icc (-r) r :=
        closure_minimal (hsupport.trans Ioo_subset_Icc_self) isClosed_Icc
      exact hx (htopSupport (support_deriv_subset hne))
    rw [deriv_suzukiYoshidaBoundaryCutoffMode hdelta mode x,
      hcutoff, hderiv]
    simp [hx]

/-- Uniform `L1` bound for the derivative of every member of the shrinking
boundary-cutoff mode family.  This is the analytic input for the common
`1 / |xi|` Fourier majorant. -/
theorem integral_norm_deriv_suzukiYoshidaBoundaryCutoffMode_le
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) (mode : Int) :
    (∫ x : Real, ‖deriv (fun y : Real =>
      (suzukiBoundaryLayerCutoff r delta y : Complex) *
        suzukiIntervalExponentialCore r mode y) x‖) ≤
      (suzukiIntervalModeAmplitude r : Real) *
        (4 * suzukiSmoothTransitionDerivativeBound +
          2 * r * ‖suzukiIntervalModeFrequency r mode‖) := by
  let f : Real → Complex := fun y =>
    (suzukiBoundaryLayerCutoff r delta y : Complex) *
      suzukiIntervalExponentialCore r mode y
  let frequencyNorm : Real := ‖suzukiIntervalModeFrequency r mode‖
  let majorant : Real → Real := fun x =>
    (suzukiIntervalModeAmplitude r : Real) *
      (|deriv (suzukiBoundaryLayerCutoff r delta) x| +
        (Icc (-r) r).indicator (fun _ : Real => frequencyNorm) x)
  have hcutoffCompact :
      HasCompactSupport (suzukiBoundaryLayerCutoff r delta) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hne
    have hopen := support_suzukiBoundaryLayerCutoff_subset hdelta hne
    exact hx ⟨hopen.1.le, hopen.2.le⟩
  have hfCompact : HasCompactSupport f := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    by_contra hne
    have hcutoffNe : suzukiBoundaryLayerCutoff r delta x ≠ 0 := by
      intro hzero
      apply hne
      simp [f, hzero]
    have hopen := support_suzukiBoundaryLayerCutoff_subset hdelta hcutoffNe
    exact hx ⟨hopen.1.le, hopen.2.le⟩
  have hfContDiff : ContDiff Real (⊤ : ℕ∞) f := by
    exact (Complex.ofRealCLM.contDiff.comp
      (contDiff_suzukiBoundaryLayerCutoff r delta)).mul
        (contDiff_suzukiIntervalExponentialCore r mode)
  have hfDerivIntegrable : Integrable (fun x : Real => ‖deriv f x‖) :=
    (hfContDiff.continuous_deriv (by norm_num)).norm
      |>.integrable_of_hasCompactSupport hfCompact.deriv.norm
  have hcutoffDerivIntegrable : Integrable (fun x : Real =>
      |deriv (suzukiBoundaryLayerCutoff r delta) x|) :=
    ((contDiff_suzukiBoundaryLayerCutoff r delta).continuous_deriv
      (by norm_num)).abs.integrable_of_hasCompactSupport
        hcutoffCompact.deriv.abs
  have hindicatorIntegrable : Integrable
      ((Icc (-r) r).indicator (fun _ : Real => frequencyNorm)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator
      measurableSet_Icc
  have hmajorantIntegrable : Integrable majorant :=
    (hcutoffDerivIntegrable.add hindicatorIntegrable).const_mul _
  have hintegral : (∫ x : Real, ‖deriv f x‖) ≤ ∫ x : Real, majorant x := by
    apply integral_mono hfDerivIntegrable hmajorantIntegrable
    intro x
    exact norm_deriv_suzukiYoshidaBoundaryCutoffMode_le_indicator
      hdelta mode x
  have hmajorantIntegral :
      (∫ x : Real, majorant x) =
        (suzukiIntervalModeAmplitude r : Real) *
          ((∫ x : Real, |deriv (suzukiBoundaryLayerCutoff r delta) x|) +
            (volume : Measure Real).real (Icc (-r) r) * frequencyNorm) := by
    dsimp only [majorant]
    rw [integral_const_mul, integral_add hcutoffDerivIntegrable
      hindicatorIntegrable,
      integral_indicator_const frequencyNorm measurableSet_Icc]
    simp only [smul_eq_mul]
  rw [hmajorantIntegral] at hintegral
  calc
    (∫ x : Real, ‖deriv f x‖) ≤
        (suzukiIntervalModeAmplitude r : Real) *
          ((∫ x : Real, |deriv (suzukiBoundaryLayerCutoff r delta) x|) +
            (volume : Measure Real).real (Icc (-r) r) * frequencyNorm) := hintegral
    _ ≤ (suzukiIntervalModeAmplitude r : Real) *
        (4 * suzukiSmoothTransitionDerivativeBound +
          (volume : Measure Real).real (Icc (-r) r) * frequencyNorm) := by
      gcongr
      exact integral_abs_deriv_suzukiBoundaryLayerCutoff_le hdelta
    _ = (suzukiIntervalModeAmplitude r : Real) *
        (4 * suzukiSmoothTransitionDerivativeBound +
          2 * r * ‖suzukiIntervalModeFrequency r mode‖) := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      dsimp only [frequencyNorm]
      ring

/-- The preceding derivative bound is uniform along the canonical shrinking
sequence. -/
theorem integral_norm_deriv_suzukiYoshidaBoundaryCutoffModeSmoothCore_le
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) :
    (∫ x : Real,
      ‖deriv
        ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 :
          Real → Complex) x‖) ≤
      (suzukiIntervalModeAmplitude r : Real) *
        (4 * suzukiSmoothTransitionDerivativeBound +
          2 * r * ‖suzukiIntervalModeFrequency r mode‖) := by
  have hfunction :
      ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 :
        Real → Complex) = fun y : Real =>
          (suzukiBoundaryLayerCutoff r (suzukiBoundaryLayerWidth r k) y :
              Complex) *
            suzukiIntervalExponentialCore r mode y := by
    funext y
    rw [suzukiYoshidaBoundaryCutoffModeSmoothCore_apply]
    rfl
  rw [hfunction]
  exact integral_norm_deriv_suzukiYoshidaBoundaryCutoffMode_le
    hr (suzukiBoundaryLayerWidth_pos hr k) mode

/-- Width-independent high-frequency control for the ordinary Fourier
transforms of the explicit cutoff sequence.  It is stated without division,
so it also remains valid at zero frequency. -/
theorem mul_norm_fourier_suzukiYoshidaBoundaryCutoffMode_le
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) (xi : Real) :
    (2 * Real.pi * |xi|) *
        ‖FourierTransform.fourier
          (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ≤
      (suzukiIntervalModeAmplitude r : Real) *
        (4 * suzukiSmoothTransitionDerivativeBound +
          2 * r * ‖suzukiIntervalModeFrequency r mode‖) := by
  let v : SchwartzMap Real Complex :=
    (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1
  let derivative : SchwartzMap Real Complex :=
    SchwartzMap.derivCLM Complex Complex v
  have hderiv : deriv (v : Real → Complex) =
      (derivative : Real → Complex) := by
    funext x
    exact (SchwartzMap.derivCLM_apply Complex v x).symm
  have hfourierFunction :=
    congrFun (Real.fourier_deriv v.integrable v.differentiable
      derivative.integrable) xi
  rw [hderiv] at hfourierFunction
  have hfourier : FourierTransform.fourier
      (derivative : Real → Complex) xi =
      (((2 * Real.pi * xi : Real) : Complex) * Complex.I) *
        FourierTransform.fourier (v : Real → Complex) xi := by
    rw [hfourierFunction]
    push_cast
    ring
  have hfrequencyNorm :
      ‖(((2 * Real.pi * xi : Real) : Complex) * Complex.I)‖ =
        2 * Real.pi * |xi| := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
      abs_of_pos Real.pi_pos]
  calc
    (2 * Real.pi * |xi|) *
        ‖FourierTransform.fourier (v : Real → Complex) xi‖ =
        ‖FourierTransform.fourier
          (derivative : Real → Complex) xi‖ := by
      rw [hfourier, norm_mul, hfrequencyNorm]
    _ ≤ ∫ x : Real, ‖(derivative : Real → Complex) x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ = ∫ x : Real,
        ‖deriv (v : Real → Complex) x‖ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← hderiv]
    _ ≤ (suzukiIntervalModeAmplitude r : Real) *
        (4 * suzukiSmoothTransitionDerivativeBound +
          2 * r * ‖suzukiIntervalModeFrequency r mode‖) :=
      integral_norm_deriv_suzukiYoshidaBoundaryCutoffModeSmoothCore_le
        hr mode k

/-- A common low-frequency bound for the ordinary Fourier transforms of the
cutoff modes, obtained directly from their fixed support and pointwise
amplitude bound. -/
theorem norm_fourier_suzukiYoshidaBoundaryCutoffMode_le
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) (xi : Real) :
    ‖FourierTransform.fourier
      (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ≤
      (2 * r) * (suzukiIntervalModeAmplitude r : Real) := by
  let v : SchwartzMap Real Complex :=
    (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1
  let amplitude : Real := suzukiIntervalModeAmplitude r
  have hindicatorIntegrable : Integrable
      ((Icc (-r) r).indicator (fun _ : Real => amplitude)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator
      measurableSet_Icc
  have hpointwise : ∀ x : Real,
      ‖(v : Real → Complex) x‖ ≤
        (Icc (-r) r).indicator (fun _ : Real => amplitude) x := by
    intro x
    by_cases hx : x ∈ Icc (-r) r
    · rw [Set.indicator_of_mem hx]
      dsimp only [v, amplitude]
      rw [suzukiYoshidaBoundaryCutoffModeSmoothCore_apply,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_suzukiIntervalExponentialCore]
      exact mul_le_of_le_one_left (suzukiIntervalModeAmplitude r).2
        (by
          change |suzukiBoundaryLayerCutoff r
            (suzukiBoundaryLayerWidth r k) x| ≤ 1
          rw [abs_of_nonneg
            (suzukiBoundaryLayerCutoff_nonneg r
              (suzukiBoundaryLayerWidth r k) x)]
          exact suzukiBoundaryLayerCutoff_le_one r
            (suzukiBoundaryLayerWidth r k) x)
    · have hvx : (v : Real → Complex) x = 0 := by
        by_contra hne
        exact hx ⟨((suzukiYoshidaBoundaryCutoffModeSmoothCore
          hr mode k).2 hne).1.le,
          ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2
            hne).2.le⟩
      simp [hx, hvx]
  calc
    ‖FourierTransform.fourier (v : Real → Complex) xi‖ ≤
        ∫ x : Real, ‖(v : Real → Complex) x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _
    _ ≤ ∫ x : Real,
        (Icc (-r) r).indicator (fun _ : Real => amplitude) x :=
      integral_mono v.integrable.norm hindicatorIntegrable hpointwise
    _ = (volume : Measure Real).real (Icc (-r) r) * amplitude := by
      rw [integral_indicator_const amplitude measurableSet_Icc]
      simp only [smul_eq_mul]
    _ = (2 * r) * (suzukiIntervalModeAmplitude r : Real) := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      dsimp only [amplitude]
      ring

/-- Divided form of the uniform high-frequency estimate. -/
theorem norm_fourier_suzukiYoshidaBoundaryCutoffMode_le_highFrequency
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) {xi : Real}
    (hxi : 0 < |xi|) :
    ‖FourierTransform.fourier
      (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ≤
      ((suzukiIntervalModeAmplitude r : Real) *
        (4 * suzukiSmoothTransitionDerivativeBound +
          2 * r * ‖suzukiIntervalModeFrequency r mode‖)) /
        (2 * Real.pi * |xi|) := by
  rw [le_div_iff₀ (mul_pos (mul_pos (by norm_num) Real.pi_pos) hxi)]
  simpa only [mul_comm] using
    (mul_norm_fourier_suzukiYoshidaBoundaryCutoffMode_le
      hr mode k xi)

/-- An explicit integrable majorant for the graph-weighted Fourier square of
every cutoff mode.  The compact part uses the uniform `L1` bound and the two
tails use the width-independent derivative estimate. -/
def suzukiYoshidaBoundaryCutoffFourierSqMajorant
    (r : Real) (mode : Int) (xi : Real) : Real :=
  let lowBound := (2 * r) * (suzukiIntervalModeAmplitude r : Real)
  let tailBound := ((suzukiIntervalModeAmplitude r : Real) *
    (4 * suzukiSmoothTransitionDerivativeBound +
      2 * r * ‖suzukiIntervalModeFrequency r mode‖)) /
      (2 * Real.pi)
  (Icc (-1 : Real) 1).indicator
      (fun x => suzukiLogFourierWeight x * lowBound ^ 2) xi +
    (Iio (-1 : Real)).indicator
      (fun x => 3 * tailBound ^ 2 *
        (Real.sqrt (-x) / (-x) ^ 2)) xi +
    (Ioi (1 : Real)).indicator
      (fun x => 3 * tailBound ^ 2 *
        (Real.sqrt x / x ^ 2)) xi

theorem integrable_suzukiYoshidaBoundaryCutoffFourierSqMajorant
    (r : Real) (mode : Int) :
    Integrable (suzukiYoshidaBoundaryCutoffFourierSqMajorant r mode) := by
  let lowBound := (2 * r) * (suzukiIntervalModeAmplitude r : Real)
  let tailBound := ((suzukiIntervalModeAmplitude r : Real) *
    (4 * suzukiSmoothTransitionDerivativeBound +
      2 * r * ‖suzukiIntervalModeFrequency r mode‖)) /
      (2 * Real.pi)
  have hcompact : IntegrableOn
      (fun x : Real => suzukiLogFourierWeight x * lowBound ^ 2)
      (Icc (-1) 1) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (continuous_suzukiLogFourierWeight.mul continuous_const).continuousOn
  have hpositive : IntegrableOn
      (fun x : Real => 3 * tailBound ^ 2 *
        (Real.sqrt x / x ^ 2)) (Ioi 1) :=
    (integrableOn_sqrt_div_sq_Ioi (by norm_num)).const_mul
      (3 * tailBound ^ 2)
  have hnegativeBase : IntegrableOn
      (fun x : Real => Real.sqrt (-x) / (-x) ^ 2) (Iio (-1)) := by
    let f : Real → Real := fun x => Real.sqrt x / x ^ 2
    have hpositiveBase : IntegrableOn f (Ioi (-(-1 : Real))) := by
      simpa only [f, neg_neg] using
        (integrableOn_sqrt_div_sq_Ioi (R := (1 : Real)) (by norm_num))
    have hreflected : IntegrableOn (fun x : Real => f (-x)) (Iio (-1)) :=
      MeasureTheory.IntegrableOn.comp_neg_Iio
        (G := Real) (F := Real) (μ := volume) (c := (-1 : Real))
        hpositiveBase
    simpa only [f] using hreflected
  have hnegative : IntegrableOn
      (fun x : Real => 3 * tailBound ^ 2 *
        (Real.sqrt (-x) / (-x) ^ 2)) (Iio (-1)) :=
    hnegativeBase.const_mul (3 * tailBound ^ 2)
  have hcompactIndicator := hcompact.integrable_indicator measurableSet_Icc
  have hnegativeIndicator := hnegative.integrable_indicator measurableSet_Iio
  have hpositiveIndicator := hpositive.integrable_indicator measurableSet_Ioi
  unfold suzukiYoshidaBoundaryCutoffFourierSqMajorant
  dsimp only [lowBound, tailBound]
  exact (hcompactIndicator.add hnegativeIndicator).add hpositiveIndicator

theorem suzukiLogFourierWeight_mul_normSq_fourier_boundaryCutoff_le_majorant
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) (xi : Real) :
    suzukiLogFourierWeight xi *
        ‖FourierTransform.fourier
          (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ^ 2 ≤
      suzukiYoshidaBoundaryCutoffFourierSqMajorant r mode xi := by
  let lowBound := (2 * r) * (suzukiIntervalModeAmplitude r : Real)
  let tailBound := ((suzukiIntervalModeAmplitude r : Real) *
    (4 * suzukiSmoothTransitionDerivativeBound +
      2 * r * ‖suzukiIntervalModeFrequency r mode‖)) /
      (2 * Real.pi)
  rcases lt_or_ge xi (-1) with hnegative | hnotNegative
  · have hxneg : xi < 0 := hnegative.trans (by norm_num)
    have habs : |xi| = -xi := abs_of_neg hxneg
    have habsOne : 1 ≤ |xi| := by
      rw [habs]
      linarith
    have hsqrtOne : 1 ≤ Real.sqrt (-xi) :=
      Real.one_le_sqrt.mpr (by linarith)
    have hweight : suzukiLogFourierWeight xi ≤ 3 * Real.sqrt (-xi) := by
      unfold suzukiLogFourierWeight
      have hlog := posLog_abs_le_two_mul_sqrt_abs habsOne
      rw [habs] at hlog
      rw [habs]
      linarith
    have hfourier :=
      norm_fourier_suzukiYoshidaBoundaryCutoffMode_le_highFrequency
        hr mode k (show 0 < |xi| by positivity)
    rw [habs] at hfourier
    have hfourierTail :
        ‖FourierTransform.fourier
          (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ≤
          tailBound / (-xi) := by
      dsimp only [tailBound]
      convert hfourier using 1 <;> ring
    have hfourierSq :=
      (sq_le_sq₀ (norm_nonneg _)
        ((norm_nonneg _).trans hfourierTail)).2 hfourierTail
    have hnotIcc : xi ∉ Icc (-1 : Real) 1 := fun hx =>
      (not_lt_of_ge hx.1) hnegative
    have hnotIoi : xi ∉ Ioi (1 : Real) := fun hx =>
      (not_lt_of_ge (hnegative.le.trans (by norm_num))) hx
    have hnegativeMem : xi ∈ Iio (-1 : Real) := hnegative
    unfold suzukiYoshidaBoundaryCutoffFourierSqMajorant
    simp only [Set.indicator_of_notMem hnotIcc,
      Set.indicator_of_notMem hnotIoi,
      zero_add, add_zero]
    rw [Set.indicator_of_mem hnegativeMem]
    calc
      suzukiLogFourierWeight xi *
          ‖FourierTransform.fourier
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ^ 2 ≤
          (3 * Real.sqrt (-xi)) *
            ‖FourierTransform.fourier
              (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
      _ ≤ (3 * Real.sqrt (-xi)) * (tailBound / (-xi)) ^ 2 :=
        mul_le_mul_of_nonneg_left hfourierSq (by positivity)
      _ = 3 * tailBound ^ 2 * (Real.sqrt (-xi) / (-xi) ^ 2) := by ring
  · rcases le_or_gt xi 1 with hmiddle | hpositive
    · have hxMiddle : xi ∈ Icc (-1 : Real) 1 := ⟨hnotNegative, hmiddle⟩
      have hfourier :=
        norm_fourier_suzukiYoshidaBoundaryCutoffMode_le hr mode k xi
      have hfourierSq :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hfourier
      have hnotIio : xi ∉ Iio (-1 : Real) := fun hx =>
        (not_lt_of_ge hnotNegative) hx
      have hnotIoi : xi ∉ Ioi (1 : Real) := fun hx =>
        (not_lt_of_ge hmiddle) hx
      unfold suzukiYoshidaBoundaryCutoffFourierSqMajorant
      simp only [Set.indicator_of_mem hxMiddle,
        Set.indicator_of_notMem hnotIio,
        Set.indicator_of_notMem hnotIoi,
        add_zero]
      exact mul_le_mul_of_nonneg_left hfourierSq
        (suzukiLogFourierWeight_nonneg xi)
    · have hxpos : 0 < xi := (by linarith)
      have habs : |xi| = xi := abs_of_pos hxpos
      have habsOne : 1 ≤ |xi| := by rw [habs]; exact hpositive.le
      have hsqrtOne : 1 ≤ Real.sqrt xi :=
        Real.one_le_sqrt.mpr hpositive.le
      have hweight : suzukiLogFourierWeight xi ≤ 3 * Real.sqrt xi := by
        unfold suzukiLogFourierWeight
        have hlog := posLog_abs_le_two_mul_sqrt_abs habsOne
        rw [habs] at hlog
        rw [habs]
        linarith
      have hfourier :=
        norm_fourier_suzukiYoshidaBoundaryCutoffMode_le_highFrequency
          hr mode k (show 0 < |xi| by positivity)
      rw [habs] at hfourier
      have hfourierTail :
          ‖FourierTransform.fourier
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ≤
            tailBound / xi := by
        dsimp only [tailBound]
        convert hfourier using 1 <;> ring
      have hfourierSq :=
        (sq_le_sq₀ (norm_nonneg _)
          ((norm_nonneg _).trans hfourierTail)).2 hfourierTail
      have hnotIcc : xi ∉ Icc (-1 : Real) 1 := fun hx =>
        (not_lt_of_ge hx.2) hpositive
      have hnotIio : xi ∉ Iio (-1 : Real) := fun hx =>
        (not_lt_of_ge hnotNegative) hx
      have hpositiveMem : xi ∈ Ioi (1 : Real) := hpositive
      unfold suzukiYoshidaBoundaryCutoffFourierSqMajorant
      simp only [Set.indicator_of_notMem hnotIcc,
        Set.indicator_of_notMem hnotIio,
        zero_add]
      rw [Set.indicator_of_mem hpositiveMem]
      calc
        suzukiLogFourierWeight xi *
            ‖FourierTransform.fourier
              (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ^ 2 ≤
            (3 * Real.sqrt xi) *
              ‖FourierTransform.fourier
                (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
        _ ≤ (3 * Real.sqrt xi) * (tailBound / xi) ^ 2 :=
          mul_le_mul_of_nonneg_left hfourierSq (by positivity)
        _ = 3 * tailBound ^ 2 * (Real.sqrt xi / xi ^ 2) := by ring

/-- The finite-interval norm error of the explicit boundary-cutoff mode is
exactly the physical error integral already controlled by dominated
convergence. -/
theorem norm_sq_suzukiYoshidaBoundaryCutoffMode_finiteInterval_sub
    {r : Real} (hr : 0 < r) (mode : Int) (k : Nat) :
    ‖suzukiSmoothCoreFiniteIntervalL2LinearMap r
          ⟨(suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1,
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2⟩ -
        suzukiIntervalExponentialL2 r mode‖ ^ 2 =
      ∫ x : SuzukiFiniteInterval r,
        ‖(((suzukiQuantitativeIntervalCutoff r k x.1 : Real) : Complex) - 1) *
            suzukiIntervalExponentialCore r mode x.1‖ ^ 2 := by
  let U : SuzukiFiniteIntervalL2 r :=
    suzukiSmoothCoreFiniteIntervalL2LinearMap r
      ⟨(suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1,
        (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2⟩
  let V : SuzukiFiniteIntervalL2 r := suzukiIntervalExponentialL2 r mode
  let W : SuzukiFiniteIntervalL2 r := U - V
  have hnorm := norm_sq_toLp_finiteInterval_eq_integral_norm_sq
    (fun x : SuzukiFiniteInterval r => W x) (Lp.memLp W)
  rw [Lp.toLp_coeFn] at hnorm
  change ‖W‖ ^ 2 = _
  rw [hnorm]
  apply integral_congr_ae
  have hU : (U : SuzukiFiniteInterval r → Complex) =ᵐ[volume]
      fun x => (suzukiQuantitativeIntervalCutoff r k x.1 : Complex) *
        suzukiIntervalExponentialCore r mode x.1 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval r))
      (suzukiSmoothCoreFiniteIntervalContinuous
        (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k))
  have hV : (V : SuzukiFiniteInterval r → Complex) =ᵐ[volume]
      fun x => suzukiIntervalExponentialCore r mode x.1 :=
    suzukiIntervalExponentialL2_coeFn r mode
  filter_upwards [Lp.coeFn_sub U V, hU, hV] with x hsub hUx hVx
  dsimp only [W]
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hUx, hVx]
  congr 2
  ring

/-- The explicit boundary-cutoff smooth modes converge to the normalized
periodic mode in finite-interval `L²`. -/
theorem tendsto_suzukiYoshidaBoundaryCutoffMode_finiteIntervalL2
    {r : Real} (hr : 0 < r) (mode : Int) :
    Tendsto
      (fun k : Nat => suzukiSmoothCoreFiniteIntervalL2LinearMap r
        ⟨(suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1,
          (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2⟩)
      atTop (𝓝 (suzukiIntervalExponentialL2 r mode)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hsq : Tendsto
      (fun k : Nat =>
        ‖suzukiSmoothCoreFiniteIntervalL2LinearMap r
              ⟨(suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1,
                (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2⟩ -
            suzukiIntervalExponentialL2 r mode‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [norm_sq_suzukiYoshidaBoundaryCutoffMode_finiteInterval_sub]
      using tendsto_integral_norm_sq_suzukiQuantitativeModeCutoff_error
        hr mode
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

/-- Zero extension of the normalized interval exponential is the global
endpoint `L²` class used by B2S. -/
theorem suzukiFiniteIntervalL2ZeroExtension_exponential
    {r : Real} (hr : 0 < r) (mode : Int) :
    suzukiFiniteIntervalL2ZeroExtension r
        (suzukiIntervalExponentialL2 r mode) =
      suzukiYoshidaExponentialL2 r hr mode := by
  apply Lp.ext
  let U : SuzukiFiniteIntervalL2 r := suzukiIntervalExponentialL2 r mode
  let F : Real → Complex := suzukiFiniteIntervalL2ZeroExtensionFunction r U
  let e : SuzukiFiniteInterval r → Real := (↑)
  have he : MeasurableEmbedding e :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hmap : Measure.map e (volume : Measure (SuzukiFiniteInterval r)) =
      (volume : Measure Real).restrict (Icc (-r) r) := by
    rw [Measure.Subtype.volume_def, map_comap_subtype_coe measurableSet_Icc]
  have hsub : (fun x : SuzukiFiniteInterval r => U x) =ᵐ[volume]
      fun x => suzukiIntervalExponentialCore r mode x.1 :=
    suzukiIntervalExponentialL2_coeFn r mode
  have hrestrict : F =ᵐ[(volume : Measure Real).restrict (Icc (-r) r)]
      fun x => suzukiIntervalExponentialCore r mode x := by
    rw [← hmap]
    apply (he.ae_map_iff).2
    filter_upwards [hsub] with x hx
    change suzukiFiniteIntervalL2ZeroExtensionFunction r U x.1 = _
    rw [suzukiFiniteIntervalL2ZeroExtensionFunction_apply, hx]
  have hfun : F =ᵐ[volume] suzukiYoshidaExponentialFunction r mode := by
    have hin : ∀ᵐ x ∂(volume : Measure Real),
        x ∈ Icc (-r) r → F x = suzukiIntervalExponentialCore r mode x :=
      ae_imp_of_ae_restrict hrestrict
    filter_upwards [hin] with x hx
    by_cases hxi : x ∈ Icc (-r) r
    · rw [hx hxi]
      simp [suzukiYoshidaExponentialFunction, hxi,
        suzukiIntervalExponentialCore]
    · have hF : F x = 0 := by
        unfold F suzukiFiniteIntervalL2ZeroExtensionFunction
        rw [Function.extend_apply']
        simp only [Pi.zero_apply]
        rintro ⟨y, hy⟩
        exact hxi (hy ▸ y.2)
      rw [hF]
      simp [suzukiYoshidaExponentialFunction, hxi]
  filter_upwards [suzukiFiniteIntervalL2ZeroExtension_coeFn r U,
    suzukiYoshidaExponentialL2_coeFn hr mode, hfun] with
      x hzero hendpoint hpoint
  change (suzukiFiniteIntervalL2ZeroExtension r U : Real → Complex) x =
    (suzukiYoshidaExponentialL2 r hr mode : Real → Complex) x
  rw [hzero, hendpoint]
  exact hpoint

/-- The physical coordinate of the explicit Section 3.2 boundary-cutoff
sequence converges to the global endpoint mode. -/
theorem tendsto_suzukiYoshidaBoundaryCutoffMode_L2
    {r : Real} (hr : 0 < r) (mode : Int) :
    Tendsto
      (fun k : Nat => suzukiSmoothCoreToL2
        (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k))
      atTop (𝓝 (suzukiYoshidaExponentialL2 r hr mode)) := by
  have hfinite :=
    tendsto_suzukiYoshidaBoundaryCutoffMode_finiteIntervalL2 hr mode
  have hglobal :=
    (suzukiFiniteIntervalL2ZeroExtensionLinearIsometry r).continuous.tendsto
      (suzukiIntervalExponentialL2 r mode) |>.comp hfinite
  change Tendsto
      (fun k : Nat => suzukiFiniteIntervalL2ZeroExtension r
        (suzukiSmoothCoreFiniteIntervalL2LinearMap r
          ⟨(suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1,
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2⟩))
      atTop
      (𝓝 (suzukiFiniteIntervalL2ZeroExtension r
        (suzukiIntervalExponentialL2 r mode))) at hglobal
  rw [suzukiFiniteIntervalL2ZeroExtension_exponential hr mode] at hglobal
  apply hglobal.congr'
  exact Filter.Eventually.of_forall fun k =>
    suzukiFiniteIntervalL2ZeroExtension_smoothCore
      ⟨(suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1,
        (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2⟩

/-- The physical error of the explicit boundary-cutoff sequence tends to zero
in `L¹`. Fixed support upgrades the already proved `L²` convergence by
Cauchy--Schwarz. -/
theorem integral_norm_suzukiYoshidaBoundaryCutoffMode_sub_endpoint_tendsto_zero
    {r : Real} (hr : 0 < r) (mode : Int) :
    Tendsto
      (fun k : Nat => ∫ x : Real,
        ‖(suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 x -
          suzukiYoshidaExponentialFunction r mode x‖)
      atTop (𝓝 0) := by
  let difference : Nat → Real → Complex := fun k x =>
    (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 x -
      suzukiYoshidaExponentialFunction r mode x
  have hdifference : ∀ k,
      MemLp (difference k) (2 : ENNReal) (volume : Measure Real) := by
    intro k
    exact ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1.memLp
      (2 : ENNReal) volume).sub
        (suzukiYoshidaExponentialFunction_memLp hr mode)
  have hsupport : ∀ k x, x ∉ Icc (-r) r → difference k x = 0 := by
    intro k x hx
    have hvx :
        (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 x = 0 := by
      by_contra hne
      exact hx ⟨((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2
        hne).1.le, ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).2
          hne).2.le⟩
    dsimp only [difference]
    rw [hvx]
    simp [suzukiYoshidaExponentialFunction, hx]
  have htoLp : ∀ k,
      (hdifference k).toLp (difference k) =
        suzukiSmoothCoreToL2
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k) -
          suzukiYoshidaExponentialL2 r hr mode := by
    intro k
    apply Lp.ext
    filter_upwards [
      (hdifference k).coeFn_toLp,
      ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1.memLp
        (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
      suzukiYoshidaExponentialL2_coeFn hr mode,
      Lp.coeFn_sub
        (suzukiSmoothCoreToL2
          (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k))
        (suzukiYoshidaExponentialL2 r hr mode)] with
        x hdiff hsmooth hendpoint hsub
    rw [hdiff, hsub]
    change difference k x =
      (suzukiSmoothCoreToL2
        (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k) :
          Real → Complex) x -
        (suzukiYoshidaExponentialL2 r hr mode : Real → Complex) x
    rw [hendpoint]
    unfold suzukiSmoothCoreToL2
    rw [hsmooth]
  have hnorm : Tendsto
      (fun k : Nat =>
        ‖suzukiSmoothCoreToL2
              (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k) -
            suzukiYoshidaExponentialL2 r hr mode‖)
      atTop (𝓝 0) := by
    have hphysical := tendsto_suzukiYoshidaBoundaryCutoffMode_L2 hr mode
    simpa using (hphysical.sub_const
      (suzukiYoshidaExponentialL2 r hr mode)).norm
  have hupper : Tendsto
      (fun k : Nat => Real.sqrt (2 * r) *
        ‖suzukiSmoothCoreToL2
              (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k) -
            suzukiYoshidaExponentialL2 r hr mode‖)
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hnorm
  apply squeeze_zero
  · exact fun k => integral_nonneg fun x => norm_nonneg _
  · intro k
    apply (sq_le_sq₀
      (integral_nonneg fun x => norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _)
        (norm_nonneg
          (suzukiSmoothCoreToL2
              (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k) -
            suzukiYoshidaExponentialL2 r hr mode)))).mp
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * r)]
    have hbound := sq_integral_norm_le_of_memLp_two_supported hr
      (hdifference k) (hsupport k)
    simpa only [difference, htoLp k] using hbound
  · exact hupper

/-- At every fixed frequency, the ordinary Fourier transforms of the
explicit smooth boundary cutoffs converge to the independently defined
endpoint Fourier integral. -/
theorem fourier_suzukiYoshidaBoundaryCutoffMode_tendsto_endpoint
    {r : Real} (hr : 0 < r) (mode : Int) (xi : Real) :
    Tendsto
      (fun k : Nat => FourierTransform.fourier
        (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi)
      atTop
      (𝓝 (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r mode) xi)) := by
  have hendpoint : Integrable (suzukiYoshidaExponentialFunction r mode) :=
    memLp_one_iff_integrable.mp
      (suzukiYoshidaExponentialFunction_memLp_one hr mode)
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero
  · exact fun k => norm_nonneg _
  · intro k
    let f : Real → Complex :=
      (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1
    let g : Real → Complex := suzukiYoshidaExponentialFunction r mode
    have hf : Integrable f :=
      (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1.integrable
    have hg : Integrable g := by simpa only [g] using hendpoint
    change ‖FourierTransform.fourier f xi -
        FourierTransform.fourier g xi‖ ≤ ∫ x : Real, ‖f x - g x‖
    rw [Real.fourier_eq f xi, Real.fourier_eq g xi]
    rw [← integral_sub
      ((Real.fourierIntegral_convergent_iff xi).2 hf)
      ((Real.fourierIntegral_convergent_iff xi).2 hg)]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards with x
    rw [← smul_sub, Circle.norm_smul]
  · exact
      integral_norm_suzukiYoshidaBoundaryCutoffMode_sub_endpoint_tendsto_zero
        hr mode

/-- The Plancherel transform of the endpoint `L2` class is represented almost
everywhere by its ordinary Fourier integral.  This is unconditional for the
explicit cutoff sequence: physical `L2` convergence and pointwise ordinary
Fourier convergence identify the two subsequential limits. -/
theorem fourier_suzukiYoshidaExponentialL2_coe_ae_of_boundaryCutoff
    {r : Real} (hr : 0 < r) (mode : Int) :
    ((FourierTransform.fourier
        (suzukiYoshidaExponentialL2 r hr mode) : SuzukiL2) :
          Real → Complex) =ᵐ[volume]
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r mode) := by
  have hphysical :=
    tendsto_suzukiYoshidaBoundaryCutoffMode_L2 hr mode
  have hfourier :
      Tendsto
        (fun k => FourierTransform.fourier
          (suzukiSmoothCoreToL2
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k)))
        atTop
        (𝓝 (FourierTransform.fourier
          (suzukiYoshidaExponentialL2 r hr mode))) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.tendsto
      (suzukiYoshidaExponentialL2 r hr mode)).comp hphysical
  obtain ⟨indices, hindices, hfourierAe⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hfourier).exists_seq_tendsto_ae
  have hcore : ∀ k,
      ((FourierTransform.fourier
        (suzukiSmoothCoreToL2
          (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k)) :
            SuzukiL2) : Real → Complex) =ᵐ[volume]
        FourierTransform.fourier
          ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 :
            Real → Complex) := by
    intro k
    exact fourier_suzukiSmoothCoreToL2_coe_ae
      (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k)
  have hcoreAll : ∀ᵐ xi ∂(volume : Measure Real), ∀ k,
      ((FourierTransform.fourier
        (suzukiSmoothCoreToL2
          (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k)) :
            SuzukiL2) xi) =
        FourierTransform.fourier
          ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 :
            Real → Complex) xi :=
    ae_all_iff.mpr hcore
  filter_upwards [hfourierAe, hcoreAll] with xi hfourierXi hcoreXi
  have hordinary :=
    (fourier_suzukiYoshidaBoundaryCutoffMode_tendsto_endpoint
      hr mode xi).comp hindices.tendsto_atTop
  have hordinary' :
      Tendsto
        (fun k =>
          ((FourierTransform.fourier
            (suzukiSmoothCoreToL2
              (suzukiYoshidaBoundaryCutoffModeSmoothCore
                hr mode (indices k))) : SuzukiL2) xi))
        atTop
        (𝓝 (FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r mode) xi)) := by
    apply hordinary.congr'
    exact Filter.Eventually.of_forall fun k => (hcoreXi (indices k)).symm
  exact tendsto_nhds_unique hfourierXi hordinary'

/-- Endpoint modes belong unconditionally to the logarithmic Fourier domain.
The ordinary endpoint transform already has an integrable graph-weighted
square, and the preceding theorem identifies it with the Plancherel
representative. -/
theorem suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff
    {r : Real} (hr : 0 < r) (mode : Int) :
    SuzukiLogFourierDomain
      (suzukiYoshidaExponentialL2 r hr mode) := by
  let ordinaryWeighted : Real → Complex := fun xi =>
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r mode) xi
  have hordinaryMeasurable :
      AEStronglyMeasurable ordinaryWeighted volume := by
    exact ((Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp continuous_suzukiLogFourierWeight)).mul
        (continuous_fourier_suzukiYoshidaExponentialFunction hr mode)
      ).aestronglyMeasurable
  have hordinaryMemLp : MemLp ordinaryWeighted
      (2 : ENNReal) (volume : Measure Real) := by
    apply (memLp_two_iff_integrable_sq_norm hordinaryMeasurable).2
    have hintegrable :=
      integrable_suzukiLogFourierWeight_mul_endpointFourierSq hr mode
    apply hintegrable.congr
    filter_upwards with xi
    dsimp only [ordinaryWeighted]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (suzukiLogFourierWeight_nonneg xi)]
  unfold SuzukiLogFourierDomain suzukiLogWeightedFourier
  apply hordinaryMemLp.ae_eq
  filter_upwards [
    fourier_suzukiYoshidaExponentialL2_coe_ae_of_boundaryCutoff
      hr mode] with xi hxi
  rw [hxi]

/-- The graph-weighted ordinary Fourier representatives of the explicit
boundary cutoffs converge in squared `L2` distance to the endpoint ordinary
Fourier representative.  The proof is dominated convergence using the
uniform compact/tail majorant above. -/
theorem tendsto_integral_norm_sq_suzukiYoshidaBoundaryCutoff_weightedFourier_error
    {r : Real} (hr : 0 < r) (mode : Int) :
    Tendsto
      (fun k : Nat => ∫ xi : Real,
        ‖((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
              FourierTransform.fourier
                ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 :
                  Real → Complex) xi -
            ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
              FourierTransform.fourier
                (suzukiYoshidaExponentialFunction r mode) xi‖ ^ 2)
      atTop (𝓝 0) := by
  let approximate : Nat → Real → Complex := fun k xi =>
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
      FourierTransform.fourier
        ((suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 :
          Real → Complex) xi
  let endpoint : Real → Complex := fun xi =>
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r mode) xi
  let G : Nat → Real → Real := fun k xi =>
    ‖approximate k xi - endpoint xi‖ ^ 2
  let endpointSquare : Real → Real := fun xi =>
    suzukiLogFourierWeight xi *
      ‖FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r mode) xi‖ ^ 2
  let bound : Real → Real := fun xi =>
    2 * (suzukiYoshidaBoundaryCutoffFourierSqMajorant r mode xi +
      endpointSquare xi)
  have hApproximateContinuous : ∀ k, Continuous (approximate k) := by
    intro k
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp continuous_suzukiLogFourierWeight)).mul
        (SchwartzMap.continuous
          (SchwartzMap.fourierTransformCLM Complex
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1))
  have hEndpointContinuous : Continuous endpoint := by
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp continuous_suzukiLogFourierWeight)).mul
        (continuous_fourier_suzukiYoshidaExponentialFunction hr mode)
  have hGMeasurable : ∀ k, AEStronglyMeasurable (G k) volume := by
    intro k
    exact ((hApproximateContinuous k).sub hEndpointContinuous).norm.pow 2
      |>.aestronglyMeasurable
  have hBoundIntegrable : Integrable bound volume := by
    have hsum :=
      (integrable_suzukiYoshidaBoundaryCutoffFourierSqMajorant r mode).add
        (integrable_suzukiLogFourierWeight_mul_endpointFourierSq hr mode)
    dsimp only [bound, endpointSquare]
    exact hsum.const_mul 2
  have hBound : ∀ k, ∀ᵐ xi : Real, ‖G k xi‖ ≤ bound xi := by
    intro k
    exact Filter.Eventually.of_forall fun xi => by
      have hApproximateSquare :
          ‖approximate k xi‖ ^ 2 =
            suzukiLogFourierWeight xi *
              ‖FourierTransform.fourier
                (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k).1 xi‖ ^ 2 := by
        dsimp only [approximate]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
          Real.sq_sqrt (suzukiLogFourierWeight_nonneg xi)]
        rw [SchwartzMap.fourier_coe]
      have hEndpointSquare : ‖endpoint xi‖ ^ 2 = endpointSquare xi := by
        dsimp only [endpoint, endpointSquare]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
          Real.sq_sqrt (suzukiLogFourierWeight_nonneg xi)]
      have hApproximateMajorant :
          ‖approximate k xi‖ ^ 2 ≤
            suzukiYoshidaBoundaryCutoffFourierSqMajorant r mode xi := by
        rw [hApproximateSquare]
        exact
          suzukiLogFourierWeight_mul_normSq_fourier_boundaryCutoff_le_majorant
            hr mode k xi
      have hTriangle := norm_sub_le (approximate k xi) (endpoint xi)
      have hTriangleSquare :
          ‖approximate k xi - endpoint xi‖ ^ 2 ≤
            (‖approximate k xi‖ + ‖endpoint xi‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hTriangle 2
      have hSumSquare :
          (‖approximate k xi‖ + ‖endpoint xi‖) ^ 2 ≤
            2 * (‖approximate k xi‖ ^ 2 + ‖endpoint xi‖ ^ 2) := by
        nlinarith [sq_nonneg (‖approximate k xi‖ - ‖endpoint xi‖)]
      dsimp only [G, bound]
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      calc
        ‖approximate k xi - endpoint xi‖ ^ 2 ≤
            2 * (‖approximate k xi‖ ^ 2 + ‖endpoint xi‖ ^ 2) :=
          hTriangleSquare.trans hSumSquare
        _ ≤ 2 *
            (suzukiYoshidaBoundaryCutoffFourierSqMajorant r mode xi +
              endpointSquare xi) := by
          exact mul_le_mul_of_nonneg_left
            (add_le_add hApproximateMajorant hEndpointSquare.le) (by norm_num)
  have hLimit : ∀ᵐ xi : Real,
      Tendsto (fun k => G k xi) atTop (𝓝 0) := by
    exact Filter.Eventually.of_forall fun xi => by
      have hWeighted : Tendsto (fun k => approximate k xi) atTop
          (𝓝 (endpoint xi)) := by
        dsimp only [approximate, endpoint]
        exact tendsto_const_nhds.mul
          (fourier_suzukiYoshidaBoundaryCutoffMode_tendsto_endpoint
            hr mode xi)
      simpa only [G, sub_self, norm_zero,
        zero_pow (by norm_num : (2 : Nat) ≠ 0)] using
        (hWeighted.sub_const (endpoint xi)).norm.pow 2
  have hDCT := tendsto_integral_of_dominated_convergence
    bound hGMeasurable hBoundIntegrable hBound hLimit
  simpa only [G, approximate, endpoint, integral_zero] using hDCT

/-- The narrowed B2S statement for the explicit cutoff sequence: weighted
Fourier coordinates converge to the endpoint graph representative. -/
def SuzukiYoshidaBoundaryCutoffWeightedFourierConvergenceAt
    (r : Real) : Prop :=
  ∀ (hr : 0 < r) (mode : Int),
    Tendsto
      (fun k : Nat => suzukiLogWeightedFourierToL2
        ⟨suzukiSmoothCoreToL2
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k),
          suzukiSmoothCoreToL2_mem_logFourierDomain
            (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k)⟩)
      atTop
      (𝓝 (suzukiLogWeightedFourierToL2
        ⟨suzukiYoshidaExponentialL2 r hr mode,
          suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff
            hr mode⟩))

/-- The explicit boundary-cutoff sequence converges in the logarithmically
weighted Fourier coordinate.  This closes the remaining analytic statement
in the narrowed B2S source premise. -/
theorem suzukiYoshidaBoundaryCutoffWeightedFourierConvergenceAt
    (r : Real) :
    SuzukiYoshidaBoundaryCutoffWeightedFourierConvergenceAt r := by
  intro hr mode
  let core : Nat → SuzukiSmoothCore r := fun k =>
    suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k
  let approximateRepresentative : Nat → Real → Complex := fun k =>
    suzukiLogWeightedFourier (suzukiSmoothCoreToL2 (core k))
  let endpointRepresentative : Real → Complex :=
    suzukiLogWeightedFourier (suzukiYoshidaExponentialL2 r hr mode)
  let ordinaryApproximate : Nat → Real → Complex := fun k xi =>
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
      FourierTransform.fourier ((core k).1 : Real → Complex) xi
  let ordinaryEndpoint : Real → Complex := fun xi =>
    ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r mode) xi
  have hApproximateMem : ∀ k,
      MemLp (approximateRepresentative k) (2 : ENNReal) volume := by
    intro k
    exact suzukiSmoothCoreToL2_mem_logFourierDomain (core k)
  have hEndpointMem :
      MemLp endpointRepresentative (2 : ENNReal) volume := by
    exact suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff
      hr mode
  have hApproximateAe : ∀ k,
      approximateRepresentative k =ᵐ[volume] ordinaryApproximate k := by
    intro k
    filter_upwards [fourier_suzukiSmoothCoreToL2_coe_ae (core k)] with xi hxi
    dsimp only [approximateRepresentative, ordinaryApproximate]
    unfold suzukiLogWeightedFourier
    rw [hxi]
  have hEndpointAe : endpointRepresentative =ᵐ[volume] ordinaryEndpoint := by
    filter_upwards [
      fourier_suzukiYoshidaExponentialL2_coe_ae_of_boundaryCutoff
        hr mode] with xi hxi
    dsimp only [endpointRepresentative, ordinaryEndpoint]
    unfold suzukiLogWeightedFourier
    rw [hxi]
  have hNormSquare : ∀ k,
      ‖suzukiLogWeightedFourierToL2
            ⟨suzukiSmoothCoreToL2 (core k),
              suzukiSmoothCoreToL2_mem_logFourierDomain (core k)⟩ -
          suzukiLogWeightedFourierToL2
            ⟨suzukiYoshidaExponentialL2 r hr mode,
              suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff
                hr mode⟩‖ ^ 2 =
        ∫ xi : Real,
          ‖ordinaryApproximate k xi - ordinaryEndpoint xi‖ ^ 2 := by
    intro k
    have hDifferenceMem := (hApproximateMem k).sub hEndpointMem
    have hnorm := norm_sq_toLp_eq_integral_norm_sq
      (approximateRepresentative k - endpointRepresentative)
      hDifferenceMem
    rw [MemLp.toLp_sub] at hnorm
    calc
      ‖suzukiLogWeightedFourierToL2
            ⟨suzukiSmoothCoreToL2 (core k),
              suzukiSmoothCoreToL2_mem_logFourierDomain (core k)⟩ -
          suzukiLogWeightedFourierToL2
            ⟨suzukiYoshidaExponentialL2 r hr mode,
              suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff
                hr mode⟩‖ ^ 2 =
          ∫ xi : Real,
            ‖approximateRepresentative k xi - endpointRepresentative xi‖ ^ 2 := by
        simpa only [suzukiLogWeightedFourierToL2,
          approximateRepresentative, endpointRepresentative,
          Pi.sub_apply] using hnorm
      _ = ∫ xi : Real,
          ‖ordinaryApproximate k xi - ordinaryEndpoint xi‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [hApproximateAe k, hEndpointAe] with xi happrox hendpoint
        rw [happrox, hendpoint]
  have hIntegral :=
    tendsto_integral_norm_sq_suzukiYoshidaBoundaryCutoff_weightedFourier_error
      hr mode
  have hSquares : Tendsto
      (fun k : Nat =>
        ‖suzukiLogWeightedFourierToL2
              ⟨suzukiSmoothCoreToL2 (core k),
                suzukiSmoothCoreToL2_mem_logFourierDomain (core k)⟩ -
            suzukiLogWeightedFourierToL2
              ⟨suzukiYoshidaExponentialL2 r hr mode,
                suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff
                  hr mode⟩‖ ^ 2)
      atTop (𝓝 0) := by
    apply hIntegral.congr'
    exact Filter.Eventually.of_forall fun k => by
      symm
      simpa only [core, ordinaryApproximate, ordinaryEndpoint] using hNormSquare k
  have hNorms := hSquares.sqrt
  apply tendsto_iff_norm_sub_tendsto_zero.2
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero, core] using hNorms

/-- Compatibility form of the explicit Section 3.2 source statement: the
endpoint domain witness is packaged together with weighted convergence.

Unlike `SuzukiYoshidaExponentialFormCoreSourceAt`, this premise contains no
existential approximation sequence. The endpoint witness is supplied by
`suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff`, and the
weighted convergence by
`suzukiYoshidaBoundaryCutoffWeightedFourierConvergenceAt`. -/
def SuzukiYoshidaBoundaryCutoffFourierSourceAt (r : Real) : Prop :=
  ∀ (hr : 0 < r) (mode : Int),
    ∃ hDomain : SuzukiLogFourierDomain
        (suzukiYoshidaExponentialL2 r hr mode),
      Tendsto
        (fun k : Nat => suzukiLogWeightedFourierToL2
          ⟨suzukiSmoothCoreToL2
              (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k),
            suzukiSmoothCoreToL2_mem_logFourierDomain
              (suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k)⟩)
        atTop
        (𝓝 (suzukiLogWeightedFourierToL2
          ⟨suzukiYoshidaExponentialL2 r hr mode, hDomain⟩))

theorem suzukiYoshidaBoundaryCutoffFourierSourceAt_of_weightedConvergence
    {r : Real}
    (hweighted : SuzukiYoshidaBoundaryCutoffWeightedFourierConvergenceAt r) :
    SuzukiYoshidaBoundaryCutoffFourierSourceAt r := by
  intro hr mode
  exact
    ⟨suzukiYoshidaExponentialL2_mem_logFourierDomain_of_boundaryCutoff hr mode,
      hweighted hr mode⟩

/-- The weighted-Fourier statement for the explicit boundary cutoffs is
sufficient for the original B2S form-core source theorem.  The physical
coordinate is supplied by the unconditional convergence theorem above. -/
theorem suzukiYoshidaExponentialFormCoreSourceAt_of_boundaryCutoffFourier
    {r : Real} (hsource : SuzukiYoshidaBoundaryCutoffFourierSourceAt r) :
    SuzukiYoshidaExponentialFormCoreSourceAt r := by
  intro hr mode
  obtain ⟨hDomain, hweighted⟩ := hsource hr mode
  refine ⟨hDomain, fun k =>
    suzukiYoshidaBoundaryCutoffModeSmoothCore hr mode k, ?_⟩
  rw [tendsto_subtype_rng]
  apply (Prod.tendsto_iff _ _).2
  exact ⟨tendsto_suzukiYoshidaBoundaryCutoffMode_L2 hr mode, hweighted⟩

theorem
    suzukiYoshidaExponentialFormCoreSourceAt_of_boundaryCutoffWeightedConvergence
    {r : Real}
    (hweighted : SuzukiYoshidaBoundaryCutoffWeightedFourierConvergenceAt r) :
    SuzukiYoshidaExponentialFormCoreSourceAt r :=
  suzukiYoshidaExponentialFormCoreSourceAt_of_boundaryCutoffFourier
    (suzukiYoshidaBoundaryCutoffFourierSourceAt_of_weightedConvergence
      hweighted)

/-- The explicit boundary-cutoff Fourier source package is inhabited for
every radius. -/
theorem suzukiYoshidaBoundaryCutoffFourierSourceAt
    (r : Real) : SuzukiYoshidaBoundaryCutoffFourierSourceAt r :=
  suzukiYoshidaBoundaryCutoffFourierSourceAt_of_weightedConvergence
    (suzukiYoshidaBoundaryCutoffWeightedFourierConvergenceAt r)

/-- Unconditional B2S source closure: the normalized periodic endpoint modes
are graph-norm limits of the explicit smooth boundary-cutoff sequence. -/
theorem suzukiYoshidaExponentialFormCoreSourceAt_boundaryCutoff
    (r : Real) : SuzukiYoshidaExponentialFormCoreSourceAt r :=
  suzukiYoshidaExponentialFormCoreSourceAt_of_boundaryCutoffFourier
    (suzukiYoshidaBoundaryCutoffFourierSourceAt r)

end

end RiemannHypothesisProject.Experiments.M100
