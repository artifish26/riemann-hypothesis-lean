import RiemannHypothesisProject.Experiments.M100.SuzukiSingularFourierPolarizedCutoff
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierL1L2Bridge
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Finite reciprocal-kernel pairings at Yoshida endpoints

This module begins the passage from the ordered Schwartz finite-cutoff identity
to the source-selected endpoint modes.  The physical cutoff pairing is defined
directly on ambient `L²`, proved integrable, and shown continuous along jointly
convergent `L²` sequences.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate ENNReal Topology

/-- Translation is strongly continuous on the ambient `L²` space. -/
theorem continuous_suzukiL2Translate_orbit (u : SuzukiL2) :
    Continuous (fun t : Real => suzukiL2Translate t u) := by
  let g : Real → C(Real, Real) := fun t =>
    ⟨fun x => x + t, by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (by fun_prop : Continuous (fun p : Real × Real => p.2 + p.1))
  have hcomp := (continuous_const : Continuous (fun _ : Real => u))
    |>.compMeasurePreservingLp hg
      (fun t => measurePreserving_add_right (volume : Measure Real) t)
      (by norm_num : (2 : ENNReal) ≠ ∞)
  apply hcomp.congr
  intro t
  rfl

/-- Ordered physical endpoint pairing corresponding to the Fourier product
`F(u) * conj(F(v))`. -/
def suzukiReciprocalCutoffL2CrossCorrelationPairing
    (ε R : Real) (u v : SuzukiL2) : Complex :=
  ∫ t : Real,
    suzukiReciprocalCutoffKernel ε R t *
      conj (inner Complex (suzukiL2Translate t u) v)

theorem continuous_suzukiReciprocalCutoffL2CrossCorrelationFactor
    (u v : SuzukiL2) :
    Continuous (fun t : Real =>
      conj (inner Complex (suzukiL2Translate t u) v)) :=
  Complex.continuous_conj.comp
    ((continuous_suzukiL2Translate_orbit u).inner continuous_const)

theorem integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
    {ε R : Real} (hε : 0 < ε) (u v : SuzukiL2) :
    Integrable (fun t : Real =>
      suzukiReciprocalCutoffKernel ε R t *
        conj (inner Complex (suzukiL2Translate t u) v)) := by
  have hk := integrable_suzukiReciprocalCutoffKernel (R := R) hε
  have hmul := hk.bdd_mul (c := ‖u‖ * ‖v‖)
    (continuous_suzukiReciprocalCutoffL2CrossCorrelationFactor u v
      |>.aestronglyMeasurable) (by
        filter_upwards with t
        rw [Complex.norm_conj]
        exact (norm_inner_le_norm _ _).trans_eq
          (by rw [suzukiL2Translate_norm]))
  apply hmul.congr
  filter_upwards with t
  ring

/-- The physical reciprocal-kernel pairing is continuous along jointly
convergent ambient-`L²` sequences. -/
theorem tendsto_suzukiReciprocalCutoffL2CrossCorrelationPairing
    {ε R : Real} (hε : 0 < ε)
    {uSeq vSeq : Nat → SuzukiL2} {u v : SuzukiL2}
    (hu : Tendsto uSeq atTop (𝓝 u))
    (hv : Tendsto vSeq atTop (𝓝 v)) :
    Tendsto
      (fun k => suzukiReciprocalCutoffL2CrossCorrelationPairing
        ε R (uSeq k) (vSeq k))
      atTop
      (𝓝 (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R u v)) := by
  let U : Real := ‖u‖ + 1
  let V : Real := ‖v‖ + 1
  let majorant : Real → Real := fun t => U * V *
    ‖suzukiReciprocalCutoffKernel ε R t‖
  have huBound : ∀ᶠ k in atTop, ‖uSeq k‖ ≤ U := by
    have hmem : Set.Iio U ∈ 𝓝 ‖u‖ :=
      Iio_mem_nhds (by simp [U])
    exact hu.norm.eventually hmem |>.mono fun k hk => hk.le
  have hvBound : ∀ᶠ k in atTop, ‖vSeq k‖ ≤ V := by
    have hmem : Set.Iio V ∈ 𝓝 ‖v‖ :=
      Iio_mem_nhds (by simp [V])
    exact hv.norm.eventually hmem |>.mono fun k hk => hk.le
  have hmajorant : Integrable majorant := by
    have hk := (integrable_suzukiReciprocalCutoffKernel
      (R := R) hε).norm.const_mul (U * V)
    simpa only [majorant, mul_assoc] using hk
  have hmeas : ∀ᶠ k in atTop, AEStronglyMeasurable
      (fun t : Real =>
        suzukiReciprocalCutoffKernel ε R t *
          conj (inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k))) :=
    Filter.Eventually.of_forall fun k =>
      (integrable_suzukiReciprocalCutoffL2CrossCorrelationIntegrand
        hε (uSeq k) (vSeq k)).aestronglyMeasurable
  have hbound : ∀ᶠ k in atTop, ∀ᵐ t ∂volume,
      ‖suzukiReciprocalCutoffKernel ε R t *
          conj (inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k))‖ ≤
        majorant t := by
    filter_upwards [huBound, hvBound] with k huk hvk
    filter_upwards with t
    rw [norm_mul, Complex.norm_conj]
    have hinner :
        ‖inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)‖ ≤
          U * V := by
      calc
        _ ≤ ‖suzukiL2Translate t (uSeq k)‖ * ‖vSeq k‖ :=
          norm_inner_le_norm _ _
        _ = ‖uSeq k‖ * ‖vSeq k‖ := by rw [suzukiL2Translate_norm]
        _ ≤ U * V := mul_le_mul huk hvk (norm_nonneg _)
          (add_nonneg (norm_nonneg _) zero_le_one)
    dsimp only [majorant]
    calc
      ‖suzukiReciprocalCutoffKernel ε R t‖ *
          ‖inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)‖ =
          ‖inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)‖ *
            ‖suzukiReciprocalCutoffKernel ε R t‖ := mul_comm _ _
      _ ≤ (U * V) * ‖suzukiReciprocalCutoffKernel ε R t‖ :=
        mul_le_mul_of_nonneg_right hinner (norm_nonneg _)
  have hlimit : ∀ᵐ t ∂volume,
      Tendsto
        (fun k => suzukiReciprocalCutoffKernel ε R t *
          conj (inner Complex (suzukiL2Translate t (uSeq k)) (vSeq k)))
        atTop
        (𝓝 (suzukiReciprocalCutoffKernel ε R t *
          conj (inner Complex (suzukiL2Translate t u) v))) := by
    filter_upwards with t
    have htu : Tendsto (fun k => suzukiL2Translate t (uSeq k))
        atTop (𝓝 (suzukiL2Translate t u)) :=
      (suzukiL2TranslateCLM t).continuous.tendsto u |>.comp hu
    have hinner : Tendsto
        (fun k => inner Complex
          (suzukiL2Translate t (uSeq k)) (vSeq k))
        atTop
        (𝓝 (inner Complex (suzukiL2Translate t u) v)) :=
      htu.inner hv
    exact tendsto_const_nhds.mul
      ((Complex.continuous_conj.tendsto _).comp hinner)
  unfold suzukiReciprocalCutoffL2CrossCorrelationPairing
  exact tendsto_integral_filter_of_dominated_convergence
    majorant hmeas hbound hmajorant hlimit

/-- The ordered Schwartz cross-correlation is the conjugate of the ambient
`L²` translation pairing, with the argument order fixed to match
`F(u) * conj(F(v))`. -/
theorem schwartzCrossCorrelation_eq_conj_inner_suzukiL2Translate
    {r : Real} (u v : SuzukiSmoothCore r) (t : Real) :
    schwartzCrossCorrelation u.1 v.1 t =
      conj (inner Complex
        (suzukiL2Translate t (suzukiSmoothCoreToL2 u))
        (suzukiSmoothCoreToL2 v)) := by
  have hu :
      (suzukiSmoothCoreToL2 u : Real → Complex) =ᵐ[volume] u.1 :=
    (u.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
  have hv :
      (suzukiSmoothCoreToL2 v : Real → Complex) =ᵐ[volume] v.1 :=
    (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
  have hinner :
      conj (inner Complex
        (suzukiL2Translate t (suzukiSmoothCoreToL2 u))
        (suzukiSmoothCoreToL2 v)) =
        ∫ x : Real, u.1 (x + t) * conj (v.1 x) := by
    rw [inner_suzukiL2Translate_eq_integral_of_ae_two
      t (suzukiSmoothCoreToL2 u) (suzukiSmoothCoreToL2 v) u.1 v.1 hu hv,
      ← integral_conj]
    apply integral_congr_ae
    filter_upwards with x
    rw [map_mul, Complex.conj_conj]
    ring
  rw [hinner]
  unfold schwartzCrossCorrelation
  rw [SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
  have htranslate := integral_sub_right_eq_self
    (fun x : Real => u.1 (x + t) * conj (v.1 x)) t (μ := volume)
  calc
    (∫ x : Real,
        (ContinuousLinearMap.mul Complex Complex) (u.1 x)
          ((SchwartzLineTestFunction.star v.1) (t - x))) =
        ∫ x : Real, u.1 x * conj (v.1 (x - t)) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [ContinuousLinearMap.mul_apply',
        SchwartzLineTestFunction.star_apply]
      congr 2
      ring
    _ = ∫ x : Real, u.1 (x + t) * conj (v.1 x) := by
      simpa only [sub_add_cancel] using htranslate

/-- The ordered Schwartz physical pairing is exactly the ambient-`L²`
cross-correlation pairing. -/
theorem suzukiReciprocalCutoffCrossCorrelationPairing_eq_L2
    {r ε R : Real} (u v : SuzukiSmoothCore r) :
    suzukiReciprocalCutoffCrossCorrelationPairing ε R u.1 v.1 =
      suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
        (suzukiSmoothCoreToL2 u) (suzukiSmoothCoreToL2 v) := by
  unfold suzukiReciprocalCutoffCrossCorrelationPairing
    suzukiReciprocalCutoffL2CrossCorrelationPairing
  apply integral_congr_ae
  filter_upwards with t
  rw [schwartzCrossCorrelation_eq_conj_inner_suzukiL2Translate]

/-- The source-selected smooth-core approximation converges in the physical
ambient `L²` coordinate. -/
theorem suzukiYoshidaExponentialApproximationOfSource_tendsto_L2
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    Tendsto
      (fun k => suzukiSmoothCoreToL2
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k))
      atTop
      (𝓝 (suzukiYoshidaExponentialL2 r hr n)) := by
  have hlinear :=
    suzukiYoshidaExponentialApproximationOfSource_tendsto_linear
      hsource hr n
  have hmapped :=
    (suzukiLogRadiusLinearCompletionToL2.continuous.tendsto
      (suzukiYoshidaExponentialDirectLinearCompletionOfSource
        hsource hr n)).comp hlinear
  rw [suzukiYoshidaExponentialDirectLinearCompletionOfSource_toL2] at hmapped
  apply hmapped.congr'
  exact Filter.Eventually.of_forall fun k => rfl

/-- The physical finite-cutoff pairings of the source-selected approximations
converge to the ordered endpoint pairing. -/
theorem tendsto_suzukiYoshidaApproximationReciprocalCutoffL2Pairing
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (m n : Int) :
    Tendsto
      (fun k => suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
        (suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource hsource hr m k))
        (suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource hsource hr n k)))
      atTop
      (𝓝 (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
        (suzukiYoshidaExponentialL2 r hr m)
        (suzukiYoshidaExponentialL2 r hr n))) :=
  tendsto_suzukiReciprocalCutoffL2CrossCorrelationPairing hε
    (suzukiYoshidaExponentialApproximationOfSource_tendsto_L2
      hsource hr m)
    (suzukiYoshidaExponentialApproximationOfSource_tendsto_L2
      hsource hr n)

/-- The physical sides of the ordered Schwartz finite-cutoff identities
converge to the corresponding endpoint pairing. -/
theorem tendsto_suzukiYoshidaApproximationReciprocalCutoffCrossPairing
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (m n : Int) :
    Tendsto
      (fun k => suzukiReciprocalCutoffCrossCorrelationPairing ε R
        (suzukiYoshidaExponentialApproximationOfSource hsource hr m k).1
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1)
      atTop
      (𝓝 (suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
        (suzukiYoshidaExponentialL2 r hr m)
        (suzukiYoshidaExponentialL2 r hr n))) := by
  apply (tendsto_suzukiYoshidaApproximationReciprocalCutoffL2Pairing
    hsource hr hε m n).congr'
  exact Filter.Eventually.of_forall fun k =>
    (suzukiReciprocalCutoffCrossCorrelationPairing_eq_L2
      (suzukiYoshidaExponentialApproximationOfSource hsource hr m k)
      (suzukiYoshidaExponentialApproximationOfSource hsource hr n k)).symm

/-- An explicit uniform bound for the finite cosine multiplier. -/
def suzukiReciprocalCutoffMultiplierBound (ε R : Real) : Real :=
  ∫ t : Real, ‖suzukiReciprocalCutoffKernel ε R t‖

theorem norm_suzukiReciprocalCutoffCosineMultiplier_le
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (ξ : Real) :
    ‖(suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex)‖ ≤
      suzukiReciprocalCutoffMultiplierBound ε R := by
  rw [← suzukiReciprocalCutoffFourierMultiplier_eq_cosine hε hεR]
  unfold suzukiReciprocalCutoffFourierMultiplier
    suzukiReciprocalCutoffMultiplierBound
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

/-- Multiplication by the finite cosine multiplier preserves ambient `L²`. -/
theorem memLp_suzukiReciprocalCutoffCosineMultiplier_mul
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (u : SuzukiL2) :
    MemLp (fun ξ : Real =>
      (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) * u ξ)
      (2 : ENNReal) volume := by
  have hmultiplier : MemLp
      (fun ξ : Real =>
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex))
      ∞ volume := by
    apply memLp_top_of_bound
    · exact (Complex.continuous_ofReal.comp
        (continuous_suzukiReciprocalCutoffCosineMultiplier hε hεR)
          ).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ =>
        norm_suzukiReciprocalCutoffCosineMultiplier_le hε hεR ξ
  exact (Lp.memLp u).mul' hmultiplier

/-- The bounded finite cosine multiplier acting on ambient Fourier `L²`. -/
def suzukiReciprocalCutoffCosineMultiplierL2
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (u : SuzukiL2) : SuzukiL2 :=
  (memLp_suzukiReciprocalCutoffCosineMultiplier_mul hε hεR u).toLp
    (fun ξ : Real =>
      (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) * u ξ)

theorem suzukiReciprocalCutoffCosineMultiplierL2_coe_ae
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (u : SuzukiL2) :
    (suzukiReciprocalCutoffCosineMultiplierL2 hε hεR u :
        Real → Complex) =ᵐ[volume]
      fun ξ : Real =>
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) * u ξ :=
  (memLp_suzukiReciprocalCutoffCosineMultiplier_mul hε hεR u).coeFn_toLp

theorem norm_suzukiReciprocalCutoffCosineMultiplierL2_le
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) (u : SuzukiL2) :
    ‖suzukiReciprocalCutoffCosineMultiplierL2 hε hεR u‖ ≤
      suzukiReciprocalCutoffMultiplierBound ε R * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [
    suzukiReciprocalCutoffCosineMultiplierL2_coe_ae hε hεR u] with ξ hξ
  rw [hξ, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (norm_suzukiReciprocalCutoffCosineMultiplier_le hε hεR ξ)
    (norm_nonneg (u ξ))

/-- Multiplication by the finite cosine multiplier as a bounded linear map on
ambient Fourier `L²`. -/
def suzukiReciprocalCutoffCosineMultiplierCLM
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R) :
    SuzukiL2 →L[Complex] SuzukiL2 :=
  LinearMap.mkContinuous
    { toFun := suzukiReciprocalCutoffCosineMultiplierL2 hε hεR
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [
          suzukiReciprocalCutoffCosineMultiplierL2_coe_ae hε hεR (u + v),
          suzukiReciprocalCutoffCosineMultiplierL2_coe_ae hε hεR u,
          suzukiReciprocalCutoffCosineMultiplierL2_coe_ae hε hεR v,
          Lp.coeFn_add u v,
          Lp.coeFn_add
            (suzukiReciprocalCutoffCosineMultiplierL2 hε hεR u)
            (suzukiReciprocalCutoffCosineMultiplierL2 hε hεR v)] with
            ξ huv hu hv haddIn haddOut
        rw [huv, haddOut, haddIn]
        simp only [Pi.add_apply]
        rw [hu, hv]
        ring
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [
          suzukiReciprocalCutoffCosineMultiplierL2_coe_ae hε hεR (c • u),
          suzukiReciprocalCutoffCosineMultiplierL2_coe_ae hε hεR u,
          Lp.coeFn_smul c u,
          Lp.coeFn_smul c
            (suzukiReciprocalCutoffCosineMultiplierL2 hε hεR u)] with
            ξ hcu hu hsmulIn hsmulOut
        rw [hcu]
        simp only [RingHom.id_apply]
        rw [hsmulOut, hsmulIn]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hu]
        ring }
    (suzukiReciprocalCutoffMultiplierBound ε R)
    (norm_suzukiReciprocalCutoffCosineMultiplierL2_le hε hεR)

/-- The finite Fourier pairing on ambient `L²`, with argument order matching
`F(u) * conj(F(v))`. -/
def suzukiReciprocalCutoffL2FourierPairing
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (u v : SuzukiL2) : Complex :=
  inner Complex v (suzukiReciprocalCutoffCosineMultiplierCLM hε hεR u)

theorem suzukiReciprocalCutoffL2FourierPairing_eq_integral
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (u v : SuzukiL2) :
    suzukiReciprocalCutoffL2FourierPairing hε hεR u v =
      ∫ ξ : Real,
        (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
          (u ξ * conj (v ξ)) := by
  unfold suzukiReciprocalCutoffL2FourierPairing
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    suzukiReciprocalCutoffCosineMultiplierL2_coe_ae hε hεR u] with ξ hξ
  rw [RCLike.inner_apply]
  change (suzukiReciprocalCutoffCosineMultiplierL2 hε hεR u) ξ *
      conj (v ξ) = _
  rw [hξ]
  ring

theorem tendsto_suzukiReciprocalCutoffL2FourierPairing
    {ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    {uSeq vSeq : Nat → SuzukiL2} {u v : SuzukiL2}
    (hu : Tendsto uSeq atTop (𝓝 u))
    (hv : Tendsto vSeq atTop (𝓝 v)) :
    Tendsto
      (fun k => suzukiReciprocalCutoffL2FourierPairing
        hε hεR (uSeq k) (vSeq k))
      atTop
      (𝓝 (suzukiReciprocalCutoffL2FourierPairing hε hεR u v)) :=
  hv.inner ((suzukiReciprocalCutoffCosineMultiplierCLM hε hεR
    ).continuous.tendsto u |>.comp hu)

/-- The finite cosine-multiplier pairing of two independently evaluated
Yoshida endpoint transforms. -/
def suzukiYoshidaEndpointReciprocalCutoffFourierPairing
    (r ε R : Real) (m n : Int) : Complex :=
  ∫ ξ : Real,
    (suzukiReciprocalCutoffCosineMultiplier ε R ξ : Complex) *
      (FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r m) ξ *
        conj (FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) ξ))

/-- The Schwartz finite Fourier pairing is the bounded-multiplier pairing of
the corresponding Plancherel `L²` transforms. -/
theorem suzukiReciprocalCutoffPolarizedFourierPairing_eq_L2
    {r ε R : Real} (hε : 0 < ε) (hεR : ε ≤ R)
    (u v : SuzukiSmoothCore r) :
    suzukiReciprocalCutoffPolarizedFourierPairing ε R u.1 v.1 =
      suzukiReciprocalCutoffL2FourierPairing hε hεR
        (FourierTransform.fourier (suzukiSmoothCoreToL2 u))
        (FourierTransform.fourier (suzukiSmoothCoreToL2 v)) := by
  rw [suzukiReciprocalCutoffL2FourierPairing_eq_integral]
  unfold suzukiReciprocalCutoffPolarizedFourierPairing
  apply integral_congr_ae
  filter_upwards [
    fourier_suzukiSmoothCoreToL2_coe_ae u,
    fourier_suzukiSmoothCoreToL2_coe_ae v] with ξ hu hv
  rw [hu, hv]
  simp only [SchwartzMap.fourier_coe]

/-- The independently evaluated endpoint integral represents the ambient
bounded-multiplier Fourier pairing. -/
theorem suzukiYoshidaEndpointReciprocalCutoffFourierPairing_eq_L2
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (hεR : ε ≤ R) (m n : Int) :
    suzukiYoshidaEndpointReciprocalCutoffFourierPairing r ε R m n =
      suzukiReciprocalCutoffL2FourierPairing hε hεR
        (FourierTransform.fourier
          (suzukiYoshidaExponentialL2 r hr m))
        (FourierTransform.fourier
          (suzukiYoshidaExponentialL2 r hr n)) := by
  rw [suzukiReciprocalCutoffL2FourierPairing_eq_integral]
  unfold suzukiYoshidaEndpointReciprocalCutoffFourierPairing
  apply integral_congr_ae
  filter_upwards [
    fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr m,
    fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr n] with ξ hm hn
  rw [hm, hn]

/-- The Fourier sides of the source-selected Schwartz identities converge to
the independently evaluated endpoint finite-cutoff pairing. -/
theorem tendsto_suzukiYoshidaApproximationReciprocalCutoffFourierPairing
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (hεR : ε ≤ R) (m n : Int) :
    Tendsto
      (fun k => suzukiReciprocalCutoffPolarizedFourierPairing ε R
        (suzukiYoshidaExponentialApproximationOfSource hsource hr m k).1
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1)
      atTop
      (𝓝 (suzukiYoshidaEndpointReciprocalCutoffFourierPairing
        r ε R m n)) := by
  have hmPhysical :=
    suzukiYoshidaExponentialApproximationOfSource_tendsto_L2
      hsource hr m
  have hnPhysical :=
    suzukiYoshidaExponentialApproximationOfSource_tendsto_L2
      hsource hr n
  have hmFourier : Tendsto
      (fun k => FourierTransform.fourier
        (suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource hsource hr m k)))
      atTop
      (𝓝 (FourierTransform.fourier
        (suzukiYoshidaExponentialL2 r hr m))) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.tendsto
      (suzukiYoshidaExponentialL2 r hr m)).comp hmPhysical
  have hnFourier : Tendsto
      (fun k => FourierTransform.fourier
        (suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource hsource hr n k)))
      atTop
      (𝓝 (FourierTransform.fourier
        (suzukiYoshidaExponentialL2 r hr n))) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.tendsto
      (suzukiYoshidaExponentialL2 r hr n)).comp hnPhysical
  have hL2 := tendsto_suzukiReciprocalCutoffL2FourierPairing
    hε hεR hmFourier hnFourier
  have hSchwartz : Tendsto
      (fun k => suzukiReciprocalCutoffPolarizedFourierPairing ε R
        (suzukiYoshidaExponentialApproximationOfSource hsource hr m k).1
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1)
      atTop
      (𝓝 (suzukiReciprocalCutoffL2FourierPairing hε hεR
        (FourierTransform.fourier
          (suzukiYoshidaExponentialL2 r hr m))
        (FourierTransform.fourier
          (suzukiYoshidaExponentialL2 r hr n)))) := by
    apply hL2.congr'
    exact Filter.Eventually.of_forall fun k =>
      (suzukiReciprocalCutoffPolarizedFourierPairing_eq_L2 hε hεR
        (suzukiYoshidaExponentialApproximationOfSource hsource hr m k)
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k)).symm
  rw [← suzukiYoshidaEndpointReciprocalCutoffFourierPairing_eq_L2
    hsource hr hε hεR m n] at hSchwartz
  exact hSchwartz

/-- Honest finite-cutoff Plancherel/correlation identity for every ordered
pair of source-selected Yoshida endpoints. -/
theorem suzukiYoshidaEndpointReciprocalCutoffPairing_eq_fourier
    {r ε R : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (hε : 0 < ε) (hεR : ε ≤ R) (m n : Int) :
    suzukiReciprocalCutoffL2CrossCorrelationPairing ε R
        (suzukiYoshidaExponentialL2 r hr m)
        (suzukiYoshidaExponentialL2 r hr n) =
      suzukiYoshidaEndpointReciprocalCutoffFourierPairing r ε R m n := by
  have hphysical :=
    tendsto_suzukiYoshidaApproximationReciprocalCutoffCrossPairing
      (R := R) hsource hr hε m n
  have hfourier :=
    tendsto_suzukiYoshidaApproximationReciprocalCutoffFourierPairing
      hsource hr hε hεR m n
  have hfourier' : Tendsto
      (fun k => suzukiReciprocalCutoffCrossCorrelationPairing ε R
        (suzukiYoshidaExponentialApproximationOfSource hsource hr m k).1
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1)
      atTop
      (𝓝 (suzukiYoshidaEndpointReciprocalCutoffFourierPairing
        r ε R m n)) := by
    apply hfourier.congr'
    exact Filter.Eventually.of_forall fun k =>
      (suzukiReciprocalCutoffCrossCorrelationPairing_eq_fourier
        hε hεR
        (suzukiYoshidaExponentialApproximationOfSource hsource hr m k).1
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1).symm
  exact tendsto_nhds_unique hphysical hfourier'

end

end RiemannHypothesisProject.Experiments.M100
