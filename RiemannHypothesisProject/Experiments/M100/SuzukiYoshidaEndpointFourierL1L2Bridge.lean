import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointLowFrequencyIdentification

/-!
# `L¹`/`L²` Fourier representative bridge for endpoint modes

This module proves the representative bridge from the source-selected
physical `L²` approximation to the already evaluated ordinary endpoint
Fourier integral. Fixed compact support upgrades the approximation to `L¹`,
pointwise ordinary Fourier convergence is combined with Plancherel `L²`
convergence, and subsequence uniqueness identifies the two endpoint
representatives almost everywhere.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology RealInnerProductSpace

/-- Cauchy--Schwarz on `[-r,r]` for an arbitrary `L²` function represented
pointwise and vanishing off that interval. -/
theorem sq_integral_norm_le_of_memLp_two_supported
    {r : Real} (hr : 0 < r) {f : Real → Complex}
    (hf : MemLp f (2 : ENNReal) (volume : Measure Real))
    (hsupport : ∀ x, x ∉ Icc (-r) r → f x = 0) :
    (∫ x : Real, ‖f x‖) ^ 2 ≤
      (2 * r) * ‖hf.toLp f‖ ^ 2 := by
  let mu : Measure Real := volume.restrict (Icc (-r) r)
  have hfinite : mu Set.univ ≠ ∞ := by
    dsimp only [mu]
    rw [Measure.restrict_apply_univ]
    rw [Real.volume_Icc]
    simp
  letI : IsFiniteMeasure mu :=
    IsFiniteMeasure.mk hfinite.lt_top
  have hfmu : MemLp f (2 : ENNReal) mu :=
    hf.restrict (Icc (-r) r)
  have hone : MemLp (fun _ : Real => (1 : Complex))
      (2 : ENNReal) mu := memLp_const 1
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := mu) (f := fun _ : Real => (1 : Complex)) (g := f)
    Real.HolderConjugate.two_two (by simpa using hone) (by simpa using hfmu)
  have hleft :
      (∫ x : Real, ‖f x‖) = ∫ x : Real, ‖f x‖ ∂mu := by
    dsimp only [mu]
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (-r) r
    · simp only [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupport x hx, norm_zero]
  have honeIntegral :
      (∫ _x : Real, ‖(1 : Complex)‖ ^ (2 : Real) ∂mu) = 2 * r := by
    dsimp only [mu]
    simp [hr.le]
    ring
  have hfIntegral :
      (∫ x : Real, ‖f x‖ ^ (2 : Real) ∂mu) =
        ‖hf.toLp f‖ ^ 2 := by
    dsimp only [mu]
    rw [← integral_indicator measurableSet_Icc]
    have hglobal :
        (∫ x : Real, ‖f x‖ ^ 2) = ‖hf.toLp f‖ ^ 2 := by
      symm
      exact norm_sq_toLp_eq_integral_norm_sq f hf
    rw [← hglobal]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Icc (-r) r
    · simp only [Set.indicator_of_mem hx]
      rw [Real.rpow_two]
    · rw [Set.indicator_of_notMem hx, hsupport x hx, norm_zero,
        zero_pow (by norm_num : (2 : Nat) ≠ 0)]
  simp only [norm_one, one_mul] at hholder
  have honeIntegral' :
      (∫ _x : Real, (1 : Real) ^ (2 : Real) ∂mu) = 2 * r := by
    simpa only [norm_one] using honeIntegral
  rw [← hleft, honeIntegral', hfIntegral] at hholder
  have hroot : 0 ≤ (2 * r) ^ (1 / (2 : Real)) :=
    Real.rpow_nonneg (by positivity) _
  have hfroot : 0 ≤ (‖hf.toLp f‖ ^ 2) ^ (1 / (2 : Real)) :=
    Real.rpow_nonneg (sq_nonneg _) _
  have hsqRoot : ((2 * r) ^ (1 / (2 : Real))) ^ 2 = 2 * r := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by positivity : 0 ≤ (2 * r))]
    norm_num
  have hfSqRoot :
      ((‖hf.toLp f‖ ^ 2) ^ (1 / (2 : Real))) ^ 2 =
        ‖hf.toLp f‖ ^ 2 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (sq_nonneg _)]
    norm_num
  have hsquare := (sq_le_sq₀ (integral_nonneg fun x => norm_nonneg (f x))
    (mul_nonneg hroot hfroot)).2 hholder
  rw [mul_pow, hsqRoot, hfSqRoot] at hsquare
  exact hsquare

/-- The pointwise difference between a source approximant and its endpoint
mode satisfies the sharp compact-support `L¹`-by-`L²` estimate. -/
theorem sq_integral_norm_suzukiYoshidaApproximation_sub_endpoint_le
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) (k : Nat) :
    (∫ x : Real,
        ‖(suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1 x -
          suzukiYoshidaExponentialFunction r n x‖) ^ 2 ≤
      (2 * r) *
        ‖suzukiSmoothCoreToL2
            (suzukiYoshidaExponentialApproximationOfSource hsource hr n k) -
          suzukiYoshidaExponentialL2 r hr n‖ ^ 2 := by
  let v : SuzukiSmoothCore r :=
    suzukiYoshidaExponentialApproximationOfSource hsource hr n k
  let difference : Real → Complex := fun x =>
    v.1 x - suzukiYoshidaExponentialFunction r n x
  have hdifference :
      MemLp difference (2 : ENNReal) (volume : Measure Real) :=
    (v.1.memLp (2 : ENNReal) volume).sub
      (suzukiYoshidaExponentialFunction_memLp hr n)
  have hsupport : ∀ x, x ∉ Icc (-r) r → difference x = 0 := by
    intro x hx
    have hvx : v.1 x = 0 := by
      by_contra hne
      exact hx ⟨(v.2 hne).1.le, (v.2 hne).2.le⟩
    dsimp only [difference]
    rw [hvx]
    simp [suzukiYoshidaExponentialFunction, hx]
  have hbound :=
    sq_integral_norm_le_of_memLp_two_supported hr hdifference hsupport
  have htoLp :
      hdifference.toLp difference =
        suzukiSmoothCoreToL2 v -
          suzukiYoshidaExponentialL2 r hr n := by
    have hvCoe :
        ((suzukiSmoothCoreToL2 v : SuzukiL2) : Real → Complex) =ᵐ[volume]
          v.1 :=
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
    apply Lp.ext
    filter_upwards [
      hdifference.coeFn_toLp,
      hvCoe,
      suzukiYoshidaExponentialL2_coeFn hr n,
      Lp.coeFn_sub (suzukiSmoothCoreToL2 v)
        (suzukiYoshidaExponentialL2 r hr n)] with x hdiff hv hend hsub
    rw [hdiff, hsub]
    change difference x =
      (suzukiSmoothCoreToL2 v : Real → Complex) x -
        (suzukiYoshidaExponentialL2 r hr n : Real → Complex) x
    rw [hv, hend]
  simpa only [v, difference, htoLp] using hbound

/-- Physical `L²` convergence of the source sequence upgrades to `L¹`
convergence because every difference is supported on the same finite
interval. -/
theorem integral_norm_suzukiYoshidaApproximation_sub_endpoint_tendsto_zero
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    Tendsto
      (fun k => ∫ x : Real,
        ‖(suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1 x -
          suzukiYoshidaExponentialFunction r n x‖)
      atTop (nhds 0) := by
  have hlinear :=
    suzukiYoshidaExponentialApproximationOfSource_tendsto_linear
      hsource hr n
  have hphysical :
      Tendsto
        (fun k => suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource hsource hr n k))
        atTop
        (nhds (suzukiYoshidaExponentialL2 r hr n)) := by
    have hmapped :=
      (suzukiLogRadiusLinearCompletionToL2.continuous.tendsto
        (suzukiYoshidaExponentialDirectLinearCompletionOfSource
          hsource hr n)).comp hlinear
    rw [suzukiYoshidaExponentialDirectLinearCompletionOfSource_toL2] at hmapped
    apply hmapped.congr'
    exact Filter.Eventually.of_forall fun k => rfl
  have hnorm :
      Tendsto
        (fun k =>
          ‖suzukiSmoothCoreToL2
              (suzukiYoshidaExponentialApproximationOfSource hsource hr n k) -
            suzukiYoshidaExponentialL2 r hr n‖)
        atTop (nhds 0) := by
    have hsub := hphysical.sub_const
      (suzukiYoshidaExponentialL2 r hr n)
    simpa using hsub.norm
  have hupper :
      Tendsto
        (fun k => Real.sqrt (2 * r) *
          ‖suzukiSmoothCoreToL2
              (suzukiYoshidaExponentialApproximationOfSource hsource hr n k) -
            suzukiYoshidaExponentialL2 r hr n‖)
        atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hnorm
  apply squeeze_zero
  · exact fun k => integral_nonneg fun x => norm_nonneg _
  · exact fun k => by
      apply (sq_le_sq₀
        (integral_nonneg fun x => norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (norm_nonneg
            (suzukiSmoothCoreToL2
                (suzukiYoshidaExponentialApproximationOfSource
                  hsource hr n k) -
              suzukiYoshidaExponentialL2 r hr n)))).mp
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * r)]
      exact
        sq_integral_norm_suzukiYoshidaApproximation_sub_endpoint_le
          hsource hr n k
  · exact hupper

/-- At each frequency, the ordinary Fourier integrals of the selected smooth
approximants converge to the independently defined endpoint Fourier
integral. -/
theorem fourier_suzukiYoshidaApproximation_tendsto_endpoint
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) (xi : Real) :
    Tendsto
      (fun k => FourierTransform.fourier
        (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1 xi)
      atTop
      (nhds (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi)) := by
  have hendpoint : Integrable
      (suzukiYoshidaExponentialFunction r n) :=
    memLp_one_iff_integrable.mp
      (suzukiYoshidaExponentialFunction_memLp_one hr n)
  have hbound : ∀ k,
      ‖FourierTransform.fourier
          (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1 xi -
        FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi‖ ≤
        ∫ x : Real,
          ‖(suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1 x -
            suzukiYoshidaExponentialFunction r n x‖ := by
    intro k
    let f : Real → Complex := fun x =>
      (suzukiYoshidaExponentialApproximationOfSource hsource hr n k).1 x
    let g : Real → Complex := suzukiYoshidaExponentialFunction r n
    have happ : Integrable f := by
      dsimp only [f]
      exact (suzukiYoshidaExponentialApproximationOfSource
        hsource hr n k).1.integrable
    have hendpoint' : Integrable g := by
      simpa only [g] using hendpoint
    change
      ‖FourierTransform.fourier f xi - FourierTransform.fourier g xi‖ ≤
        ∫ x : Real, ‖f x - g x‖
    rw [Real.fourier_eq f xi, Real.fourier_eq g xi]
    rw [← integral_sub
      ((Real.fourierIntegral_convergent_iff xi).2 happ)
      ((Real.fourierIntegral_convergent_iff xi).2 hendpoint')]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    apply integral_congr_ae
    filter_upwards with x
    rw [← smul_sub, Circle.norm_smul]
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero
  · exact fun k => norm_nonneg _
  · exact hbound
  · exact
      integral_norm_suzukiYoshidaApproximation_sub_endpoint_tendsto_zero
        hsource hr n

/-- For a smooth-core vector, the Plancherel `L²` Fourier transform is
represented almost everywhere by its ordinary Schwartz Fourier transform. -/
theorem fourier_suzukiSmoothCoreToL2_coe_ae
    {r : Real} (v : SuzukiSmoothCore r) :
    ((FourierTransform.fourier (suzukiSmoothCoreToL2 v) : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      FourierTransform.fourier (v.1 : Real → Complex) := by
  have hsmoothToLp :
      suzukiSmoothCoreToL2 v =
        v.1.toLp (2 : ENNReal) (volume : Measure Real) := by
    apply Lp.ext
    filter_upwards [
      (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp,
      SchwartzMap.coeFn_toLp v.1 (2 : ENNReal)
        (volume : Measure Real)] with xi hleft hright
    exact hleft.trans hright.symm
  have hfourier :
      FourierTransform.fourier (suzukiSmoothCoreToL2 v) =
        (SchwartzMap.fourierTransformCLM Complex v.1).toLp
          (2 : ENNReal) (volume : Measure Real) := by
    rw [hsmoothToLp]
    simpa only [SchwartzMap.fourierTransformCLM_apply] using
      (SchwartzMap.toLp_fourier_eq v.1)
  rw [hfourier]
  have hcoe :=
    ((SchwartzMap.fourierTransformCLM Complex v.1).memLp
      (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
  filter_upwards [hcoe] with xi hxi
  exact hxi

/-- The Plancherel transform of an endpoint `L²` class is represented almost
everywhere by the independently evaluated ordinary Fourier integral.  This
is the representative-identification bridge needed by the comparison
kernel. -/
theorem fourier_suzukiYoshidaExponentialL2_coe_ae
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ((FourierTransform.fourier
        (suzukiYoshidaExponentialL2 r hr n) : SuzukiL2) :
          Real → Complex) =ᵐ[volume]
      FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) := by
  have hlinear :=
    suzukiYoshidaExponentialApproximationOfSource_tendsto_linear
      hsource hr n
  have hphysical :
      Tendsto
        (fun k => suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource hsource hr n k))
        atTop
        (nhds (suzukiYoshidaExponentialL2 r hr n)) := by
    have hmapped :=
      (suzukiLogRadiusLinearCompletionToL2.continuous.tendsto
        (suzukiYoshidaExponentialDirectLinearCompletionOfSource
          hsource hr n)).comp hlinear
    rw [suzukiYoshidaExponentialDirectLinearCompletionOfSource_toL2] at hmapped
    apply hmapped.congr'
    exact Filter.Eventually.of_forall fun k => rfl
  have hfourier :
      Tendsto
        (fun k => FourierTransform.fourier
          (suzukiSmoothCoreToL2
            (suzukiYoshidaExponentialApproximationOfSource
              hsource hr n k)))
        atTop
        (nhds (FourierTransform.fourier
          (suzukiYoshidaExponentialL2 r hr n))) :=
    ((MeasureTheory.Lp.fourierTransformₗᵢ Real Complex).continuous.tendsto
      (suzukiYoshidaExponentialL2 r hr n)).comp hphysical
  obtain ⟨ns, hns, hfourierAe⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hfourier).exists_seq_tendsto_ae
  have hcore : ∀ k,
      ((FourierTransform.fourier
        (suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource
            hsource hr n k)) : SuzukiL2) : Real → Complex) =ᵐ[volume]
        FourierTransform.fourier
          ((suzukiYoshidaExponentialApproximationOfSource
            hsource hr n k).1 : Real → Complex) := by
    intro k
    exact fourier_suzukiSmoothCoreToL2_coe_ae
      (suzukiYoshidaExponentialApproximationOfSource hsource hr n k)
  have hcoreAll : ∀ᵐ xi ∂(volume : Measure Real), ∀ k,
      ((FourierTransform.fourier
        (suzukiSmoothCoreToL2
          (suzukiYoshidaExponentialApproximationOfSource
            hsource hr n k)) : SuzukiL2) xi) =
        FourierTransform.fourier
          ((suzukiYoshidaExponentialApproximationOfSource
            hsource hr n k).1 : Real → Complex) xi :=
    ae_all_iff.mpr hcore
  filter_upwards [hfourierAe, hcoreAll] with xi hfourierXi hcoreXi
  have hordinary :=
    (fourier_suzukiYoshidaApproximation_tendsto_endpoint
      hsource hr n xi).comp hns.tendsto_atTop
  have hordinary' :
      Tendsto
        (fun k =>
          ((FourierTransform.fourier
            (suzukiSmoothCoreToL2
              (suzukiYoshidaExponentialApproximationOfSource
                hsource hr n (ns k))) : SuzukiL2) xi))
        atTop
        (nhds (FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi)) := by
    apply hordinary.congr'
    exact Filter.Eventually.of_forall fun k => (hcoreXi (ns k)).symm
  exact tendsto_nhds_unique hfourierXi hordinary'

/-- Final ordinary-transform form of the endpoint low-frequency
identification.  The comparison kernel can now rewrite the closed extension
directly to the independently evaluated endpoint Fourier function. -/
theorem
    suzukiLowFrequencyWeightedFourierCompletionMap_source_ordinary_coe_ae
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ((suzukiLowFrequencyWeightedFourierCompletionMap hr
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource hr n) : SuzukiL2) : Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi := by
  filter_upwards [
    suzukiLowFrequencyWeightedFourierCompletionMap_source_coe_ae
      hsource hr n,
    fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr n] with
      xi hweighted hfourier
  rw [hweighted, hfourier]

end

end RiemannHypothesisProject.Experiments.M100
