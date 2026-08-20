import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointFourierL1L2Bridge

/-!
# Endpoint comparison-form assembly

This module expands the closed comparison form on the source-provided
endpoint exponential lifts.  It identifies the physical, logarithmic graph,
and low-frequency-loss inner products with ordinary Fourier integrals, then
reassembles their weights into Suzuki's project-normalized source multiplier.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Filter MeasureTheory
open scoped ComplexConjugate ENNReal

/-- An `L²` inner product can be evaluated from any chosen almost-everywhere
representatives, in the argument order used by the source Fourier pairing. -/
theorem inner_suzukiL2_eq_integral_mul_conj_of_coe_ae
    {u v : SuzukiL2} {fu fv : Real → Complex}
    (hu : (u : Real → Complex) =ᵐ[volume] fu)
    (hv : (v : Real → Complex) =ᵐ[volume] fv) :
    inner Complex u v = ∫ x : Real, fv x * conj (fu x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu, hv] with x hux hvx
  rw [hux, hvx]
  rw [RCLike.inner_apply]

/-- Products of representatives of two `L²` classes are integrable by
Cauchy--Schwarz. -/
theorem integrable_mul_conj_of_suzukiL2_coe_ae
    {u v : SuzukiL2} {fu fv : Real → Complex}
    (hu : (u : Real → Complex) =ᵐ[volume] fu)
    (hv : (v : Real → Complex) =ᵐ[volume] fv) :
    Integrable (fun x : Real => fv x * conj (fu x)) := by
  have hinter := L2.integrable_inner (𝕜 := Complex) u v
  apply hinter.congr
  filter_upwards [hu, hv] with x hux hvx
  rw [hux, hvx]
  rw [RCLike.inner_apply]

/-- Plancherel plus the endpoint representative bridge evaluates the
physical endpoint inner product as the unweighted ordinary Fourier pairing. -/
theorem inner_suzukiYoshidaExponentialL2_eq_fourierIntegral
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    inner Complex
        (suzukiYoshidaExponentialL2 r hr m)
        (suzukiYoshidaExponentialL2 r hr n) =
      ∫ xi : Real,
        FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi *
          conj (FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r m) xi) := by
  rw [← Lp.inner_fourier_eq]
  exact inner_suzukiL2_eq_integral_mul_conj_of_coe_ae
    (fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr m)
    (fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr n)

theorem integrable_suzukiYoshidaEndpointFourierPairing
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    Integrable (fun xi : Real =>
      FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r n) xi *
        conj (FourierTransform.fourier
          (suzukiYoshidaExponentialFunction r m) xi)) :=
  integrable_mul_conj_of_suzukiL2_coe_ae
    (fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr m)
    (fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr n)

/-- The logarithmically weighted Fourier coordinate of one endpoint mode. -/
noncomputable def suzukiYoshidaEndpointLogWeightedFourierL2
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) : SuzukiL2 :=
  suzukiLogWeightedFourierToL2
    ⟨suzukiYoshidaExponentialL2 r hr n,
      suzukiYoshidaExponentialFourierDomainOfSource hsource hr n⟩

/-- The weighted graph coordinate is represented by the square-root graph
weight times the ordinary endpoint Fourier transform. -/
theorem suzukiYoshidaEndpointLogWeightedFourierL2_coe_ae
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ((suzukiYoshidaEndpointLogWeightedFourierL2 hsource hr n : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLogFourierWeight xi) : Real) : Complex) *
          FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi := by
  unfold suzukiYoshidaEndpointLogWeightedFourierL2
  have hweighted := suzukiLogWeightedFourierToL2_coe_ae
    ⟨suzukiYoshidaExponentialL2 r hr n,
      suzukiYoshidaExponentialFourierDomainOfSource hsource hr n⟩
  have hfourier :=
    fourier_suzukiYoshidaExponentialL2_coe_ae hsource hr n
  filter_upwards [hweighted, hfourier] with xi hweightedXi hfourierXi
  rw [hweightedXi]
  unfold suzukiLogWeightedFourier
  rw [hfourierXi]

/-- Multiplying both arguments by a nonnegative real square root multiplies
the source-ordered complex pairing by the underlying real weight. -/
theorem sqrt_weight_mul_mul_conj_sqrt_weight_mul
    {w : Real} (hw : 0 ≤ w) (a b : Complex) :
    (((Real.sqrt w : Real) : Complex) * b) *
        conj (((Real.sqrt w : Real) : Complex) * a) =
      (w : Complex) * (b * conj a) := by
  calc
    (((Real.sqrt w : Real) : Complex) * b) *
          conj (((Real.sqrt w : Real) : Complex) * a) =
        (((Real.sqrt w * Real.sqrt w : Real) : Complex)) *
          (b * conj a) := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    _ = (w : Complex) * (b * conj a) := by
      rw [Real.mul_self_sqrt hw]

/-- The second graph-coordinate inner product is the ordinary endpoint
pairing weighted by `1 + posLog |xi|`. -/
theorem inner_suzukiYoshidaEndpointLogWeightedFourierL2_eq_integral
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    inner Complex
        (suzukiYoshidaEndpointLogWeightedFourierL2 hsource hr m)
        (suzukiYoshidaEndpointLogWeightedFourierL2 hsource hr n) =
      ∫ xi : Real,
        ((suzukiLogFourierWeight xi : Real) : Complex) *
          (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) xi *
            conj (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r m) xi)) := by
  rw [inner_suzukiL2_eq_integral_mul_conj_of_coe_ae
    (suzukiYoshidaEndpointLogWeightedFourierL2_coe_ae
      hsource hr m)
    (suzukiYoshidaEndpointLogWeightedFourierL2_coe_ae
      hsource hr n)]
  apply integral_congr_ae
  filter_upwards with xi
  exact sqrt_weight_mul_mul_conj_sqrt_weight_mul
    (suzukiLogFourierWeight_nonneg xi) _ _

theorem integrable_suzukiLogFourierWeight_mul_endpointFourierPairing
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    Integrable (fun xi : Real =>
      ((suzukiLogFourierWeight xi : Real) : Complex) *
        (FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi *
          conj (FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r m) xi))) := by
  have hweighted := integrable_mul_conj_of_suzukiL2_coe_ae
    (suzukiYoshidaEndpointLogWeightedFourierL2_coe_ae
      hsource hr m)
    (suzukiYoshidaEndpointLogWeightedFourierL2_coe_ae
      hsource hr n)
  apply hweighted.congr
  filter_upwards with xi
  exact sqrt_weight_mul_mul_conj_sqrt_weight_mul
    (suzukiLogFourierWeight_nonneg xi)
    (FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r m) xi)
    (FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r n) xi)

/-- The closed low-frequency-loss coordinate of one endpoint mode. -/
noncomputable def suzukiYoshidaEndpointLowFrequencyFourierL2
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) : SuzukiL2 :=
  suzukiLowFrequencyWeightedFourierCompletionMap hr
    (suzukiYoshidaExponentialLinearCompletionOfSource hsource hr n)

/-- The low-frequency-loss coordinate is represented by the square-root loss
times the ordinary endpoint Fourier transform. -/
theorem suzukiYoshidaEndpointLowFrequencyFourierL2_coe_ae
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (n : Int) :
    ((suzukiYoshidaEndpointLowFrequencyFourierL2 hsource hr n : SuzukiL2) :
        Real → Complex) =ᵐ[volume]
      fun xi =>
        ((Real.sqrt (suzukiLowFrequencyLogLoss xi) : Real) : Complex) *
          FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi := by
  exact
    suzukiLowFrequencyWeightedFourierCompletionMap_source_ordinary_coe_ae
      hsource hr n

/-- The closed low-frequency inner product is the ordinary endpoint pairing
weighted by the low-frequency logarithmic loss. -/
theorem inner_suzukiYoshidaEndpointLowFrequencyFourierL2_eq_integral
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    inner Complex
        (suzukiYoshidaEndpointLowFrequencyFourierL2 hsource hr m)
        (suzukiYoshidaEndpointLowFrequencyFourierL2 hsource hr n) =
      ∫ xi : Real,
        ((suzukiLowFrequencyLogLoss xi : Real) : Complex) *
          (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) xi *
            conj (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r m) xi)) := by
  rw [inner_suzukiL2_eq_integral_mul_conj_of_coe_ae
    (suzukiYoshidaEndpointLowFrequencyFourierL2_coe_ae
      hsource hr m)
    (suzukiYoshidaEndpointLowFrequencyFourierL2_coe_ae
      hsource hr n)]
  apply integral_congr_ae
  filter_upwards with xi
  exact sqrt_weight_mul_mul_conj_sqrt_weight_mul
    (suzukiLowFrequencyLogLoss_nonneg xi) _ _

theorem integrable_suzukiLowFrequencyLogLoss_mul_endpointFourierPairing
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    Integrable (fun xi : Real =>
      ((suzukiLowFrequencyLogLoss xi : Real) : Complex) *
        (FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r n) xi *
          conj (FourierTransform.fourier
            (suzukiYoshidaExponentialFunction r m) xi))) := by
  have hloss := integrable_mul_conj_of_suzukiL2_coe_ae
    (suzukiYoshidaEndpointLowFrequencyFourierL2_coe_ae
      hsource hr m)
    (suzukiYoshidaEndpointLowFrequencyFourierL2_coe_ae
      hsource hr n)
  apply hloss.congr
  filter_upwards with xi
  exact sqrt_weight_mul_mul_conj_sqrt_weight_mul
    (suzukiLowFrequencyLogLoss_nonneg xi)
    (FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r m) xi)
    (FourierTransform.fourier
      (suzukiYoshidaExponentialFunction r n) xi)

/-- The ordinary endpoint source pairing splits into the exact three pieces
appearing in the closed comparison form. -/
theorem suzukiYoshidaEndpointSourceFourierPairing_eq_graph_scalar_sub_loss
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    suzukiYoshidaEndpointSourceFourierPairing r n m =
      (∫ xi : Real,
        ((suzukiLogFourierWeight xi : Real) : Complex) *
          (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r n) xi *
            conj (FourierTransform.fourier
              (suzukiYoshidaExponentialFunction r m) xi))) +
        ((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex) *
          (∫ xi : Real,
            FourierTransform.fourier
                (suzukiYoshidaExponentialFunction r n) xi *
              conj (FourierTransform.fourier
                (suzukiYoshidaExponentialFunction r m) xi)) -
        ∫ xi : Real,
          ((suzukiLowFrequencyLogLoss xi : Real) : Complex) *
            (FourierTransform.fourier
                (suzukiYoshidaExponentialFunction r n) xi *
              conj (FourierTransform.fourier
                (suzukiYoshidaExponentialFunction r m) xi)) := by
  let p : Real → Complex := fun xi =>
    FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r n) xi *
      conj (FourierTransform.fourier
        (suzukiYoshidaExponentialFunction r m) xi)
  have hbase : Integrable p := by
    simpa only [p] using
      integrable_suzukiYoshidaEndpointFourierPairing hsource hr m n
  have hgraph : Integrable (fun xi : Real =>
      ((suzukiLogFourierWeight xi : Real) : Complex) * p xi) := by
    simpa only [p] using
      integrable_suzukiLogFourierWeight_mul_endpointFourierPairing
        hsource hr m n
  have hloss : Integrable (fun xi : Real =>
      ((suzukiLowFrequencyLogLoss xi : Real) : Complex) * p xi) := by
    simpa only [p] using
      integrable_suzukiLowFrequencyLogLoss_mul_endpointFourierPairing
        hsource hr m n
  unfold suzukiYoshidaEndpointSourceFourierPairing
    suzukiYoshidaEndpointSourceFourierIntegrand
  change (∫ xi : Real,
      ((suzukiSourceLogFourierWeight xi : Real) : Complex) * p xi) = _
  rw [show (∫ xi : Real,
      ((suzukiSourceLogFourierWeight xi : Real) : Complex) * p xi) =
      ∫ xi : Real,
        ((suzukiLogFourierWeight xi : Real) : Complex) * p xi +
          ((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex) *
            p xi -
          ((suzukiLowFrequencyLogLoss xi : Real) : Complex) * p xi by
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0 : Real)] with xi hxi
    rw [suzukiSourceLogFourierWeight_eq_graph_sub_loss hxi]
    push_cast
    ring]
  calc
    (∫ xi : Real,
        ((suzukiLogFourierWeight xi : Real) : Complex) * p xi +
          ((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex) *
            p xi -
          ((suzukiLowFrequencyLogLoss xi : Real) : Complex) * p xi) =
        (∫ xi : Real,
          ((suzukiLogFourierWeight xi : Real) : Complex) * p xi +
            ((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex) *
              p xi) -
          ∫ xi : Real,
            ((suzukiLowFrequencyLogLoss xi : Real) : Complex) * p xi := by
      exact integral_sub
        (hgraph.add (hbase.const_mul
          (((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex))))
        hloss
    _ = ((∫ xi : Real,
          ((suzukiLogFourierWeight xi : Real) : Complex) * p xi) +
          ∫ xi : Real,
            ((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex) *
              p xi) -
        ∫ xi : Real,
          ((suzukiLowFrequencyLogLoss xi : Real) : Complex) * p xi := by
      exact congrArg
        (fun z : Complex => z -
          ∫ xi : Real,
            ((suzukiLowFrequencyLogLoss xi : Real) : Complex) * p xi)
        (integral_add hgraph
          (hbase.const_mul
            (((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex))))
    _ = ((∫ xi : Real,
          ((suzukiLogFourierWeight xi : Real) : Complex) * p xi) +
          ((suzukiSourceLogNormalizationConstant - 1 : Real) : Complex) *
            ∫ xi : Real, p xi) -
        ∫ xi : Real,
          ((suzukiLowFrequencyLogLoss xi : Real) : Complex) * p xi := by
      rw [integral_const_mul]
    _ = _ := by rfl

/-- The graph inner product of two canonical endpoint lifts splits into its
physical and logarithmically weighted Fourier coordinates. -/
theorem inner_suzukiYoshidaExponentialLinearCompletionOfSource_eq
    {r : Real} (hsource : SuzukiYoshidaExponentialFormCoreSourceAt r)
    (hr : 0 < r) (m n : Int) :
    inner Complex
        (suzukiYoshidaExponentialLinearCompletionOfSource hsource hr m)
        (suzukiYoshidaExponentialLinearCompletionOfSource hsource hr n) =
      inner Complex
          (suzukiYoshidaExponentialL2 r hr m)
          (suzukiYoshidaExponentialL2 r hr n) +
        inner Complex
          (suzukiYoshidaEndpointLogWeightedFourierL2 hsource hr m)
          (suzukiYoshidaEndpointLogWeightedFourierL2 hsource hr n) := by
  rw [suzukiLogRadiusLinear_inner_eq_legacyEnergy]
  unfold suzukiLogRadiusEnergy
  rw [suzukiYoshidaExponentialLinearCompletionOfSource_legacyGraph,
    suzukiYoshidaExponentialLinearCompletionOfSource_legacyGraph]
  unfold suzukiYoshidaEndpointLogWeightedFourierL2
  rfl

/-- On canonical endpoint exponentials, the closed comparison form is exactly
the project-normalized ordinary source Fourier pairing.  The reversed mode
order records Lean's conjugate-linear-in-the-first inner-product convention. -/
theorem suzukiYoshidaComparisonForm_exponential_eq_endpointSourceFourierPairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialLinearCompletionOfSource
          hsource suzukiProjectAStar_pos n) =
      suzukiYoshidaEndpointSourceFourierPairing
        suzukiProjectAStar n m := by
  unfold suzukiYoshidaComparisonForm suzukiLowFrequencyLogLossEnergy
  rw [inner_suzukiYoshidaExponentialLinearCompletionOfSource_eq
      hsource suzukiProjectAStar_pos m n,
    suzukiYoshidaExponentialLinearCompletionOfSource_toL2,
    suzukiYoshidaExponentialLinearCompletionOfSource_toL2]
  change
    (inner Complex
        (suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos m)
        (suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos n) +
      inner Complex
        (suzukiYoshidaEndpointLogWeightedFourierL2
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaEndpointLogWeightedFourierL2
          hsource suzukiProjectAStar_pos n)) +
      ((suzukiSourceLogNormalizationConstant - 2 : Real) : Complex) *
        inner Complex
          (suzukiYoshidaExponentialL2 suzukiProjectAStar
            suzukiProjectAStar_pos m)
          (suzukiYoshidaExponentialL2 suzukiProjectAStar
            suzukiProjectAStar_pos n) -
      inner Complex
        (suzukiYoshidaEndpointLowFrequencyFourierL2
          hsource suzukiProjectAStar_pos m)
        (suzukiYoshidaEndpointLowFrequencyFourierL2
          hsource suzukiProjectAStar_pos n) = _
  rw [inner_suzukiYoshidaExponentialL2_eq_fourierIntegral
      hsource suzukiProjectAStar_pos m n,
    inner_suzukiYoshidaEndpointLogWeightedFourierL2_eq_integral
      hsource suzukiProjectAStar_pos m n,
    inner_suzukiYoshidaEndpointLowFrequencyFourierL2_eq_integral
      hsource suzukiProjectAStar_pos m n,
    suzukiYoshidaEndpointSourceFourierPairing_eq_graph_scalar_sub_loss
      hsource suzukiProjectAStar_pos m n]
  push_cast
  ring

/-- The closed comparison-limit kernel is identified with the ordinary
endpoint source pairing for every integer-mode pair. -/
theorem suzukiYoshidaComparisonLimitKernel_eq_endpointSourceFourierPairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Int) :
    suzukiYoshidaComparisonLimitKernel hsource m n =
      suzukiYoshidaEndpointSourceFourierPairing
        suzukiProjectAStar n m := by
  rw [← suzukiYoshidaComparisonForm_exponential_eq_limitKernel hsource m n]
  exact
    suzukiYoshidaComparisonForm_exponential_eq_endpointSourceFourierPairing
      hsource m n

end

end RiemannHypothesisProject.Experiments.M100
