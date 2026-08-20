import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaResidualModalNormalization

/-!
# Exact modal coefficients for the B3R-E residual functionals

This module identifies the completed-mode pairings constructed in B3R-E4
with the independently frozen DF6D4 residual coefficients.  The comparison
diagonal uses the corrected C1 cosine tail; the equation-(2.5) source and
form-core hypotheses remain explicit.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-! ## Corrected comparison diagonals -/

private theorem integral_scaled_suzukiCosineRegularPart
    (mode : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      ((mode : Real) * Real.pi / suzukiProjectAStar) *
        suzukiCosineRegularPart
          (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
      ∫ u in (0 : Real)..suzukiDF6D4ComparisonWave mode,
        suzukiCosineRegularPart u := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hw : 0 < w := by
    unfold w
    exact div_pos (mul_pos (by exact_mod_cast hmode) Real.pi_pos)
      suzukiProjectAStar_pos
  calc
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      ((mode : Real) * Real.pi / suzukiProjectAStar) *
        suzukiCosineRegularPart
          (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
        w * ∫ t in (0 : Real)..2 * suzukiProjectAStar,
          suzukiCosineRegularPart (w * t) := by
            simp only [w, intervalIntegral.integral_const_mul]
    _ = ∫ u in w * 0..w * (2 * suzukiProjectAStar),
        suzukiCosineRegularPart u := by
          simpa only [smul_eq_mul] using
            (intervalIntegral.smul_integral_comp_mul_left
              suzukiCosineRegularPart w (a := (0 : Real))
                (b := 2 * suzukiProjectAStar))
    _ = ∫ u in (0 : Real)..suzukiDF6D4ComparisonWave mode,
        suzukiCosineRegularPart u := by
          congr 1
          · ring
          · unfold w suzukiDF6D4ComparisonWave
            field_simp [suzukiProjectAStar_pos.ne']

private theorem integral_scaled_cosine_eq_zero
    (mode : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      ((mode : Real) * Real.pi / suzukiProjectAStar) *
        Real.cos (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) = 0 := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hw : 0 < w := by
    unfold w
    exact div_pos (mul_pos (by exact_mod_cast hmode) Real.pi_pos)
      suzukiProjectAStar_pos
  calc
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      ((mode : Real) * Real.pi / suzukiProjectAStar) *
        Real.cos (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
        ∫ u in w * 0..w * (2 * suzukiProjectAStar), Real.cos u := by
          rw [intervalIntegral.integral_const_mul]
          simpa only [w, smul_eq_mul] using
            (intervalIntegral.smul_integral_comp_mul_left
              Real.cos w (a := (0 : Real))
                (b := 2 * suzukiProjectAStar))
    _ = 0 := by
      rw [integral_cos]
      simp only [mul_zero, Real.sin_zero, sub_zero]
      rw [show w * (2 * suzukiProjectAStar) =
          (2 * mode : Nat) * Real.pi by
        unfold w
        push_cast
        field_simp [suzukiProjectAStar_pos.ne']]
      rw [Real.sin_nat_mul_pi]

private theorem integral_scaled_sinc_eq_comparisonSineIntegral
    (mode : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      ((mode : Real) * Real.pi / suzukiProjectAStar) *
        Real.sinc (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
      suzukiDF6D4ComparisonSineIntegral mode := by
  have hsine :=
    suzukiDF6D4SingularSineIntegral_eq_comparisonSineIntegral'
      mode hmode
  calc
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      ((mode : Real) * Real.pi / suzukiProjectAStar) *
        Real.sinc (((mode : Real) * Real.pi / suzukiProjectAStar) * t)) =
        2 * (∫ t in (0 : Real)..2 * suzukiProjectAStar,
          (1 / (2 * t)) *
            Real.sin (((mode : Real) * Real.pi /
              suzukiProjectAStar) * t)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_ae
      filter_upwards [volume.ae_ne (0 : Real)] with t ht
      intro _
      rw [Real.sinc_of_ne_zero]
      · field_simp [ht, suzukiProjectAStar_pos.ne']
      · exact mul_ne_zero
          (div_ne_zero (mul_ne_zero (by exact_mod_cast hmode.ne')
            Real.pi_ne_zero) suzukiProjectAStar_pos.ne') ht
    _ = suzukiDF6D4ComparisonSineIntegral mode := hsine

theorem integral_suzukiYoshidaEvenPositiveDiagonalRegularPart
    (mode : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      suzukiYoshidaEvenPositiveDiagonalRegularPart mode t) =
      -Real.eulerMascheroniConstant -
        Real.log (suzukiDF6D4ComparisonWave mode) -
          suzukiDF6D4ComparisonCosineTail mode -
            suzukiDF6D4ComparisonSineIntegral mode /
              suzukiDF6D4ComparisonWave mode := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hw : 0 < w := by
    unfold w
    exact div_pos (mul_pos (by exact_mod_cast hmode) Real.pi_pos)
      suzukiProjectAStar_pos
  have hwave : suzukiDF6D4ComparisonWave mode =
      (2 * suzukiProjectAStar) * w := by
    unfold suzukiDF6D4ComparisonWave w
    push_cast
    field_simp [suzukiProjectAStar_pos.ne']
  have hreg := integral_scaled_suzukiCosineRegularPart mode hmode
  have hcos := integral_scaled_cosine_eq_zero mode hmode
  have hsinc := integral_scaled_sinc_eq_comparisonSineIntegral mode hmode
  have htail := integral_suzukiCosineRegularPart_to_wave mode hmode
  unfold suzukiYoshidaEvenPositiveDiagonalRegularPart
  dsimp only
  change (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      w * suzukiCosineRegularPart (w * t) -
        Real.cos (w * t) / (2 * suzukiProjectAStar) -
          Real.sinc (w * t) / (2 * suzukiProjectAStar)) = _
  have hregInt : IntervalIntegrable
      (fun t : Real => w * suzukiCosineRegularPart (w * t)) volume
      0 (2 * suzukiProjectAStar) :=
    (continuous_const.mul
      (continuous_suzukiCosineRegularPart.comp
        (continuous_const.mul continuous_id))).intervalIntegrable _ _
  have hcosInt : IntervalIntegrable
      (fun t : Real => Real.cos (w * t) / (2 * suzukiProjectAStar)) volume
      0 (2 * suzukiProjectAStar) :=
    ((Real.continuous_cos.comp
      (continuous_const.mul continuous_id)).div_const _).intervalIntegrable _ _
  have hsincInt : IntervalIntegrable
      (fun t : Real => Real.sinc (w * t) / (2 * suzukiProjectAStar)) volume
      0 (2 * suzukiProjectAStar) :=
    ((Real.continuous_sinc.comp
      (continuous_const.mul continuous_id)).div_const _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hregInt.sub hcosInt) hsincInt,
    intervalIntegral.integral_sub hregInt hcosInt]
  rw [show (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      Real.cos (w * t) / (2 * suzukiProjectAStar)) = 0 by
        rw [show (fun t : Real => Real.cos (w * t) /
            (2 * suzukiProjectAStar)) =
          fun t => (suzukiDF6D4ComparisonWave mode)⁻¹ *
            (w * Real.cos (w * t)) by
              funext t
              rw [hwave]
              field_simp [hw.ne', suzukiProjectAStar_pos.ne']]
        rw [intervalIntegral.integral_const_mul, hcos, mul_zero],
    show (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      Real.sinc (w * t) / (2 * suzukiProjectAStar)) =
        suzukiDF6D4ComparisonSineIntegral mode /
          suzukiDF6D4ComparisonWave mode by
      rw [show (fun t : Real => Real.sinc (w * t) /
          (2 * suzukiProjectAStar)) =
        fun t => (suzukiDF6D4ComparisonWave mode)⁻¹ *
          (w * Real.sinc (w * t)) by
            funext t
            rw [hwave]
            field_simp [hw.ne', suzukiProjectAStar_pos.ne']]
      rw [intervalIntegral.integral_const_mul, hsinc]
      ring]
  rw [hreg, htail]
  ring

theorem integral_suzukiYoshidaOddDiagonalRegularPart
    (mode : Nat) (hmode : 0 < mode) :
    (∫ t in (0 : Real)..2 * suzukiProjectAStar,
      suzukiYoshidaOddDiagonalRegularPart mode t) =
      -Real.eulerMascheroniConstant -
        Real.log (suzukiDF6D4ComparisonWave mode) -
          suzukiDF6D4ComparisonCosineTail mode +
            suzukiDF6D4ComparisonSineIntegral mode /
              suzukiDF6D4ComparisonWave mode := by
  let w : Real := (mode : Real) * Real.pi / suzukiProjectAStar
  have hw : 0 < w := by
    unfold w
    exact div_pos (mul_pos (by exact_mod_cast hmode) Real.pi_pos)
      suzukiProjectAStar_pos
  have hwave : suzukiDF6D4ComparisonWave mode =
      (2 * suzukiProjectAStar) * w := by
    unfold suzukiDF6D4ComparisonWave w
    push_cast
    field_simp [suzukiProjectAStar_pos.ne']
  have heven :=
    integral_suzukiYoshidaEvenPositiveDiagonalRegularPart mode hmode
  have hsinc := integral_scaled_sinc_eq_comparisonSineIntegral mode hmode
  have hpoint : suzukiYoshidaOddDiagonalRegularPart mode =
      fun t => suzukiYoshidaEvenPositiveDiagonalRegularPart mode t +
        2 * (Real.sinc (w * t) / (2 * suzukiProjectAStar)) := by
    funext t
    unfold suzukiYoshidaOddDiagonalRegularPart
      suzukiYoshidaEvenPositiveDiagonalRegularPart
    dsimp only
    change w * suzukiCosineRegularPart (w * t) -
        Real.cos (w * t) / (2 * suzukiProjectAStar) +
          Real.sinc (w * t) / (2 * suzukiProjectAStar) = _
    ring
  rw [hpoint]
  have hevenInt : IntervalIntegrable
      (suzukiYoshidaEvenPositiveDiagonalRegularPart mode) volume
      0 (2 * suzukiProjectAStar) :=
    (continuous_suzukiYoshidaEvenPositiveDiagonalRegularPart mode).intervalIntegrable _ _
  have hsincInt : IntervalIntegrable
      (fun t : Real => 2 *
        (Real.sinc (w * t) / (2 * suzukiProjectAStar))) volume
      0 (2 * suzukiProjectAStar) :=
    (continuous_const.mul
      ((Real.continuous_sinc.comp
        (continuous_const.mul continuous_id)).div_const _)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hevenInt hsincInt, heven]
  have hsincDiv :
      (∫ t in (0 : Real)..2 * suzukiProjectAStar,
        Real.sinc (w * t) / (2 * suzukiProjectAStar)) =
          suzukiDF6D4ComparisonSineIntegral mode /
            suzukiDF6D4ComparisonWave mode := by
    rw [show (fun t : Real => Real.sinc (w * t) /
        (2 * suzukiProjectAStar)) =
      fun t => (suzukiDF6D4ComparisonWave mode)⁻¹ *
        (w * Real.sinc (w * t)) by
          funext t
          rw [hwave]
          field_simp [hw.ne', suzukiProjectAStar_pos.ne']]
    rw [intervalIntegral.integral_const_mul, hsinc]
    ring
  rw [intervalIntegral.integral_const_mul, hsincDiv]
  ring

theorem suzukiYoshidaComparisonForm_evenPositive_diagonal_eq_df6d4
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaEvenLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      (suzukiDF6D4EvenComparisonDiagonal mode : Complex) := by
  rw [suzukiYoshidaComparisonForm_evenPositive_diagonal
      hsource mode hmode,
    integral_suzukiYoshidaEvenPositiveDiagonalRegularPart mode hmode]
  norm_cast
  unfold suzukiDF6D4EvenComparisonDiagonal
    suzukiDF6D4ComparisonWave
  have hmode0 : (mode : Real) ≠ 0 := by exact_mod_cast hmode.ne'
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      suzukiProjectAStar_pos.ne',
    Real.log_mul (mul_ne_zero (by norm_num : (2 : Real) ≠ 0) hmode0)
      Real.pi_ne_zero,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0) hmode0]
  ring

theorem suzukiYoshidaComparisonForm_odd_diagonal_eq_df6d4
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) (hmode : 0 < mode) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode)
        (suzukiYoshidaOddLinearCompletionOfSource
          hsource suzukiProjectAStar_pos mode) =
      (suzukiDF6D4OddComparisonDiagonal mode : Complex) := by
  rw [suzukiYoshidaComparisonForm_odd_diagonal hsource mode hmode,
    integral_suzukiYoshidaOddDiagonalRegularPart mode hmode]
  norm_cast
  unfold suzukiDF6D4OddComparisonDiagonal
    suzukiDF6D4ComparisonWave
  have hmode0 : (mode : Real) ≠ 0 := by exact_mod_cast hmode.ne'
  rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      suzukiProjectAStar_pos.ne',
    Real.log_mul (mul_ne_zero (by norm_num : (2 : Real) ≠ 0) hmode0)
      Real.pi_ne_zero,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0) hmode0]
  ring

/-! ## Frozen Galerkin comparison entries -/

theorem suzukiYoshidaComparisonForm_evenGalerkinMode_eq_df6d4
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (j k : Fin 256) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))
        (suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j)) =
      (suzukiDF6D4EvenComparisonGalerkinEntry j k : Complex) := by
  have hcomparison :=
    (suzukiEquation25OffDiagonalComparisonEvaluations_of_source hsource).1
  by_cases heq : j = k
  · subst k
    simp only [suzukiDF6D4EvenComparisonGalerkinEntry, if_pos]
    exact suzukiYoshidaComparisonForm_evenPositive_diagonal_eq_df6d4
      hsource (suzukiDF6D4GalerkinMode j)
        (by simp [suzukiDF6D4GalerkinMode])
  · by_cases hjk : j.val < k.val
    · have hmode : suzukiDF6D4GalerkinMode j <
          suzukiDF6D4GalerkinMode k := by
        simp [suzukiDF6D4GalerkinMode]
        omega
      calc
        suzukiYoshidaComparisonForm
            (suzukiYoshidaEvenLinearCompletionOfSource hsource
              suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))
            (suzukiYoshidaEvenLinearCompletionOfSource hsource
              suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j)) =
            conj (suzukiYoshidaComparisonForm
              (suzukiYoshidaEvenLinearCompletionOfSource hsource
                suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j))
              (suzukiYoshidaEvenLinearCompletionOfSource hsource
                suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))) :=
          suzukiYoshidaComparisonForm_conj_symm _ _
        _ = (suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode j)
            (suzukiDF6D4GalerkinMode k) : Complex) := by
          rw [hcomparison _ _ hmode]
          simp
        _ = (suzukiDF6D4EvenComparisonGalerkinEntry j k : Complex) := by
          simp [suzukiDF6D4EvenComparisonGalerkinEntry, heq, hjk]
    · have hkj : k.val < j.val := by
        have hne : k.val ≠ j.val := fun h => heq (Fin.ext h.symm)
        omega
      have hmode : suzukiDF6D4GalerkinMode k <
          suzukiDF6D4GalerkinMode j := by
        simp [suzukiDF6D4GalerkinMode]
        omega
      rw [hcomparison _ _ hmode]
      simp [suzukiDF6D4EvenComparisonGalerkinEntry, heq, hjk]

theorem suzukiYoshidaComparisonForm_oddGalerkinMode_eq_df6d4
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (j k : Fin 256) :
    suzukiYoshidaComparisonForm
        (suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))
        (suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j)) =
      (suzukiDF6D4OddComparisonGalerkinEntry j k : Complex) := by
  have hcomparison :=
    (suzukiEquation25OffDiagonalComparisonEvaluations_of_source hsource).2
  by_cases heq : j = k
  · subst k
    simp only [suzukiDF6D4OddComparisonGalerkinEntry, if_pos]
    exact suzukiYoshidaComparisonForm_odd_diagonal_eq_df6d4
      hsource (suzukiDF6D4GalerkinMode j)
        (by simp [suzukiDF6D4GalerkinMode])
  · by_cases hjk : j.val < k.val
    · have hmode : suzukiDF6D4GalerkinMode j <
          suzukiDF6D4GalerkinMode k := by
        simp [suzukiDF6D4GalerkinMode]
        omega
      calc
        suzukiYoshidaComparisonForm
            (suzukiYoshidaOddLinearCompletionOfSource hsource
              suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))
            (suzukiYoshidaOddLinearCompletionOfSource hsource
              suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j)) =
            conj (suzukiYoshidaComparisonForm
              (suzukiYoshidaOddLinearCompletionOfSource hsource
                suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j))
              (suzukiYoshidaOddLinearCompletionOfSource hsource
                suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))) :=
          suzukiYoshidaComparisonForm_conj_symm _ _
        _ = (suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode j)
            (suzukiDF6D4GalerkinMode k) : Complex) := by
          rw [hcomparison _ _ (by simp [suzukiDF6D4GalerkinMode]) hmode]
          simp
        _ = (suzukiDF6D4OddComparisonGalerkinEntry j k : Complex) := by
          simp [suzukiDF6D4OddComparisonGalerkinEntry, heq, hjk]
    · have hkj : k.val < j.val := by
        have hne : k.val ≠ j.val := fun h => heq (Fin.ext h.symm)
        omega
      have hmode : suzukiDF6D4GalerkinMode k <
          suzukiDF6D4GalerkinMode j := by
        simp [suzukiDF6D4GalerkinMode]
        omega
      rw [hcomparison _ _ (by simp [suzukiDF6D4GalerkinMode]) hmode]
      simp [suzukiDF6D4OddComparisonGalerkinEntry, heq, hjk]

private theorem suzukiYoshidaComparisonForm_sum_left
    {ι : Type*} (s : Finset ι)
    (f : ι → SuzukiYoshidaCorrectedCommonFormDomain)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm (∑ i ∈ s, f i) v =
      ∑ i ∈ s, suzukiYoshidaComparisonForm (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (suzukiYoshidaComparisonForm_smul_left
          (0 : Complex) (0 : SuzukiYoshidaCorrectedCommonFormDomain) v)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [suzukiYoshidaComparisonForm_add_left, ih]

theorem suzukiYoshidaComparisonForm_evenGalerkinTrial_mode
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) (j : Fin 256) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i)
        (suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j)) =
      ((∑ k : Fin 256,
        suzukiDF6D4EvenComparisonGalerkinEntry j k *
          (suzukiDF6D4EvenGalerkinApproximant k i : Real) : Real) :
            Complex) := by
  unfold suzukiDF6D5B3REEvenGalerkinTrialCompletion
  rw [show (∑ k : Fin 256,
      ((suzukiDF6D4EvenGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k)) =
      ∑ k ∈ Finset.univ,
      ((suzukiDF6D4EvenGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) by simp]
  rw [suzukiYoshidaComparisonForm_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left,
    suzukiYoshidaComparisonForm_evenGalerkinMode_eq_df6d4 hsource]
  simp
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiYoshidaComparisonForm_oddGalerkinTrial_mode
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) (j : Fin 256) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i)
        (suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode j)) =
      ((∑ k : Fin 256,
        suzukiDF6D4OddComparisonGalerkinEntry j k *
          (suzukiDF6D4OddGalerkinApproximant k i : Real) : Real) :
            Complex) := by
  unfold suzukiDF6D5B3REOddGalerkinTrialCompletion
  rw [show (∑ k : Fin 256,
      ((suzukiDF6D4OddGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k)) =
      ∑ k ∈ Finset.univ,
      ((suzukiDF6D4OddGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) by simp]
  rw [suzukiYoshidaComparisonForm_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left,
    suzukiYoshidaComparisonForm_oddGalerkinMode_eq_df6d4 hsource]
  simp
  apply Finset.sum_congr rfl
  intro k _
  ring

/-! ## Corrected low-to-tail entries and the far comparison columns -/

private theorem suzukiEquation25ParityEntries_of_source
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiEquation25EvenYoshidaEntryEvaluation hsource ∧
      SuzukiEquation25OddYoshidaEntryEvaluation hsource := by
  have hcomparison :=
    suzukiEquation25OffDiagonalComparisonEvaluations_of_source hsource
  exact suzukiEquation25ParityEntries_of_componentEvaluations
    hsource hequation25 hcomparison.1
      (suzukiEquation25EvenOffDiagonalCorrectionEvaluation_of_gamma hsource
        (suzukiEquation25EvenOffDiagonalGammaEvaluation hsource))
      hcomparison.2
      (suzukiEquation25OddOffDiagonalCorrectionEvaluation_of_gamma hsource
        (suzukiEquation25OddOffDiagonalGammaEvaluation hsource))
      (suzukiEquation25EvenDiagonalPrimeEvaluation hsource)
      (suzukiEquation25EvenDiagonalArchimedeanEvaluation hsource)
      (suzukiEquation25OddDiagonalPrimeEvaluation hsource)
      (suzukiEquation25OddDiagonalArchimedeanEvaluation hsource)

theorem suzukiYoshidaCorrectedCompleteForm_evenLow_tail
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i : Fin 45) (mode : Nat) (hmode : 45 ≤ mode) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REEvenLowSourceCompletion hsource i)
        (suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos mode) =
      (suzukiDF6D4EvenOffDiagonal
        (suzukiDF6D4EvenLowMode i) mode : Complex) := by
  have hlt : suzukiDF6D4EvenLowMode i < mode := by
    unfold suzukiDF6D4EvenLowMode
    have := i.isLt
    omega
  unfold suzukiDF6D5B3REEvenLowSourceCompletion
  rw [suzukiYoshidaCorrectedCompleteForm_evenSource
    hsource hequation25]
  rw [(suzukiEquation25ParityEntries_of_source hsource hequation25).1]
  simp [suzukiYoshidaCorrectedEvenEntry, ne_of_lt hlt,
    min_eq_left hlt.le, max_eq_right hlt.le]

theorem suzukiYoshidaCorrectedCompleteForm_oddLow_tail
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i : Fin 44) (mode : Nat) (hmode : 45 ≤ mode) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REOddLowSourceCompletion hsource i)
        (suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos mode) =
      (suzukiDF6D4OddOffDiagonal
        (suzukiDF6D4OddLowMode i) mode : Complex) := by
  have hlow : 0 < suzukiDF6D4OddLowMode i := by
    simp [suzukiDF6D4OddLowMode]
  have hlt : suzukiDF6D4OddLowMode i < mode := by
    unfold suzukiDF6D4OddLowMode
    have := i.isLt
    omega
  unfold suzukiDF6D5B3REOddLowSourceCompletion
  rw [suzukiYoshidaCorrectedCompleteForm_oddSource
    hsource hequation25]
  rw [(suzukiEquation25ParityEntries_of_source hsource hequation25).2
    _ _ hlow (hlow.trans hlt)]
  simp [suzukiYoshidaCorrectedOddEntry, ne_of_lt hlt,
    min_eq_left hlt.le, max_eq_right hlt.le]

theorem suzukiYoshidaComparisonForm_evenGalerkinTrial_farMode
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) (mode : Nat) (hmode : 301 ≤ mode) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i)
        (suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos mode) =
      ((∑ k : Fin 256,
        (suzukiDF6D4EvenGalerkinApproximant k i : Real) *
          suzukiDF6D4ComparisonEvenOffDiagonal
            (suzukiDF6D4GalerkinMode k) mode : Real) : Complex) := by
  have hcomparison :=
    (suzukiEquation25OffDiagonalComparisonEvaluations_of_source hsource).1
  unfold suzukiDF6D5B3REEvenGalerkinTrialCompletion
  rw [show (∑ k : Fin 256,
      ((suzukiDF6D4EvenGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k)) =
      ∑ k ∈ Finset.univ,
      ((suzukiDF6D4EvenGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) by simp]
  rw [suzukiYoshidaComparisonForm_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left]
  have hentry (k : Fin 256) :
      suzukiYoshidaComparisonForm
          (suzukiYoshidaEvenLinearCompletionOfSource hsource
            suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))
          (suzukiYoshidaEvenLinearCompletionOfSource hsource
            suzukiProjectAStar_pos mode) =
        (suzukiDF6D4ComparisonEvenOffDiagonal
          (suzukiDF6D4GalerkinMode k) mode : Complex) := by
    apply hcomparison
    have := k.isLt
    simp [suzukiDF6D4GalerkinMode] at *
    omega
  simp_rw [hentry]
  simp

theorem suzukiYoshidaComparisonForm_oddGalerkinTrial_farMode
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) (mode : Nat) (hmode : 301 ≤ mode) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i)
        (suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos mode) =
      ((∑ k : Fin 256,
        (suzukiDF6D4OddGalerkinApproximant k i : Real) *
          suzukiDF6D4ComparisonOddOffDiagonal
            (suzukiDF6D4GalerkinMode k) mode : Real) : Complex) := by
  have hcomparison :=
    (suzukiEquation25OffDiagonalComparisonEvaluations_of_source hsource).2
  unfold suzukiDF6D5B3REOddGalerkinTrialCompletion
  rw [show (∑ k : Fin 256,
      ((suzukiDF6D4OddGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k)) =
      ∑ k ∈ Finset.univ,
      ((suzukiDF6D4OddGalerkinApproximant k i : Real) : Complex) •
        suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) by simp]
  rw [suzukiYoshidaComparisonForm_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left]
  have hentry (k : Fin 256) :
      suzukiYoshidaComparisonForm
          (suzukiYoshidaOddLinearCompletionOfSource hsource
            suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k))
          (suzukiYoshidaOddLinearCompletionOfSource hsource
            suzukiProjectAStar_pos mode) =
        (suzukiDF6D4ComparisonOddOffDiagonal
          (suzukiDF6D4GalerkinMode k) mode : Complex) := by
    apply hcomparison
    · simp [suzukiDF6D4GalerkinMode]
    · have := k.isLt
      simp [suzukiDF6D4GalerkinMode] at *
      omega
  simp_rw [hentry]
  simp

/-! ## Ambient residual modal coefficients -/

theorem suzukiDF6D5B3REEvenAmbientResidualFunctional_coefficient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i : Fin 45) (n : SuzukiDF6D5B3RTailMode) :
    suzukiDF6D5B3REEvenAmbientResidualFunctional hsource i
        (suzukiDF6D5B3REvenAmbientMode n) =
      (suzukiDF6D5B3REvenFullResidualCoefficient i n : Complex) := by
  rw [suzukiDF6D5B3REEvenAmbientResidualFunctional_mode_pairing]
  by_cases hnear : n.1 < 301
  · let j : Fin 256 := ⟨n.1 - 45, by omega⟩
    have hj : suzukiDF6D4GalerkinMode j = n.1 := by
      change 45 + (n.1 - 45) = n.1
      omega
    have hn : n =
        ⟨suzukiDF6D4GalerkinMode j, by
          simp [suzukiDF6D4GalerkinMode]⟩ := by
      apply Subtype.ext
      exact hj.symm
    rw [hn]
    rw [suzukiYoshidaCorrectedCompleteForm_evenLow_tail
        hsource hequation25 i (suzukiDF6D4GalerkinMode j)
          (by simp [suzukiDF6D4GalerkinMode]),
      suzukiYoshidaComparisonForm_evenGalerkinTrial_mode hsource i j,
      suzukiDF6D5B3REvenFullResidualCoefficient_galerkin]
    norm_cast
  · have hfar : 301 ≤ n.1 := by omega
    rw [suzukiYoshidaCorrectedCompleteForm_evenLow_tail
        hsource hequation25 i n.1 n.2,
      suzukiYoshidaComparisonForm_evenGalerkinTrial_farMode
        hsource i n.1 hfar,
      suzukiDF6D5B3REvenFullResidualCoefficient_of_ge i n.1 hfar]
    norm_cast

theorem suzukiDF6D5B3REOddAmbientResidualFunctional_coefficient
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i : Fin 44) (n : SuzukiDF6D5B3RTailMode) :
    suzukiDF6D5B3REOddAmbientResidualFunctional hsource i
        (suzukiDF6D5B3ROddAmbientMode n) =
      (suzukiDF6D5B3ROddFullResidualCoefficient i n : Complex) := by
  rw [suzukiDF6D5B3REOddAmbientResidualFunctional_mode_pairing]
  by_cases hnear : n.1 < 301
  · let j : Fin 256 := ⟨n.1 - 45, by omega⟩
    have hj : suzukiDF6D4GalerkinMode j = n.1 := by
      change 45 + (n.1 - 45) = n.1
      omega
    have hn : n =
        ⟨suzukiDF6D4GalerkinMode j, by
          simp [suzukiDF6D4GalerkinMode]⟩ := by
      apply Subtype.ext
      exact hj.symm
    rw [hn]
    rw [suzukiYoshidaCorrectedCompleteForm_oddLow_tail
        hsource hequation25 i (suzukiDF6D4GalerkinMode j)
          (by simp [suzukiDF6D4GalerkinMode]),
      suzukiYoshidaComparisonForm_oddGalerkinTrial_mode hsource i j,
      suzukiDF6D5B3ROddFullResidualCoefficient_galerkin]
    norm_cast
  · have hfar : 301 ≤ n.1 := by omega
    rw [suzukiYoshidaCorrectedCompleteForm_oddLow_tail
        hsource hequation25 i n.1 n.2,
      suzukiYoshidaComparisonForm_oddGalerkinTrial_farMode
        hsource i n.1 hfar,
      suzukiDF6D5B3ROddFullResidualCoefficient_of_ge i n.1 hfar]
    norm_cast

end

end RiemannHypothesisProject.Experiments.M100
