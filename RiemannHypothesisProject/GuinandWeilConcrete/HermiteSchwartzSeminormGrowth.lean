import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import RiemannHypothesisProject.GuinandWeilConcrete.HermiteSchwartzCoefficients

/-!
# Polynomial Schwartz-seminorm growth of normalized Hermite tests

This module develops the reverse half of the Hermite--Schwartz coefficient
correspondence.  The normalized creation/annihilation identities from
`HermiteSchwartzCoefficients` are used to control arbitrary words in coordinate
multiplication and differentiation in `L2`; Fourier inversion and a weighted
`L2` estimate then convert those bounds into project Schwartz seminorm bounds.
-/

namespace RiemannHypothesisProject

open Filter MeasureTheory Topology
open scoped FourierTransform

noncomputable section

/-- The two first-order operators needed to generate the project Schwartz
seminorms of the Hermite family. -/
inductive GuinandWeilPiHermiteFirstOrderOperator
  | coordinate
  | deriv
  deriving DecidableEq

/-- Interpret a first-order Hermite operator as a continuous linear
endomorphism of project Schwartz space. -/
noncomputable def guinandWeilPiHermiteFirstOrderOperatorCLM
    (op : GuinandWeilPiHermiteFirstOrderOperator) :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  match op with
  | .coordinate => guinandWeilPiOscillatorCoordinateCLM
  | .deriv => SchwartzMap.derivCLM Complex Complex

/-- Apply a word of first-order operators from left to right. -/
noncomputable def guinandWeilPiHermiteOperatorWordCLM :
    List GuinandWeilPiHermiteFirstOrderOperator →
      SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction
  | [] => ContinuousLinearMap.id Complex SchwartzLineTestFunction
  | op :: ops =>
      guinandWeilPiHermiteOperatorWordCLM ops ∘L
        guinandWeilPiHermiteFirstOrderOperatorCLM op

@[simp]
theorem guinandWeilPiHermiteOperatorWordCLM_nil
    (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteOperatorWordCLM [] f = f :=
  rfl

@[simp]
theorem guinandWeilPiHermiteOperatorWordCLM_cons
    (op : GuinandWeilPiHermiteFirstOrderOperator)
    (ops : List GuinandWeilPiHermiteFirstOrderOperator)
    (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteOperatorWordCLM (op :: ops) f =
      guinandWeilPiHermiteOperatorWordCLM ops
        (guinandWeilPiHermiteFirstOrderOperatorCLM op f) :=
  rfl

/-- A convenient fixed positive constant for coarse polynomial bounds on all
normalized ladder weights. -/
noncomputable def guinandWeilPiHermiteLadderGrowthConstant : Real :=
  2 * guinandWeilPiOscillatorScale + 1

theorem guinandWeilPiHermiteLadderGrowthConstant_pos :
    0 < guinandWeilPiHermiteLadderGrowthConstant := by
  unfold guinandWeilPiHermiteLadderGrowthConstant
  nlinarith [guinandWeilPiOscillatorScale_pos]

/-- The square-root ladder weight is bounded by a linear function of its
index.  This deliberately coarse estimate is stable under iterating words of
coordinate and derivative operators. -/
theorem guinandWeilPiHermiteLadderWeight_le_linear (n : Nat) :
    guinandWeilPiHermiteLadderWeight n ≤
      guinandWeilPiHermiteLadderGrowthConstant * ((n + 1 : Nat) : Real) := by
  let z : Real := 2 * guinandWeilPiOscillatorScale * (n : Real)
  have hz : 0 ≤ z := by
    dsimp [z]
    exact mul_nonneg
      (mul_nonneg (by norm_num) guinandWeilPiOscillatorScale_pos.le)
      (by positivity)
  have hsqrt : Real.sqrt z ≤ z + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · nlinarith
    · nlinarith [sq_nonneg z]
  have hlinear :
      z + 1 ≤
        guinandWeilPiHermiteLadderGrowthConstant * ((n + 1 : Nat) : Real) := by
    dsimp [z, guinandWeilPiHermiteLadderGrowthConstant]
    push_cast
    nlinarith [guinandWeilPiOscillatorScale_pos.le]
  exact hsqrt.trans hlinear

/-- Apply an operator word and then take the canonical `L2` image. -/
noncomputable def guinandWeilPiHermiteOperatorWordToL2CLM
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) :
    SchwartzLineTestFunction →L[Complex]
      Lp Complex (2 : ENNReal) (volume : Measure Real) :=
  SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume ∘L
    guinandWeilPiHermiteOperatorWordCLM ops

@[simp]
theorem guinandWeilPiHermiteOperatorWordToL2CLM_cons
    (op : GuinandWeilPiHermiteFirstOrderOperator)
    (ops : List GuinandWeilPiHermiteFirstOrderOperator)
    (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteOperatorWordToL2CLM (op :: ops) f =
      guinandWeilPiHermiteOperatorWordToL2CLM ops
        (guinandWeilPiHermiteFirstOrderOperatorCLM op f) :=
  rfl

/-- `L2` norm of an operator word applied to the `n`th normalized Hermite
test. -/
noncomputable def guinandWeilPiHermiteOperatorWordL2Norm
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) : Real :=
  ‖guinandWeilPiHermiteOperatorWordToL2CLM ops
      (guinandWeilPiNormalizedHermiteSchwartz n)‖

@[simp]
theorem norm_toLp_guinandWeilPiHermiteOperatorWordCLM_normalizedHermite
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) :
    ‖(guinandWeilPiHermiteOperatorWordCLM ops
        (guinandWeilPiNormalizedHermiteSchwartz n)).toLp
          (2 : ENNReal) volume‖ =
      guinandWeilPiHermiteOperatorWordL2Norm ops n :=
  rfl

theorem guinandWeilPiHermiteLadderWeight_nonneg (n : Nat) :
    0 ≤ guinandWeilPiHermiteLadderWeight n := by
  exact Real.sqrt_nonneg _

/-- One coordinate or derivative step gives the same two-neighbour `L2`
majorant; the sign in the derivative formula disappears under the norm. -/
theorem guinandWeilPiHermiteOperatorWordL2Norm_cons_le
    (op : GuinandWeilPiHermiteFirstOrderOperator)
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) :
    guinandWeilPiHermiteOperatorWordL2Norm (op :: ops) n ≤
      (1 / 2 : Real) *
        (guinandWeilPiHermiteLadderWeight n *
            guinandWeilPiHermiteOperatorWordL2Norm ops (n - 1) +
          guinandWeilPiHermiteLadderWeight (n + 1) *
            guinandWeilPiHermiteOperatorWordL2Norm ops (n + 1)) := by
  unfold guinandWeilPiHermiteOperatorWordL2Norm
  rw [guinandWeilPiHermiteOperatorWordToL2CLM_cons]
  change
    ‖guinandWeilPiHermiteOperatorWordToL2CLM ops
        (guinandWeilPiHermiteFirstOrderOperatorCLM op
          (guinandWeilPiNormalizedHermiteSchwartz n))‖ ≤ _
  cases op with
  | coordinate =>
      rw [show guinandWeilPiHermiteFirstOrderOperatorCLM
          GuinandWeilPiHermiteFirstOrderOperator.coordinate =
            guinandWeilPiOscillatorCoordinateCLM by rfl,
        guinandWeilPiOscillatorCoordinateCLM_normalizedHermite]
      simp only [ContinuousLinearMap.map_smul_of_tower, map_add]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply le_trans (norm_add_le _ _)
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (guinandWeilPiHermiteLadderWeight_nonneg n),
        abs_of_nonneg (guinandWeilPiHermiteLadderWeight_nonneg (n + 1))]
      rfl
  | deriv =>
      rw [show guinandWeilPiHermiteFirstOrderOperatorCLM
          GuinandWeilPiHermiteFirstOrderOperator.deriv =
            SchwartzMap.derivCLM Complex Complex by rfl,
        guinandWeilPiDerivCLM_normalizedHermite]
      simp only [ContinuousLinearMap.map_smul_of_tower, map_sub]
      rw [norm_smul]
      simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply le_trans (norm_sub_le _ _)
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (guinandWeilPiHermiteLadderWeight_nonneg n),
        abs_of_nonneg (guinandWeilPiHermiteLadderWeight_nonneg (n + 1))]
      rfl

/-- Recursive constant for the coarse polynomial `L2` bound on words of a
fixed length. -/
noncomputable def guinandWeilPiHermiteOperatorWordGrowthConstant :
    Nat → Real
  | 0 => 1
  | length + 1 =>
      2 * guinandWeilPiHermiteLadderGrowthConstant * (2 : Real) ^ length *
        guinandWeilPiHermiteOperatorWordGrowthConstant length

theorem guinandWeilPiHermiteOperatorWordGrowthConstant_pos (length : Nat) :
    0 < guinandWeilPiHermiteOperatorWordGrowthConstant length := by
  induction length with
  | zero => simp [guinandWeilPiHermiteOperatorWordGrowthConstant]
  | succ length ih =>
      simp only [guinandWeilPiHermiteOperatorWordGrowthConstant]
      exact mul_pos
        (mul_pos
          (mul_pos (by norm_num)
            guinandWeilPiHermiteLadderGrowthConstant_pos)
          (pow_pos (by norm_num) length))
        ih

theorem guinandWeilPiHermiteOperatorWordL2Norm_nonneg
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) :
    0 ≤ guinandWeilPiHermiteOperatorWordL2Norm ops n :=
  norm_nonneg _

/-- Every word of coordinate multipliers and derivatives has polynomial `L2`
growth on the normalized Hermite family. -/
theorem guinandWeilPiHermiteOperatorWordL2Norm_le_polynomial
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) :
    guinandWeilPiHermiteOperatorWordL2Norm ops n ≤
      guinandWeilPiHermiteOperatorWordGrowthConstant ops.length *
        (((n + 1 : Nat) : Real) ^ ops.length) := by
  induction ops generalizing n with
  | nil =>
      simp [guinandWeilPiHermiteOperatorWordL2Norm,
        guinandWeilPiHermiteOperatorWordToL2CLM,
        guinandWeilPiHermiteOperatorWordGrowthConstant,
        norm_toLp_guinandWeilPiNormalizedHermiteSchwartz]
  | cons op ops ih =>
      let K := guinandWeilPiHermiteLadderGrowthConstant
      let C := guinandWeilPiHermiteOperatorWordGrowthConstant ops.length
      let M : Real := ((n + 1 : Nat) : Real)
      have hK : 0 ≤ K := guinandWeilPiHermiteLadderGrowthConstant_pos.le
      have hC : 0 ≤ C :=
        (guinandWeilPiHermiteOperatorWordGrowthConstant_pos ops.length).le
      have hM : 0 ≤ M := by
        dsimp [M]
        positivity
      have hminus_index :
          (((n - 1 + 1 : Nat) : Real)) ≤ M := by
        dsimp [M]
        exact_mod_cast (by omega : n - 1 + 1 ≤ n + 1)
      have hplus_index :
          (((n + 1 + 1 : Nat) : Real)) ≤ 2 * M := by
        dsimp [M]
        push_cast
        nlinarith
      have hminus_pow :
          (((n - 1 + 1 : Nat) : Real)) ^ ops.length ≤ M ^ ops.length :=
        pow_le_pow_left₀ (by positivity) hminus_index _
      have hplus_pow :
          (((n + 1 + 1 : Nat) : Real)) ^ ops.length ≤
            (2 * M) ^ ops.length :=
        pow_le_pow_left₀ (by positivity) hplus_index _
      have hword_minus :
          guinandWeilPiHermiteOperatorWordL2Norm ops (n - 1) ≤
            C * M ^ ops.length := by
        apply le_trans (ih (n - 1))
        exact mul_le_mul_of_nonneg_left hminus_pow hC
      have hword_plus :
          guinandWeilPiHermiteOperatorWordL2Norm ops (n + 1) ≤
            C * ((2 : Real) ^ ops.length * M ^ ops.length) := by
        apply le_trans (ih (n + 1))
        calc
          C * (((n + 1 + 1 : Nat) : Real)) ^ ops.length ≤
              C * (2 * M) ^ ops.length :=
            mul_le_mul_of_nonneg_left hplus_pow hC
          _ = C * ((2 : Real) ^ ops.length * M ^ ops.length) := by
            rw [mul_pow]
      have hweight_n :
          guinandWeilPiHermiteLadderWeight n ≤ K * M := by
        simpa [K, M] using guinandWeilPiHermiteLadderWeight_le_linear n
      have hweight_succ :
          guinandWeilPiHermiteLadderWeight (n + 1) ≤ 2 * K * M := by
        apply le_trans (guinandWeilPiHermiteLadderWeight_le_linear (n + 1))
        dsimp [K, M]
        push_cast
        nlinarith [guinandWeilPiHermiteLadderGrowthConstant_pos.le]
      have hproduct_minus :
          guinandWeilPiHermiteLadderWeight n *
              guinandWeilPiHermiteOperatorWordL2Norm ops (n - 1) ≤
            K * C * M ^ (ops.length + 1) := by
        calc
          _ ≤ (K * M) * (C * M ^ ops.length) :=
            mul_le_mul hweight_n hword_minus
              (guinandWeilPiHermiteOperatorWordL2Norm_nonneg ops (n - 1))
              (mul_nonneg hK hM)
          _ = _ := by rw [pow_succ]; ring
      have hproduct_plus :
          guinandWeilPiHermiteLadderWeight (n + 1) *
              guinandWeilPiHermiteOperatorWordL2Norm ops (n + 1) ≤
            2 * K * C * (2 : Real) ^ ops.length *
              M ^ (ops.length + 1) := by
        calc
          _ ≤ (2 * K * M) *
              (C * ((2 : Real) ^ ops.length * M ^ ops.length)) :=
            mul_le_mul hweight_succ hword_plus
              (guinandWeilPiHermiteOperatorWordL2Norm_nonneg ops (n + 1))
              (by positivity)
          _ = _ := by rw [pow_succ]; ring
      apply le_trans
        (guinandWeilPiHermiteOperatorWordL2Norm_cons_le op ops n)
      apply le_trans
        (mul_le_mul_of_nonneg_left
          (add_le_add hproduct_minus hproduct_plus) (by norm_num))
      rw [List.length_cons,
        guinandWeilPiHermiteOperatorWordGrowthConstant]
      change
        (1 / 2 : Real) *
            (K * C * M ^ (ops.length + 1) +
              2 * K * C * (2 : Real) ^ ops.length *
                M ^ (ops.length + 1)) ≤
          (2 * K * (2 : Real) ^ ops.length * C) *
            M ^ (ops.length + 1)
      rw [show
          (1 / 2 : Real) *
              (K * C * M ^ (ops.length + 1) +
                2 * K * C * (2 : Real) ^ ops.length *
                  M ^ (ops.length + 1)) =
            (K * C * ((1 / 2 : Real) *
              (1 + 2 * (2 : Real) ^ ops.length))) *
                M ^ (ops.length + 1) by ring]
      rw [show
          (2 * K * (2 : Real) ^ ops.length * C) *
              M ^ (ops.length + 1) =
            (K * C * (2 * (2 : Real) ^ ops.length)) *
              M ^ (ops.length + 1) by ring]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hM _)
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK hC)
      have hpow : (1 : Real) ≤ (2 : Real) ^ ops.length := by
        exact one_le_pow₀ (by norm_num)
      nlinarith

/-- The integrable weight used to pass from Fourier `L2` control to Fourier
`L1` control. -/
def guinandWeilPiFourierSobolevWeight (x : Real) : Real :=
  (1 + x ^ 2)⁻¹

theorem guinandWeilPiFourierSobolevWeight_nonneg (x : Real) :
    0 ≤ guinandWeilPiFourierSobolevWeight x := by
  unfold guinandWeilPiFourierSobolevWeight
  positivity

theorem guinandWeilPiFourierSobolevWeight_le_one (x : Real) :
    guinandWeilPiFourierSobolevWeight x ≤ 1 := by
  unfold guinandWeilPiFourierSobolevWeight
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])

theorem continuous_guinandWeilPiFourierSobolevWeight :
    Continuous guinandWeilPiFourierSobolevWeight := by
  unfold guinandWeilPiFourierSobolevWeight
  apply Continuous.inv₀
  · fun_prop
  · intro x
    positivity

theorem integrable_sq_guinandWeilPiFourierSobolevWeight :
    Integrable (fun x : Real => guinandWeilPiFourierSobolevWeight x ^ 2) := by
  have hbase : Integrable guinandWeilPiFourierSobolevWeight := by
    change Integrable (fun x : Real => (1 + x ^ 2)⁻¹)
    exact integrable_inv_one_add_sq
  have hmeas :
      AEStronglyMeasurable guinandWeilPiFourierSobolevWeight := by
    exact continuous_guinandWeilPiFourierSobolevWeight.aestronglyMeasurable
  have hmul := hbase.bdd_mul hmeas
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (guinandWeilPiFourierSobolevWeight_nonneg x)]
      exact guinandWeilPiFourierSobolevWeight_le_one x)
  simpa [pow_two] using hmul

theorem memLp_two_guinandWeilPiFourierSobolevWeight :
    MemLp guinandWeilPiFourierSobolevWeight
      (ENNReal.ofReal (2 : Real)) volume := by
  have hmeas :
      AEStronglyMeasurable guinandWeilPiFourierSobolevWeight := by
    exact continuous_guinandWeilPiFourierSobolevWeight.aestronglyMeasurable
  have htwo : MemLp guinandWeilPiFourierSobolevWeight (2 : ENNReal) volume :=
    (memLp_two_iff_integrable_sq hmeas).2
      integrable_sq_guinandWeilPiFourierSobolevWeight
  convert htwo using 1
  norm_num

/-- Temperate multiplier `1 + x^2`. -/
def guinandWeilPiOneAddSquareMultiplier (x : Real) : Complex :=
  1 + x ^ 2

theorem guinandWeilPiOneAddSquareMultiplier_hasTemperateGrowth :
    guinandWeilPiOneAddSquareMultiplier.HasTemperateGrowth := by
  unfold guinandWeilPiOneAddSquareMultiplier
  fun_prop

@[simp]
theorem norm_one_add_complex_sq_real (x : Real) :
    ‖(1 : Complex) + (x : Complex) ^ 2‖ = 1 + x ^ 2 := by
  rw [show (1 : Complex) + (x : Complex) ^ 2 =
      ((1 + x ^ 2 : Real) : Complex) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

@[simp]
theorem norm_guinandWeilPiOneAddSquareMultiplier (x : Real) :
    ‖guinandWeilPiOneAddSquareMultiplier x‖ = 1 + x ^ 2 := by
  unfold guinandWeilPiOneAddSquareMultiplier
  exact norm_one_add_complex_sq_real x

/-- Multiplication by `1 + x^2` on project Schwartz space. -/
noncomputable def guinandWeilPiOneAddSquareMultiplierCLM :
    SchwartzLineTestFunction →L[Complex] SchwartzLineTestFunction :=
  SchwartzMap.smulLeftCLM Complex guinandWeilPiOneAddSquareMultiplier

@[simp]
theorem guinandWeilPiOneAddSquareMultiplierCLM_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiOneAddSquareMultiplierCLM f x =
      (1 + x ^ 2) * f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply
    guinandWeilPiOneAddSquareMultiplier_hasTemperateGrowth f x

/-- The norm of `(1 + x^2) f` as a real-valued function. -/
def guinandWeilPiOneAddSquareNorm
    (f : SchwartzLineTestFunction) (x : Real) : Real :=
  (1 + x ^ 2) * ‖f x‖

theorem guinandWeilPiOneAddSquareNorm_nonneg
    (f : SchwartzLineTestFunction) (x : Real) :
    0 ≤ guinandWeilPiOneAddSquareNorm f x := by
  unfold guinandWeilPiOneAddSquareNorm
  positivity

theorem memLp_two_guinandWeilPiOneAddSquareNorm
    (f : SchwartzLineTestFunction) :
    MemLp (guinandWeilPiOneAddSquareNorm f)
      (ENNReal.ofReal (2 : Real)) volume := by
  have hq :=
    (guinandWeilPiOneAddSquareMultiplierCLM f).memLp
      (ENNReal.ofReal (2 : Real)) volume
  have hnorm := hq.norm
  apply (memLp_congr_ae (μ := volume) (Filter.Eventually.of_forall fun x => ?_)).2
  · exact hnorm
  · rw [guinandWeilPiOneAddSquareMultiplierCLM_apply, norm_mul,
      norm_one_add_complex_sq_real]
    rfl

/-- Fixed finite constant in the Fourier--Sobolev `L1` estimate. -/
noncomputable def guinandWeilPiFourierSobolevConstant : Real :=
  (∫ x : Real,
      ‖guinandWeilPiFourierSobolevWeight x‖ ^ (2 : Real)) ^
    (1 / (2 : Real))

theorem guinandWeilPiFourierSobolevConstant_nonneg :
    0 ≤ guinandWeilPiFourierSobolevConstant := by
  unfold guinandWeilPiFourierSobolevConstant
  exact Real.rpow_nonneg
    (integral_nonneg fun x => by positivity) _

/-- Weighted Cauchy--Schwarz controls the `L1` norm of a Schwartz test by the
`L2` norm after multiplication by `1 + x^2`. -/
theorem norm_toLp_one_le_guinandWeilPiFourierSobolevConstant_mul_weighted_l2
    (f : SchwartzLineTestFunction) :
    ‖f.toLp (1 : ENNReal) volume‖ ≤
      guinandWeilPiFourierSobolevConstant *
        ‖(guinandWeilPiOneAddSquareMultiplierCLM f).toLp
          (2 : ENNReal) volume‖ := by
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two
    memLp_two_guinandWeilPiFourierSobolevWeight
    (memLp_two_guinandWeilPiOneAddSquareNorm f)
  have hleft :
      (∫ x : Real, ‖f x‖) =
        ∫ x : Real,
          ‖guinandWeilPiFourierSobolevWeight x‖ *
            ‖guinandWeilPiOneAddSquareNorm f x‖ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_eq_abs,
      abs_of_nonneg (guinandWeilPiFourierSobolevWeight_nonneg x),
      Real.norm_eq_abs,
      abs_of_nonneg (guinandWeilPiOneAddSquareNorm_nonneg f x)]
    unfold guinandWeilPiFourierSobolevWeight
    unfold guinandWeilPiOneAddSquareNorm
    field_simp [show (1 : Real) + x ^ 2 ≠ 0 by positivity]
  have hright :
      (∫ x : Real, ‖guinandWeilPiOneAddSquareNorm f x‖ ^ (2 : Real)) ^
          (1 / (2 : Real)) =
        ‖(guinandWeilPiOneAddSquareMultiplierCLM f).toLp
          (2 : ENNReal) volume‖ := by
    have hintegral :
        (∫ x : Real,
            ‖guinandWeilPiOneAddSquareNorm f x‖ ^ (2 : Real)) =
          ∫ x : Real,
            ‖guinandWeilPiOneAddSquareMultiplierCLM f x‖ ^ (2 : Real) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      rw [Real.norm_eq_abs,
        abs_of_nonneg (guinandWeilPiOneAddSquareNorm_nonneg f x)]
      rw [guinandWeilPiOneAddSquareMultiplierCLM_apply, norm_mul,
        norm_one_add_complex_sq_real]
      rfl
    rw [hintegral, guinandWeilPiSchwartz_l2_eq_norm_toLp]
  rw [SchwartzMap.norm_toLp_one, hleft]
  apply hholder.trans_eq
  rw [hright]
  rfl

/-- Fourier inversion plus the weighted `L1` estimate gives a uniform
point-evaluation bound. -/
theorem norm_apply_le_guinandWeilPiFourierSobolevConstant_mul_weighted_fourier_l2
    (f : SchwartzLineTestFunction) (x : Real) :
    ‖f x‖ ≤
      guinandWeilPiFourierSobolevConstant *
        ‖(guinandWeilPiOneAddSquareMultiplierCLM
            (SchwartzLineTestFunction.fourier f)).toLp
          (2 : ENNReal) volume‖ := by
  calc
    ‖f x‖ = ‖(𝓕⁻ (𝓕 f)) x‖ := by
      rw [FourierTransform.fourierInv_fourier_eq]
    _ = ‖𝓕 (𝓕 f) (-x)‖ := by
      rw [SchwartzMap.fourierInv_apply_eq]
      rfl
    _ ≤ ‖(𝓕 f).toLp (1 : ENNReal) volume‖ :=
      SchwartzMap.norm_fourier_apply_le_toLp_one (𝓕 f) (-x)
    _ ≤ _ :=
      norm_toLp_one_le_guinandWeilPiFourierSobolevConstant_mul_weighted_l2
        (𝓕 f)

open LineDeriv

/-- On the real line, the unit-direction Schwartz line derivative is the
ordinary derivative CLM. -/
theorem guinandWeilPiLineDerivOp_one_eq_derivCLM
    (f : SchwartzLineTestFunction) :
    ∂_{(1 : Real)} f = SchwartzMap.derivCLM Complex Complex f := by
  ext x
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.derivCLM_apply]

theorem guinandWeilPiInnerOneMultiplier_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    SchwartzMap.smulLeftCLM Complex (inner Real · (1 : Real)) f x =
      x * f x := by
  have hgrowth :
      (fun y : Real => inner Real y (1 : Real)).HasTemperateGrowth := by
    fun_prop
  rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
  simp

theorem guinandWeilPiIdentityMultiplier_apply
    (f : SchwartzLineTestFunction) (x : Real) :
    SchwartzMap.smulLeftCLM Complex (fun y : Real => y) f x =
      x * f x := by
  have hgrowth : (fun y : Real => y).HasTemperateGrowth := by
    fun_prop
  rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
  change (x : Complex) * f x = (x : Complex) * f x
  rfl

/-- Fourier transform sends differentiation to `I` times the scaled
coordinate multiplier. -/
theorem fourier_guinandWeilPiDerivCLM
    (f : SchwartzLineTestFunction) :
    SchwartzMap.fourierTransformCLM Complex
        (SchwartzMap.derivCLM Complex Complex f) =
      Complex.I •
        guinandWeilPiOscillatorCoordinateCLM
          (SchwartzMap.fourierTransformCLM Complex f) := by
  calc
    SchwartzMap.fourierTransformCLM Complex
        (SchwartzMap.derivCLM Complex Complex f) =
        SchwartzMap.fourierTransformCLM Complex (∂_{(1 : Real)} f) := by
      rw [guinandWeilPiLineDerivOp_one_eq_derivCLM]
    _ = (2 * Real.pi * Complex.I) •
        SchwartzMap.smulLeftCLM Complex (inner Real · (1 : Real))
          (SchwartzMap.fourierTransformCLM Complex f) :=
      SchwartzMap.fourier_lineDerivOp_eq f (1 : Real)
    _ = Complex.I •
        guinandWeilPiOscillatorCoordinateCLM
          (SchwartzMap.fourierTransformCLM Complex f) := by
      ext x
      change
        (2 * (Real.pi : Complex) * Complex.I) *
            (SchwartzMap.smulLeftCLM Complex (inner Real · (1 : Real))
              (SchwartzMap.fourierTransformCLM Complex f)) x =
          Complex.I * guinandWeilPiOscillatorCoordinateCLM
            (SchwartzMap.fourierTransformCLM Complex f) x
      rw [guinandWeilPiInnerOneMultiplier_apply,
        guinandWeilPiOscillatorCoordinateCLM_apply]
      simp [guinandWeilPiOscillatorCoordinate,
        guinandWeilPiOscillatorScale]
      ring

/-- The multiplier inside the Fourier derivative identity is `-I` times the
project coordinate operator. -/
theorem neg_fourier_scale_inner_smul_eq_neg_I_coordinate
    (f : SchwartzLineTestFunction) :
    (-(2 * Real.pi * Complex.I)) •
        SchwartzMap.smulLeftCLM Complex (inner Real · (1 : Real)) f =
      (-Complex.I) • guinandWeilPiOscillatorCoordinateCLM f := by
  ext x
  change
    (-(2 * (Real.pi : Complex) * Complex.I)) *
        (SchwartzMap.smulLeftCLM Complex (inner Real · (1 : Real)) f) x =
      (-Complex.I) * guinandWeilPiOscillatorCoordinateCLM f x
  rw [guinandWeilPiInnerOneMultiplier_apply,
    guinandWeilPiOscillatorCoordinateCLM_apply]
  simp [guinandWeilPiOscillatorCoordinate,
    guinandWeilPiOscillatorScale]
  ring

/-- Fourier transform sends the scaled coordinate multiplier to `I` times
differentiation. -/
theorem fourier_guinandWeilPiOscillatorCoordinateCLM
    (f : SchwartzLineTestFunction) :
    SchwartzMap.fourierTransformCLM Complex
        (guinandWeilPiOscillatorCoordinateCLM f) =
      Complex.I •
        SchwartzMap.derivCLM Complex Complex
          (SchwartzMap.fourierTransformCLM Complex f) := by
  have hderiv := SchwartzMap.lineDerivOp_fourier_eq f (1 : Real)
  rw [guinandWeilPiLineDerivOp_one_eq_derivCLM,
    neg_fourier_scale_inner_smul_eq_neg_I_coordinate] at hderiv
  have hderiv' :
      SchwartzMap.derivCLM Complex Complex
          (SchwartzMap.fourierTransformCLM Complex f) =
        (-Complex.I) •
          SchwartzMap.fourierTransformCLM Complex
            (guinandWeilPiOscillatorCoordinateCLM f) := by
    calc
      _ = 𝓕 ((-Complex.I) •
          guinandWeilPiOscillatorCoordinateCLM f) := hderiv
      _ = _ := by
        change
          SchwartzMap.fourierTransformCLM Complex
              ((-Complex.I) • guinandWeilPiOscillatorCoordinateCLM f) = _
        rw [map_smul]
  change
    SchwartzMap.fourierTransformCLM Complex
        (guinandWeilPiOscillatorCoordinateCLM f) =
      Complex.I •
        SchwartzMap.derivCLM Complex Complex
          (SchwartzMap.fourierTransformCLM Complex f)
  rw [hderiv', smul_smul]
  simp

/-- Fourier transform intertwines the creation operator with multiplication
by `-I`. -/
theorem fourier_guinandWeilPiHermiteCreationCLM
    (f : SchwartzLineTestFunction) :
    SchwartzMap.fourierTransformCLM Complex
        (guinandWeilPiHermiteCreationCLM f) =
      (-Complex.I) •
        guinandWeilPiHermiteCreationCLM
          (SchwartzMap.fourierTransformCLM Complex f) := by
  change
    SchwartzMap.fourierTransformCLM Complex
      (-(SchwartzMap.derivCLM Complex Complex f) +
        guinandWeilPiOscillatorCoordinateCLM f) = _
  rw [map_add, map_neg, fourier_guinandWeilPiDerivCLM,
    fourier_guinandWeilPiOscillatorCoordinateCLM]
  ext x
  simp [guinandWeilPiHermiteCreationCLM_apply,
    SchwartzMap.derivCLM_apply]
  ring

/-- The unnormalized Gaussian ground state is fixed by Fourier transform. -/
theorem fourier_guinandWeilPiOscillatorHermiteSchwartz_zero :
    SchwartzMap.fourierTransformCLM Complex
        (guinandWeilPiOscillatorHermiteSchwartz 0) =
      guinandWeilPiOscillatorHermiteSchwartz 0 := by
  ext x
  change
    (𝓕 fun y : Real => guinandWeilPiOscillatorHermiteSchwartz 0 y) x =
      guinandWeilPiOscillatorHermiteSchwartz 0 x
  rw [guinandWeilPiOscillatorHermiteSchwartz_apply]
  simpa [guinandWeilPiOscillatorHermiteRealPolynomial,
    guinandWeilPiPolynomialGaussianSource, Polynomial.aeval_def] using
    congrFun fourier_guinandWeilPiGaussianSource_real x

/-- The `n`th oscillator Hermite test has Fourier eigenvalue `(-I)^n`. -/
theorem fourier_guinandWeilPiOscillatorHermiteSchwartz (n : Nat) :
    SchwartzMap.fourierTransformCLM Complex
        (guinandWeilPiOscillatorHermiteSchwartz n) =
      (-Complex.I) ^ n • guinandWeilPiOscillatorHermiteSchwartz n := by
  induction n with
  | zero =>
      simpa using fourier_guinandWeilPiOscillatorHermiteSchwartz_zero
  | succ n ih =>
      rw [← guinandWeilPiHermiteCreationCLM_hermite n,
        fourier_guinandWeilPiHermiteCreationCLM, ih,
        ContinuousLinearMap.map_smul, smul_smul, pow_succ']

/-- The normalized oscillator Hermite test has the same Fourier eigenvalue. -/
theorem fourier_guinandWeilPiNormalizedHermiteSchwartz (n : Nat) :
    SchwartzMap.fourierTransformCLM Complex
        (guinandWeilPiNormalizedHermiteSchwartz n) =
      (-Complex.I) ^ n • guinandWeilPiNormalizedHermiteSchwartz n := by
  unfold guinandWeilPiNormalizedHermiteSchwartz
  rw [ContinuousLinearMap.map_smul_of_tower,
    fourier_guinandWeilPiOscillatorHermiteSchwartz]
  exact smul_comm
    (Real.sqrt (guinandWeilPiHermiteNormSq n))⁻¹
    ((-Complex.I) ^ n)
    (guinandWeilPiOscillatorHermiteSchwartz n)

/-- The coordinate multiplier applied to a Fourier transform is `-I` times
the Fourier transform of the derivative. -/
theorem guinandWeilPiOscillatorCoordinateCLM_fourier
    (f : SchwartzLineTestFunction) :
    guinandWeilPiOscillatorCoordinateCLM
        (SchwartzMap.fourierTransformCLM Complex f) =
      (-Complex.I) •
        SchwartzMap.fourierTransformCLM Complex
          (SchwartzMap.derivCLM Complex Complex f) := by
  rw [fourier_guinandWeilPiDerivCLM, smul_smul]
  simp

/-- Two coordinate multipliers on the Fourier side correspond to minus two
derivatives on the original side. -/
theorem guinandWeilPiOscillatorCoordinateCLM_sq_fourier
    (f : SchwartzLineTestFunction) :
    guinandWeilPiOscillatorCoordinateCLM
        (guinandWeilPiOscillatorCoordinateCLM
          (SchwartzMap.fourierTransformCLM Complex f)) =
      -SchwartzMap.fourierTransformCLM Complex
        (SchwartzMap.derivCLM Complex Complex
          (SchwartzMap.derivCLM Complex Complex f)) := by
  rw [guinandWeilPiOscillatorCoordinateCLM_fourier,
    ContinuousLinearMap.map_smul,
    guinandWeilPiOscillatorCoordinateCLM_fourier, smul_smul]
  simp

/-- Multiplication by `1 + x^2` is the identity plus the square of the scaled
coordinate operator divided by the scale squared. -/
theorem guinandWeilPiOneAddSquareMultiplierCLM_eq_coordinate_sq
    (f : SchwartzLineTestFunction) :
    guinandWeilPiOneAddSquareMultiplierCLM f =
      f + (guinandWeilPiOscillatorScale ^ 2)⁻¹ •
        guinandWeilPiOscillatorCoordinateCLM
          (guinandWeilPiOscillatorCoordinateCLM f) := by
  ext x
  simp [guinandWeilPiOscillatorCoordinate,
    guinandWeilPiOscillatorScale]
  field_simp [Real.pi_ne_zero]

/-- The weighted Fourier `L2` norm is controlled by the original `L2` norm
and the `L2` norm of two further derivatives. -/
theorem norm_weighted_fourier_toLp_two_le
    (f : SchwartzLineTestFunction) :
    ‖(guinandWeilPiOneAddSquareMultiplierCLM
        (SchwartzMap.fourierTransformCLM Complex f)).toLp
          (2 : ENNReal) volume‖ ≤
      ‖f.toLp (2 : ENNReal) volume‖ +
        (guinandWeilPiOscillatorScale ^ 2)⁻¹ *
          ‖(SchwartzMap.derivCLM Complex Complex
              (SchwartzMap.derivCLM Complex Complex f)).toLp
            (2 : ENNReal) volume‖ := by
  rw [guinandWeilPiOneAddSquareMultiplierCLM_eq_coordinate_sq]
  change
    ‖SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
        (_ + _ • _)‖ ≤ _
  rw [map_add, ContinuousLinearMap.map_smul_of_tower]
  apply le_trans (norm_add_le _ _)
  rw [norm_smul, Real.norm_of_nonneg (by positivity :
    0 ≤ (guinandWeilPiOscillatorScale ^ 2)⁻¹)]
  change
    ‖(SchwartzMap.fourierTransformCLM Complex f).toLp
        (2 : ENNReal) volume‖ +
        (guinandWeilPiOscillatorScale ^ 2)⁻¹ *
          ‖(guinandWeilPiOscillatorCoordinateCLM
              (guinandWeilPiOscillatorCoordinateCLM
                (SchwartzMap.fourierTransformCLM Complex f))).toLp
            (2 : ENNReal) volume‖ ≤ _
  have hfourier :
      ‖(SchwartzMap.fourierTransformCLM Complex f).toLp
          (2 : ENNReal) volume‖ =
        ‖f.toLp (2 : ENNReal) volume‖ := by
    simpa only [SchwartzMap.fourierTransformCLM_apply] using
      SchwartzMap.norm_fourier_toL2_eq f
  rw [hfourier]
  have hsq := congrArg
    (fun g : SchwartzLineTestFunction =>
      ‖SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume g‖)
    (guinandWeilPiOscillatorCoordinateCLM_sq_fourier f)
  simp only [map_neg, norm_neg] at hsq
  have hfourier_deriv :
      ‖SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
          (SchwartzMap.fourierTransformCLM Complex
            (SchwartzMap.derivCLM Complex Complex
              (SchwartzMap.derivCLM Complex Complex f)))‖ =
        ‖SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
          (SchwartzMap.derivCLM Complex Complex
            (SchwartzMap.derivCLM Complex Complex f))‖ := by
    change
      ‖(SchwartzMap.fourierTransformCLM Complex
          (SchwartzMap.derivCLM Complex Complex
            (SchwartzMap.derivCLM Complex Complex f))).toLp
            (2 : ENNReal) volume‖ =
        ‖(SchwartzMap.derivCLM Complex Complex
            (SchwartzMap.derivCLM Complex Complex f)).toLp
          (2 : ENNReal) volume‖
    simpa only [SchwartzMap.fourierTransformCLM_apply] using
      SchwartzMap.norm_fourier_toL2_eq
        (SchwartzMap.derivCLM Complex Complex
          (SchwartzMap.derivCLM Complex Complex f))
  rw [hfourier_deriv] at hsq
  have hsq' :
      ‖(guinandWeilPiOscillatorCoordinateCLM
          (guinandWeilPiOscillatorCoordinateCLM
            (SchwartzMap.fourierTransformCLM Complex f))).toLp
          (2 : ENNReal) volume‖ =
        ‖(SchwartzMap.derivCLM Complex Complex
            (SchwartzMap.derivCLM Complex Complex f)).toLp
          (2 : ENNReal) volume‖ := by
    change
      ‖SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
          (guinandWeilPiOscillatorCoordinateCLM
            (guinandWeilPiOscillatorCoordinateCLM
              (SchwartzMap.fourierTransformCLM Complex f)))‖ =
        ‖SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
          (SchwartzMap.derivCLM Complex Complex
            (SchwartzMap.derivCLM Complex Complex f))‖
    exact hsq
  rw [hsq']

/-- A one-dimensional Fourier--Sobolev estimate expressed entirely in the
original-side `L2` norms. -/
theorem norm_apply_le_guinandWeilPiFourierSobolev
    (f : SchwartzLineTestFunction) (x : Real) :
    ‖f x‖ ≤
      guinandWeilPiFourierSobolevConstant *
        (‖f.toLp (2 : ENNReal) volume‖ +
          (guinandWeilPiOscillatorScale ^ 2)⁻¹ *
            ‖(SchwartzMap.derivCLM Complex Complex
                (SchwartzMap.derivCLM Complex Complex f)).toLp
              (2 : ENNReal) volume‖) := by
  apply le_trans
    (norm_apply_le_guinandWeilPiFourierSobolevConstant_mul_weighted_fourier_l2
      f x)
  exact mul_le_mul_of_nonneg_left
    (norm_weighted_fourier_toLp_two_le f)
    guinandWeilPiFourierSobolevConstant_nonneg

/-- Appending one operator applies it after the existing word. -/
theorem guinandWeilPiHermiteOperatorWordCLM_append_singleton
    (ops : List GuinandWeilPiHermiteFirstOrderOperator)
    (op : GuinandWeilPiHermiteFirstOrderOperator)
    (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteOperatorWordCLM (ops ++ [op]) f =
      guinandWeilPiHermiteFirstOrderOperatorCLM op
        (guinandWeilPiHermiteOperatorWordCLM ops f) := by
  induction ops generalizing f with
  | nil => rfl
  | cons head tail ih =>
      rw [List.cons_append,
        guinandWeilPiHermiteOperatorWordCLM_cons,
        guinandWeilPiHermiteOperatorWordCLM_cons,
        ih]

theorem guinandWeilPiHermiteOperatorWordCLM_append_two_deriv
    (ops : List GuinandWeilPiHermiteFirstOrderOperator)
    (f : SchwartzLineTestFunction) :
    guinandWeilPiHermiteOperatorWordCLM
        (ops ++ [.deriv, .deriv]) f =
      SchwartzMap.derivCLM Complex Complex
        (SchwartzMap.derivCLM Complex Complex
          (guinandWeilPiHermiteOperatorWordCLM ops f)) := by
  rw [show ops ++ [.deriv, .deriv] =
      (ops ++ [.deriv]) ++ [.deriv] by simp,
    guinandWeilPiHermiteOperatorWordCLM_append_singleton,
    guinandWeilPiHermiteOperatorWordCLM_append_singleton]
  rfl

/-- The general polynomial word estimate specialized to two appended
derivatives. -/
theorem guinandWeilPiHermiteOperatorWordL2Norm_append_two_deriv_le
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) :
    guinandWeilPiHermiteOperatorWordL2Norm
        (ops ++ [.deriv, .deriv]) n ≤
      guinandWeilPiHermiteOperatorWordGrowthConstant (ops.length + 2) *
        (((n + 1 : Nat) : Real) ^ (ops.length + 2)) := by
  have h := guinandWeilPiHermiteOperatorWordL2Norm_le_polynomial
    (ops ++ [.deriv, .deriv]) n
  have hlength :
      (ops ++ [GuinandWeilPiHermiteFirstOrderOperator.deriv,
        GuinandWeilPiHermiteFirstOrderOperator.deriv]).length =
          ops.length + 2 := by
    simp
  rw [hlength] at h
  exact h

/-- Two derivatives after a word have exactly the `L2` norm represented by
the word with two derivative letters appended. -/
theorem norm_toLp_deriv_sq_guinandWeilPiHermiteOperatorWord_eq
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) :
    ‖(SchwartzMap.derivCLM Complex Complex
        (SchwartzMap.derivCLM Complex Complex
          (guinandWeilPiHermiteOperatorWordCLM ops
            (guinandWeilPiNormalizedHermiteSchwartz n)))).toLp
        (2 : ENNReal) volume‖ =
      guinandWeilPiHermiteOperatorWordL2Norm
        (ops ++ [.deriv, .deriv]) n := by
  calc
    _ = ‖(guinandWeilPiHermiteOperatorWordCLM
        (ops ++ [.deriv, .deriv])
          (guinandWeilPiNormalizedHermiteSchwartz n)).toLp
            (2 : ENNReal) volume‖ := by
      exact congrArg
        (fun g : SchwartzLineTestFunction =>
          ‖g.toLp (2 : ENNReal) volume‖)
        (guinandWeilPiHermiteOperatorWordCLM_append_two_deriv ops
          (guinandWeilPiNormalizedHermiteSchwartz n)).symm
    _ = _ :=
      norm_toLp_guinandWeilPiHermiteOperatorWordCLM_normalizedHermite _ _

theorem norm_toLp_deriv_sq_guinandWeilPiHermiteOperatorWord_le
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (n : Nat) :
    ‖(SchwartzMap.derivCLM Complex Complex
        (SchwartzMap.derivCLM Complex Complex
          (guinandWeilPiHermiteOperatorWordCLM ops
            (guinandWeilPiNormalizedHermiteSchwartz n)))).toLp
        (2 : ENNReal) volume‖ ≤
      guinandWeilPiHermiteOperatorWordGrowthConstant (ops.length + 2) *
        (((n + 1 : Nat) : Real) ^ (ops.length + 2)) := by
  rw [norm_toLp_deriv_sq_guinandWeilPiHermiteOperatorWord_eq]
  exact guinandWeilPiHermiteOperatorWordL2Norm_append_two_deriv_le ops n

/-- Explicit constant for the pointwise polynomial bound on an operator
word. -/
noncomputable def guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) : Real :=
  guinandWeilPiFourierSobolevConstant *
    (guinandWeilPiHermiteOperatorWordGrowthConstant ops.length +
      (guinandWeilPiOscillatorScale ^ 2)⁻¹ *
        guinandWeilPiHermiteOperatorWordGrowthConstant (ops.length + 2))

theorem guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant_nonneg
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) :
    0 ≤ guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant ops := by
  unfold guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant
  exact mul_nonneg guinandWeilPiFourierSobolevConstant_nonneg
    (add_nonneg
      (guinandWeilPiHermiteOperatorWordGrowthConstant_pos ops.length).le
      (mul_nonneg (inv_nonneg.2 (sq_nonneg _))
        (guinandWeilPiHermiteOperatorWordGrowthConstant_pos
          (ops.length + 2)).le))

/-- Every fixed coordinate/derivative word has polynomial pointwise growth on
the normalized Hermite family. -/
theorem norm_guinandWeilPiHermiteOperatorWordCLM_normalizedHermite_le
    (ops : List GuinandWeilPiHermiteFirstOrderOperator)
    (n : Nat) (x : Real) :
    ‖guinandWeilPiHermiteOperatorWordCLM ops
        (guinandWeilPiNormalizedHermiteSchwartz n) x‖ ≤
      guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant ops *
        (((n + 1 : Nat) : Real) ^ (ops.length + 2)) := by
  have hsobolev := norm_apply_le_guinandWeilPiFourierSobolev
    (guinandWeilPiHermiteOperatorWordCLM ops
      (guinandWeilPiNormalizedHermiteSchwartz n)) x
  have hbase : (1 : Real) ≤ ((n + 1 : Nat) : Real) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpow :
      ((n + 1 : Nat) : Real) ^ ops.length ≤
        ((n + 1 : Nat) : Real) ^ (ops.length + 2) := by
    exact pow_le_pow_right₀ hbase (by omega)
  have hword :
      ‖(guinandWeilPiHermiteOperatorWordCLM ops
          (guinandWeilPiNormalizedHermiteSchwartz n)).toLp
            (2 : ENNReal) volume‖ ≤
        guinandWeilPiHermiteOperatorWordGrowthConstant ops.length *
          (((n + 1 : Nat) : Real) ^ (ops.length + 2)) := by
    rw [norm_toLp_guinandWeilPiHermiteOperatorWordCLM_normalizedHermite]
    apply le_trans
      (guinandWeilPiHermiteOperatorWordL2Norm_le_polynomial ops n)
    exact mul_le_mul_of_nonneg_left hpow
      (guinandWeilPiHermiteOperatorWordGrowthConstant_pos ops.length).le
  have hderiv :=
    norm_toLp_deriv_sq_guinandWeilPiHermiteOperatorWord_le ops n
  apply le_trans hsobolev
  unfold guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant
  have hinv : 0 ≤ (guinandWeilPiOscillatorScale ^ 2)⁻¹ :=
    inv_nonneg.2 (sq_nonneg _)
  calc
    guinandWeilPiFourierSobolevConstant *
        (‖(guinandWeilPiHermiteOperatorWordCLM ops
              (guinandWeilPiNormalizedHermiteSchwartz n)).toLp
              (2 : ENNReal) volume‖ +
          (guinandWeilPiOscillatorScale ^ 2)⁻¹ *
            ‖(SchwartzMap.derivCLM Complex Complex
                (SchwartzMap.derivCLM Complex Complex
                  (guinandWeilPiHermiteOperatorWordCLM ops
                    (guinandWeilPiNormalizedHermiteSchwartz n)))).toLp
              (2 : ENNReal) volume‖) ≤
      guinandWeilPiFourierSobolevConstant *
        (guinandWeilPiHermiteOperatorWordGrowthConstant ops.length *
            (((n + 1 : Nat) : Real) ^ (ops.length + 2)) +
          (guinandWeilPiOscillatorScale ^ 2)⁻¹ *
            (guinandWeilPiHermiteOperatorWordGrowthConstant (ops.length + 2) *
              (((n + 1 : Nat) : Real) ^ (ops.length + 2)))) := by
        apply mul_le_mul_of_nonneg_left _
          guinandWeilPiFourierSobolevConstant_nonneg
        exact add_le_add hword (mul_le_mul_of_nonneg_left hderiv hinv)
    _ = _ := by ring

/-- A word consisting of `m` derivative letters computes the `m`th ordinary
derivative. -/
theorem guinandWeilPiHermiteOperatorWordCLM_replicate_deriv_apply
    (m : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiHermiteOperatorWordCLM
        (List.replicate m .deriv) f x =
      iteratedDeriv m (fun y : Real => f y) x := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
      rw [List.replicate_succ,
        guinandWeilPiHermiteOperatorWordCLM_cons, ih]
      simp only [guinandWeilPiHermiteFirstOrderOperatorCLM,
        SchwartzMap.derivCLM_apply]
      rw [iteratedDeriv_succ']

/-- Appending `k` coordinate letters multiplies pointwise by
`(oscillatorScale * x)^k`. -/
theorem guinandWeilPiHermiteOperatorWordCLM_append_replicate_coordinate_apply
    (ops : List GuinandWeilPiHermiteFirstOrderOperator) (k : Nat)
    (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiHermiteOperatorWordCLM
        (ops ++ List.replicate k .coordinate) f x =
      (guinandWeilPiOscillatorScale ^ k * x ^ k) •
        guinandWeilPiHermiteOperatorWordCLM ops f x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ', ← List.append_assoc,
        guinandWeilPiHermiteOperatorWordCLM_append_singleton]
      simp only [guinandWeilPiHermiteFirstOrderOperatorCLM,
        guinandWeilPiOscillatorCoordinateCLM_apply]
      rw [ih]
      simp only [guinandWeilPiOscillatorCoordinate, Complex.real_smul]
      push_cast
      rw [pow_succ, pow_succ]
      ring

/-- Canonical operator word representing the `(k,m)` Schwartz seminorm:
first take `m` derivatives, then multiply by the scaled coordinate `k` times. -/
def guinandWeilPiHermiteSchwartzSeminormWord (k m : Nat) :
    List GuinandWeilPiHermiteFirstOrderOperator :=
  List.replicate m .deriv ++ List.replicate k .coordinate

theorem guinandWeilPiHermiteSchwartzSeminormWord_length (k m : Nat) :
    (guinandWeilPiHermiteSchwartzSeminormWord k m).length = m + k := by
  simp [guinandWeilPiHermiteSchwartzSeminormWord]

theorem guinandWeilPiHermiteSchwartzSeminormWord_apply
    (k m : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    guinandWeilPiHermiteOperatorWordCLM
        (guinandWeilPiHermiteSchwartzSeminormWord k m) f x =
      (guinandWeilPiOscillatorScale ^ k * x ^ k) •
        iteratedDeriv m (fun y : Real => f y) x := by
  rw [guinandWeilPiHermiteSchwartzSeminormWord,
    guinandWeilPiHermiteOperatorWordCLM_append_replicate_coordinate_apply,
    guinandWeilPiHermiteOperatorWordCLM_replicate_deriv_apply]

/-- Explicit constant controlling the `(k,m)` project Schwartz seminorm of
normalized Hermite tests. -/
noncomputable def guinandWeilPiNormalizedHermiteSchwartzSeminormGrowthConstant
    (k m : Nat) : Real :=
  guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant
      (guinandWeilPiHermiteSchwartzSeminormWord k m) /
    guinandWeilPiOscillatorScale ^ k

theorem guinandWeilPiNormalizedHermiteSchwartzSeminormGrowthConstant_nonneg
    (k m : Nat) :
    0 ≤ guinandWeilPiNormalizedHermiteSchwartzSeminormGrowthConstant k m := by
  unfold guinandWeilPiNormalizedHermiteSchwartzSeminormGrowthConstant
  exact div_nonneg
    (guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant_nonneg _)
    (pow_nonneg guinandWeilPiOscillatorScale_pos.le _)

/-- Every project Schwartz seminorm of the normalized Hermite family grows at
most polynomially in the Hermite index. -/
theorem seminorm_guinandWeilPiNormalizedHermiteSchwartz_le_polynomial
    (k m n : Nat) :
    SchwartzMap.seminorm Complex k m
        (guinandWeilPiNormalizedHermiteSchwartz n) ≤
      guinandWeilPiNormalizedHermiteSchwartzSeminormGrowthConstant k m *
        (((n + 1 : Nat) : Real) ^ (m + k + 2)) := by
  let ops := guinandWeilPiHermiteSchwartzSeminormWord k m
  let C := guinandWeilPiHermiteOperatorWordPointwiseGrowthConstant ops
  have hscale : 0 < guinandWeilPiOscillatorScale ^ k :=
    pow_pos guinandWeilPiOscillatorScale_pos k
  refine SchwartzMap.seminorm_le_bound' Complex k m
    (guinandWeilPiNormalizedHermiteSchwartz n) ?_ ?_
  · exact mul_nonneg
      (guinandWeilPiNormalizedHermiteSchwartzSeminormGrowthConstant_nonneg k m)
      (pow_nonneg (by positivity) _)
  · intro x
    have hword :=
      norm_guinandWeilPiHermiteOperatorWordCLM_normalizedHermite_le
        ops n x
    have hlength : ops.length = m + k := by
      exact guinandWeilPiHermiteSchwartzSeminormWord_length k m
    rw [hlength] at hword
    change
      |x| ^ k *
          ‖iteratedDeriv m
            (fun y : Real => guinandWeilPiNormalizedHermiteSchwartz n y) x‖ ≤
        (C / guinandWeilPiOscillatorScale ^ k) *
          (((n + 1 : Nat) : Real) ^ (m + k + 2))
    rw [show
        (C / guinandWeilPiOscillatorScale ^ k) *
            (((n + 1 : Nat) : Real) ^ (m + k + 2)) =
          (C * (((n + 1 : Nat) : Real) ^ (m + k + 2))) /
            guinandWeilPiOscillatorScale ^ k by ring]
    apply (le_div_iff₀ hscale).2
    calc
      (|x| ^ k *
          ‖iteratedDeriv m
            (fun y : Real => guinandWeilPiNormalizedHermiteSchwartz n y) x‖) *
          guinandWeilPiOscillatorScale ^ k =
        ‖guinandWeilPiHermiteOperatorWordCLM ops
            (guinandWeilPiNormalizedHermiteSchwartz n) x‖ := by
          rw [show ops = guinandWeilPiHermiteSchwartzSeminormWord k m by rfl,
            guinandWeilPiHermiteSchwartzSeminormWord_apply, norm_smul,
            Real.norm_eq_abs, abs_mul,
            abs_pow guinandWeilPiOscillatorScale k, abs_pow x k,
            abs_of_pos guinandWeilPiOscillatorScale_pos]
          ring
      _ ≤ C * (((n + 1 : Nat) : Real) ^ (m + k + 2)) := hword

/-- The normalized Hermite expansion of a Schwartz test is absolutely
summable under every generating project Schwartz seminorm. -/
theorem summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries
    (k m : Nat) (f : SchwartzLineTestFunction) :
    Summable (fun n : Nat =>
      SchwartzMap.seminorm Complex k m
        (guinandWeilPiNormalizedHermiteCoefficient n f •
          guinandWeilPiNormalizedHermiteSchwartz n)) := by
  let C := guinandWeilPiNormalizedHermiteSchwartzSeminormGrowthConstant k m
  have hweighted :=
    summable_nat_add_one_pow_mul_norm_guinandWeilPiNormalizedHermiteCoefficient
      (m + k + 2) f
  have hmajorant : Summable (fun n : Nat =>
      C * ((((n + 1 : Nat) : Real) ^ (m + k + 2)) *
        ‖guinandWeilPiNormalizedHermiteCoefficient n f‖)) :=
    hweighted.mul_left C
  refine Summable.of_nonneg_of_le
    (fun n => apply_nonneg (SchwartzMap.seminorm Complex k m) _) ?_
    hmajorant
  intro n
  rw [map_smul_eq_mul]
  calc
    ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ *
        SchwartzMap.seminorm Complex k m
          (guinandWeilPiNormalizedHermiteSchwartz n) ≤
      ‖guinandWeilPiNormalizedHermiteCoefficient n f‖ *
        (C * (((n + 1 : Nat) : Real) ^ (m + k + 2))) :=
      mul_le_mul_of_nonneg_left
        (seminorm_guinandWeilPiNormalizedHermiteSchwartz_le_polynomial
          k m n) (norm_nonneg _)
    _ = C * ((((n + 1 : Nat) : Real) ^ (m + k + 2)) *
        ‖guinandWeilPiNormalizedHermiteCoefficient n f‖) := by ring

/-- A single term of the normalized Hermite expansion, retained as a Schwartz
function so all derivative and decay estimates remain available. -/
noncomputable def guinandWeilPiNormalizedHermiteSchwartzSeriesTerm
    (f : SchwartzLineTestFunction) (n : Nat) : SchwartzLineTestFunction :=
  guinandWeilPiNormalizedHermiteCoefficient n f •
    guinandWeilPiNormalizedHermiteSchwartz n

/-- The pointwise sum of the normalized Hermite expansion. -/
noncomputable def guinandWeilPiHermitePointwiseExpansion
    (f : SchwartzLineTestFunction) (x : Real) : Complex :=
  ∑' n : Nat, guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n x

/-- The pointwise Hermite sum is smooth.  Absolute summability in the zeroth
coordinate-weight seminorm at every derivative order supplies the uniform
majorants required by `contDiff_tsum`. -/
theorem contDiff_guinandWeilPiHermitePointwiseExpansion
    (f : SchwartzLineTestFunction) :
    ContDiff Real (⊤ : ℕ∞) (guinandWeilPiHermitePointwiseExpansion f) := by
  unfold guinandWeilPiHermitePointwiseExpansion
  apply contDiff_tsum
  · intro n
    exact (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n).smooth'
  · intro r hr
    simpa only [guinandWeilPiNormalizedHermiteSchwartzSeriesTerm] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries 0 r f
  · intro r n x hr
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm
      (𝕜 := Complex)
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) r x

/-- Iterated derivatives pass through the pointwise Hermite sum. -/
theorem iteratedFDeriv_guinandWeilPiHermitePointwiseExpansion
    (m : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    iteratedFDeriv Real m (guinandWeilPiHermitePointwiseExpansion f) x =
      ∑' n : Nat, iteratedFDeriv Real m
        (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) x := by
  unfold guinandWeilPiHermitePointwiseExpansion
  apply iteratedFDeriv_tsum_apply
  · intro n
    exact (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n).smooth'
  · intro r hr
    simpa only [guinandWeilPiNormalizedHermiteSchwartzSeriesTerm] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries 0 r f
  · intro r n y hr
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm
      (𝕜 := Complex)
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) r y
  · exact le_top

/-- Every weighted derivative of the pointwise Hermite sum has a global
bound, obtained by summing the corresponding project Schwartz seminorms of
the individual terms. -/
theorem exists_decay_bound_guinandWeilPiHermitePointwiseExpansion
    (k m : Nat) (f : SchwartzLineTestFunction) :
    ∃ C : Real, ∀ x : Real,
      ‖x‖ ^ k *
          ‖iteratedFDeriv Real m
            (guinandWeilPiHermitePointwiseExpansion f) x‖ ≤ C := by
  let q : Nat → Real := fun n =>
    SchwartzMap.seminorm Complex k m
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n)
  let q₀ : Nat → Real := fun n =>
    SchwartzMap.seminorm Complex 0 m
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n)
  have hq : Summable q := by
    simpa only [q, guinandWeilPiNormalizedHermiteSchwartzSeriesTerm] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries k m f
  have hq₀ : Summable q₀ := by
    simpa only [q₀, guinandWeilPiNormalizedHermiteSchwartzSeriesTerm] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries 0 m f
  refine ⟨∑' n : Nat, q n, fun x => ?_⟩
  let d := fun n : Nat => iteratedFDeriv Real m
    (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) x
  have hd_le (n : Nat) : ‖d n‖ ≤ q₀ n := by
    dsimp only [d, q₀]
    simpa only [pow_zero, one_mul] using
      SchwartzMap.le_seminorm (𝕜 := Complex) 0 m
        (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) x
  have hd : Summable (fun n : Nat => ‖d n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (d n)) hd_le hq₀
  have hweighted : Summable (fun n : Nat => ‖x‖ ^ k * ‖d n‖) :=
    hd.mul_left (‖x‖ ^ k)
  rw [iteratedFDeriv_guinandWeilPiHermitePointwiseExpansion]
  change ‖x‖ ^ k * ‖∑' n : Nat, d n‖ ≤ ∑' n : Nat, q n
  calc
    ‖x‖ ^ k * ‖∑' n : Nat, d n‖ ≤
        ‖x‖ ^ k * ∑' n : Nat, ‖d n‖ :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hd) (pow_nonneg (norm_nonneg x) k)
    _ = ∑' n : Nat, ‖x‖ ^ k * ‖d n‖ := by rw [tsum_mul_left]
    _ ≤ ∑' n : Nat, q n := hweighted.tsum_le_tsum (fun n => by
      dsimp only [d, q]
      exact SchwartzMap.le_seminorm (𝕜 := Complex) k m
        (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) x) hq

/-- The normalized Hermite series defines an actual Schwartz function, not
merely an `L2` or pointwise limit. -/
noncomputable def guinandWeilPiHermiteSchwartzExpansion
    (f : SchwartzLineTestFunction) : SchwartzLineTestFunction where
  toFun := guinandWeilPiHermitePointwiseExpansion f
  smooth' := contDiff_guinandWeilPiHermitePointwiseExpansion f
  decay' := fun k m =>
    exists_decay_bound_guinandWeilPiHermitePointwiseExpansion k m f

/-- Iterated derivatives of a finite Hermite truncation are the corresponding
finite sums of the termwise iterated derivatives. -/
theorem iteratedFDeriv_guinandWeilPiHermiteTruncation
    (m N : Nat) (f : SchwartzLineTestFunction) (x : Real) :
    iteratedFDeriv Real m (guinandWeilPiHermiteTruncation N f) x =
      ∑ n ∈ Finset.range N, iteratedFDeriv Real m
        (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) x := by
  change iteratedFDeriv Real m
      (⇑(∑ n ∈ Finset.range N,
        guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n)) x = _
  have hfun :
      (⇑(∑ n ∈ Finset.range N,
        guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) : Real → Complex) =
        fun y => ∑ n ∈ Finset.range N,
          guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n y := by
    funext y
    exact SchwartzMap.sum_apply (Finset.range N)
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f) y
  rw [hfun]
  exact iteratedFDeriv_fun_sum_apply (𝕜 := Real) (n := m) (x := x)
    (fun n _ =>
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n).contDiffAt m)

/-- The seminorm of the difference between the full Schwartz Hermite sum and
its `N`-term truncation is bounded by the scalar tail of the termwise
seminorms. -/
theorem seminorm_guinandWeilPiHermiteSchwartzExpansion_sub_truncation_le
    (k m N : Nat) (f : SchwartzLineTestFunction) :
    SchwartzMap.seminorm Complex k m
        (guinandWeilPiHermiteSchwartzExpansion f -
          guinandWeilPiHermiteTruncation N f) ≤
      ∑' r : Nat, SchwartzMap.seminorm Complex k m
        (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f (r + N)) := by
  let q : Nat → Real := fun n =>
    SchwartzMap.seminorm Complex k m
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n)
  let q₀ : Nat → Real := fun n =>
    SchwartzMap.seminorm Complex 0 m
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n)
  have hq : Summable q := by
    simpa only [q, guinandWeilPiNormalizedHermiteSchwartzSeriesTerm] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries k m f
  have hq₀ : Summable q₀ := by
    simpa only [q₀, guinandWeilPiNormalizedHermiteSchwartzSeriesTerm] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries 0 m f
  apply SchwartzMap.seminorm_le_bound Complex k m
  · exact tsum_nonneg fun r => apply_nonneg (SchwartzMap.seminorm Complex k m) _
  · intro x
    let d := fun n : Nat => iteratedFDeriv Real m
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) x
    have hd_norm : Summable (fun n : Nat => ‖d n‖) :=
      Summable.of_nonneg_of_le (fun n => norm_nonneg (d n)) (fun n => by
        dsimp only [d, q₀]
        simpa only [pow_zero, one_mul] using
          SchwartzMap.le_seminorm (𝕜 := Complex) 0 m
            (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n) x) hq₀
    have hd : Summable d := hd_norm.of_norm
    have hd_tail_norm : Summable (fun r : Nat => ‖d (r + N)‖) := by
      simpa only [Nat.add_comm] using
        (summable_nat_add_iff N).mpr hd_norm
    have hq_tail : Summable (fun r : Nat => q (r + N)) := by
      simpa only [Nat.add_comm] using (summable_nat_add_iff N).mpr hq
    have hsplit := hd.sum_add_tsum_nat_add N
    have htail :
        (∑' n : Nat, d n) - ∑ n ∈ Finset.range N, d n =
          ∑' r : Nat, d (r + N) := by
      rw [← hsplit]
      abel
    change ‖x‖ ^ k * ‖iteratedFDeriv Real m
      ((guinandWeilPiHermiteSchwartzExpansion f : Real → Complex) -
        (guinandWeilPiHermiteTruncation N f : Real → Complex)) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply
      ((guinandWeilPiHermiteSchwartzExpansion f).smooth (m : ℕ∞)).contDiffAt
      ((guinandWeilPiHermiteTruncation N f).smooth (m : ℕ∞)).contDiffAt]
    change ‖x‖ ^ k *
      ‖iteratedFDeriv Real m (guinandWeilPiHermitePointwiseExpansion f) x -
        iteratedFDeriv Real m (guinandWeilPiHermiteTruncation N f) x‖ ≤ _
    rw [iteratedFDeriv_guinandWeilPiHermitePointwiseExpansion,
      iteratedFDeriv_guinandWeilPiHermiteTruncation]
    change ‖x‖ ^ k * ‖(∑' n : Nat, d n) -
      ∑ n ∈ Finset.range N, d n‖ ≤ ∑' r : Nat, q (r + N)
    rw [htail]
    calc
      ‖x‖ ^ k * ‖∑' r : Nat, d (r + N)‖ ≤
          ‖x‖ ^ k * ∑' r : Nat, ‖d (r + N)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hd_tail_norm)
          (pow_nonneg (norm_nonneg x) k)
      _ = ∑' r : Nat, ‖x‖ ^ k * ‖d (r + N)‖ := by rw [tsum_mul_left]
      _ ≤ ∑' r : Nat, q (r + N) :=
        (hd_tail_norm.mul_left (‖x‖ ^ k)).tsum_le_tsum (fun r => by
          dsimp only [d, q]
          exact SchwartzMap.le_seminorm (𝕜 := Complex) k m
            (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f (r + N)) x)
          hq_tail

/-- The scalar tail of the termwise Schwartz seminorms tends to zero. -/
theorem tendsto_tsum_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries_natAdd
    (k m : Nat) (f : SchwartzLineTestFunction) :
    Tendsto (fun N : Nat =>
      ∑' r : Nat, SchwartzMap.seminorm Complex k m
        (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f (r + N)))
      atTop (𝓝 0) := by
  let q : Nat → Real := fun n =>
    SchwartzMap.seminorm Complex k m
      (guinandWeilPiNormalizedHermiteSchwartzSeriesTerm f n)
  have hq : Summable q := by
    simpa only [q, guinandWeilPiNormalizedHermiteSchwartzSeriesTerm] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries k m f
  have hpartial : Tendsto (fun N : Nat => ∑ n ∈ Finset.range N, q n)
      atTop (𝓝 (∑' n : Nat, q n)) := hq.hasSum.tendsto_sum_nat
  have htail (N : Nat) :
      (∑' r : Nat, q (r + N)) =
        (∑' n : Nat, q n) - ∑ n ∈ Finset.range N, q n := by
    have hsplit := hq.sum_add_tsum_nat_add N
    rw [← hsplit]
    abel
  change Tendsto (fun N : Nat => ∑' r : Nat, q (r + N)) atTop (𝓝 0)
  simp_rw [htail]
  have hconstant : Tendsto (fun _ : Nat => ∑' n : Nat, q n) atTop
      (𝓝 (∑' n : Nat, q n)) := tendsto_const_nhds
  simpa only [sub_self] using hconstant.sub hpartial

/-- Hermite truncations converge to the constructed Hermite sum in every
individual project Schwartz seminorm. -/
theorem tendsto_schwartzSeminorm_guinandWeilPiHermiteSchwartzExpansion_sub_truncation
    (k m : Nat) (f : SchwartzLineTestFunction) :
    Tendsto (fun N : Nat => SchwartzMap.seminorm Complex k m
      (guinandWeilPiHermiteSchwartzExpansion f -
        guinandWeilPiHermiteTruncation N f)) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro N
    exact apply_nonneg (SchwartzMap.seminorm Complex k m) _
  · intro N
    exact seminorm_guinandWeilPiHermiteSchwartzExpansion_sub_truncation_le
      k m N f
  · exact
      tendsto_tsum_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries_natAdd
        k m f

/-- The actual finite Hermite truncations converge to the constructed series
in the full intended Schwartz topology. -/
theorem tendsto_guinandWeilPiHermiteTruncation_schwartz
    (f : SchwartzLineTestFunction) :
    Tendsto (fun N : Nat => guinandWeilPiHermiteTruncation N f) atTop
      (𝓝 (guinandWeilPiHermiteSchwartzExpansion f)) := by
  rw [(schwartz_withSeminorms Complex Real Complex).tendsto_nhds_atTop]
  rintro ⟨k, m⟩ ε hε
  have hseminorm :=
    tendsto_schwartzSeminorm_guinandWeilPiHermiteSchwartzExpansion_sub_truncation
      k m f
  have hevent : ∀ᶠ N : Nat in atTop,
      SchwartzMap.seminorm Complex k m
        (guinandWeilPiHermiteSchwartzExpansion f -
          guinandWeilPiHermiteTruncation N f) < ε :=
    hseminorm.eventually (Iio_mem_nhds hε)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  refine ⟨N, fun M hM => ?_⟩
  change SchwartzMap.seminorm Complex k m
      (guinandWeilPiHermiteTruncation M f -
        guinandWeilPiHermiteSchwartzExpansion f) < ε
  rw [← neg_sub, map_neg_eq_map]
  exact hN M hM

/-- The constructed Schwartz Hermite sum has exactly the same normalized
Hermite coefficients as the original test.  Thus the final identification
problem is precisely that these coefficients separate `L2` functions. -/
theorem guinandWeilPiNormalizedHermiteCoefficient_schwartzExpansion
    (n : Nat) (f : SchwartzLineTestFunction) :
    guinandWeilPiNormalizedHermiteCoefficient n
        (guinandWeilPiHermiteSchwartzExpansion f) =
      guinandWeilPiNormalizedHermiteCoefficient n f := by
  have htrunc := tendsto_guinandWeilPiHermiteTruncation_schwartz f
  have hlimitExpansion : Tendsto (fun N : Nat =>
      guinandWeilPiNormalizedHermiteCoefficient n
        (guinandWeilPiHermiteTruncation N f)) atTop
      (𝓝 (guinandWeilPiNormalizedHermiteCoefficient n
        (guinandWeilPiHermiteSchwartzExpansion f))) := by
    change Tendsto (fun N : Nat =>
      guinandWeilPiNormalizedHermiteCoefficientCLM n
        (guinandWeilPiHermiteTruncation N f)) atTop
      (𝓝 (guinandWeilPiNormalizedHermiteCoefficientCLM n
        (guinandWeilPiHermiteSchwartzExpansion f)))
    have hmap :=
      ((guinandWeilPiNormalizedHermiteCoefficientCLM n).continuous.tendsto
        (guinandWeilPiHermiteSchwartzExpansion f)).comp htrunc
    exact Tendsto.congr' (Eventually.of_forall fun _ => rfl) hmap
  have hevent : (fun N : Nat =>
      guinandWeilPiNormalizedHermiteCoefficient n
        (guinandWeilPiHermiteTruncation N f)) =ᶠ[atTop]
      fun _ => guinandWeilPiNormalizedHermiteCoefficient n f := by
    filter_upwards [eventually_ge_atTop (n + 1)] with N hN
    exact guinandWeilPiNormalizedHermiteCoefficient_truncation (by omega) f
  have hlimitOriginal : Tendsto (fun N : Nat =>
      guinandWeilPiNormalizedHermiteCoefficient n
        (guinandWeilPiHermiteTruncation N f)) atTop
      (𝓝 (guinandWeilPiNormalizedHermiteCoefficient n f)) :=
    (tendsto_congr' hevent).mpr tendsto_const_nhds
  exact tendsto_nhds_unique hlimitExpansion hlimitOriginal

/-- A seminorm of a finite sum is at most the sum of the individual
seminorms.  This elementary form is kept local because it is the exact bridge
from scalar absolute summability to control in the Schwartz topology. -/
theorem schwartzSeminorm_finset_sum_le
    {ι : Type*} (k m : Nat) (s : Finset ι)
    (g : ι → SchwartzLineTestFunction) :
    SchwartzMap.seminorm Complex k m (∑ i ∈ s, g i) ≤
      ∑ i ∈ s, SchwartzMap.seminorm Complex k m (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (map_add_le_add (SchwartzMap.seminorm Complex k m) _ _).trans
        (add_le_add le_rfl ih)

/-- Every finite tail of the normalized Hermite expansion is small in any
prescribed project Schwartz seminorm, uniformly in the upper cutoff.  This is
the Cauchy estimate required before constructing the Schwartz-space limit. -/
theorem exists_guinandWeilPiHermiteTruncation_schwartzSeminorm_tail_bound
    (k m : Nat) (f : SchwartzLineTestFunction) {ε : Real} (hε : 0 < ε) :
    ∃ N : Nat, ∀ a ≥ N, ∀ b ≥ a,
      SchwartzMap.seminorm Complex k m
          (guinandWeilPiHermiteTruncation b f -
            guinandWeilPiHermiteTruncation a f) < ε := by
  let term : Nat → SchwartzLineTestFunction := fun n =>
    guinandWeilPiNormalizedHermiteCoefficient n f •
      guinandWeilPiNormalizedHermiteSchwartz n
  let q : Nat → Real := fun n => SchwartzMap.seminorm Complex k m (term n)
  have hq : Summable q := by
    simpa only [q, term] using
      summable_schwartzSeminorm_guinandWeilPiNormalizedHermiteSeries k m f
  have hcauchy : CauchySeq (fun N : Nat => ∑ n ∈ Finset.range N, q n) :=
    hq.hasSum.tendsto_sum_nat.cauchySeq
  rcases (Metric.cauchySeq_iff.mp hcauchy ε hε) with ⟨N, hN⟩
  refine ⟨N, fun a ha b hab => ?_⟩
  have hdist := hN b (ha.trans hab) a ha
  change SchwartzMap.seminorm Complex k m
      ((∑ n ∈ Finset.range b, term n) -
        ∑ n ∈ Finset.range a, term n) < ε
  rw [← Finset.sum_Ico_eq_sub _ hab]
  calc
    SchwartzMap.seminorm Complex k m
        (∑ n ∈ Finset.Ico a b, term n) ≤
      ∑ n ∈ Finset.Ico a b, q n := by
        simpa only [q] using
          schwartzSeminorm_finset_sum_le k m (Finset.Ico a b) term
    _ = (∑ n ∈ Finset.range b, q n) -
        ∑ n ∈ Finset.range a, q n := Finset.sum_Ico_eq_sub _ hab
    _ ≤ |(∑ n ∈ Finset.range b, q n) -
        ∑ n ∈ Finset.range a, q n| := le_abs_self _
    _ < ε := by simpa only [Real.dist_eq] using hdist

end

end RiemannHypothesisProject
