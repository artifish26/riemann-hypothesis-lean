import Mathlib.Analysis.Distribution.TestFunction
import RiemannHypothesisProject.GuinandWeilTestFunctionTarget

/-!
# Real-axis Schwartz seminorms and evaluation continuity

This module contains the real-line seminorm bounds and fixed evaluation
continuity facts used by the shifted-radius p-series certificate route.
-/

namespace RiemannHypothesisProject

open scoped Topology

/--
The concrete one-dimensional Schwartz seminorm bound that any real-axis part of
the p-series strategy may use: finitely many Schwartz seminorms control the
weighted value `(1 + ||t||)^k * ||f(t)||`.

This is not yet a complex-plane extension estimate, but it is a checked
analytic input rather than a bookkeeping bridge.
-/
noncomputable def schwartzLineRealAxisOneAddSeminormConstant
    (k : Nat) (f : SchwartzLineTestFunction) : Real :=
  (2 : Real) ^ k *
    (((Finset.Iic (k, 0)).sup
      (fun m : Nat × Nat => SchwartzMap.seminorm ℝ m.1 m.2)) f)

theorem schwartzLineRealAxisOneAddSeminormConstant_nonneg
    (k : Nat) (f : SchwartzLineTestFunction) :
    0 <= schwartzLineRealAxisOneAddSeminormConstant k f := by
  dsimp [schwartzLineRealAxisOneAddSeminormConstant]
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
    (apply_nonneg _ f)

theorem schwartzLine_realAxis_oneAdd_weighted_norm_le_nat
    (k : Nat) (f : SchwartzLineTestFunction) (t : Real) :
    (1 + ‖t‖) ^ k * ‖f t‖ <=
      schwartzLineRealAxisOneAddSeminormConstant k f := by
  simpa [schwartzLineRealAxisOneAddSeminormConstant] using
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (E := ℝ) (F := ℂ) (m := (k, 0)) (k := k) (n := 0)
      (by simp) (by simp) f t)

/--
A shifted real-axis version of the same checked Schwartz decay estimate.  The
constant is intentionally non-sharp; the point is that every natural polynomial
weight on the real axis is absorbed by explicit Schwartz seminorm data.
-/
noncomputable def schwartzLineRealAxisShiftedSeminormConstant
    (k : Nat) (f : SchwartzLineTestFunction) : Real :=
  (2 : Real) ^ k * schwartzLineRealAxisOneAddSeminormConstant k f

theorem schwartzLineRealAxisShiftedSeminormConstant_nonneg
    (k : Nat) (f : SchwartzLineTestFunction) :
    0 <= schwartzLineRealAxisShiftedSeminormConstant k f := by
  dsimp [schwartzLineRealAxisShiftedSeminormConstant]
  exact mul_nonneg (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
    (schwartzLineRealAxisOneAddSeminormConstant_nonneg k f)

theorem schwartzLineRealAxisOneAddSeminormConstant_continuous
    (k : Nat) :
    Continuous (schwartzLineRealAxisOneAddSeminormConstant k) := by
  classical
  let seminormFamily : Nat × Nat → Seminorm ℝ SchwartzLineTestFunction :=
    fun m => SchwartzMap.seminorm ℝ m.1 m.2
  have hseminorm_cont :
      forall m : Nat × Nat, Continuous (seminormFamily m) := by
    intro m
    simpa [seminormFamily, schwartzSeminormFamily] using
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm m
  have hfinset_cont :
      forall s : Finset (Nat × Nat),
        Continuous fun f : SchwartzLineTestFunction => (s.sup seminormFamily) f := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        change Continuous (0 : SchwartzLineTestFunction → Real)
        exact continuous_zero
    | insert a s _ha hs =>
        simp only [Finset.sup_insert, Seminorm.coe_sup, Pi.sup_apply]
        exact Continuous.max (hseminorm_cont a) hs
  change Continuous fun f : SchwartzLineTestFunction =>
    (2 : Real) ^ k *
      (((Finset.Iic (k, 0)).sup
        (fun m : Nat × Nat => SchwartzMap.seminorm ℝ m.1 m.2)) f)
  simpa [seminormFamily] using
    (hfinset_cont (Finset.Iic (k, 0))).const_mul ((2 : Real) ^ k)

theorem schwartzLineRealAxisShiftedSeminormConstant_continuous
    (k : Nat) :
    Continuous (schwartzLineRealAxisShiftedSeminormConstant k) := by
  change Continuous fun f : SchwartzLineTestFunction =>
    (2 : Real) ^ k * schwartzLineRealAxisOneAddSeminormConstant k f
  exact (schwartzLineRealAxisOneAddSeminormConstant_continuous k).const_mul
    ((2 : Real) ^ k)

/-- The shifted real-axis seminorm constant remains continuous after Fourier
transform. -/
theorem schwartzLineFourierRealAxisShiftedSeminormConstant_continuous
    (k : Nat) :
    Continuous fun f : SchwartzLineTestFunction =>
      schwartzLineRealAxisShiftedSeminormConstant k
        (SchwartzLineTestFunction.fourier f) := by
  change Continuous fun f : SchwartzLineTestFunction =>
    schwartzLineRealAxisShiftedSeminormConstant k
      ((SchwartzMap.fourierTransformCLM Complex) f)
  exact (schwartzLineRealAxisShiftedSeminormConstant_continuous k).comp
    (SchwartzMap.fourierTransformCLM Complex).continuous

/-- Evaluation of a Schwartz line test at a fixed real point, as a continuous
complex-linear map. -/
noncomputable def schwartzLineEvaluationCLM
    (t : Real) : SchwartzLineTestFunction →L[Complex] Complex :=
  (BoundedContinuousFunction.evalCLM Complex t).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM Complex Real Complex)

@[simp]
theorem schwartzLineEvaluationCLM_apply
    (t : Real) (f : SchwartzLineTestFunction) :
    schwartzLineEvaluationCLM t f = f t := by
  rfl

/-- Fixed real-point evaluation is continuous on the Schwartz line test space. -/
theorem schwartzLineEvaluation_continuous
    (t : Real) :
    Continuous fun f : SchwartzLineTestFunction => f t := by
  change Continuous fun f : SchwartzLineTestFunction =>
    schwartzLineEvaluationCLM t f
  exact (schwartzLineEvaluationCLM t).continuous

/-- The norm of a fixed real-point evaluation is continuous on Schwartz line
tests. -/
theorem schwartzLineEvaluation_norm_continuous
    (t : Real) :
    Continuous fun f : SchwartzLineTestFunction => ‖f t‖ :=
  (schwartzLineEvaluation_continuous t).norm

/-- Fixed real-frequency Fourier evaluation, as a continuous complex-linear
map on Schwartz line tests. -/
noncomputable def schwartzLineFourierEvaluationCLM
    (t : Real) : SchwartzLineTestFunction →L[Complex] Complex :=
  (schwartzLineEvaluationCLM t).comp
    (SchwartzMap.fourierTransformCLM Complex)

@[simp]
theorem schwartzLineFourierEvaluationCLM_apply
    (t : Real) (f : SchwartzLineTestFunction) :
    schwartzLineFourierEvaluationCLM t f =
      (SchwartzLineTestFunction.fourier f) t := by
  rfl

/-- Fixed real-frequency Fourier evaluation is continuous on the Schwartz line
test space. -/
theorem schwartzLineFourierEvaluation_continuous
    (t : Real) :
    Continuous fun f : SchwartzLineTestFunction =>
      (SchwartzLineTestFunction.fourier f) t := by
  change Continuous fun f : SchwartzLineTestFunction =>
    schwartzLineFourierEvaluationCLM t f
  exact (schwartzLineFourierEvaluationCLM t).continuous

/-- The norm of fixed real-frequency Fourier evaluation is continuous on
Schwartz line tests. -/
theorem schwartzLineFourierEvaluation_norm_continuous
    (t : Real) :
    Continuous fun f : SchwartzLineTestFunction =>
      ‖(SchwartzLineTestFunction.fourier f) t‖ :=
  (schwartzLineFourierEvaluation_continuous t).norm

theorem schwartzLine_realAxis_shifted_weighted_norm_le_nat
    (k : Nat) (f : SchwartzLineTestFunction) (t : Real) :
    ‖f t‖ * (‖t‖ + 2) ^ k <=
      schwartzLineRealAxisShiftedSeminormConstant k f := by
  have hshift_base :
      ‖t‖ + 2 <= (2 : Real) * (1 + ‖t‖) := by
    nlinarith [norm_nonneg t]
  have hshift_pow :
      (‖t‖ + 2) ^ k <= ((2 : Real) * (1 + ‖t‖)) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hshift_base k
  have hshift_pow' :
      (‖t‖ + 2) ^ k <= (2 : Real) ^ k * (1 + ‖t‖) ^ k := by
    simpa [mul_pow] using hshift_pow
  have hmul :
      ‖f t‖ * (‖t‖ + 2) ^ k <=
        ‖f t‖ * ((2 : Real) ^ k * (1 + ‖t‖) ^ k) := by
    exact mul_le_mul_of_nonneg_left hshift_pow' (norm_nonneg (f t))
  have hone :=
    schwartzLine_realAxis_oneAdd_weighted_norm_le_nat k f t
  have hone_scaled :
      (2 : Real) ^ k * ((1 + ‖t‖) ^ k * ‖f t‖) <=
        (2 : Real) ^ k * schwartzLineRealAxisOneAddSeminormConstant k f := by
    exact mul_le_mul_of_nonneg_left hone
      (pow_nonneg (by norm_num : (0 : Real) <= 2) k)
  calc
    ‖f t‖ * (‖t‖ + 2) ^ k
        <= ‖f t‖ * ((2 : Real) ^ k * (1 + ‖t‖) ^ k) := hmul
    _ = (2 : Real) ^ k * ((1 + ‖t‖) ^ k * ‖f t‖) := by ring
    _ <= (2 : Real) ^ k *
        schwartzLineRealAxisOneAddSeminormConstant k f := hone_scaled
    _ = schwartzLineRealAxisShiftedSeminormConstant k f := by
      rfl

/--
The same shifted real-axis decay estimate written with the complex norm of the
embedded real point.  This is the notation used by the global extension
certificate on `Complex`.
-/
theorem schwartzLine_realAxis_complexShifted_weighted_norm_le_nat
    (k : Nat) (f : SchwartzLineTestFunction) (t : Real) :
    ‖f t‖ * (norm ((t : Complex)) + 2) ^ k <=
      schwartzLineRealAxisShiftedSeminormConstant k f := by
  simpa using schwartzLine_realAxis_shifted_weighted_norm_le_nat k f t

/--
Natural polynomial weights can be read as real-exponent shifted-radius weights
on the real axis.  This is the exact exponent convention used by
`RiemannWeilShiftedRadiusDecayCertificate`.
-/
theorem schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast
    (k : Nat) (f : SchwartzLineTestFunction) (t : Real) :
    ‖f t‖ * (norm ((t : Complex)) + 2) ^ (k : Real) <=
      schwartzLineRealAxisShiftedSeminormConstant k f := by
  rw [Real.rpow_natCast]
  exact schwartzLine_realAxis_complexShifted_weighted_norm_le_nat k f t

/--
The Fourier transform of a Schwartz line test has the same shifted real-axis
polynomial decay, with the seminorm constant applied to the Fourier transform.
-/
theorem schwartzLine_fourier_realAxis_complexShifted_weighted_norm_le_rpow_natCast
    (k : Nat) (f : SchwartzLineTestFunction) (t : Real) :
    ‖(SchwartzLineTestFunction.fourier f) t‖ *
        (norm ((t : Complex)) + 2) ^ (k : Real) <=
      schwartzLineRealAxisShiftedSeminormConstant k
        (SchwartzLineTestFunction.fourier f) :=
  schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast
    k (SchwartzLineTestFunction.fourier f) t

/--
Positive two-channel real/Fourier shifted decay estimate.

This is the pointwise analytic inequality behind the finite-component
real/Fourier strip route: if a component is controlled by nonnegative
coefficients times the real-axis values of `f` and `𝓕 f`, then the same
component is controlled after the shifted polynomial weight by the corresponding
two seminorm majorants.
-/
theorem schwartzLine_realFourier_linearCombination_complexShifted_weighted_norm_le
    (k : Nat) (f : SchwartzLineTestFunction) (t : Real)
    (realConstant fourierConstant : Real)
    (realConstant_nonneg : 0 <= realConstant)
    (fourierConstant_nonneg : 0 <= fourierConstant) :
    (realConstant * ‖f t‖ +
        fourierConstant * ‖(SchwartzLineTestFunction.fourier f) t‖) *
        (norm ((t : Complex)) + 2) ^ (k : Real) <=
      realConstant * schwartzLineRealAxisShiftedSeminormConstant k f +
        fourierConstant *
          schwartzLineRealAxisShiftedSeminormConstant k
            (SchwartzLineTestFunction.fourier f) := by
  let radiusPower : Real := (norm ((t : Complex)) + 2) ^ (k : Real)
  have hf_decay :
      ‖f t‖ * radiusPower <=
        schwartzLineRealAxisShiftedSeminormConstant k f := by
    simpa [radiusPower] using
      schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast
        k f t
  have hfourier_decay :
      ‖(SchwartzLineTestFunction.fourier f) t‖ * radiusPower <=
        schwartzLineRealAxisShiftedSeminormConstant k
          (SchwartzLineTestFunction.fourier f) := by
    simpa [radiusPower] using
      schwartzLine_fourier_realAxis_complexShifted_weighted_norm_le_rpow_natCast
        k f t
  have hf_scaled :
      realConstant * (‖f t‖ * radiusPower) <=
        realConstant * schwartzLineRealAxisShiftedSeminormConstant k f :=
    mul_le_mul_of_nonneg_left hf_decay realConstant_nonneg
  have hfourier_scaled :
      fourierConstant *
          (‖(SchwartzLineTestFunction.fourier f) t‖ * radiusPower) <=
        fourierConstant *
          schwartzLineRealAxisShiftedSeminormConstant k
            (SchwartzLineTestFunction.fourier f) :=
    mul_le_mul_of_nonneg_left hfourier_decay fourierConstant_nonneg
  calc
    (realConstant * ‖f t‖ +
        fourierConstant * ‖(SchwartzLineTestFunction.fourier f) t‖) *
        (norm ((t : Complex)) + 2) ^ (k : Real)
        =
          realConstant * (‖f t‖ * radiusPower) +
            fourierConstant *
              (‖(SchwartzLineTestFunction.fourier f) t‖ * radiusPower) := by
          dsimp [radiusPower]
          ring
    _ <= realConstant * schwartzLineRealAxisShiftedSeminormConstant k f +
        fourierConstant *
          schwartzLineRealAxisShiftedSeminormConstant k
            (SchwartzLineTestFunction.fourier f) :=
      add_le_add hf_scaled hfourier_scaled

/--
Component-level real/Fourier shifted-radius majorization.

This is the reusable constructive estimate used by finite-component strip
routes: a component bounded by nonnegative real/Fourier profiles on `z.re`
inherits the assembled shifted-seminorm majorant after multiplying by the
project shifted-radius weight.
-/
theorem realFourierProfile_bound_weighted_norm_le_shiftedSeminormMajorant
    (k : Nat) (f : SchwartzLineTestFunction) (z value : Complex)
    (realConstant fourierConstant : Real)
    (realConstant_nonneg : 0 <= realConstant)
    (fourierConstant_nonneg : 0 <= fourierConstant)
    (profile_bound :
      norm value <=
        realConstant * norm (f z.re) +
          fourierConstant *
            norm ((SchwartzLineTestFunction.fourier f) z.re)) :
    norm value * (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
      realConstant * schwartzLineRealAxisShiftedSeminormConstant k f +
        fourierConstant *
          schwartzLineRealAxisShiftedSeminormConstant k
            (SchwartzLineTestFunction.fourier f) := by
  let radiusPower : Real := (norm ((z.re : Complex)) + 2) ^ (k : Real)
  have hbase_pos : 0 < norm ((z.re : Complex)) + 2 := by
    have hnorm_nonneg : 0 <= norm ((z.re : Complex)) := norm_nonneg _
    linarith
  have hradiusPower_nonneg : 0 <= radiusPower := by
    exact le_of_lt (Real.rpow_pos_of_pos hbase_pos (k : Real))
  have hweighted :
      norm value * radiusPower <=
        (realConstant * norm (f z.re) +
            fourierConstant *
              norm ((SchwartzLineTestFunction.fourier f) z.re)) *
          radiusPower :=
    mul_le_mul_of_nonneg_right profile_bound hradiusPower_nonneg
  have hprofiles :
      (realConstant * norm (f z.re) +
          fourierConstant *
            norm ((SchwartzLineTestFunction.fourier f) z.re)) *
          radiusPower <=
        realConstant * schwartzLineRealAxisShiftedSeminormConstant k f +
          fourierConstant *
            schwartzLineRealAxisShiftedSeminormConstant k
              (SchwartzLineTestFunction.fourier f) := by
    simpa [radiusPower] using
      schwartzLine_realFourier_linearCombination_complexShifted_weighted_norm_le
        k f z.re realConstant fourierConstant realConstant_nonneg
        fourierConstant_nonneg
  calc
    norm value * (norm ((z.re : Complex)) + 2) ^ (k : Real)
        = norm value * radiusPower := by
          rfl
    _ <= (realConstant * norm (f z.re) +
            fourierConstant *
              norm ((SchwartzLineTestFunction.fourier f) z.re)) *
          radiusPower := hweighted
    _ <= realConstant * schwartzLineRealAxisShiftedSeminormConstant k f +
        fourierConstant *
          schwartzLineRealAxisShiftedSeminormConstant k
            (SchwartzLineTestFunction.fourier f) := hprofiles

/--
Source-normalized component-level real/Fourier shifted-radius majorization.

This is the source-side form of
`realFourierProfile_bound_weighted_norm_le_shiftedSeminormMajorant`: Lean uses
the source Fourier normalization field to reuse the project Fourier estimate,
then rewrites the result back into the source seminorms consumed by the
source-indexed p-series constructor.
-/
theorem sourceRealFourierProfile_bound_weighted_norm_le_shiftedSeminormMajorant
    (testData : GuinandWeilSourceTestFunctionClass)
    (k : Nat) (g : testData.SourceTestFunction) (hg : testData.admissible g)
    (z value : Complex)
    (realConstant fourierConstant : Real)
    (realConstant_nonneg : 0 <= realConstant)
    (fourierConstant_nonneg : 0 <= fourierConstant)
    (profile_bound :
      norm value <=
        realConstant * norm ((testData.toSchwartz g) z.re) +
          fourierConstant * norm ((testData.sourceFourier g) z.re)) :
    norm value * (norm ((z.re : Complex)) + 2) ^ (k : Real) <=
      realConstant *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.toSchwartz g) +
        fourierConstant *
          schwartzLineRealAxisShiftedSeminormConstant k
            (testData.sourceFourier g) := by
  have hsourceFourier :
      testData.sourceFourier g =
        SchwartzLineTestFunction.fourier (testData.toSchwartz g) :=
    testData.sourceFourier_eq_projectFourier g hg
  have hproject_profile :
      norm value <=
        realConstant * norm ((testData.toSchwartz g) z.re) +
          fourierConstant *
            norm
              ((SchwartzLineTestFunction.fourier (testData.toSchwartz g))
                z.re) := by
    simpa [hsourceFourier] using profile_bound
  have hproject :=
    realFourierProfile_bound_weighted_norm_le_shiftedSeminormMajorant
      k (testData.toSchwartz g) z value realConstant fourierConstant
      realConstant_nonneg fourierConstant_nonneg hproject_profile
  simpa [hsourceFourier] using hproject

/--
Every Schwartz line test function has arbitrary natural shifted polynomial
decay on the real axis, in the same real-exponent convention as the global
certificate.  The remaining p-series obstruction is therefore genuinely the
off-real complex extension estimate, not real-axis Schwartz decay.
-/
theorem exists_schwartzLine_realAxis_shifted_decay_rpow_natCast
    (k : Nat) (f : SchwartzLineTestFunction) :
    exists C : Real,
      0 <= C /\
        forall t : Real,
          ‖f t‖ * (norm ((t : Complex)) + 2) ^ (k : Real) <= C := by
  refine ⟨schwartzLineRealAxisShiftedSeminormConstant k f,
    schwartzLineRealAxisShiftedSeminormConstant_nonneg k f, ?_⟩
  intro t
  exact schwartzLine_realAxis_complexShifted_weighted_norm_le_rpow_natCast k f t

end RiemannHypothesisProject
