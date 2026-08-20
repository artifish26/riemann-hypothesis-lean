import RiemannHypothesisProject.Experiments.M100.SuzukiScalarKernelIdentity
import RiemannHypothesisProject.Experiments.M100.SuzukiSingularShiftedCompletion
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# M100-DF6D3 Suzuki project-form normalization

This module fixes the exact equation-(2.5) data used to compare Suzuki's
source-coordinate complete form with the X13/X14 project-normalized
Guinand--Weil residual.  It also exposes the smooth differential core and the
source-to-project support scaling before naming the remaining complete-form
identity.

No positivity, endpoint certificate, or source-operator inverse estimate is
assumed or concluded here.  The parity and low/far data below only freeze the
FT2 decomposition; they assert no spectral bound.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open MeasureTheory Set SchwartzLineTestFunction
open scoped ComplexConjugate

/-- Prime indices whose logarithmic translations can meet a radius-`a`
support window. -/
def suzukiProjectPrimeIndexSet (a : Real) : Finset Nat :=
  Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊

/-- The signed prime coefficient in Suzuki (2.5). -/
def suzukiProjectPrimeCoefficient (n : Nat) : Real :=
  -(ArithmeticFunction.vonMangoldt n / Real.sqrt n)

/-- The source-coordinate translation attached to a prime-power index. -/
def suzukiProjectPrimeShift (n : Nat) : Real :=
  Real.log n

/-- The scalar term in Suzuki (2.5), kept separate from the local energy and
the prime and smooth-kernel remainders. -/
def suzukiProjectCompleteScalar : Real :=
  -suzukiSourceLogNormalizationConstant

/-- Suzuki's constant `A`; exposing it checks that the source scalar is
`-(2*A+1)`. -/
def suzukiProjectA : Real :=
  (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant - 1) / 2

theorem two_mul_suzukiProjectA_add_one :
    2 * suzukiProjectA + 1 = suzukiSourceLogNormalizationConstant := by
  unfold suzukiProjectA suzukiSourceLogNormalizationConstant
  ring

theorem suzukiProjectCompleteScalar_eq :
    suzukiProjectCompleteScalar = -(2 * suzukiProjectA + 1) := by
  rw [suzukiProjectCompleteScalar, two_mul_suzukiProjectA_add_one]

/-- The exact frozen source endpoint `A_(1/2)` used by FT2 and the direct-form
certificate lane. -/
def suzukiProjectAStar : Real :=
  let L := Real.log 2
  (L + Real.sqrt (L ^ 2 +
    4 * Real.exp (-2 * Real.sqrt 2 * L))) / 4

/-- The frozen FT2 low-mode cutoff. -/
def suzukiProjectLowModeCutoff : Nat := 36

/-- The last explicit low-plus-boundary mode in the FT2 split. -/
def suzukiProjectFarBoundary : Nat := 44

/-- The two reflection-parity blocks used by the endpoint decomposition. -/
inductive SuzukiProjectParity
  | even
  | odd
  deriving DecidableEq

/-- Frozen low-mode indices: `0,...,36` in even parity and `1,...,36` in odd
parity. -/
def suzukiProjectLowModes : SuzukiProjectParity → Finset Nat
  | .even => Finset.range (suzukiProjectLowModeCutoff + 1)
  | .odd => Finset.Icc 1 suzukiProjectLowModeCutoff

/-- Frozen low-plus-boundary indices: `0,...,44` in even parity and
`1,...,44` in odd parity. -/
def suzukiProjectLowPlusBoundaryModes :
    SuzukiProjectParity → Finset Nat
  | .even => Finset.range (suzukiProjectFarBoundary + 1)
  | .odd => Finset.Icc 1 suzukiProjectFarBoundary

/-- The complete, non-terminally-truncated far index set begins after mode
`44`. -/
def suzukiProjectFarModes : Set Nat :=
  Ici (suzukiProjectFarBoundary + 1)

@[simp]
theorem suzukiProjectLowModes_even :
    suzukiProjectLowModes .even = Finset.range 37 := by
  rfl

@[simp]
theorem suzukiProjectLowModes_odd :
    suzukiProjectLowModes .odd = Finset.Icc 1 36 := by
  rfl

@[simp]
theorem suzukiProjectLowPlusBoundaryModes_even :
    suzukiProjectLowPlusBoundaryModes .even = Finset.range 45 := by
  rfl

@[simp]
theorem suzukiProjectLowPlusBoundaryModes_odd :
    suzukiProjectLowPlusBoundaryModes .odd = Finset.Icc 1 44 := by
  rfl

@[simp]
theorem suzukiProjectFarModes_eq :
    suzukiProjectFarModes = Ici 45 := by
  rfl

/-- One auditable theorem freezes the complete FT2 mode convention: low rows
through `36`, explicit boundary rows through `44`, and every far mode from
`45` onward in both parity blocks. -/
theorem suzukiDF6D3_frozenModeData :
    suzukiProjectLowModeCutoff = 36 ∧
    suzukiProjectFarBoundary = 44 ∧
    suzukiProjectLowModes .even = Finset.range 37 ∧
    suzukiProjectLowModes .odd = Finset.Icc 1 36 ∧
    suzukiProjectLowPlusBoundaryModes .even = Finset.range 45 ∧
    suzukiProjectLowPlusBoundaryModes .odd = Finset.Icc 1 44 ∧
    suzukiProjectFarModes = Ici 45 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem suzukiProjectAStar_pos : 0 < suzukiProjectAStar := by
  unfold suzukiProjectAStar
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : 0 ≤ Real.sqrt
      (Real.log 2 ^ 2 +
        4 * Real.exp (-2 * Real.sqrt 2 * Real.log 2)) :=
    Real.sqrt_nonneg _
  nlinarith

theorem suzukiProjectPrimeFloor_at_aStar :
    ⌊Real.exp (2 * suzukiProjectAStar)⌋₊ = 2 := by
  let L : Real := Real.log 2
  let z : Real := L ^ 2 + 4 * Real.exp (-2 * Real.sqrt 2 * L)
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  have hzpos : 0 < z := by
    dsimp only [z]
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt z := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hzpos.le
  have hL_le_sqrt : L ≤ Real.sqrt z := by
    dsimp only [z] at hsqrt_sq
    nlinarith [Real.exp_pos (-2 * Real.sqrt 2 * L)]
  have htwo_le : (2 : Real) ≤ Real.exp (2 * suzukiProjectAStar) := by
    have hlog_le : L ≤ 2 * suzukiProjectAStar := by
      dsimp only [suzukiProjectAStar]
      change L ≤ 2 * ((L + Real.sqrt z) / 4)
      linarith
    calc
      (2 : Real) = Real.exp L := by
        dsimp only [L]
        rw [Real.exp_log (by norm_num)]
      _ ≤ Real.exp (2 * suzukiProjectAStar) :=
        Real.exp_le_exp.mpr hlog_le
  have hexp_lt_quarter :
      Real.exp (-2 * Real.sqrt 2 * L) < 1 / 4 := by
    have hexponent : -2 * Real.sqrt 2 * L < -2 * L := by
      nlinarith [Real.one_lt_sqrt_two]
    calc
      Real.exp (-2 * Real.sqrt 2 * L) < Real.exp (-2 * L) :=
        Real.exp_lt_exp.mpr hexponent
      _ = 1 / 4 := by
        dsimp only [L]
        rw [show -2 * Real.log 2 = -(Real.log 2 + Real.log 2) by ring,
          Real.exp_neg, Real.exp_add,
          Real.exp_log (by norm_num)]
        norm_num
  have hL_lt : L < 7 / 10 := by
    dsimp only [L]
    linarith [Real.log_two_lt_d9]
  have hz_lt : z < (13 / 10 : Real) ^ 2 := by
    dsimp only [z]
    nlinarith [sq_nonneg (L - 7 / 10)]
  have hsqrt_lt : Real.sqrt z < 13 / 10 :=
    (Real.sqrt_lt' (by norm_num)).2 hz_lt
  have htwoA_lt_one : 2 * suzukiProjectAStar < 1 := by
    dsimp only [suzukiProjectAStar]
    change 2 * ((L + Real.sqrt z) / 4) < 1
    linarith
  have hone_lt_log_three : (1 : Real) < Real.log 3 := by
    linarith [Real.log_three_gt_d9]
  have hexp_lt_three : Real.exp (2 * suzukiProjectAStar) < 3 := by
    calc
      Real.exp (2 * suzukiProjectAStar) < Real.exp (Real.log 3) :=
        Real.exp_lt_exp.mpr (htwoA_lt_one.trans hone_lt_log_three)
      _ = 3 := Real.exp_log (by norm_num)
  exact (Nat.floor_eq_iff (Real.exp_nonneg _)).2
    ⟨by exact_mod_cast htwo_le, by exact_mod_cast hexp_lt_three⟩

theorem suzukiProjectPrimeIndexSet_at_aStar :
    suzukiProjectPrimeIndexSet suzukiProjectAStar = {2} := by
  unfold suzukiProjectPrimeIndexSet
  rw [suzukiProjectPrimeFloor_at_aStar]
  simp

/-- The global-`L²` translation correlation used by DF6D2 is the source
autocorrelation at the opposite displacement.  This fixes the translation
orientation before the symmetric prime term is assembled. -/
theorem suzukiL2TranslationCorrelation_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) (t : Real) :
    suzukiL2TranslationCorrelation t (suzukiSmoothCoreToL2 v) =
      autocorrelation v.1 (-t) := by
  rw [suzukiL2TranslationCorrelation, L2.inner_def,
    autocorrelation_apply, MeasureTheory.convolution_def]
  have hv :
      (suzukiSmoothCoreToL2 v : Real → Complex) =ᵐ[volume] v.1 :=
    (v.1.memLp (2 : ENNReal) (volume : Measure Real)).coeFn_toLp
  have htranslate :
      (suzukiL2Translate t (suzukiSmoothCoreToL2 v) : Real → Complex) =ᵐ[volume]
        fun x => (suzukiSmoothCoreToL2 v) (x + t) :=
    Lp.coeFn_compMeasurePreserving (suzukiSmoothCoreToL2 v)
      (measurePreserving_add_right (volume : Measure Real) t)
  have hvtranslate :
      (fun x => (suzukiSmoothCoreToL2 v) (x + t)) =ᵐ[volume]
        fun x => v.1 (x + t) :=
    (measurePreserving_add_right (volume : Measure Real) t).quasiMeasurePreserving
      |>.ae_eq_comp hv
  apply integral_congr_ae
  filter_upwards [htranslate, hvtranslate, hv] with x hxTranslate hxShift hx
  rw [hxTranslate, hxShift, hx]
  simp [star_apply, RCLike.inner_apply]

/-- Autocorrelation Hermitian symmetry in the exact source convention. -/
theorem conj_autocorrelation_neg_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) (t : Real) :
    conj (autocorrelation v.1 (-t)) = autocorrelation v.1 t := by
  rw [autocorrelation_apply, autocorrelation_apply,
    MeasureTheory.convolution_def, MeasureTheory.convolution_def,
    ← integral_conj]
  calc
    (∫ x : Real, conj (v.1 x * star v.1 (-t - x))) =
        ∫ x : Real, (fun y : Real => v.1 y * conj (v.1 (y - t))) (x + t) := by
      apply integral_congr_ae
      filter_upwards with x
      have hneg : -(-t - x) = x + t := by ring
      have hsub : x + t - t = x := by ring
      simp [star_apply, hneg, hsub]
      ring
    _ = ∫ y : Real, v.1 y * conj (v.1 (y - t)) := by
      exact integral_add_right_eq_self
        (fun y : Real => v.1 y * conj (v.1 (y - t))) t
    _ = ∫ x : Real, v.1 x * star v.1 (t - x) := by
      apply integral_congr_ae
      filter_upwards with x
      have hneg : -(t - x) = x - t := by ring
      simp [star_apply, hneg]

/-- The DF6D2 symmetric translation diagonal is literally the pair of source
autocorrelation samples in Suzuki's equation (2.5). -/
theorem suzukiL2SymmetricTranslationDiagonal_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) (t : Real) :
    suzukiL2SymmetricTranslationDiagonal t (suzukiSmoothCoreToL2 v) =
      (autocorrelation v.1 t + autocorrelation v.1 (-t)).re := by
  rw [suzukiL2SymmetricTranslationDiagonal,
    suzukiL2TranslationCorrelation_smoothCore]
  have hsym := congrArg Complex.re (conj_autocorrelation_neg_smoothCore v t)
  simp only [Complex.conj_re, Complex.add_re] at hsym ⊢
  linarith

/-- The scalar `L²` mass in the complete form is the zero-displacement
autocorrelation mass used by the project formula. -/
theorem norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re
    {a : Real} (v : SuzukiSmoothCore a) :
    ‖suzukiSmoothCoreToL2 v‖ ^ 2 = (autocorrelation v.1 0).re := by
  have hcorr := suzukiL2TranslationCorrelation_smoothCore v 0
  have htranslate :
      suzukiL2Translate 0 (suzukiSmoothCoreToL2 v) =
        suzukiSmoothCoreToL2 v := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving
      (suzukiSmoothCoreToL2 v)
      (measurePreserving_add_right (volume : Measure Real) 0)] with x hx
    simpa [suzukiL2Translate] using hx
  unfold suzukiL2TranslationCorrelation at hcorr
  rw [htranslate] at hcorr
  calc
    ‖suzukiSmoothCoreToL2 v‖ ^ 2 =
        (inner Complex (suzukiSmoothCoreToL2 v)
          (suzukiSmoothCoreToL2 v)).re :=
      (inner_self_eq_norm_sq (𝕜 := Complex) (suzukiSmoothCoreToL2 v)).symm
    _ = (autocorrelation v.1 0).re := by
      simpa using congrArg Complex.re hcorr

/-- The complete finite prime translation remainder is the exact finite sum
of symmetric source autocorrelation samples. -/
theorem suzukiL2FiniteTranslationRemainder_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiL2FiniteTranslationRemainder
        (suzukiProjectPrimeIndexSet a)
        suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
        (suzukiSmoothCoreToL2 v) =
      ∑ n ∈ suzukiProjectPrimeIndexSet a,
        suzukiProjectPrimeCoefficient n *
          (autocorrelation v.1 (suzukiProjectPrimeShift n) +
            autocorrelation v.1 (-suzukiProjectPrimeShift n)).re := by
  unfold suzukiL2FiniteTranslationRemainder
  apply Finset.sum_congr rfl
  intro n hn
  rw [suzukiL2SymmetricTranslationDiagonal_smoothCore]

/-- X14's prime screw pairing and DF6D2's global-`L²` translation remainder
are the same signed finite form. -/
theorem re_suzukiFiniteKernelPairingComplex_primeScrewTerm_eq_translation
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    (suzukiFiniteKernelPairingComplex suzukiPrimeScrewTerm a
        (SchwartzMap.derivCLM Complex Complex v.1)).re =
      suzukiL2FiniteTranslationRemainder
        (suzukiProjectPrimeIndexSet a)
        suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
        (suzukiSmoothCoreToL2 v) := by
  rw [suzukiFiniteKernelPairingComplex_primeScrewTerm_eq_finiteSum
    ha (by
      intro x hx
      exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩)]
  rw [suzukiL2FiniteTranslationRemainder_smoothCore, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, zero_mul, sub_zero]
  rfl

/-- The literature-normalized project prime side is exactly the signed
finite translation part of the concrete source form. -/
theorem guinandWeilLiteraturePrimeSide_suzukiProjectBase_eq_translation
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    guinandWeilLiteraturePrimeSide
        (fourierAutocorrelation (suzukiProjectBase v.1)) =
      suzukiL2FiniteTranslationRemainder
        (suzukiProjectPrimeIndexSet a)
        suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
        (suzukiSmoothCoreToL2 v) := by
  rw [guinandWeilLiteraturePrimeSide_suzukiProjectBase_eq_kernelPairing
    ha (by
      intro x hx
      exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩)]
  exact re_suzukiFiniteKernelPairingComplex_primeScrewTerm_eq_translation ha v

/-- The scalar separated by FT2 from the raw project Gamma component. -/
def suzukiProjectRawConstant : Real :=
  -(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)

/-- The raw project Gamma form after removing FT2's separate scalar block. -/
def suzukiProjectRawGammaCoreForm
    {a : Real} (v : SuzukiSmoothCore a) : Real :=
  guinandWeilLiteratureGammaSide
      (fourierAutocorrelation (suzukiProjectBase v.1)) -
    suzukiProjectRawConstant * ‖suzukiSmoothCoreToL2 v‖ ^ 2

theorem suzukiProjectCompleteScalar_sub_rawConstant :
    suzukiProjectCompleteScalar - suzukiProjectRawConstant = Real.log 2 := by
  unfold suzukiProjectCompleteScalar suzukiProjectRawConstant
    suzukiSourceLogNormalizationConstant
  rw [show (4 : Real) * Real.pi = 2 * (2 * Real.pi) by ring,
    Real.log_mul (by norm_num : (2 : Real) ≠ 0)
      (by positivity : (2 : Real) * Real.pi ≠ 0)]
  ring

/-- The exact unshifted smooth-core complete form assembled from the DF6D2
local energy, source scalar, complete finite prime sum, and smooth `r''`
remainder. -/
def suzukiProjectNormalizedCompleteCoreForm
    {a : Real} (u : SuzukiSmoothCore a) : Real :=
  suzukiSingularLocalForm a u.1 +
    suzukiRSecondFiniteRadiusRemainder
      (suzukiProjectPrimeIndexSet a) a suzukiProjectCompleteScalar
      suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
      (suzukiSmoothCoreToL2 u)

theorem suzukiProjectNormalizedCompleteCoreForm_eq
    {a : Real} (u : SuzukiSmoothCore a) :
    suzukiProjectNormalizedCompleteCoreForm u =
      suzukiSingularLocalForm a u.1 +
        suzukiRSecondFiniteRadiusRemainder
          (suzukiProjectPrimeIndexSet a) a
          (-suzukiSourceLogNormalizationConstant)
          (fun n =>
            -(ArithmeticFunction.vonMangoldt n / Real.sqrt n))
          (fun n => Real.log n) (suzukiSmoothCoreToL2 u) := by
  rfl

/-- Fully unfolded equation-(2.5) decomposition on the smooth core.  The
scalar, every active prime-power translate, and the signed exact `r''` operator
are separate summands. -/
theorem suzukiProjectNormalizedCompleteCoreForm_eq_components
    {a : Real} (u : SuzukiSmoothCore a) :
    suzukiProjectNormalizedCompleteCoreForm u =
      suzukiSingularLocalForm a u.1 +
        suzukiProjectCompleteScalar * ‖suzukiSmoothCoreToL2 u‖ ^ 2 +
        Finset.sum (suzukiProjectPrimeIndexSet a) (fun n =>
          suzukiProjectPrimeCoefficient n *
            suzukiL2SymmetricTranslationDiagonal
              (suzukiProjectPrimeShift n) (suzukiSmoothCoreToL2 u)) +
        suzukiL2BoundedOperatorDiagonal
          (suzukiRSecondSourceRemainderOperator a)
          (suzukiSmoothCoreToL2 u) := by
  unfold suzukiProjectNormalizedCompleteCoreForm
    suzukiRSecondFiniteRadiusRemainder
    suzukiL2FiniteRadiusRemainder
    suzukiL2FiniteTranslationRemainder
  ring

/-- The same decomposition with the complete finite prime block grouped as
the DF6D2 translation remainder. -/
theorem suzukiProjectNormalizedCompleteCoreForm_eq_groupedComponents
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiProjectNormalizedCompleteCoreForm v =
      suzukiSingularLocalForm a v.1 +
        suzukiProjectCompleteScalar * ‖suzukiSmoothCoreToL2 v‖ ^ 2 +
        suzukiL2FiniteTranslationRemainder
          (suzukiProjectPrimeIndexSet a)
          suzukiProjectPrimeCoefficient suzukiProjectPrimeShift
          (suzukiSmoothCoreToL2 v) +
        suzukiL2BoundedOperatorDiagonal
          (suzukiRSecondSourceRemainderOperator a)
          (suzukiSmoothCoreToL2 v) := by
  unfold suzukiProjectNormalizedCompleteCoreForm
    suzukiRSecondFiniteRadiusRemainder
    suzukiL2FiniteRadiusRemainder
  ring

/-- The source remainder is minus the positive-sign smooth `r''` operator
diagonal used in FT2's notation. -/
theorem suzukiRSecondSourceRemainderDiagonal_eq_neg_global
    (a : Real) (v : SuzukiL2) :
    suzukiL2BoundedOperatorDiagonal
        (suzukiRSecondSourceRemainderOperator a) v =
      -suzukiL2BoundedOperatorDiagonal
        (suzukiRSecondGlobalL2Operator a) v := by
  unfold suzukiL2BoundedOperatorDiagonal
    suzukiRSecondSourceRemainderOperator
  simp

/-- The bounded remainder diagonal is the negative exact `r''` finite-square
pairing from Suzuki (2.5). -/
theorem suzukiRSecondSourceRemainderDiagonal_smoothCore
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiL2BoundedOperatorDiagonal
        (suzukiRSecondSourceRemainderOperator a)
        (suzukiSmoothCoreToL2 v) =
      -(suzukiFiniteKernelPairingComplex
          suzukiRSecondKernel a v.1).re := by
  unfold suzukiL2BoundedOperatorDiagonal
  rw [inner_suzukiRSecondSourceRemainderOperator_smoothCore_self,
    Complex.neg_re]

/-- Equation (2.5) with every core-level source component displayed as a
literal scalar, autocorrelation sample, or exact `r''` integral. -/
theorem suzukiProjectNormalizedCompleteCoreForm_eq_sourceComponents
    {a : Real} (v : SuzukiSmoothCore a) :
    suzukiProjectNormalizedCompleteCoreForm v =
      suzukiSingularLocalForm a v.1 +
        suzukiProjectCompleteScalar * (autocorrelation v.1 0).re +
        ∑ n ∈ suzukiProjectPrimeIndexSet a,
          suzukiProjectPrimeCoefficient n *
            (autocorrelation v.1 (suzukiProjectPrimeShift n) +
              autocorrelation v.1 (-suzukiProjectPrimeShift n)).re -
        (suzukiFiniteKernelPairingComplex
          suzukiRSecondKernel a v.1).re := by
  rw [suzukiProjectNormalizedCompleteCoreForm_eq_components,
    norm_sq_suzukiSmoothCoreToL2_eq_autocorrelation_zero_re,
    suzukiRSecondSourceRemainderDiagonal_smoothCore]
  simp_rw [suzukiL2SymmetricTranslationDiagonal_smoothCore]
  ring

/-- At the frozen endpoint the complete arithmetic sum consists of the one
signed prime-`2` translation, with no hidden cutoff term. -/
theorem suzukiProjectNormalizedCompleteCoreForm_at_aStar_eq_components
    (v : SuzukiSmoothCore suzukiProjectAStar) :
    suzukiProjectNormalizedCompleteCoreForm v =
      suzukiSingularLocalForm suzukiProjectAStar v.1 -
        (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
        (Real.log 2 / Real.sqrt 2) *
          suzukiL2SymmetricTranslationDiagonal (Real.log 2)
            (suzukiSmoothCoreToL2 v) +
        suzukiL2BoundedOperatorDiagonal
          (suzukiRSecondSourceRemainderOperator suzukiProjectAStar)
          (suzukiSmoothCoreToL2 v) := by
  rw [suzukiProjectNormalizedCompleteCoreForm_eq_components,
    suzukiProjectPrimeIndexSet_at_aStar]
  simp only [Finset.sum_singleton]
  have hcoefficient :
      suzukiProjectPrimeCoefficient 2 =
        -(Real.log 2 / Real.sqrt 2) := by
    unfold suzukiProjectPrimeCoefficient
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [hcoefficient]
  unfold suzukiProjectCompleteScalar suzukiSourceLogNormalizationConstant
    suzukiProjectPrimeShift
  ring

/-- FT2's pole/Gamma bookkeeping is literal in the smooth source kernel:
`r₀''` is the negative two-pole exponential term and `r₁''` is the regular
Gamma remainder. -/
theorem suzukiRSecondKernel_eq_pole_add_gamma (t : Real) :
    suzukiRSecondKernel t =
      -(Real.exp (t / 2) + Real.exp (-t / 2)) +
        suzukiR1SecondKernel t := by
  rfl

private theorem suzukiSmoothCore_support_subset_Icc
    {a : Real} (v : SuzukiSmoothCore a) :
    Function.support v.1 ⊆ Icc (-a) a := by
  intro x hx
  exact ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩

/-- The source differential `D = i d/dx` preserves the open-interval smooth
core.  The open support of a continuous function removes the apparent endpoint
gap between X14's closed support window and DF6D2's open smooth core. -/
def suzukiSmoothCoreDifferential
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    SuzukiSmoothCore a :=
  ⟨suzukiDifferential v.1, by
    have hclosed :
        Function.support (suzukiDifferential v.1) ⊆ Icc (-a) a :=
      support_suzukiDifferential_subset_Icc
        (suzukiSmoothCore_support_subset_Icc v)
    have hopen : IsOpen (Function.support (suzukiDifferential v.1)) :=
      (suzukiDifferential v.1).continuous.isOpen_support
    have hinterior :
        Function.support (suzukiDifferential v.1) ⊆
          interior (Icc (-a) a) :=
      (hopen.subset_interior_iff).2 hclosed
    simpa only [interior_Icc] using hinterior⟩

@[simp]
theorem suzukiSmoothCoreDifferential_apply
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) (x : Real) :
    (suzukiSmoothCoreDifferential ha v).1 x =
      Complex.I * SchwartzMap.derivCLM Complex Complex v.1 x := by
  rfl

/-- The differential core has zero interval mean, matching Suzuki's
`L^2_0(-a,a)` receiving space. -/
theorem setIntegral_suzukiSmoothCoreDifferential_eq_zero
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    (∫ x in Icc (-a) a, (suzukiSmoothCoreDifferential ha v).1 x) = 0 := by
  exact setIntegral_suzukiDifferential_eq_zero ha
    (suzukiSmoothCore_support_subset_Icc v)

/-- Source radius `a` becomes the exact X13/X14 project Schwartz radius
`a/(2*pi)`. -/
theorem support_suzukiProjectBase_smoothCore_subset_Icc
    {a : Real} (v : SuzukiSmoothCore a) :
    Function.support (suzukiProjectBase v.1) ⊆
      Icc (-a / suzukiTwoPi) (a / suzukiTwoPi) :=
  support_suzukiProjectBase_subset_Icc
    (suzukiSmoothCore_support_subset_Icc v)

/-- The exact X13/X14 Fourier-coordinate map, with its reflection, amplitude,
and `2*pi` scale exposed rather than hidden behind the project-base name. -/
theorem suzukiProjectBase_smoothCore_apply
    {a : Real} (v : SuzukiSmoothCore a) (x : Real) :
    suzukiProjectBase v.1 x =
      ((2 * Real.pi : Real) : Complex) *
        v.1 (-(2 * Real.pi) * x) := by
  rw [suzukiProjectBase_apply]
  rfl

/-- Unconditional X14 residual identity on the exact DF6D smooth source core,
written with Suzuki's differential rather than a raw derivative. -/
theorem guinandWeilBurnolLiteratureResidualSide_suzukiProjectBase_smoothCore
    {a : Real} (ha : 0 < a) (v : SuzukiSmoothCore a) :
    guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v.1) =
      suzukiFiniteKernelPairing suzukiScrewFunction a
        (suzukiSmoothCoreDifferential ha v).1 := by
  have hidentity := suzukiScalarKernelIdentityAt_of_support ha
    (suzukiSmoothCore_support_subset_Icc v)
  unfold SuzukiScalarKernelIdentityAt at hidentity
  exact hidentity.trans
    (suzukiFiniteKernelPairing_differential_eq_deriv
      suzukiScrewFunction a v.1).symm

/-- The precise source theorem supplied by Suzuki's equations (1.8) and (2.5).
Its left side is the source screw form on `D v`; its right side is the concrete
DF6D2 complete form on `v`, not a bounded continuous-kernel surrogate. -/
def SuzukiEquation25SourceIdentityAt (a : Real) : Prop :=
  ∀ (ha : 0 < a) (v : SuzukiSmoothCore a),
    suzukiFiniteKernelPairing suzukiScrewFunction a
        (suzukiSmoothCoreDifferential ha v).1 =
      suzukiProjectNormalizedCompleteCoreForm v

/-- Compatibility name emphasizing the screw-form side of the borrowed source
identity. -/
abbrev SuzukiScrewCompleteFormIdentityAt :=
  SuzukiEquation25SourceIdentityAt

/-- The project-facing statement of DF6D3 on the smooth source core. -/
def SuzukiProjectCompleteFormNormalizationAt (a : Real) : Prop :=
  ∀ (ha : 0 < a) (v : SuzukiSmoothCore a),
    guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v.1) =
      suzukiProjectNormalizedCompleteCoreForm v

/-- The genuine source identity implies the project-facing normalization via
the already checked X14 scale and residual theorem. -/
theorem suzukiProjectCompleteFormNormalizationAt_of_screwIdentity
    {a : Real} (hsource : SuzukiEquation25SourceIdentityAt a) :
    SuzukiProjectCompleteFormNormalizationAt a := by
  intro ha v
  exact
    (guinandWeilBurnolLiteratureResidualSide_suzukiProjectBase_smoothCore
      ha v).trans (hsource ha v)

/-- Conversely, the project-facing theorem contains no more and no less than
the explicit source identity because X14 already fixes the project scale. -/
theorem suzukiScrewCompleteFormIdentityAt_of_projectNormalization
    {a : Real} (hproject : SuzukiProjectCompleteFormNormalizationAt a) :
    SuzukiScrewCompleteFormIdentityAt a := by
  intro ha v
  exact
    (guinandWeilBurnolLiteratureResidualSide_suzukiProjectBase_smoothCore
      ha v).symm.trans (hproject ha v)

/-- FT2's raw Gamma reconciliation on the exact smooth core.  Once the
published equation-(2.5) identity is supplied, the project Gamma block after
removing its separate scalar is exactly local energy minus pole minus the
positive-sign smooth `r''` operator, plus the visible `log 2` correction. -/
theorem suzukiProjectRawGammaCoreForm_eq_local_sub_pole_sub_rSecond
    {a : Real} (hsource : SuzukiEquation25SourceIdentityAt a)
    (ha : 0 < a) (v : SuzukiSmoothCore a) :
    suzukiProjectRawGammaCoreForm v =
      suzukiSingularLocalForm a v.1 -
        guinandWeilBurnolLiteraturePoleSide (suzukiProjectBase v.1) +
        Real.log 2 * ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
        suzukiL2BoundedOperatorDiagonal
          (suzukiRSecondGlobalL2Operator a)
          (suzukiSmoothCoreToL2 v) := by
  have hproject :=
    suzukiProjectCompleteFormNormalizationAt_of_screwIdentity hsource ha v
  have hprime :=
    guinandWeilLiteraturePrimeSide_suzukiProjectBase_eq_translation ha v
  have hcomplete :=
    suzukiProjectNormalizedCompleteCoreForm_eq_groupedComponents v
  have hscalar := suzukiProjectCompleteScalar_sub_rawConstant
  unfold guinandWeilBurnolLiteratureResidualSide at hproject
  rw [hprime, hcomplete] at hproject
  unfold suzukiProjectRawGammaCoreForm
  rw [suzukiRSecondSourceRemainderDiagonal_eq_neg_global] at hproject
  rw [← hscalar]
  linear_combination hproject

/-- The frozen-endpoint DF6D3 normalization target.  The cutoff, parity, and
complete far-space conventions are the constants above; they do not alter the
underlying full form. -/
def SuzukiDF6D3ProjectNormalization : Prop :=
  SuzukiProjectCompleteFormNormalizationAt suzukiProjectAStar

theorem suzukiDF6D3ProjectNormalization_of_equation25
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar) :
    SuzukiDF6D3ProjectNormalization :=
  suzukiProjectCompleteFormNormalizationAt_of_screwIdentity hsource

/-- The frozen-endpoint project residual with the complete source split fully
displayed.  The only source input is the precisely named published
equation-(2.5) identity; the scale, endpoint, prime cutoff, signs, and smooth
remainder normalization are all discharged by checked bridges above. -/
theorem guinandWeilBurnolLiteratureResidualSide_aStar_eq_completeComponents
    (hsource : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (v : SuzukiSmoothCore suzukiProjectAStar) :
    guinandWeilBurnolLiteratureResidualSide (suzukiProjectBase v.1) =
      suzukiSingularLocalForm suzukiProjectAStar v.1 -
        (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant) *
          ‖suzukiSmoothCoreToL2 v‖ ^ 2 -
        (Real.log 2 / Real.sqrt 2) *
          suzukiL2SymmetricTranslationDiagonal (Real.log 2)
            (suzukiSmoothCoreToL2 v) +
        suzukiL2BoundedOperatorDiagonal
          (suzukiRSecondSourceRemainderOperator suzukiProjectAStar)
          (suzukiSmoothCoreToL2 v) := by
  exact (suzukiProjectCompleteFormNormalizationAt_of_screwIdentity hsource
    suzukiProjectAStar_pos v).trans
      (suzukiProjectNormalizedCompleteCoreForm_at_aStar_eq_components v)

end

end M100
end Experiments
end RiemannHypothesisProject
