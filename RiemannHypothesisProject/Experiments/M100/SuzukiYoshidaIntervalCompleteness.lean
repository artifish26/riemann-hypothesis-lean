import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEndpointModes
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Interval Fourier completeness for the Suzuki--Yoshida endpoint modes

This module transports Mathlib's interval Fourier completeness theorem to the
project's global `L²(Real, Complex)` convention.  The functions are supported
in `[-r,r]`, so completeness of the interval exponentials becomes density in
the corresponding closed supported subspace of the global `L²` space.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open scoped ENNReal InnerProductSpace

/-- The linear subspace of global `L²` classes supported in `[-r,r]`. -/
def suzukiL2SupportedSubmodule (r : Real) : Submodule Complex SuzukiL2 where
  carrier := {v | suzukiL2SupportedAt r v}
  zero_mem' := by
    show suzukiL2SupportedAt r 0
    filter_upwards [] with x
    simp
  add_mem' := by
    intro u v hu hv
    show suzukiL2SupportedAt r (u + v)
    filter_upwards [hu, hv, MeasureTheory.Lp.coeFn_add u v] with
      x hux hvx huv
    intro hx
    rw [huv, Pi.add_apply, hux hx, hvx hx]
    simp
  smul_mem' := by
    intro c v hv
    show suzukiL2SupportedAt r (c • v)
    filter_upwards [hv, MeasureTheory.Lp.coeFn_smul c v] with x hvx hcv
    intro hx
    rw [hcv, Pi.smul_apply, hvx hx]
    simp

/-- The supported subspace is closed in global `L²`. -/
theorem isClosed_suzukiL2SupportedSubmodule (r : Real) :
    IsClosed (suzukiL2SupportedSubmodule r : Set SuzukiL2) :=
  isClosed_suzukiL2SupportedAt r

/-- Every truncated endpoint exponential belongs to the supported subspace. -/
theorem suzukiYoshidaExponentialL2_mem_supportedSubmodule
    {r : Real} (hr : 0 < r) (n : Int) :
    suzukiYoshidaExponentialL2 r hr n ∈ suzukiL2SupportedSubmodule r := by
  filter_upwards [suzukiYoshidaExponentialL2_coeFn hr n] with x hx
  intro hxOutside
  rw [hx]
  simp [suzukiYoshidaExponentialFunction, hxOutside]

/-- Every even Yoshida mode is supported in the defining interval. -/
theorem suzukiYoshidaEvenL2_mem_supportedSubmodule
    {r : Real} (hr : 0 < r) (n : Nat) :
    suzukiYoshidaEvenL2 r hr n ∈ suzukiL2SupportedSubmodule r := by
  unfold suzukiYoshidaEvenL2
  split_ifs
  · exact suzukiYoshidaExponentialL2_mem_supportedSubmodule hr 0
  · exact (suzukiL2SupportedSubmodule r).smul_mem _
      ((suzukiL2SupportedSubmodule r).add_mem
        (suzukiYoshidaExponentialL2_mem_supportedSubmodule hr _)
        (suzukiYoshidaExponentialL2_mem_supportedSubmodule hr _))

/-- Every odd Yoshida mode is supported in the defining interval. -/
theorem suzukiYoshidaOddL2_mem_supportedSubmodule
    {r : Real} (hr : 0 < r) (n : Nat) :
    suzukiYoshidaOddL2 r hr n ∈ suzukiL2SupportedSubmodule r := by
  unfold suzukiYoshidaOddL2
  exact (suzukiL2SupportedSubmodule r).smul_mem _
    ((suzukiL2SupportedSubmodule r).sub_mem
      (suzukiYoshidaExponentialL2_mem_supportedSubmodule hr _)
      (suzukiYoshidaExponentialL2_mem_supportedSubmodule hr _))

/-- The interval Fourier coefficient is the normalized global `L²` pairing
with the corresponding truncated exponential. -/
theorem fourierCoeffOn_eq_smul_inner_suzukiYoshidaExponentialL2
    {r : Real} (hr : 0 < r) (v : SuzukiL2) (n : Int) :
    fourierCoeffOn (by linarith : -r < r)
        (fun x : Real => v x) n =
      ((Real.sqrt (2 * r))⁻¹ : Complex) •
        inner Complex (suzukiYoshidaExponentialL2 r hr n) v := by
  rw [fourierCoeffOn_eq_integral, MeasureTheory.L2.inner_def]
  have hmode := suzukiYoshidaExponentialL2_coeFn hr n
  have hinner :
      (fun x : Real =>
        inner Complex
          ((suzukiYoshidaExponentialL2 r hr n : SuzukiL2) x) (v x)) =ᵐ[volume]
        fun x =>
          inner Complex (suzukiYoshidaExponentialFunction r n x) (v x) := by
    filter_upwards [hmode] with x hx
    rw [hx]
  rw [integral_congr_ae hinner]
  simp only [RCLike.inner_apply, smul_eq_mul]
  let s : Complex := ((Real.sqrt (2 * r))⁻¹ : Complex)
  have hpoint :
      (fun x : Real =>
        (v x) * (starRingEnd Complex)
          (suzukiYoshidaExponentialFunction r n x)) =
        Set.indicator (Set.Icc (-r) r)
          (fun x =>
            s * (fourier (-n) (x : AddCircle (r - -r)) * v x)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-r) r
    · rw [Set.indicator_of_mem hx]
      simp only [suzukiYoshidaExponentialFunction,
        Set.indicator_of_mem hx, map_mul, map_inv₀,
        Complex.conj_ofReal, s]
      have hfreq :
          (starRingEnd Complex)
              (Complex.exp
                (Complex.I *
                  ((n : Complex) * (Real.pi : Complex) / (r : Complex)) *
                    (x : Complex))) =
            fourier (-n) (x : AddCircle (r - -r)) := by
        rw [← Complex.exp_conj, fourier_coe_apply]
        congr 1
        simp only [map_mul, map_div₀, Complex.conj_I,
          map_intCast, Complex.conj_ofReal, neg_mul]
        field_simp [hr.ne']
        push_cast
        ring
      rw [hfreq]
      ring
    · simp [suzukiYoshidaExponentialFunction, hx]
  rw [hpoint, MeasureTheory.integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r)]
  rw [intervalIntegral.integral_const_mul]
  have hsqrt : Real.sqrt (2 * r) ≠ 0 := by positivity
  have hsquare : Real.sqrt (2 * r) ^ 2 = 2 * r :=
    Real.sq_sqrt (by positivity)
  have hsqrtC : ((Real.sqrt (2 * r) : Real) : Complex) ≠ 0 := by
    exact_mod_cast hsqrt
  have hsquareC :
      (((Real.sqrt (2 * r) : Real) : Complex) ^ 2) =
        ((2 * r : Real) : Complex) := by
    exact_mod_cast hsquare
  have hsquareC' :
      (((Real.sqrt (2 * r) : Real) : Complex) ^ 2) =
        2 * (r : Complex) := by
    rw [hsquareC]
    push_cast
    ring
  dsimp [s]
  have hscalar :
      (((1 / (r - -r)) : Real) : Complex) =
        ((Real.sqrt (2 * r) : Complex)⁻¹) *
          ((Real.sqrt (2 * r) : Complex)⁻¹) := by
    rw [show r - -r = 2 * r by ring]
    push_cast
    rw [← hsquareC']
    field_simp [hsqrtC]
  rw [hscalar]
  ring

/-- Interval Fourier uniqueness in the supported global `L²` model. -/
theorem eq_zero_of_supportedAt_of_forall_inner_exponential_eq_zero
    {r : Real} (hr : 0 < r) (v : SuzukiL2)
    (hv : suzukiL2SupportedAt r v)
    (horth : ∀ n : Int,
      inner Complex (suzukiYoshidaExponentialL2 r hr n) v = 0) :
    v = 0 := by
  have hab : -r < r := by linarith
  have hcoeff : ∀ n : Int,
      fourierCoeffOn hab (fun x : Real => v x) n = 0 := by
    intro n
    rw [fourierCoeffOn_eq_smul_inner_suzukiYoshidaExponentialL2 hr,
      horth n, smul_zero]
  have hL2 :
      MemLp (fun x : Real => v x) 2
        ((volume : Measure Real).restrict (Set.Ioc (-r) r)) :=
    (MeasureTheory.Lp.memLp v).restrict _
  have hparseval :=
    hasSum_sq_fourierCoeffOn hab hL2
  have hsumzero :
      HasSum (fun _ : Int => (0 : Real))
        ((r - -r)⁻¹ • ∫ x in -r..r, ‖v x‖ ^ 2) := by
    simpa only [hcoeff, norm_zero, zero_pow (by norm_num : (2 : Nat) ≠ 0)] using
      hparseval
  have hrhs :
      (r - -r)⁻¹ • ∫ x in -r..r, ‖v x‖ ^ 2 = 0 :=
    hsumzero.unique hasSum_zero
  have hinv : (r - -r)⁻¹ ≠ 0 := by
    exact inv_ne_zero (by linarith)
  have hint : (∫ x in -r..r, ‖v x‖ ^ 2) = 0 := by
    rw [smul_eq_mul] at hrhs
    exact (mul_eq_zero.mp hrhs).resolve_left hinv
  have hintIntegrable :
      IntervalIntegrable (fun x : Real => ‖v x‖ ^ 2) volume (-r) r := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact hL2.integrable_norm_pow (by norm_num)
  have hnormzero :
      (fun x : Real => ‖v x‖ ^ 2) =ᵐ[
        (volume : Measure Real).restrict (Set.Ioc (-r) r)] 0 := by
    exact
      (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hab.le
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        hintIntegrable).1 hint
  have hvzeroIoc :
      (fun x : Real => v x) =ᵐ[
        (volume : Measure Real).restrict (Set.Ioc (-r) r)] 0 := by
    filter_upwards [hnormzero] with x hx
    simpa only [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] using hx
  have hvzeroIcc :
      (fun x : Real => v x) =ᵐ[
        (volume : Measure Real).restrict (Set.Icc (-r) r)] 0 := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact hvzeroIoc
  have hvzeroIcc' :
      ∀ᵐ x ∂(volume : Measure Real).restrict (Set.Icc (-r) r),
        v x = 0 := hvzeroIcc
  rw [ae_restrict_iff' measurableSet_Icc] at hvzeroIcc'
  apply MeasureTheory.Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hv, hvzeroIcc'] with x hxOutside hxInside
  by_cases hx : x ∈ Set.Icc (-r) r
  · exact hxInside hx
  · exact hxOutside hx

/-- Even and odd reflection eigenvectors are orthogonal. -/
theorem inner_eq_zero_of_suzukiL2Even_of_suzukiL2Odd
    {u v : SuzukiL2} (hu : SuzukiL2Even u) (hv : SuzukiL2Odd v) :
    inner Complex u v = 0 := by
  have hreflect := suzukiL2Reflection.inner_map_map u v
  rw [hu, hv, inner_neg_right] at hreflect
  exact CharZero.neg_eq_self_iff.mp hreflect

/-- Completeness of the even Yoshida family inside the supported even
sector. -/
theorem eq_zero_of_supportedAt_of_even_of_forall_inner_even_eq_zero
    {r : Real} (hr : 0 < r) (v : SuzukiL2)
    (hsupport : suzukiL2SupportedAt r v)
    (heven : SuzukiL2Even v)
    (horth : ∀ n : Nat,
      inner Complex (suzukiYoshidaEvenL2 r hr n) v = 0) :
    v = 0 := by
  have hsymm : ∀ n : Int,
      inner Complex (suzukiYoshidaExponentialL2 r hr (-n)) v =
        inner Complex (suzukiYoshidaExponentialL2 r hr n) v := by
    intro n
    have hreflect :=
      suzukiL2Reflection.inner_map_map
        (suzukiYoshidaExponentialL2 r hr n) v
    rw [suzukiL2Reflection_exponential, heven] at hreflect
    exact hreflect
  have hpos : ∀ k : Nat, 0 < k →
      inner Complex (suzukiYoshidaExponentialL2 r hr (k : Int)) v = 0 := by
    intro k hk
    have hk0 : k ≠ 0 := Nat.ne_of_gt hk
    have heq := horth k
    simp only [suzukiYoshidaEvenL2, dif_neg hk0,
      inner_smul_left, inner_add_left] at heq
    rw [hsymm (k : Int)] at heq
    have hscalar :
        (starRingEnd Complex) (((Real.sqrt 2)⁻¹ : Complex)) ≠ 0 := by
      apply star_ne_zero.mpr
      exact inv_ne_zero
        (Complex.ofReal_ne_zero.mpr
          (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)).ne')
    have hsum := (mul_eq_zero.mp heq).resolve_left hscalar
    linear_combination (2 : Complex)⁻¹ * hsum
  apply eq_zero_of_supportedAt_of_forall_inner_exponential_eq_zero
    hr v hsupport
  intro n
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          simpa [suzukiYoshidaEvenL2] using horth 0
      | succ k =>
          exact hpos (k + 1) (by omega)
  | negSucc k =>
      rw [show Int.negSucc k = -((k + 1 : Nat) : Int) by omega,
        hsymm]
      exact hpos (k + 1) (by omega)

/-- Completeness of the positive odd Yoshida family inside the supported odd
sector. -/
theorem eq_zero_of_supportedAt_of_odd_of_forall_inner_odd_eq_zero
    {r : Real} (hr : 0 < r) (v : SuzukiL2)
    (hsupport : suzukiL2SupportedAt r v)
    (hodd : SuzukiL2Odd v)
    (horth : ∀ n : Nat, 0 < n →
      inner Complex (suzukiYoshidaOddL2 r hr n) v = 0) :
    v = 0 := by
  have hantisymm : ∀ n : Int,
      inner Complex (suzukiYoshidaExponentialL2 r hr (-n)) v =
        -inner Complex (suzukiYoshidaExponentialL2 r hr n) v := by
    intro n
    have hreflect :=
      suzukiL2Reflection.inner_map_map
        (suzukiYoshidaExponentialL2 r hr n) v
    rw [suzukiL2Reflection_exponential, hodd, inner_neg_right] at hreflect
    linear_combination -hreflect
  have hpos : ∀ k : Nat, 0 < k →
      inner Complex (suzukiYoshidaExponentialL2 r hr (k : Int)) v = 0 := by
    intro k hk
    have heq := horth k hk
    simp only [suzukiYoshidaOddL2, inner_smul_left,
      inner_sub_left] at heq
    rw [hantisymm (k : Int)] at heq
    have hscalar :
        (starRingEnd Complex)
            (((Complex.I * (Real.sqrt 2 : Complex))⁻¹ : Complex)) ≠ 0 := by
      apply star_ne_zero.mpr
      exact inv_ne_zero
        (mul_ne_zero Complex.I_ne_zero
          (Complex.ofReal_ne_zero.mpr
            (Real.sqrt_pos.2 (by norm_num : (0 : Real) < 2)).ne'))
    have hsum := (mul_eq_zero.mp heq).resolve_left hscalar
    linear_combination (2 : Complex)⁻¹ * hsum
  apply eq_zero_of_supportedAt_of_forall_inner_exponential_eq_zero
    hr v hsupport
  intro n
  cases n with
  | ofNat k =>
      cases k with
      | zero =>
          have hreflection :=
            suzukiL2Reflection.inner_map_map
              (suzukiYoshidaExponentialL2 r hr 0) v
          rw [suzukiL2Reflection_exponential, hodd,
            neg_zero, inner_neg_right] at hreflection
          exact CharZero.neg_eq_self_iff.mp hreflection
      | succ k =>
          exact hpos (k + 1) (by omega)
  | negSucc k =>
      rw [show Int.negSucc k = -((k + 1 : Nat) : Int) by omega,
        hantisymm]
      rw [hpos (k + 1) (by omega), neg_zero]

/-- The normalized truncated exponentials have dense span in the closed
supported global `L²` subspace. -/
theorem topologicalClosure_span_suzukiYoshidaExponentialL2_eq_supported :
    (Submodule.span Complex
      (Set.range fun n : Int =>
        suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos n)).topologicalClosure =
      suzukiL2SupportedSubmodule suzukiProjectAStar := by
  let S : Submodule Complex SuzukiL2 :=
    Submodule.span Complex
      (Set.range fun n : Int =>
        suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos n)
  let P : Submodule Complex SuzukiL2 :=
    suzukiL2SupportedSubmodule suzukiProjectAStar
  have hSP : S ≤ P := by
    dsimp [S, P]
    rw [Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    exact
      suzukiYoshidaExponentialL2_mem_supportedSubmodule
        suzukiProjectAStar_pos n
  have hclosureP : S.topologicalClosure ≤ P :=
    S.topologicalClosure_minimal hSP
      (by
        simpa only [P] using
          isClosed_suzukiL2SupportedSubmodule suzukiProjectAStar)
  apply le_antisymm hclosureP
  intro v hv
  let w : SuzukiL2 := v - S.topologicalClosure.starProjection v
  have hwOrth : w ∈ S.topologicalClosureᗮ := by
    exact S.topologicalClosure.sub_starProjection_mem_orthogonal v
  have hprojectionSupported :
      S.topologicalClosure.starProjection v ∈ P :=
    hclosureP (S.topologicalClosure.starProjection_apply_mem v)
  have hwSupported : w ∈ P :=
    P.sub_mem hv hprojectionSupported
  have hwInner : ∀ n : Int,
      inner Complex
        (suzukiYoshidaExponentialL2 suzukiProjectAStar
          suzukiProjectAStar_pos n) w = 0 := by
    intro n
    exact Submodule.inner_right_of_mem_orthogonal
      (S.le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self n))) hwOrth
  have hwZero : w = 0 :=
    eq_zero_of_supportedAt_of_forall_inner_exponential_eq_zero
      suzukiProjectAStar_pos w hwSupported hwInner
  have hvProjection :
      v = S.topologicalClosure.starProjection v := by
    exact sub_eq_zero.mp hwZero
  rw [hvProjection]
  exact S.topologicalClosure.starProjection_apply_mem v

end

end RiemannHypothesisProject.Experiments.M100
