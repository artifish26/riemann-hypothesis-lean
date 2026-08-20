import RiemannHypothesisProject.Experiments.M100.SuzukiClosedFormNesting
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# M100-DF6D1 concrete Suzuki L2 support geometry

This experimental module instantiates the DF6C global-restriction convention
in `L^2(Real, Complex)`.  Radius restriction is almost-everywhere support in a
closed symmetric interval, and zero extension is literal inclusion of the
same global `L^2` class.

Only elementary Hilbert-space geometry lives here.  No Suzuki source form,
closed form domain, normalization, or endpoint certificate is assumed.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

open Set MeasureTheory

/-- The concrete ambient Hilbert space frozen by DF6D0. -/
abbrev SuzukiL2 := MeasureTheory.Lp Complex 2 (volume : Measure Real)

/-- Almost-everywhere support in the closed symmetric interval `[-r, r]`.
This predicate is stated on the `L^2` class itself, so it is independent of a
choice of pointwise representative. -/
def suzukiL2SupportedAt (r : Real) (v : SuzukiL2) : Prop :=
  ∀ᵐ x ∂(volume : Measure Real), x ∉ Set.Icc (-r) r → v x = 0

/-- The radius-`r` support restriction inside the single global `L^2` space. -/
abbrev SuzukiL2SupportedSpace (r : Real) :=
  SuzukiClosedRestrictionDomain (Set.univ : Set SuzukiL2)
    suzukiL2SupportedAt r

private theorem suzuki_symmetricIcc_mono {a b : Real} (hab : a ≤ b) :
    Set.Icc (-a) a ⊆ Set.Icc (-b) b := by
  intro x hx
  exact ⟨(neg_le_neg hab).trans hx.1, hx.2.trans hab⟩

/-- Almost-everywhere support widens monotonically with the radius. -/
theorem suzukiL2SupportedAt_mono {a b : Real} (hab : a ≤ b)
    {v : SuzukiL2} (hv : suzukiL2SupportedAt a v) :
    suzukiL2SupportedAt b v := by
  filter_upwards [hv] with x hx
  intro hxb
  apply hx
  intro hxa
  exact hxb (suzuki_symmetricIcc_mono hab hxa)

/-- Zero extension between support radii.  Its ambient `L^2` class is
definitionally unchanged. -/
def suzukiL2ZeroExtension {a b : Real} (hab : a ≤ b) :
    SuzukiL2SupportedSpace a → SuzukiL2SupportedSpace b :=
  suzukiClosedRestrictionZeroExtension
    (fun _ hv ↦ suzukiL2SupportedAt_mono hab hv)

@[simp]
theorem suzukiL2ZeroExtension_apply {a b : Real} (hab : a ≤ b)
    (v : SuzukiL2SupportedSpace a) :
    (suzukiL2ZeroExtension hab v).1 = v.1 :=
  rfl

/-- Concrete zero extension is injective. -/
theorem suzukiL2ZeroExtension_injective {a b : Real} (hab : a ≤ b) :
    Function.Injective (suzukiL2ZeroExtension hab) :=
  suzukiClosedRestrictionZeroExtension_injective
    (fun _ hv ↦ suzukiL2SupportedAt_mono hab hv)

/-- Concrete zero extension is an ambient `L^2` isometry. -/
@[simp]
theorem suzukiL2ZeroExtension_norm {a b : Real} (hab : a ≤ b)
    (v : SuzukiL2SupportedSpace a) :
    ‖(suzukiL2ZeroExtension hab v).1‖ = ‖v.1‖ :=
  rfl

/-- Vanishing on the outer annulus between two symmetric support intervals. -/
def suzukiL2OuterVanishing (a b : Real) (v : SuzukiL2) : Prop :=
  ∀ᵐ x ∂(volume : Measure Real),
    x ∈ Set.Icc (-b) b \ Set.Icc (-a) a → v x = 0

private theorem suzukiL2OuterVanishing_of_supportedAt
    {a b : Real} {v : SuzukiL2} (hv : suzukiL2SupportedAt a v) :
    suzukiL2OuterVanishing a b v := by
  filter_upwards [hv] with x hx
  intro houter
  exact hx houter.2

private theorem suzukiL2SupportedAt_of_large_of_outer
    {a b : Real} {v : SuzukiL2}
    (hlarge : suzukiL2SupportedAt b v)
    (houter : suzukiL2OuterVanishing a b v) :
    suzukiL2SupportedAt a v := by
  filter_upwards [hlarge, houter] with x hxLarge hxOuter
  intro hxSmall
  by_cases hx : x ∈ Set.Icc (-b) b
  · exact hxOuter ⟨hx, hxSmall⟩
  · exact hxLarge hx

/-- Exact image of zero extension: the large-radius classes that vanish on
the outer annulus are precisely the unchanged small-radius classes. -/
theorem suzukiL2ZeroExtension_range {a b : Real} (hab : a ≤ b) :
    Set.range (suzukiL2ZeroExtension hab) =
      {w : SuzukiL2SupportedSpace b |
        suzukiL2OuterVanishing a b w.1} := by
  exact suzukiClosedRestrictionZeroExtension_range
    (outerVanishing := suzukiL2OuterVanishing a b)
    (fun _ hv ↦ suzukiL2SupportedAt_mono hab hv)
    (fun _ _ hv ↦ suzukiL2OuterVanishing_of_supportedAt hv)
    (fun _ _ hlarge houter ↦
      suzukiL2SupportedAt_of_large_of_outer hlarge houter)

/-- A pointwise support certificate descends to the representative-independent
almost-everywhere support predicate on the associated `L^2` class. -/
theorem suzukiL2SupportedAt_toLp_of_functionSupport
    {r : Real} {f : Real → Complex}
    (hf : MeasureTheory.MemLp f 2 (volume : Measure Real))
    (hsupport : Function.support f ⊆ Set.Icc (-r) r) :
    suzukiL2SupportedAt r (hf.toLp f) := by
  filter_upwards [hf.coeFn_toLp] with x hx
  intro hxOutside
  rw [hx]
  by_contra hfx
  exact hxOutside (hsupport hfx)

/-- Reflection of an `L^2` class through the origin. -/
def suzukiL2Reflection : SuzukiL2 →ₗᵢ[Complex] SuzukiL2 :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ Complex Neg.neg
    (Measure.measurePreserving_neg (volume : Measure Real))

/-- Reflection has the expected representative formula almost everywhere. -/
theorem suzukiL2Reflection_coeFn (v : SuzukiL2) :
    suzukiL2Reflection v =ᵐ[volume] fun x : Real ↦ v (-x) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving v
    (Measure.measurePreserving_neg (volume : Measure Real))

/-- Reflection is an involution on the ambient `L^2` space. -/
@[simp]
theorem suzukiL2Reflection_involution (v : SuzukiL2) :
    suzukiL2Reflection (suzukiL2Reflection v) = v := by
  change MeasureTheory.Lp.compMeasurePreserving Neg.neg
      (Measure.measurePreserving_neg (volume : Measure Real))
      (MeasureTheory.Lp.compMeasurePreserving Neg.neg
        (Measure.measurePreserving_neg (volume : Measure Real)) v) = v
  rw [← MeasureTheory.Lp.compMeasurePreserving_comp_apply v
    (Measure.measurePreserving_neg (volume : Measure Real))
    (Measure.measurePreserving_neg (volume : Measure Real))]
  simp

/-- Even and odd parity in the concrete ambient Hilbert space. -/
def SuzukiL2Even (v : SuzukiL2) : Prop := suzukiL2Reflection v = v

def SuzukiL2Odd (v : SuzukiL2) : Prop := suzukiL2Reflection v = -v

/-- Radius-restricted even and odd subspaces. -/
abbrev SuzukiL2EvenSpace (r : Real) :=
  {v : SuzukiL2SupportedSpace r // SuzukiL2Even v.1}

abbrev SuzukiL2OddSpace (r : Real) :=
  {v : SuzukiL2SupportedSpace r // SuzukiL2Odd v.1}

/-- Unchanged-representative zero extension preserves even parity exactly. -/
theorem suzukiL2ZeroExtension_preserves_even {a b : Real} (hab : a ≤ b)
    (v : SuzukiL2SupportedSpace a) :
    SuzukiL2Even (suzukiL2ZeroExtension hab v).1 ↔ SuzukiL2Even v.1 :=
  Iff.rfl

/-- Unchanged-representative zero extension preserves odd parity exactly. -/
theorem suzukiL2ZeroExtension_preserves_odd {a b : Real} (hab : a ≤ b)
    (v : SuzukiL2SupportedSpace a) :
    SuzukiL2Odd (suzukiL2ZeroExtension hab v).1 ↔ SuzukiL2Odd v.1 :=
  Iff.rfl

/-- Zero extension restricted to the even parity subspace. -/
def suzukiL2EvenZeroExtension {a b : Real} (hab : a ≤ b) :
    SuzukiL2EvenSpace a → SuzukiL2EvenSpace b :=
  fun v ↦ ⟨suzukiL2ZeroExtension hab v.1,
    (suzukiL2ZeroExtension_preserves_even hab v.1).2 v.2⟩

/-- Zero extension restricted to the odd parity subspace. -/
def suzukiL2OddZeroExtension {a b : Real} (hab : a ≤ b) :
    SuzukiL2OddSpace a → SuzukiL2OddSpace b :=
  fun v ↦ ⟨suzukiL2ZeroExtension hab v.1,
    (suzukiL2ZeroExtension_preserves_odd hab v.1).2 v.2⟩

/-- The `L^2` class of the indicator of `[-r, r]`. -/
def suzukiL2IntervalIndicator (r : Real) : SuzukiL2 :=
  MeasureTheory.indicatorConstLp 2
    (measurableSet_Icc : MeasurableSet (Set.Icc (-r) r))
    (by exact (measure_Icc_lt_top :
      volume (Set.Icc (-r) r) < ⊤).ne)
    (1 : Complex)

/-- The bounded interval-mean functional, represented as an `L^2` pairing. -/
def suzukiL2IntervalMean (r : Real) (v : SuzukiL2) : Complex :=
  @inner Complex SuzukiL2 _ (suzukiL2IntervalIndicator r) v

/-- The Hilbert-space mean agrees with the interval integral of any `L^2`
representative. -/
theorem suzukiL2IntervalMean_eq_setIntegral (r : Real) (v : SuzukiL2) :
    suzukiL2IntervalMean r v =
      ∫ x in Set.Icc (-r) r, v x ∂(volume : Measure Real) := by
  exact MeasureTheory.L2.inner_indicatorConstLp_one measurableSet_Icc
    (by exact (measure_Icc_lt_top :
      volume (Set.Icc (-r) r) < ⊤).ne) v

private theorem suzukiL2_setIntegral_eq_of_supportedAt
    {a b : Real} (hab : a ≤ b) {v : SuzukiL2}
    (hv : suzukiL2SupportedAt a v) :
    (∫ x in Set.Icc (-b) b, v x ∂(volume : Measure Real)) =
      ∫ x in Set.Icc (-a) a, v x ∂(volume : Measure Real) := by
  rw [← MeasureTheory.integral_indicator measurableSet_Icc,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hv] with x hx
  by_cases hxa : x ∈ Set.Icc (-a) a
  · have hxb : x ∈ Set.Icc (-b) b := suzuki_symmetricIcc_mono hab hxa
    simp [Set.indicator, hxa, hxb]
  · by_cases hxb : x ∈ Set.Icc (-b) b
    · simp [Set.indicator, hxa, hxb, hx hxa]
    · simp [Set.indicator, hxa, hxb]

/-- For a class supported in the smaller interval, enlarging the integration
interval does not change its mean. -/
theorem suzukiL2IntervalMean_eq_of_supportedAt
    {a b : Real} (hab : a ≤ b) {v : SuzukiL2}
    (hv : suzukiL2SupportedAt a v) :
    suzukiL2IntervalMean b v = suzukiL2IntervalMean a v := by
  rw [suzukiL2IntervalMean_eq_setIntegral,
    suzukiL2IntervalMean_eq_setIntegral]
  exact suzukiL2_setIntegral_eq_of_supportedAt hab hv

/-- Radius-restricted zero-mean subspace. -/
abbrev SuzukiL2ZeroMeanSpace (r : Real) :=
  {v : SuzukiL2SupportedSpace r // suzukiL2IntervalMean r v.1 = 0}

/-- Zero extension preserves the zero-mean constraint even though the
defining interval grows with the support radius. -/
theorem suzukiL2ZeroExtension_preserves_zeroMean
    {a b : Real} (hab : a ≤ b) (v : SuzukiL2SupportedSpace a) :
    suzukiL2IntervalMean b (suzukiL2ZeroExtension hab v).1 = 0 ↔
      suzukiL2IntervalMean a v.1 = 0 := by
  rw [suzukiL2ZeroExtension_apply]
  rw [suzukiL2IntervalMean_eq_of_supportedAt hab v.2.2]

/-- Zero extension restricted to the zero-mean subspace. -/
def suzukiL2ZeroMeanZeroExtension {a b : Real} (hab : a ≤ b) :
    SuzukiL2ZeroMeanSpace a → SuzukiL2ZeroMeanSpace b :=
  fun v ↦ ⟨suzukiL2ZeroExtension hab v.1,
    (suzukiL2ZeroExtension_preserves_zeroMean hab v.1).2 v.2⟩

end

end M100
end Experiments
end RiemannHypothesisProject
