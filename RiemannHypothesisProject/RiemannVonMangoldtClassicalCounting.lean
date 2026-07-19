import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import RiemannHypothesisProject.ComplexAnalyticReflection
import RiemannHypothesisProject.ZetaSetup
import RiemannHypothesisProject.ZetaConjugation
import RiemannHypothesisProject.TruncatedRiemannVonMangoldtFormulaTarget

open Filter

open scoped ComplexConjugate

/-!
# Classical height-counting adapters

Classical Riemann-von Mangoldt estimates are usually stated as height-counting
theorems for zeroes with `0 < Im rho <= T`.  The tail pipeline in this project
counts actual zeta zeroes in closed balls.  This file supplies the checked
adapter between those statement shapes.

No Riemann-von Mangoldt estimate is proved here.  The structures below package
the theorem shape future analytic work should prove, and Lean checks that such
data feed the existing closed-ball height-counting targets.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

/-- A zeta zero in the `n`th closed ball has imaginary part bounded by `n`. -/
theorem closedBallZero_im_abs_le
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZero.zetaZeroSubtypeFinset n) :
    |Complex.im (rho : Complex)| <= (n : Real) := by
  have hwindow : (rho : Complex) ∈ closedBallZero.window n :=
    (closedBallZero.mem_zetaZeroSubtypeFinset_iff n).mp hrho
  have hdist : dist (rho : Complex) 0 <= (n : Real) :=
    (mem_closedBallZero_iff n).mp hwindow
  have him_norm : |Complex.im (rho : Complex)| <= ‖(rho : Complex)‖ :=
    Complex.abs_im_le_norm (rho : Complex)
  have hnorm : ‖(rho : Complex)‖ <= (n : Real) := by
    simpa [dist_eq_norm] using hdist
  exact him_norm.trans hnorm

/-- Positive-ordinate members of the closed ball satisfy `0 < Im rho <= n`. -/
theorem closedBallZeroPositiveOrdinate_im_bounds
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZeroPositiveOrdinateFinset n) :
    0 < Complex.im (rho : Complex) ∧
      Complex.im (rho : Complex) <= (n : Real) := by
  have hmem := (mem_closedBallZeroPositiveOrdinateFinset n).mp hrho
  have him_abs := closedBallZero_im_abs_le n hmem.1
  have him_nonneg : 0 <= Complex.im (rho : Complex) := le_of_lt hmem.2
  exact ⟨hmem.2, by simpa [abs_of_nonneg him_nonneg] using him_abs⟩

/-- Negative-ordinate members of the closed ball satisfy `Im rho < 0` and `-Im rho <= n`. -/
theorem closedBallZeroNegativeOrdinate_im_bounds
    (n : Nat) {rho : ZetaZeroSubtype}
    (hrho : rho ∈ closedBallZeroNegativeOrdinateFinset n) :
    Complex.im (rho : Complex) < 0 ∧
      -Complex.im (rho : Complex) <= (n : Real) := by
  have hmem := (mem_closedBallZeroNegativeOrdinateFinset n).mp hrho
  have him_abs := closedBallZero_im_abs_le n hmem.1
  exact ⟨hmem.2, by simpa [abs_of_neg hmem.2] using him_abs⟩

/--
A positive-ordinate finite window with nonpositive height is empty. This is a
small checked endpoint of the finite-window interpretation used by published
`N(T)` sources.
-/
theorem positiveFiniteWindow_eq_empty_of_nonpos
    {s : Finset ZetaZeroSubtype} {T : Real}
    (hT : T <= 0)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T) :
    s = ∅ := by
  classical
  ext rho
  constructor
  · intro hrho
    have hbounds := hs rho hrho
    exact False.elim ((not_lt_of_ge (hbounds.2.trans hT)) hbounds.1)
  · intro hrho
    simp at hrho

/-- Positive-ordinate finite windows have cardinality zero at nonpositive height. -/
theorem positiveFiniteWindow_card_eq_zero_of_nonpos
    {s : Finset ZetaZeroSubtype} {T : Real}
    (hT : T <= 0)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T) :
    s.card = 0 := by
  rw [positiveFiniteWindow_eq_empty_of_nonpos hT hs]
  simp

/--
No zeta zero has positive imaginary ordinate at or below height `T0`.

This is the theorem-shaped small-height input needed to turn a published
zero-counting statement into the Bellotti-Wong below-domain cleanup when
`T0 = e`.
-/
def NoPositiveOrdinateZetaZerosAtOrBelow (T0 : Real) : Prop :=
  forall rho : ZetaZeroSubtype,
    0 < Complex.im (rho : Complex) ->
      Complex.im (rho : Complex) <= T0 ->
        False

/--
A lower bound for the ordinate of every positive-ordinate zeta zero.

This is often the more natural source theorem for small-height cleanup:
for example, a verified lower bound on the first positive zero ordinate implies
there are no positive-ordinate zeroes at or below any smaller threshold.
-/
def PositiveOrdinateZetaZeroLowerBound (T0 : Real) : Prop :=
  forall rho : ZetaZeroSubtype,
    0 < Complex.im (rho : Complex) ->
      T0 < Complex.im (rho : Complex)

/--
Source-shaped small-height zero-free input: no zeta zero has positive ordinate
at or below `T0`.

Unlike `NoPositiveOrdinateZetaZerosAtOrBelow`, this statement is phrased
directly over complex numbers rather than the project zero subtype. That is the
shape expected from an external analytic or verified-computation theorem.
-/
def ZetaZeroFreePositiveOrdinateBand (T0 : Real) : Prop :=
  forall s : Complex,
    IsZetaZero s ->
      0 < Complex.im s ->
        Complex.im s <= T0 ->
          False

/--
A lower bound for every positive-ordinate zeta zero implies the project's
no-positive-zero theorem at the same height.
-/
theorem noPositiveOrdinateZetaZerosAtOrBelow_of_positiveOrdinateZetaZeroLowerBound
    {T0 : Real}
    (hlower : PositiveOrdinateZetaZeroLowerBound T0) :
    NoPositiveOrdinateZetaZerosAtOrBelow T0 := by
  intro rho hpos hle
  exact (not_lt_of_ge hle) (hlower rho hpos)

/--
The subtype small-height target follows from a source-shaped zero-free
positive-ordinate band.
-/
theorem noPositiveOrdinateZetaZerosAtOrBelow_of_zetaZeroFreePositiveOrdinateBand
    {T0 : Real}
    (hfree : ZetaZeroFreePositiveOrdinateBand T0) :
    NoPositiveOrdinateZetaZerosAtOrBelow T0 := by
  intro rho hpos hle
  exact hfree (rho : Complex) rho.property hpos hle

/--
A subtype small-height target can be restated as the source-shaped zero-free
positive-ordinate band.
-/
theorem zetaZeroFreePositiveOrdinateBand_of_noPositiveOrdinateZetaZerosAtOrBelow
    {T0 : Real}
    (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0) :
    ZetaZeroFreePositiveOrdinateBand T0 := by
  intro s hz hpos hle
  exact hno ⟨s, hz⟩ hpos hle

/-- The source-shaped and subtype small-height zero-free targets are equivalent. -/
theorem zetaZeroFreePositiveOrdinateBand_iff_noPositiveOrdinateZetaZerosAtOrBelow
    {T0 : Real} :
    ZetaZeroFreePositiveOrdinateBand T0 ↔
      NoPositiveOrdinateZetaZerosAtOrBelow T0 := by
  constructor
  · exact noPositiveOrdinateZetaZerosAtOrBelow_of_zetaZeroFreePositiveOrdinateBand
  · exact zetaZeroFreePositiveOrdinateBand_of_noPositiveOrdinateZetaZerosAtOrBelow

/-- A no-positive-zero theorem is equivalent to the lower-bound formulation. -/
theorem positiveOrdinateZetaZeroLowerBound_of_noPositiveOrdinateZetaZerosAtOrBelow
    {T0 : Real}
    (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0) :
    PositiveOrdinateZetaZeroLowerBound T0 := by
  intro rho hpos
  by_contra hnot
  exact hno rho hpos (le_of_not_gt hnot)

/--
The lower-bound and no-positive-zero formulations of the small-height target
are equivalent.
-/
theorem positiveOrdinateZetaZeroLowerBound_iff_noPositiveOrdinateZetaZerosAtOrBelow
    {T0 : Real} :
    PositiveOrdinateZetaZeroLowerBound T0 ↔
      NoPositiveOrdinateZetaZerosAtOrBelow T0 := by
  constructor
  · exact noPositiveOrdinateZetaZerosAtOrBelow_of_positiveOrdinateZetaZeroLowerBound
  · exact positiveOrdinateZetaZeroLowerBound_of_noPositiveOrdinateZetaZerosAtOrBelow

/-- A source-shaped zero-free band gives the lower-bound formulation. -/
theorem positiveOrdinateZetaZeroLowerBound_of_zetaZeroFreePositiveOrdinateBand
    {T0 : Real}
    (hfree : ZetaZeroFreePositiveOrdinateBand T0) :
    PositiveOrdinateZetaZeroLowerBound T0 :=
  positiveOrdinateZetaZeroLowerBound_of_noPositiveOrdinateZetaZerosAtOrBelow
    (noPositiveOrdinateZetaZerosAtOrBelow_of_zetaZeroFreePositiveOrdinateBand
      hfree)

/--
A lower bound at height `T1` implies the no-positive-zero theorem at any
smaller height `T0`.
-/
theorem noPositiveOrdinateZetaZerosAtOrBelow_of_positiveOrdinateZetaZeroLowerBound_le
    {T0 T1 : Real}
    (hT0_le_T1 : T0 <= T1)
    (hlower : PositiveOrdinateZetaZeroLowerBound T1) :
    NoPositiveOrdinateZetaZerosAtOrBelow T0 := by
  intro rho hpos hle
  exact (not_lt_of_ge (hle.trans hT0_le_T1)) (hlower rho hpos)

/--
If there are no positive-ordinate zeta zeroes up to `T0`, every finite
positive-ordinate window at height `T <= T0` is empty.
-/
theorem positiveFiniteWindow_eq_empty_of_noPositiveOrdinateZetaZerosAtOrBelow
    {s : Finset ZetaZeroSubtype} {T T0 : Real}
    (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0)
    (hT : T <= T0)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T) :
    s = ∅ := by
  classical
  ext rho
  constructor
  · intro hrho
    have hbounds := hs rho hrho
    exact False.elim (hno rho hbounds.1 (hbounds.2.trans hT))
  · intro hrho
    simp at hrho

/--
If there are no positive-ordinate zeta zeroes up to `T0`, every finite
positive-ordinate window at height `T <= T0` has cardinality zero.
-/
theorem positiveFiniteWindow_card_eq_zero_of_noPositiveOrdinateZetaZerosAtOrBelow
    {s : Finset ZetaZeroSubtype} {T T0 : Real}
    (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0)
    (hT : T <= T0)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T) :
    s.card = 0 := by
  rw [positiveFiniteWindow_eq_empty_of_noPositiveOrdinateZetaZerosAtOrBelow hno hT hs]
  simp

/--
The closed-ball positive-ordinate finset is empty whenever its radius lies
below a known zero-free positive-ordinate height.
-/
theorem closedBallZeroPositiveOrdinateFinset_eq_empty_of_noPositiveOrdinateZetaZerosAtOrBelow
    {T0 : Real} (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0)
    {n : Nat} (hn : (n : Real) <= T0) :
    closedBallZeroPositiveOrdinateFinset n = ∅ := by
  exact
    positiveFiniteWindow_eq_empty_of_noPositiveOrdinateZetaZerosAtOrBelow
      hno hn (fun rho hrho => closedBallZeroPositiveOrdinate_im_bounds n hrho)

/--
The closed-ball positive-ordinate finset has cardinality zero whenever its
radius lies below a known zero-free positive-ordinate height.
-/
theorem closedBallZeroPositiveOrdinateFinset_card_eq_zero_of_noPositiveOrdinateZetaZerosAtOrBelow
    {T0 : Real} (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0)
    {n : Nat} (hn : (n : Real) <= T0) :
    (closedBallZeroPositiveOrdinateFinset n).card = 0 := by
  rw [closedBallZeroPositiveOrdinateFinset_eq_empty_of_noPositiveOrdinateZetaZerosAtOrBelow hno hn]
  simp

/--
A concrete finite-window realization of a positive-ordinate height-counting
function.

The abstract published-source records use an arbitrary real-valued
`heightCount`. To derive small-height vanishing from a zero-free theorem, future
analytic work should also supply the finite window whose cardinality realizes
that count.
-/
structure PositiveOrdinateHeightCountRealization
    (heightCount : Real -> Real) where
  window : Real -> Finset ZetaZeroSubtype
  window_mem_bounds :
    forall T : Real,
      forall rho : ZetaZeroSubtype,
        rho ∈ window T ->
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T
  heightCount_eq_card :
    forall T : Real,
      heightCount T = ((window T).card : Real)

/--
An exact finite-window definition of the positive-ordinate height-counting
function: membership in the window is precisely `0 < Im rho <= T`, and
`heightCount T` is its cardinality.
-/
structure ExactPositiveOrdinateHeightCountWindow
    (heightCount : Real -> Real) where
  window : Real -> Finset ZetaZeroSubtype
  mem_window_iff :
    forall T : Real,
      forall rho : ZetaZeroSubtype,
        rho ∈ window T ↔
          0 < Complex.im (rho : Complex) ∧
            Complex.im (rho : Complex) <= T
  heightCount_eq_card :
    forall T : Real,
      heightCount T = ((window T).card : Real)

/--
Source-shaped exact positive-ordinate height-counting data.

This is the form expected from an external published or verified height count:
the finite window is a finset of complex numbers whose membership is exactly
being a zeta zero with ordinate in `0 < Im s <= T`.
-/
structure SourceExactPositiveOrdinateHeightCountWindow
    (heightCount : Real -> Real) where
  window : Real -> Finset Complex
  mem_window_iff :
    forall T : Real,
      forall s : Complex,
        s ∈ window T ↔
          IsZetaZero s ∧ 0 < Complex.im s ∧ Complex.im s <= T
  heightCount_eq_card :
    forall T : Real,
      heightCount T = ((window T).card : Real)

namespace SourceExactPositiveOrdinateHeightCountWindow

/-- The embedding from a source exact window into the project zeta-zero subtype. -/
def subtypeEmbedding
    {heightCount : Real -> Real}
    (data : SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (T : Real) :
    {s : Complex // s ∈ data.window T} ↪ ZetaZeroSubtype where
  toFun := fun s =>
    ⟨s.1, ((data.mem_window_iff T s.1).mp s.2).1⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun rho : ZetaZeroSubtype => (rho : Complex)) h

/-- The source exact window, viewed as a finset of project zeta-zero subtypes. -/
noncomputable def subtypeWindow
    {heightCount : Real -> Real}
    (data : SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (T : Real) :
    Finset ZetaZeroSubtype :=
  (data.window T).attach.map (data.subtypeEmbedding T)

/--
Membership in the subtype window is exactly the positive-ordinate height
condition.
-/
theorem mem_subtypeWindow_iff
    {heightCount : Real -> Real}
    (data : SourceExactPositiveOrdinateHeightCountWindow heightCount)
    (T : Real) (rho : ZetaZeroSubtype) :
    rho ∈ data.subtypeWindow T ↔
      0 < Complex.im (rho : Complex) ∧
        Complex.im (rho : Complex) <= T := by
  classical
  constructor
  · intro hrho
    rw [subtypeWindow] at hrho
    rcases Finset.mem_map.mp hrho with ⟨s, _hs_attach, hmap⟩
    have hsource := (data.mem_window_iff T (s : Complex)).mp s.property
    have hrho_eq : (rho : Complex) = (s : Complex) :=
      (congrArg Subtype.val hmap).symm
    constructor
    · simpa [hrho_eq] using hsource.2.1
    · simpa [hrho_eq] using hsource.2.2
  · intro hbounds
    rw [subtypeWindow]
    refine Finset.mem_map.mpr ?_
    let s : {s : Complex // s ∈ data.window T} :=
      ⟨(rho : Complex),
        (data.mem_window_iff T (rho : Complex)).mpr
          ⟨rho.property, hbounds⟩⟩
    refine ⟨s, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    rfl

/--
A source-shaped exact height-counting window gives the project subtype-shaped
exact height-counting window.
-/
noncomputable def toExactPositiveOrdinateHeightCountWindow
    {heightCount : Real -> Real}
    (data : SourceExactPositiveOrdinateHeightCountWindow heightCount) :
    ExactPositiveOrdinateHeightCountWindow heightCount where
  window := data.subtypeWindow
  mem_window_iff := data.mem_subtypeWindow_iff
  heightCount_eq_card := by
    intro T
    rw [data.heightCount_eq_card T]
    simp [subtypeWindow]

end SourceExactPositiveOrdinateHeightCountWindow

/--
The remaining analytic content behind conjugation symmetry of zeta zeroes.

Mathlib does not currently expose the full `riemannZeta (conj s)` theorem in
the form this project needs, so the hard analytic input can be supplied either
as the direct zero-stability statement below or, preferably, as the stronger
function-level conjugation formula. The subtype mirror and injectivity
bookkeeping below are then checked by Lean.
-/
def ZetaZeroConjugationSymmetry : Prop :=
  forall s : Complex,
    IsZetaZero s ->
      IsZetaZero (conj s)

/--
The regular-domain function-level zeta conjugation formula implies
zero-stability under complex conjugation.
-/
theorem zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormulaOnRegularSet
    (hformula : RiemannZetaConjugationFormulaOnRegularSet) :
    ZetaZeroConjugationSymmetry := by
  intro s hz
  by_cases hs : s = 1
  · subst s
    exact False.elim (riemannZeta_one_ne_zero hz)
  · unfold IsZetaZero at hz ⊢
    rw [hformula s hs, hz]
    simp

/-- Zeta zeroes are stable under complex conjugation. -/
theorem zetaZeroConjugationSymmetry :
    ZetaZeroConjugationSymmetry :=
  zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormulaOnRegularSet
    riemannZetaConjugationFormulaOnRegularSet

/--
The function-level zeta conjugation formula implies zero-stability under
complex conjugation.
-/
theorem zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormula
    (hformula : RiemannZetaConjugationFormula) :
    ZetaZeroConjugationSymmetry := by
  intro s hz
  unfold IsZetaZero at hz ⊢
  rw [hformula s, hz]
  simp

/--
A global conjugation-style mirror on zeta zeroes, stated only in the form needed
by the finite-window counting adapter.

For the Riemann zeta function this should eventually come from the theorem that
zeroes are stable under complex conjugation.
-/
structure ConjugateOrdinateZetaZeroMirror where
  mirror : ZetaZeroSubtype -> ZetaZeroSubtype
  mirror_im_eq_neg :
    forall rho : ZetaZeroSubtype,
      Complex.im (mirror rho : Complex) = -Complex.im (rho : Complex)
  mirror_injective : Function.Injective mirror

/--
Zero-stability under complex conjugation supplies the global ordinate mirror
used by the classical height-counting adapter.
-/
def conjugateOrdinateZetaZeroMirror_of_zetaZeroConjugationSymmetry
    (hconj : ZetaZeroConjugationSymmetry) :
    ConjugateOrdinateZetaZeroMirror where
  mirror := fun rho =>
    ⟨conj (rho : Complex), hconj (rho : Complex) rho.property⟩
  mirror_im_eq_neg := by
    intro rho
    simp
  mirror_injective := by
    intro rho sigma h
    apply Subtype.ext
    have hval : conj (rho : Complex) = conj (sigma : Complex) :=
      congrArg Subtype.val h
    have hconjval : conj (conj (rho : Complex)) =
        conj (conj (sigma : Complex)) :=
      congrArg conj hval
    simpa using hconjval

/--
The regular-domain function-level zeta conjugation formula supplies the global
ordinate mirror used by the classical height-counting adapter.
-/
def conjugateOrdinateZetaZeroMirror_of_riemannZetaConjugationFormulaOnRegularSet
    (hformula : RiemannZetaConjugationFormulaOnRegularSet) :
    ConjugateOrdinateZetaZeroMirror :=
  conjugateOrdinateZetaZeroMirror_of_zetaZeroConjugationSymmetry
    (zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormulaOnRegularSet
      hformula)

/-- The concrete complex-conjugation ordinate mirror for zeta zeroes. -/
def conjugateOrdinateZetaZeroMirror :
    ConjugateOrdinateZetaZeroMirror :=
  conjugateOrdinateZetaZeroMirror_of_riemannZetaConjugationFormulaOnRegularSet
    riemannZetaConjugationFormulaOnRegularSet

/--
The function-level zeta conjugation formula supplies the global ordinate mirror
used by the classical height-counting adapter.
-/
def conjugateOrdinateZetaZeroMirror_of_riemannZetaConjugationFormula
    (hformula : RiemannZetaConjugationFormula) :
    ConjugateOrdinateZetaZeroMirror :=
  conjugateOrdinateZetaZeroMirror_of_zetaZeroConjugationSymmetry
    (zetaZeroConjugationSymmetry_of_riemannZetaConjugationFormula hformula)

namespace PositiveOrdinateHeightCountRealization

/--
The realizing window contains every positive-ordinate zeta zero up to the
given height.
-/
def CoversAllPositiveOrdinateZeros
    {heightCount : Real -> Real}
    (realization : PositiveOrdinateHeightCountRealization heightCount) :
    Prop :=
  forall T : Real,
    forall rho : ZetaZeroSubtype,
      0 < Complex.im (rho : Complex) ->
        Complex.im (rho : Complex) <= T ->
          rho ∈ realization.window T

/--
If the realizing window covers every positive-ordinate zeta zero up to `T`,
then its cardinality bounds every finite positive-ordinate window at height
`T`. This discharges the positive finite-window interpretation field used by
published `N(T)` source records.
-/
theorem positiveFiniteWindowCard_le_heightCount_of_covers
    {heightCount : Real -> Real}
    (realization : PositiveOrdinateHeightCountRealization heightCount)
    (hcover : realization.CoversAllPositiveOrdinateZeros) :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            0 < Complex.im (rho : Complex) ∧
              Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= heightCount T := by
  intro s T hs
  have hsubset : s ⊆ realization.window T := by
    intro rho hrho
    have hbounds := hs rho hrho
    exact hcover T rho hbounds.1 hbounds.2
  have hcardNat : s.card <= (realization.window T).card :=
    Finset.card_le_card hsubset
  have hcardReal :
      ((s.card : Nat) : Real) <= ((realization.window T).card : Real) := by
    exact_mod_cast hcardNat
  simpa [realization.heightCount_eq_card T] using hcardReal

/--
Symmetry-shaped data sending negative-ordinate zeroes into the realized
positive-ordinate height-counting window.

For zeta this should eventually be supplied by conjugation symmetry of the zero
set. It is kept as an explicit input so the negative finite-window field is not
hidden inside the definition of `heightCount`.
-/
structure NegativeOrdinateMirrorToPositiveWindow
    {heightCount : Real -> Real}
    (realization : PositiveOrdinateHeightCountRealization heightCount) where
  mirror : ZetaZeroSubtype -> ZetaZeroSubtype
  mirror_mem_window :
    forall T : Real,
      forall rho : ZetaZeroSubtype,
        Complex.im (rho : Complex) < 0 ->
          -Complex.im (rho : Complex) <= T ->
            mirror rho ∈ realization.window T
  mirror_injective : Function.Injective mirror

/--
A negative-ordinate mirror into the realized positive window discharges the
negative finite-window interpretation field used by published `N(T)` sources.
-/
theorem negativeFiniteWindowCard_le_heightCount_of_mirror
    {heightCount : Real -> Real}
    (realization : PositiveOrdinateHeightCountRealization heightCount)
    (mirrorData :
      NegativeOrdinateMirrorToPositiveWindow realization) :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            Complex.im (rho : Complex) < 0 ∧
              -Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= heightCount T := by
  intro s T hs
  let toWindow : s -> realization.window T := fun rho =>
    ⟨mirrorData.mirror rho.1,
      mirrorData.mirror_mem_window T rho.1
        (hs rho.1 rho.property).1 (hs rho.1 rho.property).2⟩
  have toWindow_injective : Function.Injective toWindow := by
    intro rho sigma h
    have hmirror :
        mirrorData.mirror rho.1 = mirrorData.mirror sigma.1 :=
      congrArg Subtype.val h
    have hrho : rho.1 = sigma.1 :=
      mirrorData.mirror_injective hmirror
    exact Subtype.ext hrho
  have hcardNat : s.card <= (realization.window T).card :=
    Finset.card_le_card_of_injective (f := toWindow) toWindow_injective
  have hcardReal :
      ((s.card : Nat) : Real) <= ((realization.window T).card : Real) := by
    exact_mod_cast hcardNat
  simpa [realization.heightCount_eq_card T] using hcardReal

/--
A finite-window realization of `heightCount`, together with a no-positive-zero
theorem up to `T0`, forces `heightCount T = 0` for every `T <= T0`.
-/
theorem heightCount_eq_zero_of_noPositiveOrdinateZetaZerosAtOrBelow
    {heightCount : Real -> Real}
    (realization : PositiveOrdinateHeightCountRealization heightCount)
    {T T0 : Real}
    (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0)
    (hT : T <= T0) :
    heightCount T = 0 := by
  have hcard :
      (realization.window T).card = 0 :=
    positiveFiniteWindow_card_eq_zero_of_noPositiveOrdinateZetaZerosAtOrBelow
      (s := realization.window T) hno hT
      (realization.window_mem_bounds T)
  simpa [hcard] using realization.heightCount_eq_card T

/--
The same finite-window realization gives the below-threshold cleanup shape used
by published Riemann-von-Mangoldt sources.
-/
theorem heightCount_eq_zero_below_of_noPositiveOrdinateZetaZerosAtOrBelow
    {heightCount : Real -> Real}
    (realization : PositiveOrdinateHeightCountRealization heightCount)
    {T0 : Real}
    (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0) :
    forall T : Real,
      T < T0 ->
        heightCount T = 0 := by
  intro T hT
  exact
    realization.heightCount_eq_zero_of_noPositiveOrdinateZetaZerosAtOrBelow
      hno (le_of_lt hT)

end PositiveOrdinateHeightCountRealization

namespace ExactPositiveOrdinateHeightCountWindow

/-- An exact positive height-count window gives the realization record. -/
def toRealization
    {heightCount : Real -> Real}
    (data : ExactPositiveOrdinateHeightCountWindow heightCount) :
    PositiveOrdinateHeightCountRealization heightCount where
  window := data.window
  window_mem_bounds := fun T rho hrho => (data.mem_window_iff T rho).mp hrho
  heightCount_eq_card := data.heightCount_eq_card

/-- An exact positive height-count window covers all positive-ordinate zeroes. -/
theorem coversAllPositiveOrdinateZeros
    {heightCount : Real -> Real}
    (data : ExactPositiveOrdinateHeightCountWindow heightCount) :
    data.toRealization.CoversAllPositiveOrdinateZeros := by
  intro T rho hpos hle
  exact (data.mem_window_iff T rho).mpr ⟨hpos, hle⟩

/--
An exact positive height-count window discharges the positive finite-window
interpretation field used by published `N(T)` sources.
-/
theorem positiveFiniteWindowCard_le_heightCount
    {heightCount : Real -> Real}
    (data : ExactPositiveOrdinateHeightCountWindow heightCount) :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            0 < Complex.im (rho : Complex) ∧
              Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= heightCount T :=
  data.toRealization.positiveFiniteWindowCard_le_heightCount_of_covers
    data.coversAllPositiveOrdinateZeros

/--
An exact positive height-count window plus a no-positive-zero theorem forces
the count to vanish below the zero-free threshold.
-/
theorem heightCount_eq_zero_below_of_noPositiveOrdinateZetaZerosAtOrBelow
    {heightCount : Real -> Real}
    (data : ExactPositiveOrdinateHeightCountWindow heightCount)
    {T0 : Real}
    (hno : NoPositiveOrdinateZetaZerosAtOrBelow T0) :
    forall T : Real,
      T < T0 ->
        heightCount T = 0 :=
  data.toRealization.heightCount_eq_zero_below_of_noPositiveOrdinateZetaZerosAtOrBelow
    hno

end ExactPositiveOrdinateHeightCountWindow

namespace SourceExactPositiveOrdinateHeightCountWindow

/--
A source-shaped exact height-count window discharges the positive finite-window
interpretation field used by published `N(T)` sources.
-/
theorem positiveFiniteWindowCard_le_heightCount
    {heightCount : Real -> Real}
    (data : SourceExactPositiveOrdinateHeightCountWindow heightCount) :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            0 < Complex.im (rho : Complex) ∧
              Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= heightCount T :=
  ExactPositiveOrdinateHeightCountWindow.positiveFiniteWindowCard_le_heightCount
    data.toExactPositiveOrdinateHeightCountWindow

/--
A source-shaped exact height-count window vanishes at every height covered by a
source-shaped positive-ordinate zero-free band.
-/
theorem heightCount_eq_zero_of_zetaZeroFreePositiveOrdinateBand
    {heightCount : Real -> Real}
    (data : SourceExactPositiveOrdinateHeightCountWindow heightCount)
    {T T0 : Real}
    (hfree : ZetaZeroFreePositiveOrdinateBand T0)
    (hT : T <= T0) :
    heightCount T = 0 := by
  exact
    PositiveOrdinateHeightCountRealization.heightCount_eq_zero_of_noPositiveOrdinateZetaZerosAtOrBelow
      (ExactPositiveOrdinateHeightCountWindow.toRealization
        data.toExactPositiveOrdinateHeightCountWindow)
      (noPositiveOrdinateZetaZerosAtOrBelow_of_zetaZeroFreePositiveOrdinateBand
        hfree)
      hT

/--
The same source-shaped exact window gives the below-threshold zero-count
cleanup used by Bellotti-Wong/HSW cutoff-2 source packages.
-/
theorem heightCount_eq_zero_below_of_zetaZeroFreePositiveOrdinateBand
    {heightCount : Real -> Real}
    (data : SourceExactPositiveOrdinateHeightCountWindow heightCount)
    {T0 : Real}
    (hfree : ZetaZeroFreePositiveOrdinateBand T0) :
    forall T : Real,
      T < T0 ->
        heightCount T = 0 := by
  intro T hT
  exact
    data.heightCount_eq_zero_of_zetaZeroFreePositiveOrdinateBand
      hfree (le_of_lt hT)

end SourceExactPositiveOrdinateHeightCountWindow

namespace ConjugateOrdinateZetaZeroMirror

/--
A conjugation-style mirror with imaginary part negation becomes the
window-specific negative-to-positive mirror for any exact positive height
window.
-/
def toNegativeOrdinateMirrorToPositiveWindow
    {heightCount : Real -> Real}
    (mirrorData : ConjugateOrdinateZetaZeroMirror)
    (data : ExactPositiveOrdinateHeightCountWindow heightCount) :
    PositiveOrdinateHeightCountRealization.NegativeOrdinateMirrorToPositiveWindow
      data.toRealization where
  mirror := mirrorData.mirror
  mirror_mem_window := by
    intro T rho hneg hle
    have hpos :
        0 < Complex.im (mirrorData.mirror rho : Complex) := by
      rw [mirrorData.mirror_im_eq_neg rho]
      exact neg_pos.mpr hneg
    have hle' :
        Complex.im (mirrorData.mirror rho : Complex) <= T := by
      rw [mirrorData.mirror_im_eq_neg rho]
      exact hle
    exact (data.mem_window_iff T (mirrorData.mirror rho)).mpr ⟨hpos, hle'⟩
  mirror_injective := mirrorData.mirror_injective

end ConjugateOrdinateZetaZeroMirror

/--
A negative-ordinate finite window with nonpositive reflected height is empty.
-/
theorem negativeFiniteWindow_eq_empty_of_nonpos
    {s : Finset ZetaZeroSubtype} {T : Real}
    (hT : T <= 0)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          Complex.im (rho : Complex) < 0 ∧
            -Complex.im (rho : Complex) <= T) :
    s = ∅ := by
  classical
  ext rho
  constructor
  · intro hrho
    have hbounds := hs rho hrho
    have hneg_pos : 0 < -Complex.im (rho : Complex) := neg_pos.mpr hbounds.1
    exact False.elim ((not_lt_of_ge (hbounds.2.trans hT)) hneg_pos)
  · intro hrho
    simp at hrho

/-- Negative-ordinate finite windows have cardinality zero at nonpositive reflected height. -/
theorem negativeFiniteWindow_card_eq_zero_of_nonpos
    {s : Finset ZetaZeroSubtype} {T : Real}
    (hT : T <= 0)
    (hs :
      forall rho : ZetaZeroSubtype,
        rho ∈ s ->
          Complex.im (rho : Complex) < 0 ∧
            -Complex.im (rho : Complex) <= T) :
    s.card = 0 := by
  rw [negativeFiniteWindow_eq_empty_of_nonpos hT hs]
  simp

/--
A classical Riemann-von Mangoldt-style height-counting theorem shape.

The `positiveFiniteWindowCard_le` and `negativeFiniteWindowCard_le` fields are
deliberately stated for arbitrary finite windows satisfying height predicates.
This lets a future analytic theorem be reused for the project's closed-ball
windows without mentioning their construction.
-/
structure ClassicalRiemannVonMangoldtHeightCountingTarget where
  cutoff : Nat
  positiveCountBound : Real -> Real
  negativeCountBound : Real -> Real
  axisOrTrivialBound : Nat -> Real
  heightEnvelopeConstant : Real
  growth : Real
  heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant
  positiveFiniteWindowCard_le :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            0 < Complex.im (rho : Complex) ∧
              Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= positiveCountBound T
  negativeFiniteWindowCard_le :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            Complex.im (rho : Complex) < 0 ∧
              -Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= negativeCountBound T
  axisWindowCard_le :
    forall n : Nat,
      ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
        axisOrTrivialBound n
  tail_classicalHeightEnvelope_le :
    forall n : Nat,
      positiveCountBound ((n + cutoff : Nat) : Real) +
          negativeCountBound ((n + cutoff : Nat) : Real) +
          axisOrTrivialBound (n + cutoff) <=
        heightEnvelopeConstant * |(n : Real) + 1| ^ growth

namespace ClassicalRiemannVonMangoldtHeightCountingTarget

/-- A classical positive-ordinate count bounds the project positive closed-ball window. -/
theorem positiveClosedBall_card_le
    (target : ClassicalRiemannVonMangoldtHeightCountingTarget)
    (n : Nat) :
    ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
      target.positiveCountBound (n : Real) :=
  target.positiveFiniteWindowCard_le
    (closedBallZeroPositiveOrdinateFinset n)
    (n : Real)
    (fun _rho hrho => closedBallZeroPositiveOrdinate_im_bounds n hrho)

/-- A classical negative-ordinate count bounds the project negative closed-ball window. -/
theorem negativeClosedBall_card_le
    (target : ClassicalRiemannVonMangoldtHeightCountingTarget)
    (n : Nat) :
    ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
      target.negativeCountBound (n : Real) :=
  target.negativeFiniteWindowCard_le
    (closedBallZeroNegativeOrdinateFinset n)
    (n : Real)
    (fun _rho hrho => closedBallZeroNegativeOrdinate_im_bounds n hrho)

/-- Convert a classical height-counting theorem shape into the project height target. -/
noncomputable def toHeightCountingTarget
    (target : ClassicalRiemannVonMangoldtHeightCountingTarget) :
    ClosedBallZeroHeightCountingTarget :=
  ClosedBallZeroHeightCountingTarget.ofOrdinateWindowBounds
    target.cutoff
    (fun n : Nat => target.positiveCountBound (n : Real))
    (fun n : Nat => target.negativeCountBound (n : Real))
    target.axisOrTrivialBound
    target.heightEnvelopeConstant
    target.growth
    target.heightEnvelopeConstant_nonneg
    target.positiveClosedBall_card_le
    target.negativeClosedBall_card_le
    target.axisWindowCard_le
    target.tail_classicalHeightEnvelope_le

/-- Classical height counting gives the preferred cumulative closed-ball count. -/
noncomputable def toCumulativeWindowCountingEstimate
    (target : ClassicalRiemannVonMangoldtHeightCountingTarget) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  target.toHeightCountingTarget.toCumulativeWindowCountingEstimate

/-- Classical height counting gives first-entry shell counting. -/
noncomputable def toPolynomialZeroCountingEstimate
    (target : ClassicalRiemannVonMangoldtHeightCountingTarget) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  target.toHeightCountingTarget.toPolynomialZeroCountingEstimate

end ClassicalRiemannVonMangoldtHeightCountingTarget

/--
The common symmetric classical height-counting theorem shape.

This packages the usual route where a positive-ordinate `N(T)` bound, plus
conjugation symmetry or an equivalent negative-ordinate estimate, controls both
halves of the closed-ball window.
-/
structure ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget where
  cutoff : Nat
  positiveCountBound : Real -> Real
  axisOrTrivialBound : Nat -> Real
  heightEnvelopeConstant : Real
  growth : Real
  heightEnvelopeConstant_nonneg : 0 <= heightEnvelopeConstant
  positiveFiniteWindowCard_le :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            0 < Complex.im (rho : Complex) ∧
              Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= positiveCountBound T
  negativeFiniteWindowCard_le_positiveBound :
    forall s : Finset ZetaZeroSubtype,
      forall T : Real,
        (forall rho : ZetaZeroSubtype,
          rho ∈ s ->
            Complex.im (rho : Complex) < 0 ∧
              -Complex.im (rho : Complex) <= T) ->
          ((s.card : Nat) : Real) <= positiveCountBound T
  axisWindowCard_le :
    forall n : Nat,
      ((closedBallZeroAxisOrdinateFinset n).card : Real) <=
        axisOrTrivialBound n
  tail_symmetricClassicalHeightEnvelope_le :
    forall n : Nat,
      positiveCountBound ((n + cutoff : Nat) : Real) +
          positiveCountBound ((n + cutoff : Nat) : Real) +
          axisOrTrivialBound (n + cutoff) <=
        heightEnvelopeConstant * |(n : Real) + 1| ^ growth

namespace ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget

/-- The positive `N(T)` bound controls the project positive closed-ball window. -/
theorem positiveClosedBall_card_le
    (target : ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget)
    (n : Nat) :
    ((closedBallZeroPositiveOrdinateFinset n).card : Real) <=
      target.positiveCountBound (n : Real) :=
  target.positiveFiniteWindowCard_le
    (closedBallZeroPositiveOrdinateFinset n)
    (n : Real)
    (fun _rho hrho => closedBallZeroPositiveOrdinate_im_bounds n hrho)

/-- The symmetric negative-side bound controls the project negative closed-ball window. -/
theorem negativeClosedBall_card_le_positiveBound
    (target : ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget)
    (n : Nat) :
    ((closedBallZeroNegativeOrdinateFinset n).card : Real) <=
      target.positiveCountBound (n : Real) :=
  target.negativeFiniteWindowCard_le_positiveBound
    (closedBallZeroNegativeOrdinateFinset n)
    (n : Real)
    (fun _rho hrho => closedBallZeroNegativeOrdinate_im_bounds n hrho)

/-- Convert a symmetric classical height count into the symmetric closed-ball target. -/
noncomputable def toSymmetricHeightCountingTarget
    (target : ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget) :
    ClosedBallZeroSymmetricHeightCountingTarget :=
  ClosedBallZeroSymmetricHeightCountingTarget.ofPositiveNegativeAxisWindowBounds
    target.cutoff
    (fun n : Nat => target.positiveCountBound (n : Real))
    target.axisOrTrivialBound
    target.heightEnvelopeConstant
    target.growth
    target.heightEnvelopeConstant_nonneg
    target.positiveClosedBall_card_le
    target.negativeClosedBall_card_le_positiveBound
    target.axisWindowCard_le
    target.tail_symmetricClassicalHeightEnvelope_le

/-- Forget the symmetric classical target to the general height target. -/
noncomputable def toHeightCountingTarget
    (target : ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget) :
    ClosedBallZeroHeightCountingTarget :=
  target.toSymmetricHeightCountingTarget.toHeightCountingTarget

/-- Symmetric classical height counting gives the preferred cumulative count. -/
noncomputable def toCumulativeWindowCountingEstimate
    (target : ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget) :
    ClosedBallZeroCumulativeWindowCountingEstimate :=
  target.toSymmetricHeightCountingTarget.toCumulativeWindowCountingEstimate

/-- Symmetric classical height counting gives first-entry shell counting. -/
noncomputable def toPolynomialZeroCountingEstimate
    (target : ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget) :
    SchwartzRiemannWeilPolynomialZeroCountingEstimate closedBallZero :=
  target.toSymmetricHeightCountingTarget.toPolynomialZeroCountingEstimate

end ClassicalSymmetricRiemannVonMangoldtHeightCountingTarget

end ComplexCompactExhaustion

end RiemannHypothesisProject
