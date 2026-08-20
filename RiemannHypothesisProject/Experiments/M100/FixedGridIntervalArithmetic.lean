import RiemannHypothesisProject.Experiments.M100.RationalIntervalArithmetic
import Mathlib.Algebra.BigOperators.Field

/-!
# Fixed-grid integer interval arithmetic

Intervals are stored as integer endpoint numerators over a shared positive
denominator.  The computational operations avoid normalized rational
intermediates; the theorems below connect them back to the existing checked
`RationalInterval` containment library.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

structure FixedGridInterval where
  lower : Int
  upper : Int
deriving DecidableEq, Inhabited, Repr

namespace FixedGridInterval

def toRationalInterval (D : Nat) (I : FixedGridInterval) : RationalInterval :=
  { lower := (I.lower : Rat) / D
    upper := (I.upper : Rat) / D }

def roundLowerNumerator (D : Nat) (q : Rat) : Int :=
  (q.num * D) / (q.den : Int)

def roundUpperNumerator (D : Nat) (q : Rat) : Int :=
  -((-(q.num * D)) / (q.den : Int))

def ofRationalInterval (D : Nat) (I : RationalInterval) : FixedGridInterval :=
  { lower := roundLowerNumerator D I.lower
    upper := roundUpperNumerator D I.upper }

def add (I J : FixedGridInterval) : FixedGridInterval :=
  { lower := I.lower + J.lower
    upper := I.upper + J.upper }

def sub (I J : FixedGridInterval) : FixedGridInterval :=
  { lower := I.lower - J.upper
    upper := I.upper - J.lower }

def scaleLowerNumerator (q : Rat) (I : FixedGridInterval) : Int :=
  if 0 <= q then
    (q.num * I.lower) / (q.den : Int)
  else
    (q.num * I.upper) / (q.den : Int)

def scaleUpperNumerator (q : Rat) (I : FixedGridInterval) : Int :=
  if 0 <= q then
    -((-(q.num * I.upper)) / (q.den : Int))
  else
    -((-(q.num * I.lower)) / (q.den : Int))

def scale (q : Rat) (I : FixedGridInterval) : FixedGridInterval :=
  { lower := scaleLowerNumerator q I
    upper := scaleUpperNumerator q I }

def scaleFinSum {n : Nat}
    (q : Fin n -> Rat) (I : Fin n -> FixedGridInterval) : FixedGridInterval :=
  { lower := Finset.univ.sum fun k => scaleLowerNumerator (q k) (I k)
    upper := Finset.univ.sum fun k => scaleUpperNumerator (q k) (I k) }

def finSum {n : Nat}
    (I : Fin n -> FixedGridInterval) : FixedGridInterval :=
  { lower := Finset.univ.sum fun k => (I k).lower
    upper := Finset.univ.sum fun k => (I k).upper }

/-- Exact multiplication by an integer.  Unlike `scale`, this performs no
division or rational normalization. -/
def scaleInt (a : Int) (I : FixedGridInterval) : FixedGridInterval :=
  if 0 <= a then
    { lower := a * I.lower, upper := a * I.upper }
  else
    { lower := a * I.upper, upper := a * I.lower }

/-- A dot product whose coefficients are integer numerators over one shared
denominator.  Integer products are accumulated first, so outward division is
performed only once for the complete dot product. -/
def dotCommonDenominator {n : Nat}
    (Q : Nat) (q : Fin n -> Int)
    (I : Fin n -> FixedGridInterval) : FixedGridInterval :=
  (finSum fun k => scaleInt (q k) (I k)).scale (1 / Q)

def midpointNumerator (I : FixedGridInterval) : Int :=
  I.lower + I.upper

def radiusNumerator (I : FixedGridInterval) : Int :=
  I.upper - I.lower

def mulCenteredRadiusRaw
    (I J : FixedGridInterval) : Int :=
  |midpointNumerator I| * radiusNumerator J +
    |midpointNumerator J| * radiusNumerator I +
      radiusNumerator I * radiusNumerator J

def mulCenteredLowerRaw
    (I J : FixedGridInterval) : Int :=
  midpointNumerator I * midpointNumerator J -
    mulCenteredRadiusRaw I J

def mulCenteredUpperRaw
    (I J : FixedGridInterval) : Int :=
  midpointNumerator I * midpointNumerator J +
    mulCenteredRadiusRaw I J

def mulCenteredExactDenominator (D : Nat) : Nat :=
  4 * D * D

def mulCenteredRegridDenominator (D : Nat) : Nat :=
  4 * D

def mulCenteredLowerRawSum {n : Nat}
    (I J : Fin n -> FixedGridInterval) : Int :=
  Finset.univ.sum fun k => mulCenteredLowerRaw (I k) (J k)

def mulCenteredUpperRawSum {n : Nat}
    (I J : Fin n -> FixedGridInterval) : Int :=
  Finset.univ.sum fun k => mulCenteredUpperRaw (I k) (J k)

/-- Accumulate exact midpoint-radius product numerators and perform one
outward regrid for the complete sum. -/
def mulCenteredFinSum {n : Nat}
    (D : Nat) (I J : Fin n -> FixedGridInterval) : FixedGridInterval :=
  { lower := mulCenteredLowerRawSum I J /
      (mulCenteredRegridDenominator D : Int)
    upper := -((-mulCenteredUpperRawSum I J) /
      (mulCenteredRegridDenominator D : Int)) }

def mulCentered (D : Nat)
    (I J : FixedGridInterval) : FixedGridInterval :=
  ofRationalInterval D
    ((toRationalInterval D I).mulCentered (toRationalInterval D J))

theorem roundLowerNumerator_div_eq_roundDown
    (D : Nat) (q : Rat) :
    ((roundLowerNumerator D q : Int) : Rat) / D =
      RationalInterval.roundDown D q := by
  unfold roundLowerNumerator RationalInterval.roundDown
  have hqD : q * D = ((q.num * D : Int) : Rat) / q.den := by
    calc
      q * D = ((q.num : Rat) / q.den) * D := by rw [q.num_div_den]
      _ = ((q.num * D : Int) : Rat) / q.den := by
        norm_num
        ring
  rw [hqD, Rat.floor_intCast_div_natCast]

theorem roundUpperNumerator_div_eq_roundUp
    (D : Nat) (q : Rat) :
    ((roundUpperNumerator D q : Int) : Rat) / D =
      RationalInterval.roundUp D q := by
  unfold roundUpperNumerator RationalInterval.roundUp
  have hqD : q * D = ((q.num * D : Int) : Rat) / q.den := by
    calc
      q * D = ((q.num : Rat) / q.den) * D := by rw [q.num_div_den]
      _ = ((q.num * D : Int) : Rat) / q.den := by
        norm_num
        ring
  rw [hqD, Rat.ceil_intCast_div_natCast]

theorem toRationalInterval_ofRationalInterval_eq_roundOut
    (D : Nat) (I : RationalInterval) :
    toRationalInterval D (ofRationalInterval D I) =
      RationalInterval.roundOut D I := by
  cases I
  simp [toRationalInterval, ofRationalInterval, RationalInterval.roundOut,
    roundLowerNumerator_div_eq_roundDown,
    roundUpperNumerator_div_eq_roundUp]

theorem contains_ofRationalInterval
    {D : Nat} (hD : 0 < D) {I : RationalInterval} {x : Real}
    (hx : I.Contains x) :
    (toRationalInterval D (ofRationalInterval D I)).Contains x := by
  rw [toRationalInterval_ofRationalInterval_eq_roundOut]
  exact RationalInterval.contains_roundOut hD hx

theorem toRationalInterval_add (D : Nat) (I J : FixedGridInterval) :
    toRationalInterval D (I.add J) =
      (toRationalInterval D I).add (toRationalInterval D J) := by
  cases I
  cases J
  simp [toRationalInterval, add, RationalInterval.add]
  constructor <;> ring

theorem toRationalInterval_sub (D : Nat) (I J : FixedGridInterval) :
    toRationalInterval D (I.sub J) =
      (toRationalInterval D I).sub (toRationalInterval D J) := by
  cases I
  cases J
  simp [toRationalInterval, sub, RationalInterval.sub,
    RationalInterval.add, RationalInterval.neg]
  constructor <;> ring

theorem contains_add {D : Nat} {I J : FixedGridInterval} {x y : Real}
    (hx : (toRationalInterval D I).Contains x)
    (hy : (toRationalInterval D J).Contains y) :
    (toRationalInterval D (I.add J)).Contains (x + y) := by
  rw [toRationalInterval_add]
  exact RationalInterval.contains_add hx hy

theorem contains_sub {D : Nat} {I J : FixedGridInterval} {x y : Real}
    (hx : (toRationalInterval D I).Contains x)
    (hy : (toRationalInterval D J).Contains y) :
    (toRationalInterval D (I.sub J)).Contains (x - y) := by
  rw [toRationalInterval_sub]
  exact RationalInterval.contains_sub hx hy

theorem scaledLowerNumerator_div_eq_roundDown
    {D : Nat} (hD : 0 < D) (q : Rat) (a : Int) :
    ((((q.num * a) / (q.den : Int) : Int) : Rat) / D) =
      RationalInterval.roundDown D (q * ((a : Rat) / D)) := by
  unfold RationalInterval.roundDown
  have hD0 : (D : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hscaled : q * ((a : Rat) / D) * D =
      (((q.num * a : Int) : Rat) / q.den) := by
    calc
      q * ((a : Rat) / D) * D =
          ((q.num : Rat) / q.den) * ((a : Rat) / D) * D := by
            rw [q.num_div_den]
      _ = (((q.num * a : Int) : Rat) / q.den) := by
        field_simp [hD0]
        norm_num
  rw [hscaled, Rat.floor_intCast_div_natCast]

theorem scaledUpperNumerator_div_eq_roundUp
    {D : Nat} (hD : 0 < D) (q : Rat) (a : Int) :
    (((-((-(q.num * a)) / (q.den : Int)) : Int) : Rat) / D) =
      RationalInterval.roundUp D (q * ((a : Rat) / D)) := by
  unfold RationalInterval.roundUp
  have hD0 : (D : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hscaled : q * ((a : Rat) / D) * D =
      (((q.num * a : Int) : Rat) / q.den) := by
    calc
      q * ((a : Rat) / D) * D =
          ((q.num : Rat) / q.den) * ((a : Rat) / D) * D := by
            rw [q.num_div_den]
      _ = (((q.num * a : Int) : Rat) / q.den) := by
        field_simp [hD0]
        norm_num
  rw [hscaled, Rat.ceil_intCast_div_natCast]

theorem toRationalInterval_scale_eq_roundOut_scale
    {D : Nat} (hD : 0 < D) (q : Rat) (I : FixedGridInterval)
    (hI : (toRationalInterval D I).lower <=
      (toRationalInterval D I).upper) :
    toRationalInterval D (I.scale q) =
      RationalInterval.roundOut D
        (RationalInterval.scale q (toRationalInterval D I)) := by
  by_cases hq : 0 <= q
  case pos =>
    have hmul : q * (toRationalInterval D I).lower <=
        q * (toRationalInterval D I).upper :=
      mul_le_mul_of_nonneg_left hI hq
    have hmul' : q * ((I.lower : Rat) / D) <=
        q * ((I.upper : Rat) / D) := by
      simpa [toRationalInterval] using hmul
    unfold toRationalInterval scale scaleLowerNumerator
      scaleUpperNumerator RationalInterval.roundOut RationalInterval.scale
    simp only [if_pos hq]
    rw [min_eq_left hmul', max_eq_right hmul']
    congr 1
    · exact scaledLowerNumerator_div_eq_roundDown hD q I.lower
    · simpa only [Int.cast_neg] using
        scaledUpperNumerator_div_eq_roundUp hD q I.upper
  case neg =>
    have hq' : q <= 0 := le_of_not_ge hq
    have hmul : q * (toRationalInterval D I).upper <=
        q * (toRationalInterval D I).lower :=
      mul_le_mul_of_nonpos_left hI hq'
    have hmul' : q * ((I.upper : Rat) / D) <=
        q * ((I.lower : Rat) / D) := by
      simpa [toRationalInterval] using hmul
    unfold toRationalInterval scale scaleLowerNumerator
      scaleUpperNumerator RationalInterval.roundOut RationalInterval.scale
    simp only [if_neg hq]
    rw [min_eq_right hmul', max_eq_left hmul']
    congr 1
    · exact scaledLowerNumerator_div_eq_roundDown hD q I.upper
    · simpa only [Int.cast_neg] using
        scaledUpperNumerator_div_eq_roundUp hD q I.lower

theorem contains_scale
    {D : Nat} (hD : 0 < D) {q : Rat} {I : FixedGridInterval} {x : Real}
    (hx : (toRationalInterval D I).Contains x) :
    (toRationalInterval D (I.scale q)).Contains ((q : Real) * x) := by
  have hIReal :
      ((toRationalInterval D I).lower : Real) <=
        ((toRationalInterval D I).upper : Real) :=
    le_trans hx.1 hx.2
  have hI : (toRationalInterval D I).lower <=
      (toRationalInterval D I).upper := by
    exact_mod_cast hIReal
  rw [toRationalInterval_scale_eq_roundOut_scale hD q I hI]
  exact RationalInterval.contains_roundOut hD
    (RationalInterval.contains_scale q hx)

theorem toRationalInterval_scaleFinSum {n : Nat}
    (D : Nat) (q : Fin n -> Rat) (I : Fin n -> FixedGridInterval) :
    toRationalInterval D (scaleFinSum q I) =
      RationalInterval.sum Finset.univ
        (fun k => toRationalInterval D ((I k).scale (q k))) := by
  unfold scaleFinSum toRationalInterval RationalInterval.sum scale
  congr 1
  · simp [Finset.sum_div]
  · simp [Finset.sum_div]

theorem contains_scaleFinSum {n : Nat}
    {D : Nat} (hD : 0 < D) {q : Fin n -> Rat}
    {I : Fin n -> FixedGridInterval} {x : Fin n -> Real}
    (hx : forall k, (toRationalInterval D (I k)).Contains (x k)) :
    (toRationalInterval D (scaleFinSum q I)).Contains
      (Finset.univ.sum fun k : Fin n => (q k : Real) * x k) := by
  rw [toRationalInterval_scaleFinSum]
  exact RationalInterval.contains_sum fun k _ => contains_scale hD (hx k)

theorem toRationalInterval_finSum {n : Nat}
    (D : Nat) (I : Fin n -> FixedGridInterval) :
    toRationalInterval D (finSum I) =
      RationalInterval.sum Finset.univ
        (fun k => toRationalInterval D (I k)) := by
  unfold finSum toRationalInterval RationalInterval.sum
  congr 1
  · simp [Finset.sum_div]
  · simp [Finset.sum_div]

theorem contains_finSum {n : Nat}
    {D : Nat} {I : Fin n -> FixedGridInterval} {x : Fin n -> Real}
    (hx : forall k, (toRationalInterval D (I k)).Contains (x k)) :
    (toRationalInterval D (finSum I)).Contains
      (Finset.univ.sum fun k : Fin n => x k) := by
  rw [toRationalInterval_finSum]
  exact RationalInterval.contains_sum fun k _ => hx k

theorem toRationalInterval_scaleInt
    (D : Nat) (a : Int) (I : FixedGridInterval)
    (hI : (toRationalInterval D I).lower <=
      (toRationalInterval D I).upper) :
    toRationalInterval D (scaleInt a I) =
      RationalInterval.scale (a : Rat) (toRationalInterval D I) := by
  by_cases ha : 0 <= a
  case pos =>
    have haRat : (0 : Rat) <= (a : Rat) := by exact_mod_cast ha
    have hmul := mul_le_mul_of_nonneg_left hI haRat
    have hmul' : (a : Rat) * ((I.lower : Rat) / D) <=
        (a : Rat) * ((I.upper : Rat) / D) := by
      simpa [toRationalInterval] using hmul
    unfold scaleInt toRationalInterval RationalInterval.scale
    simp only [if_pos ha, min_eq_left hmul', max_eq_right hmul']
    congr 1 <;> norm_num <;> ring
  case neg =>
    have ha' : a <= 0 := le_of_not_ge ha
    have haRat : (a : Rat) <= 0 := by exact_mod_cast ha'
    have hmul := mul_le_mul_of_nonpos_left hI haRat
    have hmul' : (a : Rat) * ((I.upper : Rat) / D) <=
        (a : Rat) * ((I.lower : Rat) / D) := by
      simpa [toRationalInterval] using hmul
    unfold scaleInt toRationalInterval RationalInterval.scale
    simp only [if_neg ha, min_eq_right hmul', max_eq_left hmul']
    congr 1 <;> norm_num <;> ring

theorem contains_scaleInt
    {D : Nat} {a : Int} {I : FixedGridInterval} {x : Real}
    (hx : (toRationalInterval D I).Contains x) :
    (toRationalInterval D (scaleInt a I)).Contains ((a : Real) * x) := by
  have hIReal :
      ((toRationalInterval D I).lower : Real) <=
        ((toRationalInterval D I).upper : Real) :=
    le_trans hx.1 hx.2
  have hI : (toRationalInterval D I).lower <=
      (toRationalInterval D I).upper := by
    exact_mod_cast hIReal
  rw [toRationalInterval_scaleInt D a I hI]
  simpa using RationalInterval.contains_scale (a : Rat) hx

theorem contains_dotCommonDenominator {n : Nat}
    {D Q : Nat} (hD : 0 < D) {q : Fin n -> Int}
    {I : Fin n -> FixedGridInterval} {x : Fin n -> Real}
    (hx : forall k, (toRationalInterval D (I k)).Contains (x k)) :
    (toRationalInterval D (dotCommonDenominator Q q I)).Contains
      (((1 / Q : Rat) : Real) *
        Finset.univ.sum fun k : Fin n => (q k : Real) * x k) := by
  exact contains_scale hD
    (contains_finSum fun k => contains_scaleInt (hx k))

theorem center_toRationalInterval
    (D : Nat) (I : FixedGridInterval) :
    (toRationalInterval D I).center =
      ((midpointNumerator I : Int) : Rat) / (2 * (D : Rat)) := by
  simp [RationalInterval.center, toRationalInterval, midpointNumerator]
  ring

theorem radius_toRationalInterval
    (D : Nat) (I : FixedGridInterval) :
    (toRationalInterval D I).radius =
      ((radiusNumerator I : Int) : Rat) / (2 * (D : Rat)) := by
  simp [RationalInterval.radius, toRationalInterval, radiusNumerator]
  ring

theorem abs_center_toRationalInterval
    {D : Nat} (hD : 0 < D) (I : FixedGridInterval) :
    |(toRationalInterval D I).center| =
      (((|midpointNumerator I| : Int) : Rat) /
        (2 * (D : Rat))) := by
  rw [center_toRationalInterval]
  rw [abs_div]
  rw [abs_of_nonneg (show (0 : Rat) <= 2 * D by positivity)]
  rw [Int.cast_abs]

theorem rational_mulCentered_lower_eq_raw
    {D : Nat} (hD : 0 < D) (I J : FixedGridInterval) :
    ((toRationalInterval D I).mulCentered
      (toRationalInterval D J)).lower =
      ((mulCenteredLowerRaw I J : Int) : Rat) /
        (mulCenteredExactDenominator D : Rat) := by
  have hD0 : (D : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hD
  unfold RationalInterval.mulCentered
  dsimp only
  rw [abs_center_toRationalInterval hD,
    abs_center_toRationalInterval hD,
    center_toRationalInterval, center_toRationalInterval,
    radius_toRationalInterval, radius_toRationalInterval]
  simp only [mulCenteredLowerRaw, mulCenteredRadiusRaw,
    midpointNumerator, radiusNumerator,
    mulCenteredExactDenominator, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_abs]
  push_cast
  field_simp [hD0]
  ring

theorem rational_mulCentered_upper_eq_raw
    {D : Nat} (hD : 0 < D) (I J : FixedGridInterval) :
    ((toRationalInterval D I).mulCentered
      (toRationalInterval D J)).upper =
      ((mulCenteredUpperRaw I J : Int) : Rat) /
        (mulCenteredExactDenominator D : Rat) := by
  have hD0 : (D : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hD
  unfold RationalInterval.mulCentered
  dsimp only
  rw [abs_center_toRationalInterval hD,
    abs_center_toRationalInterval hD,
    center_toRationalInterval, center_toRationalInterval,
    radius_toRationalInterval, radius_toRationalInterval]
  simp only [mulCenteredUpperRaw, mulCenteredRadiusRaw,
    midpointNumerator, radiusNumerator,
    mulCenteredExactDenominator, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_abs]
  push_cast
  field_simp [hD0]
  ring

theorem rational_mulCentered_sum_lower_eq_raw {n : Nat}
    {D : Nat} (hD : 0 < D)
    (I J : Fin n -> FixedGridInterval) :
    (RationalInterval.sum Finset.univ fun k =>
      (toRationalInterval D (I k)).mulCentered
        (toRationalInterval D (J k))).lower =
      ((mulCenteredLowerRawSum I J : Int) : Rat) /
        (mulCenteredExactDenominator D : Rat) := by
  change (Finset.univ.sum fun k =>
    ((toRationalInterval D (I k)).mulCentered
      (toRationalInterval D (J k))).lower) = _
  simp_rw [rational_mulCentered_lower_eq_raw hD]
  rw [← Finset.sum_div]
  congr 1
  simp [mulCenteredLowerRawSum]

theorem rational_mulCentered_sum_upper_eq_raw {n : Nat}
    {D : Nat} (hD : 0 < D)
    (I J : Fin n -> FixedGridInterval) :
    (RationalInterval.sum Finset.univ fun k =>
      (toRationalInterval D (I k)).mulCentered
        (toRationalInterval D (J k))).upper =
      ((mulCenteredUpperRawSum I J : Int) : Rat) /
        (mulCenteredExactDenominator D : Rat) := by
  change (Finset.univ.sum fun k =>
    ((toRationalInterval D (I k)).mulCentered
      (toRationalInterval D (J k))).upper) = _
  simp_rw [rational_mulCentered_upper_eq_raw hD]
  rw [← Finset.sum_div]
  congr 1
  simp [mulCenteredUpperRawSum]

theorem raw_lower_regrid_eq_roundDown
    {D : Nat} (hD : 0 < D) (s : Int) :
    (((s / (mulCenteredRegridDenominator D : Int) : Int) : Rat) / D) =
      RationalInterval.roundDown D
        ((s : Rat) / (mulCenteredExactDenominator D : Rat)) := by
  unfold RationalInterval.roundDown
  have hD0 : (D : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hD
  have hscaled :
      ((s : Rat) / (mulCenteredExactDenominator D : Rat)) * D =
        (s : Rat) / (mulCenteredRegridDenominator D : Rat) := by
    simp [mulCenteredExactDenominator,
      mulCenteredRegridDenominator]
    field_simp [hD0]
  rw [hscaled, Rat.floor_intCast_div_natCast]

theorem raw_upper_regrid_eq_roundUp
    {D : Nat} (hD : 0 < D) (s : Int) :
    (((-((-s) / (mulCenteredRegridDenominator D : Int)) : Int) : Rat) / D) =
      RationalInterval.roundUp D
        ((s : Rat) / (mulCenteredExactDenominator D : Rat)) := by
  unfold RationalInterval.roundUp
  have hD0 : (D : Rat) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hD
  have hscaled :
      ((s : Rat) / (mulCenteredExactDenominator D : Rat)) * D =
        (s : Rat) / (mulCenteredRegridDenominator D : Rat) := by
    simp [mulCenteredExactDenominator,
      mulCenteredRegridDenominator]
    field_simp [hD0]
  rw [hscaled, Rat.ceil_intCast_div_natCast]

theorem toRationalInterval_mulCenteredFinSum_eq
    {n : Nat} {D : Nat} (hD : 0 < D)
    (I J : Fin n -> FixedGridInterval) :
    toRationalInterval D (mulCenteredFinSum D I J) =
      RationalInterval.roundOut D
        (RationalInterval.sum Finset.univ fun k =>
          (toRationalInterval D (I k)).mulCentered
            (toRationalInterval D (J k))) := by
  let S := RationalInterval.sum Finset.univ fun k =>
    (toRationalInterval D (I k)).mulCentered
      (toRationalInterval D (J k))
  change
    ({ lower :=
        (((mulCenteredLowerRawSum I J /
          (mulCenteredRegridDenominator D : Int) : Int) : Rat) / D)
       upper :=
        (((-((-mulCenteredUpperRawSum I J) /
          (mulCenteredRegridDenominator D : Int)) : Int) : Rat) / D) } :
      RationalInterval) = RationalInterval.roundOut D S
  unfold RationalInterval.roundOut
  congr 1
  · rw [raw_lower_regrid_eq_roundDown hD]
    rw [show S.lower =
      ((mulCenteredLowerRawSum I J : Int) : Rat) /
        (mulCenteredExactDenominator D : Rat) by
      exact rational_mulCentered_sum_lower_eq_raw hD I J]
  · rw [raw_upper_regrid_eq_roundUp hD]
    rw [show S.upper =
      ((mulCenteredUpperRawSum I J : Int) : Rat) /
        (mulCenteredExactDenominator D : Rat) by
      exact rational_mulCentered_sum_upper_eq_raw hD I J]

theorem contains_mulCenteredFinSum {n : Nat}
    {D : Nat} (hD : 0 < D)
    {I J : Fin n -> FixedGridInterval}
    {x y : Fin n -> Real}
    (hx : forall k, (toRationalInterval D (I k)).Contains (x k))
    (hy : forall k, (toRationalInterval D (J k)).Contains (y k)) :
    (toRationalInterval D (mulCenteredFinSum D I J)).Contains
      (Finset.univ.sum fun k => x k * y k) := by
  rw [toRationalInterval_mulCenteredFinSum_eq hD]
  exact RationalInterval.contains_roundOut hD
    (RationalInterval.contains_sum fun k _ =>
      RationalInterval.contains_mulCentered (hx k) (hy k))

theorem contains_mulCentered
    {D : Nat} (hD : 0 < D) {I J : FixedGridInterval} {x y : Real}
    (hx : (toRationalInterval D I).Contains x)
    (hy : (toRationalInterval D J).Contains y) :
    (toRationalInterval D (mulCentered D I J)).Contains (x * y) := by
  exact contains_ofRationalInterval hD
    (RationalInterval.contains_mulCentered hx hy)

end FixedGridInterval

end RiemannHypothesisProject.Experiments.M100
