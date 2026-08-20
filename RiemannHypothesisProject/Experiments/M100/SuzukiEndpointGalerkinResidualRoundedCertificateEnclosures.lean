import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Rounded live-entry enclosures for M100-DF6D4

The exact residual formulas contain long rational sums.  Keeping every
intermediate result exact makes their denominators grow unnecessarily before
the final certificate admission check.  This module evaluates the same proved
interval ingredients with outward rounding after each finite-sum step.  The
fixed denominator is far finer than the generated certificate grid.
-/

namespace RiemannHypothesisProject.Experiments.M100

open RationalInterval

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RationalInterval

/-- Computationally direct form of `roundDown`.  It avoids normalizing the
intermediate rational `q * D` before taking its floor. -/
def fastRoundDown (D : Nat) (q : Rat) : Rat :=
  ((q.num * D) / q.den : Int) / D

theorem fastRoundDown_eq_roundDown (D : Nat) (q : Rat) :
    fastRoundDown D q = roundDown D q := by
  unfold fastRoundDown roundDown
  have hqD : q * D = ((q.num * D : Int) : Rat) / q.den := by
    calc
      q * D = ((q.num : Rat) / q.den) * D := by rw [q.num_div_den]
      _ = ((q.num * D : Int) : Rat) / q.den := by
        norm_num
        ring
  rw [hqD, Rat.floor_intCast_div_natCast]

/-- Computationally direct form of `roundUp`. -/
def fastRoundUp (D : Nat) (q : Rat) : Rat :=
  (-((-q.num * D) / q.den) : Int) / D

theorem fastRoundUp_eq_roundUp (D : Nat) (q : Rat) :
    fastRoundUp D q = roundUp D q := by
  unfold fastRoundUp roundUp
  have hqD : q * D = ((q.num * D : Int) : Rat) / q.den := by
    calc
      q * D = ((q.num : Rat) / q.den) * D := by rw [q.num_div_den]
      _ = ((q.num * D : Int) : Rat) / q.den := by
        norm_num
        ring
  rw [hqD, Rat.ceil_intCast_div_natCast]
  congr 2
  ring

def fastRoundOut (D : Nat) (I : RationalInterval) : RationalInterval :=
  ⟨fastRoundDown D I.lower, fastRoundUp D I.upper⟩

theorem fastRoundOut_eq_roundOut (D : Nat) (I : RationalInterval) :
    fastRoundOut D I = roundOut D I := by
  cases I
  simp [fastRoundOut, roundOut,
    fastRoundDown_eq_roundDown, fastRoundUp_eq_roundUp]

theorem contains_fastRoundOut
    {D : Nat} (hD : 0 < D) {I : RationalInterval} {x : Real}
    (hx : I.Contains x) :
    (fastRoundOut D I).Contains x := by
  rw [fastRoundOut_eq_roundOut]
  exact contains_roundOut hD hx

/-- Round a product down without first normalizing the exact rational
product.  This is the hot-path operation for the Galerkin residual sums. -/
def fastRoundMulDown (D : Nat) (q r : Rat) : Rat :=
  ((q.num * r.num * D) / (q.den * r.den) : Int) / D

theorem fastRoundMulDown_eq_fastRoundDown_mul (D : Nat) (q r : Rat) :
    fastRoundMulDown D q r = fastRoundDown D (q * r) := by
  have hqrD : q * r * D =
      ((q.num * r.num * D : Int) : Rat) / (q.den * r.den) := by
    calc
      q * r * D =
          ((q.num : Rat) / q.den) * ((r.num : Rat) / r.den) * D := by
            rw [q.num_div_den, r.num_div_den]
      _ = ((q.num * r.num * D : Int) : Rat) / (q.den * r.den) := by
        norm_num
        ring
  rw [fastRoundDown_eq_roundDown]
  unfold fastRoundMulDown roundDown
  congr 1
  rw [hqrD]
  exact_mod_cast (Rat.floor_intCast_div_natCast
    (q.num * r.num * D) (q.den * r.den)).symm

/-- Round a product up without first normalizing the exact rational
product. -/
def fastRoundMulUp (D : Nat) (q r : Rat) : Rat :=
  (-((-(q.num * r.num * D)) / (q.den * r.den)) : Int) / D

theorem fastRoundMulUp_eq_fastRoundUp_mul (D : Nat) (q r : Rat) :
    fastRoundMulUp D q r = fastRoundUp D (q * r) := by
  have hqrD : q * r * D =
      ((q.num * r.num * D : Int) : Rat) / (q.den * r.den) := by
    calc
      q * r * D =
          ((q.num : Rat) / q.den) * ((r.num : Rat) / r.den) * D := by
            rw [q.num_div_den, r.num_div_den]
      _ = ((q.num * r.num * D : Int) : Rat) / (q.den * r.den) := by
        norm_num
        ring
  rw [fastRoundUp_eq_roundUp]
  unfold fastRoundMulUp roundUp
  congr 1
  rw [hqrD]
  exact_mod_cast (Rat.ceil_intCast_div_natCast
    (q.num * r.num * D) (q.den * r.den)).symm

/-
/-- Scale an ordered interval and round outward without constructing either
exact rational endpoint product. -/
def fastScaleOut (D : Nat) (q : Rat)
    (I : RationalInterval) : RationalInterval :=
  if 0 <= q then
    âŸ¨fastRoundMulDown D q I.lower, fastRoundMulUp D q I.upperâŸ©
  else
    âŸ¨fastRoundMulDown D q I.upper, fastRoundMulUp D q I.lowerâŸ©

theorem fastScaleOut_eq_fastRoundOut_scale
    (D : Nat) (q : Rat) (I : RationalInterval)
    (hI : I.lower <= I.upper) :
    fastScaleOut D q I = fastRoundOut D (scale q I) := by
  by_cases hq : 0 <= q
  Â· have hmul : q * I.lower <= q * I.upper :=
      mul_le_mul_of_nonneg_left hI hq
    simp [fastScaleOut, hq, fastRoundOut, scale,
      fastRoundMulDown_eq_fastRoundDown_mul,
      fastRoundMulUp_eq_fastRoundUp_mul,
      min_eq_left hmul, max_eq_right hmul]
  Â· have hq' : q <= 0 := le_of_not_ge hq
    have hmul : q * I.upper <= q * I.lower :=
      mul_le_mul_of_nonpos_left hI hq'
    simp [fastScaleOut, hq, fastRoundOut, scale,
      fastRoundMulDown_eq_fastRoundDown_mul,
      fastRoundMulUp_eq_fastRoundUp_mul,
      min_eq_right hmul, max_eq_left hmul]

theorem contains_fastScaleOut
    {D : Nat} (hD : 0 < D) {q : Rat} {I : RationalInterval} {x : Real}
    (hx : I.Contains x) :
    (fastScaleOut D q I).Contains ((q : Real) * x) := by
  have hI : I.lower <= I.upper := by
    norm_num [Contains] at hx âŠ¢
    linarith
  rw [fastScaleOut_eq_fastRoundOut_scale D q I hI]
  exact contains_fastRoundOut hD (contains_scale q hx)
-/

/-- Scale an ordered interval and round outward without constructing either
exact rational endpoint product. -/
def fastScaleOut (D : Nat) (q : Rat)
    (I : RationalInterval) : RationalInterval :=
  if 0 <= q then
    { lower := fastRoundMulDown D q I.lower
      upper := fastRoundMulUp D q I.upper }
  else
    { lower := fastRoundMulDown D q I.upper
      upper := fastRoundMulUp D q I.lower }

theorem fastScaleOut_eq_fastRoundOut_scale
    (D : Nat) (q : Rat) (I : RationalInterval)
    (hI : I.lower <= I.upper) :
    fastScaleOut D q I = fastRoundOut D (scale q I) := by
  by_cases hq : 0 <= q
  case pos =>
    have hmul : q * I.lower <= q * I.upper :=
      mul_le_mul_of_nonneg_left hI hq
    simp [fastScaleOut, hq, fastRoundOut, scale,
      fastRoundMulDown_eq_fastRoundDown_mul,
      fastRoundMulUp_eq_fastRoundUp_mul,
      min_eq_left hmul, max_eq_right hmul]
  case neg =>
    have hq' : q <= 0 := le_of_not_ge hq
    have hmul : q * I.upper <= q * I.lower :=
      mul_le_mul_of_nonpos_left hI hq'
    simp [fastScaleOut, hq, fastRoundOut, scale,
      fastRoundMulDown_eq_fastRoundDown_mul,
      fastRoundMulUp_eq_fastRoundUp_mul,
      min_eq_right hmul, max_eq_left hmul]

theorem contains_fastScaleOut
    {D : Nat} (hD : 0 < D) {q : Rat} {I : RationalInterval} {x : Real}
    (hx : I.Contains x) :
    (fastScaleOut D q I).Contains ((q : Real) * x) := by
  have hI : I.lower <= I.upper := by
    have hIReal : (I.lower : Real) <= (I.upper : Real) :=
      le_trans hx.1 hx.2
    exact_mod_cast hIReal
  rw [fastScaleOut_eq_fastRoundOut_scale D q I hI]
  exact contains_fastRoundOut hD (contains_scale q hx)

def fastScaleLowerNumerator (D : Nat) (q : Rat)
    (I : RationalInterval) : Int :=
  if 0 <= q then
    (q.num * I.lower.num * D) / (q.den * I.lower.den)
  else
    (q.num * I.upper.num * D) / (q.den * I.upper.den)

def fastScaleUpperNumerator (D : Nat) (q : Rat)
    (I : RationalInterval) : Int :=
  if 0 <= q then
    -((-(q.num * I.upper.num * D)) / (q.den * I.upper.den))
  else
    -((-(q.num * I.lower.num * D)) / (q.den * I.lower.den))

/-- A fixed-grid interval dot product.  Each scalar product is rounded
outward, then the resulting grid numerators are accumulated as integers. -/
def fastScaleFinSum {n : Nat} (D : Nat)
    (q : Fin n -> Rat) (I : Fin n -> RationalInterval) : RationalInterval :=
  { lower := ((Finset.univ.sum fun k : Fin n =>
      fastScaleLowerNumerator D (q k) (I k) : Int) : Rat) / D
    upper := ((Finset.univ.sum fun k : Fin n =>
      fastScaleUpperNumerator D (q k) (I k) : Int) : Rat) / D }

theorem fastScaleOut_lower_eq_numerator_div
    (D : Nat) (q : Rat) (I : RationalInterval) :
    (fastScaleOut D q I).lower =
      (fastScaleLowerNumerator D q I : Rat) / D := by
  by_cases hq : 0 <= q <;>
    simp [fastScaleOut, fastScaleLowerNumerator, fastRoundMulDown, hq]

theorem fastScaleOut_upper_eq_numerator_div
    (D : Nat) (q : Rat) (I : RationalInterval) :
    (fastScaleOut D q I).upper =
      (fastScaleUpperNumerator D q I : Rat) / D := by
  by_cases hq : 0 <= q <;>
    simp [fastScaleOut, fastScaleUpperNumerator, fastRoundMulUp, hq]

theorem fastScaleFinSum_eq_intervalSum {n : Nat}
    (D : Nat) (q : Fin n -> Rat) (I : Fin n -> RationalInterval) :
    fastScaleFinSum D q I =
      RationalInterval.sum Finset.univ (fun k => fastScaleOut D (q k) (I k)) := by
  unfold fastScaleFinSum RationalInterval.sum
  congr 1
  · simp [fastScaleOut_lower_eq_numerator_div, Finset.sum_div]
  · simp [fastScaleOut_upper_eq_numerator_div, Finset.sum_div]

theorem contains_fastScaleFinSum {n : Nat} {D : Nat} (hD : 0 < D)
    {q : Fin n -> Rat} {I : Fin n -> RationalInterval} {x : Fin n -> Real}
    (hx : forall k, (I k).Contains (x k)) :
    (fastScaleFinSum D q I).Contains
      (Finset.univ.sum fun k : Fin n => (q k : Real) * x k) := by
  rw [fastScaleFinSum_eq_intervalSum]
  exact contains_sum fun k _ => contains_fastScaleOut hD (hx k)

end RationalInterval

/-- Common denominator used by the proof-producing admission evaluator. -/
def suzukiDF6D4ResidualAdmissionDenominator : Nat :=
  10000000000000000

def suzukiDF6D4ResidualAdmissionRound (I : RationalInterval) : RationalInterval :=
  RationalInterval.fastRoundOut suzukiDF6D4ResidualAdmissionDenominator I

/-- An outward-rounded left fold over a finite family indexed by `Fin n`. -/
def suzukiDF6D4RoundedFinSum {n : Nat}
    (D : Nat) (f : Fin n -> RationalInterval) : RationalInterval :=
  let rec go : (m : Nat) -> (m <= n) -> RationalInterval
    | 0, _ => RationalInterval.point 0
    | m + 1, hm =>
        RationalInterval.fastRoundOut D
          ((go m (Nat.le_trans (Nat.le_succ m) hm)).add
            (f ⟨m, Nat.lt_of_succ_le hm⟩))
  go n (Nat.le_refl n)

def suzukiDF6D4EvenRoundedGalerkinSolveResidualInterval
    (j : Fin 256) (i : Fin 45) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((suzukiDF6D4ResidualAdmissionRound
        (suzukiDF6D4EvenCompleteCrossEntryInterval i j)).sub
      (RationalInterval.fastScaleFinSum
        suzukiDF6D4ResidualAdmissionDenominator
        (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
        (fun k : Fin 256 => suzukiDF6D4ResidualAdmissionRound
          (suzukiDF6D4EvenComparisonGalerkinEntryInterval j k))))

def suzukiDF6D4OddRoundedGalerkinSolveResidualInterval
    (j : Fin 256) (i : Fin 44) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((suzukiDF6D4ResidualAdmissionRound
        (suzukiDF6D4OddCompleteCrossEntryInterval i j)).sub
      (RationalInterval.fastScaleFinSum
        suzukiDF6D4ResidualAdmissionDenominator
        (fun k : Fin 256 => suzukiDF6D4OddGalerkinApproximant k i)
        (fun k : Fin 256 => suzukiDF6D4ResidualAdmissionRound
          (suzukiDF6D4OddComparisonGalerkinEntryInterval j k))))

def suzukiDF6D4EvenRoundedResidualColumnInterval
    (mode : Nat) (i : Fin 45) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((suzukiDF6D4ResidualAdmissionRound
        (suzukiDF6D4FullEvenOffDiagonalInterval
          (suzukiDF6D4EvenLowMode i) mode)).sub
      (RationalInterval.fastScaleFinSum
        suzukiDF6D4ResidualAdmissionDenominator
        (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
        (fun k : Fin 256 => suzukiDF6D4ResidualAdmissionRound
          (suzukiDF6D4ComparisonEvenOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) mode))))

def suzukiDF6D4OddRoundedResidualColumnInterval
    (mode : Nat) (i : Fin 44) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((suzukiDF6D4ResidualAdmissionRound
        (suzukiDF6D4FullOddOffDiagonalInterval
          (suzukiDF6D4OddLowMode i) mode)).sub
      (RationalInterval.fastScaleFinSum
        suzukiDF6D4ResidualAdmissionDenominator
        (fun k : Fin 256 => suzukiDF6D4OddGalerkinApproximant k i)
        (fun k : Fin 256 => suzukiDF6D4ResidualAdmissionRound
          (suzukiDF6D4ComparisonOddOffDiagonalInterval
            (suzukiDF6D4GalerkinMode k) mode))))

def suzukiDF6D4RoundedIntervalMatrixCache
    {m n : Nat} {alpha : Type} [Inhabited alpha]
    (entry : Fin m -> Fin n -> alpha) : Array (Array alpha) :=
  Array.ofFn fun i => Array.ofFn fun j => entry i j

def suzukiDF6D4RoundedIntervalMatrixCacheEntry
    {m n : Nat} {alpha : Type} [Inhabited alpha]
    (cache : Array (Array alpha)) (i : Fin m) (j : Fin n) : alpha :=
  (cache[i.val]!)[j.val]!

def suzukiDF6D4EvenRoundedSolveResidualIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4RoundedIntervalMatrixCache
    suzukiDF6D4EvenRoundedGalerkinSolveResidualInterval

def suzukiDF6D4OddRoundedSolveResidualIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4RoundedIntervalMatrixCache
    suzukiDF6D4OddRoundedGalerkinSolveResidualInterval

def suzukiDF6D4EvenRoundedResidualColumnIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4RoundedIntervalMatrixCache fun r : Fin 300 =>
    suzukiDF6D4EvenRoundedResidualColumnInterval (301 + r.val)

def suzukiDF6D4OddRoundedResidualColumnIntervalCache :
    Array (Array RationalInterval) :=
  suzukiDF6D4RoundedIntervalMatrixCache fun r : Fin 300 =>
    suzukiDF6D4OddRoundedResidualColumnInterval (301 + r.val)

def suzukiDF6D4EvenRoundedGalerkinBaseEntryIntervalFromCache
    (solveResidual : Array (Array RationalInterval))
    (i j : Fin 45) : RationalInterval :=
  (RationalInterval.fastScaleFinSum suzukiDF6D4ResidualAdmissionDenominator
    (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k j)
    (fun k : Fin 256 => suzukiDF6D4ResidualAdmissionRound
      (suzukiDF6D4EvenCompleteCrossEntryInterval i k))).add
  (RationalInterval.fastScaleFinSum suzukiDF6D4ResidualAdmissionDenominator
    (fun k : Fin 256 => suzukiDF6D4EvenGalerkinApproximant k i)
    (fun k : Fin 256 =>
      suzukiDF6D4RoundedIntervalMatrixCacheEntry solveResidual k j))

def suzukiDF6D4OddRoundedGalerkinBaseEntryIntervalFromCache
    (solveResidual : Array (Array RationalInterval))
    (i j : Fin 44) : RationalInterval :=
  (RationalInterval.fastScaleFinSum suzukiDF6D4ResidualAdmissionDenominator
    (fun k : Fin 256 => suzukiDF6D4OddGalerkinApproximant k j)
    (fun k : Fin 256 => suzukiDF6D4ResidualAdmissionRound
      (suzukiDF6D4OddCompleteCrossEntryInterval i k))).add
  (RationalInterval.fastScaleFinSum suzukiDF6D4ResidualAdmissionDenominator
    (fun k : Fin 256 => suzukiDF6D4OddGalerkinApproximant k i)
    (fun k : Fin 256 =>
      suzukiDF6D4RoundedIntervalMatrixCacheEntry solveResidual k j))

def suzukiDF6D4EvenRoundedFiniteResidualGramEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 45) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((suzukiDF6D4RoundedFinSum suzukiDF6D4ResidualAdmissionDenominator
      fun k : Fin 256 =>
        (suzukiDF6D4RoundedIntervalMatrixCacheEntry solveResidual k i).mulCentered
          (suzukiDF6D4RoundedIntervalMatrixCacheEntry solveResidual k j)).add
    (suzukiDF6D4RoundedFinSum suzukiDF6D4ResidualAdmissionDenominator
      fun r : Fin 300 =>
        (suzukiDF6D4RoundedIntervalMatrixCacheEntry residualColumn r i).mulCentered
          (suzukiDF6D4RoundedIntervalMatrixCacheEntry residualColumn r j)))

def suzukiDF6D4OddRoundedFiniteResidualGramEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 44) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((suzukiDF6D4RoundedFinSum suzukiDF6D4ResidualAdmissionDenominator
      fun k : Fin 256 =>
        (suzukiDF6D4RoundedIntervalMatrixCacheEntry solveResidual k i).mulCentered
          (suzukiDF6D4RoundedIntervalMatrixCacheEntry solveResidual k j)).add
    (suzukiDF6D4RoundedFinSum suzukiDF6D4ResidualAdmissionDenominator
      fun r : Fin 300 =>
        (suzukiDF6D4RoundedIntervalMatrixCacheEntry residualColumn r i).mulCentered
          (suzukiDF6D4RoundedIntervalMatrixCacheEntry residualColumn r j)))

def suzukiDF6D4EvenRoundedResidualCertificateTargetEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 45) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((RationalInterval.scale suzukiDF6D4EvenStrictComparisonCoefficient
      (suzukiDF6D4ResidualAdmissionRound
        (suzukiDF6D4EvenEndpointEntryInterval i j))).sub
      (((suzukiDF6D4EvenRoundedGalerkinBaseEntryIntervalFromCache
          solveResidual i j).add
        (RationalInterval.scale (1 / 5)
          (suzukiDF6D4EvenRoundedFiniteResidualGramEntryIntervalFromCaches
            solveResidual residualColumn i j))).add
        (RationalInterval.scale (1 / 5)
          (suzukiDF6D4ResidualAdmissionRound
            (suzukiDF6D4EvenAnalyticTailEntryInterval i j)))))

def suzukiDF6D4OddRoundedResidualCertificateTargetEntryIntervalFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 44) : RationalInterval :=
  suzukiDF6D4ResidualAdmissionRound
    ((RationalInterval.scale suzukiDF6D4OddStrictComparisonCoefficient
      (suzukiDF6D4ResidualAdmissionRound
        (suzukiDF6D4OddEndpointEntryInterval i j))).sub
      (((suzukiDF6D4OddRoundedGalerkinBaseEntryIntervalFromCache
          solveResidual i j).add
        (RationalInterval.scale (1 / 5)
          (suzukiDF6D4OddRoundedFiniteResidualGramEntryIntervalFromCaches
            solveResidual residualColumn i j))).add
        (RationalInterval.scale (1 / 5)
          (suzukiDF6D4ResidualAdmissionRound
            (suzukiDF6D4OddAnalyticTailEntryInterval i j)))))

def suzukiDF6D4EvenRoundedResidualTargetEntryIntervalAdmittedFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 45) : Prop :=
  (suzukiDF6D4EvenResidualTargetCertificate.entry i j).lower <=
      (suzukiDF6D4EvenRoundedResidualCertificateTargetEntryIntervalFromCaches
        solveResidual residualColumn i j).lower /\
    (suzukiDF6D4EvenRoundedResidualCertificateTargetEntryIntervalFromCaches
      solveResidual residualColumn i j).upper <=
      (suzukiDF6D4EvenResidualTargetCertificate.entry i j).upper

def suzukiDF6D4OddRoundedResidualTargetEntryIntervalAdmittedFromCaches
    (solveResidual residualColumn : Array (Array RationalInterval))
    (i j : Fin 44) : Prop :=
  (suzukiDF6D4OddResidualTargetCertificate.entry i j).lower <=
      (suzukiDF6D4OddRoundedResidualCertificateTargetEntryIntervalFromCaches
        solveResidual residualColumn i j).lower /\
    (suzukiDF6D4OddRoundedResidualCertificateTargetEntryIntervalFromCaches
      solveResidual residualColumn i j).upper <=
      (suzukiDF6D4OddResidualTargetCertificate.entry i j).upper

end RiemannHypothesisProject.Experiments.M100
