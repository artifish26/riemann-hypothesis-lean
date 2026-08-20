import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCompleteSineTransformEnclosures

/-!
# Frozen complete sine-transform table for M100-DF6D4

The analytic evaluator is intentionally expensive: every mode includes exact
digamma and restoration prefixes.  This module evaluates those formulas once
for the 45 frozen modes and exposes the resulting exact rational table.  The
table-to-formula theorem is checked by `native_decide`; downstream convolution
grids then reuse the literals instead of normalizing the same prefixes for
every matrix position.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

def suzukiDF6D4CompleteSineTransformIntervalData :
    Array RationalInterval := #[
  ⟨0, 0⟩,
  ⟨(-1129459124772657 / 2000000000000000 : Rat), (-352955976491271 / 625000000000000 : Rat)⟩,
  ⟨(-8657331272387519 / 10000000000000000 : Rat), (-1731466254476329 / 2000000000000000 : Rat)⟩,
  ⟨(-3962611871776097 / 2000000000000000 : Rat), (-990652967943599 / 500000000000000 : Rat)⟩,
  ⟨(-25217444087308657 / 10000000000000000 : Rat), (-25217444087297377 / 10000000000000000 : Rat)⟩,
  ⟨(-2261394891133579 / 1250000000000000 : Rat), (-18091159129054567 / 10000000000000000 : Rat)⟩,
  ⟨(-7645021861336121 / 10000000000000000 : Rat), (-3822510930659449 / 5000000000000000 : Rat)⟩,
  ⟨(-7315540562260079 / 10000000000000000 : Rat), (-182888514056009 / 250000000000000 : Rat)⟩,
  ⟨(-8779017968203321 / 5000000000000000 : Rat), (-17558035936384211 / 10000000000000000 : Rat)⟩,
  ⟨(-1579331575995249 / 625000000000000 : Rat), (-197416446999209 / 78125000000000 : Rat)⟩,
  ⟨(-5146155251022693 / 2500000000000000 : Rat), (-1286538812753919 / 625000000000000 : Rat)⟩,
  ⟨(-595171137269299 / 625000000000000 : Rat), (-9522738196277833 / 10000000000000000 : Rat)⟩,
  ⟨(-6273030093633091 / 10000000000000000 : Rat), (-3136515046799657 / 5000000000000000 : Rat)⟩,
  ⟨(-3002061552793191 / 2000000000000000 : Rat), (-60041231055717 / 40000000000000 : Rat)⟩,
  ⟨(-24544634965802769 / 10000000000000000 : Rat), (-24544634965763109 / 10000000000000000 : Rat)⟩,
  ⟨(-22663324651858189 / 10000000000000000 : Rat), (-22663324651809439 / 10000000000000000 : Rat)⟩,
  ⟨(-2356731169135323 / 2000000000000000 : Rat), (-11783655845630819 / 10000000000000000 : Rat)⟩,
  ⟨(-2927468377309293 / 5000000000000000 : Rat), (-5854936754569617 / 10000000000000000 : Rat)⟩,
  ⟨(-99843393905851 / 80000000000000 : Rat), (-312010605954477 / 250000000000000 : Rat)⟩,
  ⟨(-23172668831133609 / 10000000000000000 : Rat), (-23172668831076449 / 10000000000000000 : Rat)⟩,
  ⟨(-193852747183629 / 80000000000000 : Rat), (-757237293684197 / 312500000000000 : Rat)⟩,
  ⟨(-446979755149107 / 312500000000000 : Rat), (-14303352164708341 / 10000000000000000 : Rat)⟩,
  ⟨(-3057775079379619 / 5000000000000000 : Rat), (-6115550158692199 / 10000000000000000 : Rat)⟩,
  ⟨(-10164870973825421 / 10000000000000000 : Rat), (-1270608871719267 / 1250000000000000 : Rat)⟩,
  ⟨(-21263971465898321 / 10000000000000000 : Rat), (-21263971465822549 / 10000000000000000 : Rat)⟩,
  ⟨(-12594951818225931 / 5000000000000000 : Rat), (-6297475909092833 / 2500000000000000 : Rat)⟩,
  ⟨(-8456536227317909 / 5000000000000000 : Rat), (-8456536227275059 / 5000000000000000 : Rat)⟩,
  ⟨(-1408693999400361 / 2000000000000000 : Rat), (-704346999691057 / 1000000000000000 : Rat)⟩,
  ⟨(-4116164681350013 / 5000000000000000 : Rat), (-8232329362600991 / 10000000000000000 : Rat)⟩,
  ⟨(-18957606323611901 / 10000000000000000 : Rat), (-4739401580877051 / 2500000000000000 : Rat)⟩,
  ⟨(-12737365245769091 / 5000000000000000 : Rat), (-6368682622856877 / 2500000000000000 : Rat)⟩,
  ⟨(-9716216818576787 / 5000000000000000 : Rat), (-19432433637035237 / 10000000000000000 : Rat)⟩,
  ⟨(-8576216232041627 / 10000000000000000 : Rat), (-8576216231910133 / 10000000000000000 : Rat)⟩,
  ⟨(-1705321496405883 / 2500000000000000 : Rat), (-1364257197097581 / 2000000000000000 : Rat)⟩,
  ⟨(-3283610098939857 / 2000000000000000 : Rat), (-1641805049455381 / 1000000000000000 : Rat)⟩,
  ⟨(-25067874770212403 / 10000000000000000 : Rat), (-4010859963209 / 1600000000000 : Rat)⟩,
  ⟨(-21685711617611833 / 10000000000000000 : Rat), (-21685711617443943 / 10000000000000000 : Rat)⟩,
  ⟨(-10607328768696653 / 10000000000000000 : Rat), (-10607328768516079 / 10000000000000000 : Rat)⟩,
  ⟨(-6032349183178281 / 10000000000000000 : Rat), (-6032349182983907 / 10000000000000000 : Rat)⟩,
  ⟨(-432038049881777 / 312500000000000 : Rat), (-13825217596007377 / 10000000000000000 : Rat)⟩,
  ⟨(-5999750299001623 / 2500000000000000 : Rat), (-11999500597890279 / 5000000000000000 : Rat)⟩,
  ⟨(-11757604750981129 / 5000000000000000 : Rat), (-23515209501718059 / 10000000000000000 : Rat)⟩,
  ⟨(-12994662340404927 / 10000000000000000 : Rat), (-649733117007091 / 500000000000000 : Rat)⟩,
  ⟨(-236872598283233 / 400000000000000 : Rat), (-5921814956796731 / 10000000000000000 : Rat)⟩,
  ⟨(-22724644236991 / 20000000000000 : Rat), (-5681161059094267 / 5000000000000000 : Rat)⟩
]

theorem suzukiDF6D4CompleteSineTransformIntervalData_size :
    suzukiDF6D4CompleteSineTransformIntervalData.size = 45 := by
  native_decide

def suzukiDF6D4TabulatedCompleteSineTransformInterval
    (mode : Nat) : RationalInterval :=
  suzukiDF6D4CompleteSineTransformIntervalData[mode]!

theorem suzukiDF6D4TabulatedCompleteSineTransformInterval_endpoints
    (mode : Nat) (hmode : mode ≤ 44) :
    (suzukiDF6D4TabulatedCompleteSineTransformInterval mode).lower =
        (suzukiDF6D4FrozenCompleteSineTransformInterval mode).lower ∧
      (suzukiDF6D4TabulatedCompleteSineTransformInterval mode).upper =
        (suzukiDF6D4FrozenCompleteSineTransformInterval mode).upper := by
  interval_cases mode <;> native_decide

theorem suzukiDF6D4TabulatedCompleteSineTransformInterval_eq
    (mode : Nat) (hmode : mode ≤ 44) :
    suzukiDF6D4TabulatedCompleteSineTransformInterval mode =
      suzukiDF6D4FrozenCompleteSineTransformInterval mode := by
  cases htab : suzukiDF6D4TabulatedCompleteSineTransformInterval mode with
  | mk tabLower tabUpper =>
    cases hfrozen : suzukiDF6D4FrozenCompleteSineTransformInterval mode with
    | mk frozenLower frozenUpper =>
      have h := suzukiDF6D4TabulatedCompleteSineTransformInterval_endpoints
        mode hmode
      simp only [htab, hfrozen] at h
      rcases h with ⟨hlower, hupper⟩
      cases hlower
      cases hupper
      rfl

theorem suzukiDF6D4TabulatedCompleteSineTransformInterval_contains
    (mode : Nat) (hmode : mode ≤ 44) :
    (suzukiDF6D4TabulatedCompleteSineTransformInterval mode).Contains
      (suzukiDF6D4CompleteSineTransform mode) := by
  rw [suzukiDF6D4TabulatedCompleteSineTransformInterval_eq mode hmode]
  exact suzukiDF6D4FrozenCompleteSineTransformInterval_contains mode
    (hmode.trans (by norm_num))

end

end RiemannHypothesisProject.Experiments.M100
