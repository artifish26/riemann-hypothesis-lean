import RiemannHypothesisProject.LiCriterion.ResidualBridgeInput

/-!
# Eventual and finite-window Li positivity targets

This file adds small checked helpers around the abstract Li/Bombieri-Lagarias
interface in `LiCriterion.lean`.

The main analytic obstruction in a Li-style route is proving coefficient
nonnegativity.  The `AbstractLiEventualPositivityData` package splits that
obligation into a finite prefix and an eventual tail.  This is useful for
future work that combines rigorous finite computation with an asymptotic tail
estimate.

The finite-window target records a weaker Palojarvi-style shape: coefficient
positivity on a finite range may imply a named zero-free region.  No such
zeta theorem is proved here; the record makes the future theorem explicit
without pretending it is full RH.
-/

namespace RiemannHypothesisProject

/--
Coefficient nonnegativity split into a finite prefix and an eventual tail.

For a cutoff `N`, future work can prove coefficients `0 < n < N` by a finite
certificate and coefficients `N <= n` by an analytic tail estimate.  Lean then
reconstructs the all-positive-coefficient hypothesis required by
`AbstractLiCriterionData`.
-/
structure AbstractLiEventualPositivityData
    {family : Complex -> Prop}
    (liData : AbstractLiCriterionData family) where
  cutoff : Nat
  prefix_nonneg :
    forall n : Nat, 0 < n -> n < cutoff -> 0 <= liData.coefficient n
  tail_nonneg :
    forall n : Nat, cutoff <= n -> 0 <= liData.coefficient n

namespace AbstractLiEventualPositivityData

/-- Eventual positivity data supplies all Li-coefficient nonnegativity. -/
theorem li_nonneg
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    (data : AbstractLiEventualPositivityData liData) :
    forall n : Nat, 0 < n -> 0 <= liData.coefficient n := by
  intro n hn
  by_cases htail : data.cutoff <= n
  · exact data.tail_nonneg n htail
  · exact data.prefix_nonneg n hn (Nat.lt_of_not_ge htail)

/-- Eventual positivity proves local RH through the packaged Li criterion. -/
theorem RHOn
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    (data : AbstractLiEventualPositivityData liData) :
    RHOn family :=
  liData.RHOn_of_li_nonneg data.li_nonneg

/-- Universal eventual Li positivity proves the project RH statement. -/
theorem RHStatement_univ
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (data : AbstractLiEventualPositivityData liData) :
    RHStatement :=
  liData.RHStatement_of_li_nonneg_univ data.li_nonneg

/-- Universal eventual Li positivity proves Mathlib's RH statement. -/
theorem mathlib_RH_univ
    {liData : AbstractLiCriterionData (fun _ : Complex => True)}
    (data : AbstractLiEventualPositivityData liData) :
    RiemannHypothesis :=
  liData.mathlib_RH_of_li_nonneg_univ data.li_nonneg

end AbstractLiEventualPositivityData

/--
All-coefficients nonnegativity, including index zero, packages as eventual
positivity with cutoff zero.
-/
noncomputable def AbstractLiEventualPositivityData.ofAllNonneg
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    (hli : forall n : Nat, 0 <= liData.coefficient n) :
    AbstractLiEventualPositivityData liData where
  cutoff := 0
  prefix_nonneg := by
    intro n _ hn
    exact False.elim (Nat.not_lt_zero n hn)
  tail_nonneg := by
    intro n _
    exact hli n

/--
For cutoff `2`, the positive finite prefix `0 < n < 2` consists only of
coefficient `1`.
-/
theorem AbstractLiEventualPositivityData.prefix_nonneg_cutoffTwo_of_one_nonneg
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    (coefficient_one_nonneg : 0 <= liData.coefficient 1) :
    forall n : Nat, 0 < n -> n < 2 -> 0 <= liData.coefficient n := by
  intro n hn hlt
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | succ n =>
      cases n with
      | zero =>
          simpa using coefficient_one_nonneg
      | succ n =>
          have htwo : 2 <= Nat.succ (Nat.succ n) :=
            Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
          exact (not_lt_of_ge htwo hlt).elim

/--
Cutoff-2 eventual Li positivity from the single finite-prefix coefficient and
the eventual tail.
-/
noncomputable def AbstractLiEventualPositivityData.ofCutoffTwo
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    (coefficient_one_nonneg : 0 <= liData.coefficient 1)
    (tail_nonneg :
      forall n : Nat, 2 <= n -> 0 <= liData.coefficient n) :
    AbstractLiEventualPositivityData liData where
  cutoff := 2
  prefix_nonneg :=
    AbstractLiEventualPositivityData.prefix_nonneg_cutoffTwo_of_one_nonneg
      coefficient_one_nonneg
  tail_nonneg := tail_nonneg

/--
A finite range of Li coefficients, used for zero-free-region criteria.

The interval is expressed by ordinary natural-number inequalities so later
finite-computation certificates can choose their preferred representation.
-/
def LiCoefficientWindow
    {family : Complex -> Prop}
    (liData : AbstractLiCriterionData family)
    (lower upper : Nat) : Prop :=
  forall n : Nat, lower <= n -> n <= upper -> 0 < n ->
    0 <= liData.coefficient n

/--
A finite-window Li-style criterion for a named zero-free region.

This packages the Palojarvi-style shape: positivity on a finite coefficient
window implies that the chosen zero family has no zero in `region`.
-/
structure AbstractLiFiniteWindowZeroFreeCriterionData
    {family : Complex -> Prop}
    (liData : AbstractLiCriterionData family)
    (region : Complex -> Prop) where
  lowerIndex : Nat
  upperIndex : Nat
  window_nonneg_implies_zeroFree :
    LiCoefficientWindow liData lowerIndex upperIndex ->
      forall z : Complex, family z -> region z -> False

namespace AbstractLiFiniteWindowZeroFreeCriterionData

/-- Coefficient nonnegativity on the packaged window proves the zero-free claim. -/
theorem zeroFree
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    {region : Complex -> Prop}
    (data : AbstractLiFiniteWindowZeroFreeCriterionData liData region)
    (hwindow : LiCoefficientWindow liData data.lowerIndex data.upperIndex) :
    forall z : Complex, family z -> region z -> False :=
  data.window_nonneg_implies_zeroFree hwindow

/--
All positive-index coefficient nonnegativity supplies any finite coefficient
window.  This lets a full Li-positivity proof feed finite-window criteria too.
-/
theorem window_nonneg_of_li_nonneg
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    {lower upper : Nat}
    (hli : forall n : Nat, 0 < n -> 0 <= liData.coefficient n) :
    LiCoefficientWindow liData lower upper := by
  intro n _ _ hn
  exact hli n hn

/-- Full Li nonnegativity proves the packaged finite-window zero-free claim. -/
theorem zeroFree_of_li_nonneg
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    {region : Complex -> Prop}
    (data : AbstractLiFiniteWindowZeroFreeCriterionData liData region)
    (hli : forall n : Nat, 0 < n -> 0 <= liData.coefficient n) :
    forall z : Complex, family z -> region z -> False :=
  data.zeroFree (window_nonneg_of_li_nonneg hli)

/-- Eventual Li positivity proves the packaged finite-window zero-free claim. -/
theorem zeroFree_of_eventual
    {family : Complex -> Prop}
    {liData : AbstractLiCriterionData family}
    {region : Complex -> Prop}
    (data : AbstractLiFiniteWindowZeroFreeCriterionData liData region)
    (eventual : AbstractLiEventualPositivityData liData) :
    forall z : Complex, family z -> region z -> False :=
  data.zeroFree_of_li_nonneg eventual.li_nonneg

end AbstractLiFiniteWindowZeroFreeCriterionData

end RiemannHypothesisProject
