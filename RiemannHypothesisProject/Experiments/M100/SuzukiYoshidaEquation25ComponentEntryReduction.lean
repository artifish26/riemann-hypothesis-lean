import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaEquation25EndpointKernelEvaluation
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointFullConvolutionEnclosures

/-!
# Component reduction for the equation-(2.5) endpoint evaluation

This module refines the residual B3Q-E source evaluation into the component
families already visible in the exact DF6D4 formulas.  It proves the scalar
mass contribution from endpoint-mode orthonormality and leaves only:

* the comparison-transform and prime/Gamma correction evaluations off the
  diagonal; and
* the prime and pole/constant/Gamma evaluations on the diagonal.

The component propositions are citation-facing theorem targets.  None contains
the complete corrected entry equality that the final theorem proves.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped ComplexConjugate

private abbrev evenCompletion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) : SuzukiYoshidaCorrectedCommonFormDomain :=
  suzukiYoshidaEvenLinearCompletionOfSource
    hsource suzukiProjectAStar_pos mode

private abbrev oddCompletion
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (mode : Nat) : SuzukiYoshidaCorrectedCommonFormDomain :=
  suzukiYoshidaOddLinearCompletionOfSource
    hsource suzukiProjectAStar_pos mode

/-! ## Source-limit pairings are completed-form pairings -/

theorem suzukiYoshidaCorrectedCompleteForm_evenSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (m n : Nat) :
    suzukiYoshidaCorrectedCompleteForm
        (evenCompletion hsource m) (evenCompletion hsource n) =
      suzukiYoshidaEvenSourceKernelPairing
        (suzukiYoshidaEquation25LimitKernel hsource) m n := by
  unfold evenCompletion
    suzukiYoshidaEvenLinearCompletionOfSource
    suzukiYoshidaEvenSourceKernelPairing
  split_ifs with hm hn hn
  · simpa using
      suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
        hsource hequation25 0 0
  · rw [suzukiYoshidaCorrectedCompleteForm_smul_right,
      suzukiYoshidaCorrectedCompleteForm_add_right]
    simp_rw [
      suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
        hsource hequation25]
  · rw [suzukiYoshidaCorrectedCompleteForm_smul_left,
      suzukiYoshidaCorrectedCompleteForm_add_left]
    simp_rw [
      suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
        hsource hequation25]
  · rw [suzukiYoshidaCorrectedCompleteForm_smul_left,
      suzukiYoshidaCorrectedCompleteForm_smul_right,
      suzukiYoshidaCorrectedCompleteForm_add_left,
      suzukiYoshidaCorrectedCompleteForm_add_right,
      suzukiYoshidaCorrectedCompleteForm_add_right]
    simp_rw [
      suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
        hsource hequation25]
    ring

private theorem suzukiYoshidaCorrectedCompleteForm_sub_left'
    (u w v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm (u - w) v =
      suzukiYoshidaCorrectedCompleteForm u v -
        suzukiYoshidaCorrectedCompleteForm w v := by
  rw [sub_eq_add_neg,
    suzukiYoshidaCorrectedCompleteForm_add_left,
    suzukiYoshidaCorrectedCompleteForm_neg_left]
  rfl

private theorem suzukiYoshidaCorrectedCompleteForm_sub_right'
    (u v w : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u (v - w) =
      suzukiYoshidaCorrectedCompleteForm u v -
        suzukiYoshidaCorrectedCompleteForm u w := by
  rw [sub_eq_add_neg,
    suzukiYoshidaCorrectedCompleteForm_add_right,
    suzukiYoshidaCorrectedCompleteForm_neg_right]
  rfl

theorem suzukiYoshidaCorrectedCompleteForm_oddSource
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (m n : Nat) :
    suzukiYoshidaCorrectedCompleteForm
        (oddCompletion hsource m) (oddCompletion hsource n) =
      suzukiYoshidaOddSourceKernelPairing
        (suzukiYoshidaEquation25LimitKernel hsource) m n := by
  unfold oddCompletion
    suzukiYoshidaOddLinearCompletionOfSource
    suzukiYoshidaOddSourceKernelPairing
  rw [suzukiYoshidaCorrectedCompleteForm_smul_left,
    suzukiYoshidaCorrectedCompleteForm_smul_right,
    suzukiYoshidaCorrectedCompleteForm_sub_left',
    suzukiYoshidaCorrectedCompleteForm_sub_right',
    suzukiYoshidaCorrectedCompleteForm_sub_right']
  simp_rw [
    suzukiYoshidaCorrectedCompleteForm_exponential_eq_limitKernel
      hsource hequation25]
  ring

/-! ## The scalar component is unconditional -/

theorem inner_evenCompletion_toL2
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (m n : Nat) :
    inner Complex
        (suzukiLogRadiusLinearCompletionToL2 (evenCompletion hsource m))
        (suzukiLogRadiusLinearCompletionToL2 (evenCompletion hsource n)) =
      if m = n then 1 else 0 := by
  rw [suzukiYoshidaEvenLinearCompletionOfSource_toL2,
    suzukiYoshidaEvenLinearCompletionOfSource_toL2]
  exact inner_suzukiYoshidaEvenL2_eq_ite suzukiProjectAStar_pos m n

theorem inner_oddCompletion_toL2
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    {m n : Nat} (hm : 0 < m) (hn : 0 < n) :
    inner Complex
        (suzukiLogRadiusLinearCompletionToL2 (oddCompletion hsource m))
        (suzukiLogRadiusLinearCompletionToL2 (oddCompletion hsource n)) =
      if m = n then 1 else 0 := by
  rw [suzukiYoshidaOddLinearCompletionOfSource_toL2,
    suzukiYoshidaOddLinearCompletionOfSource_toL2]
  exact inner_suzukiYoshidaOddL2_eq_ite
    suzukiProjectAStar_pos hm hn

/-! ## Narrow remaining analytic component targets -/

/-- Ordered even comparison-form evaluation by the exact DF6D4 comparison
transform convolution. -/
def SuzukiEquation25EvenOffDiagonalComparisonEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, left < right →
    suzukiYoshidaComparisonForm
        (evenCompletion hsource left) (evenCompletion hsource right) =
      (suzukiDF6D4ComparisonEvenOffDiagonal left right : Complex)

/-- Ordered even prime/Gamma correction.  The right side is the literal
difference between the independently defined complete and comparison
convolutions. -/
def SuzukiEquation25EvenOffDiagonalCorrectionEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, left < right →
    suzukiYoshidaPrimeTwoForm
        (evenCompletion hsource left) (evenCompletion hsource right) -
      suzukiYoshidaGammaRemainderForm
        (evenCompletion hsource left) (evenCompletion hsource right) =
      ((suzukiDF6D4EvenOffDiagonal left right -
        suzukiDF6D4ComparisonEvenOffDiagonal left right : Real) : Complex)

/-- Ordered positive odd comparison-form evaluation. -/
def SuzukiEquation25OddOffDiagonalComparisonEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, 0 < left → left < right →
    suzukiYoshidaComparisonForm
        (oddCompletion hsource left) (oddCompletion hsource right) =
      (suzukiDF6D4ComparisonOddOffDiagonal left right : Complex)

/-- Ordered positive odd prime/Gamma correction. -/
def SuzukiEquation25OddOffDiagonalCorrectionEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ left right : Nat, 0 < left → left < right →
    suzukiYoshidaPrimeTwoForm
        (oddCompletion hsource left) (oddCompletion hsource right) -
      suzukiYoshidaGammaRemainderForm
        (oddCompletion hsource left) (oddCompletion hsource right) =
      ((suzukiDF6D4OddOffDiagonal left right -
        suzukiDF6D4ComparisonOddOffDiagonal left right : Real) : Complex)

/-- Exact even prime-translation diagonal evaluation. -/
def SuzukiEquation25EvenDiagonalPrimeEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ mode : Nat,
    suzukiYoshidaPrimeTwoForm
        (evenCompletion hsource mode) (evenCompletion hsource mode) =
      (suzukiDF6D4EvenDiagonalPrimeTerm mode : Complex)

/-- Even diagonal pole/constant/Gamma evaluation before cancellation of the
source normalization scalar. -/
def SuzukiEquation25EvenDiagonalArchimedeanEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ mode : Nat,
    suzukiYoshidaComparisonForm
        (evenCompletion hsource mode) (evenCompletion hsource mode) -
      suzukiYoshidaGammaRemainderForm
        (evenCompletion hsource mode) (evenCompletion hsource mode) =
      ((suzukiDF6D4EvenDiagonalPoleTerm mode +
          suzukiDF6D4DiagonalConstantTerm +
          suzukiDF6D4EvenDiagonalGammaTerm mode +
          suzukiSourceLogNormalizationConstant : Real) : Complex)

/-- Exact positive odd prime-translation diagonal evaluation. -/
def SuzukiEquation25OddDiagonalPrimeEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ mode : Nat, 0 < mode →
    suzukiYoshidaPrimeTwoForm
        (oddCompletion hsource mode) (oddCompletion hsource mode) =
      (suzukiDF6D4OddDiagonalPrimeTerm mode : Complex)

/-- Positive odd diagonal pole/constant/Gamma evaluation before cancellation
of the source normalization scalar. -/
def SuzukiEquation25OddDiagonalArchimedeanEvaluation
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar) : Prop :=
  ∀ mode : Nat, 0 < mode →
    suzukiYoshidaComparisonForm
        (oddCompletion hsource mode) (oddCompletion hsource mode) -
      suzukiYoshidaGammaRemainderForm
        (oddCompletion hsource mode) (oddCompletion hsource mode) =
      ((suzukiDF6D4OddDiagonalPoleTerm mode +
          suzukiDF6D4DiagonalConstantTerm +
          suzukiDF6D4OddDiagonalGammaTerm mode +
          suzukiSourceLogNormalizationConstant : Real) : Complex)

/-! ## Component assembly -/

private theorem correctedEvenForm_eq_offDiagonal_of_lt
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hcomparison :
      SuzukiEquation25EvenOffDiagonalComparisonEvaluation hsource)
    (hcorrection :
      SuzukiEquation25EvenOffDiagonalCorrectionEvaluation hsource)
    {left right : Nat} (hlt : left < right) :
    suzukiYoshidaCorrectedCompleteForm
        (evenCompletion hsource left) (evenCompletion hsource right) =
      (suzukiYoshidaCorrectedEvenEntry left right : Complex) := by
  have hinner := inner_evenCompletion_toL2 hsource left right
  rw [if_neg (Nat.ne_of_lt hlt)] at hinner
  rw [suzukiYoshidaCorrectedCompleteForm,
    hcomparison left right hlt, hinner]
  have hcorr := hcorrection left right hlt
  simp [suzukiYoshidaCorrectedEvenEntry, Nat.ne_of_lt hlt,
    Nat.min_eq_left hlt.le, Nat.max_eq_right hlt.le]
  push_cast at hcorr
  linear_combination hcorr

private theorem correctedOddForm_eq_offDiagonal_of_lt
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hcomparison :
      SuzukiEquation25OddOffDiagonalComparisonEvaluation hsource)
    (hcorrection :
      SuzukiEquation25OddOffDiagonalCorrectionEvaluation hsource)
    {left right : Nat} (hleft : 0 < left) (hlt : left < right) :
    suzukiYoshidaCorrectedCompleteForm
        (oddCompletion hsource left) (oddCompletion hsource right) =
      (suzukiYoshidaCorrectedOddEntry left right : Complex) := by
  have hinner :=
    inner_oddCompletion_toL2 hsource hleft (hleft.trans hlt)
  rw [if_neg (Nat.ne_of_lt hlt)] at hinner
  rw [suzukiYoshidaCorrectedCompleteForm,
    hcomparison left right hleft hlt, hinner]
  have hcorr := hcorrection left right hleft hlt
  simp [suzukiYoshidaCorrectedOddEntry, Nat.ne_of_lt hlt,
    Nat.min_eq_left hlt.le, Nat.max_eq_right hlt.le]
  push_cast at hcorr
  linear_combination hcorr

private theorem correctedEvenForm_eq_diagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hprime : SuzukiEquation25EvenDiagonalPrimeEvaluation hsource)
    (harchimedean :
      SuzukiEquation25EvenDiagonalArchimedeanEvaluation hsource)
    (mode : Nat) :
    suzukiYoshidaCorrectedCompleteForm
        (evenCompletion hsource mode) (evenCompletion hsource mode) =
      (suzukiYoshidaCorrectedEvenEntry mode mode : Complex) := by
  have hinner := inner_evenCompletion_toL2 hsource mode mode
  rw [if_pos rfl] at hinner
  rw [suzukiYoshidaCorrectedCompleteForm]
  have harch := harchimedean mode
  have hp := hprime mode
  rw [hinner]
  rw [suzukiYoshidaCorrectedEvenEntry, if_pos rfl,
    suzukiDF6D4EvenDiagonalEntry]
  push_cast at harch ⊢
  linear_combination harch + hp

private theorem correctedOddForm_eq_diagonal
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hprime : SuzukiEquation25OddDiagonalPrimeEvaluation hsource)
    (harchimedean :
      SuzukiEquation25OddDiagonalArchimedeanEvaluation hsource)
    {mode : Nat} (hmode : 0 < mode) :
    suzukiYoshidaCorrectedCompleteForm
        (oddCompletion hsource mode) (oddCompletion hsource mode) =
      (suzukiYoshidaCorrectedOddEntry mode mode : Complex) := by
  have hinner := inner_oddCompletion_toL2 hsource hmode hmode
  rw [if_pos rfl] at hinner
  rw [suzukiYoshidaCorrectedCompleteForm]
  have harch := harchimedean mode hmode
  have hp := hprime mode hmode
  rw [hinner]
  rw [suzukiYoshidaCorrectedOddEntry, if_pos rfl,
    suzukiDF6D4OddDiagonalEntry]
  push_cast at harch ⊢
  linear_combination harch + hp

/-- The eight visible source-component families imply both all-mode B3Q-E
parity evaluations.  Scalar mass is not an input: it was evaluated above from
orthonormality. -/
theorem suzukiEquation25ParityEntries_of_componentEvaluations
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 :
      SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (hevenComparison :
      SuzukiEquation25EvenOffDiagonalComparisonEvaluation hsource)
    (hevenCorrection :
      SuzukiEquation25EvenOffDiagonalCorrectionEvaluation hsource)
    (hoddComparison :
      SuzukiEquation25OddOffDiagonalComparisonEvaluation hsource)
    (hoddCorrection :
      SuzukiEquation25OddOffDiagonalCorrectionEvaluation hsource)
    (hevenPrime : SuzukiEquation25EvenDiagonalPrimeEvaluation hsource)
    (hevenArchimedean :
      SuzukiEquation25EvenDiagonalArchimedeanEvaluation hsource)
    (hoddPrime : SuzukiEquation25OddDiagonalPrimeEvaluation hsource)
    (hoddArchimedean :
      SuzukiEquation25OddDiagonalArchimedeanEvaluation hsource) :
    SuzukiEquation25EvenYoshidaEntryEvaluation hsource ∧
      SuzukiEquation25OddYoshidaEntryEvaluation hsource := by
  constructor
  · intro m n
    rw [← suzukiYoshidaCorrectedCompleteForm_evenSource
      hsource hequation25]
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · exact correctedEvenForm_eq_offDiagonal_of_lt
        hsource hevenComparison hevenCorrection hlt
    · exact correctedEvenForm_eq_diagonal
        hsource hevenPrime hevenArchimedean m
    · calc
        suzukiYoshidaCorrectedCompleteForm
              (evenCompletion hsource m) (evenCompletion hsource n) =
            conj (suzukiYoshidaCorrectedCompleteForm
              (evenCompletion hsource n) (evenCompletion hsource m)) :=
          suzukiYoshidaCorrectedCompleteForm_conj_symm _ _
        _ = conj (suzukiYoshidaCorrectedEvenEntry n m : Complex) := by
          rw [correctedEvenForm_eq_offDiagonal_of_lt
            hsource hevenComparison hevenCorrection hgt]
        _ = (suzukiYoshidaCorrectedEvenEntry m n : Complex) := by
          simp [suzukiYoshidaCorrectedEvenEntry_comm]
  · intro m n hm hn
    rw [← suzukiYoshidaCorrectedCompleteForm_oddSource
      hsource hequation25]
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · exact correctedOddForm_eq_offDiagonal_of_lt
        hsource hoddComparison hoddCorrection hm hlt
    · exact correctedOddForm_eq_diagonal
        hsource hoddPrime hoddArchimedean hm
    · calc
        suzukiYoshidaCorrectedCompleteForm
              (oddCompletion hsource m) (oddCompletion hsource n) =
            conj (suzukiYoshidaCorrectedCompleteForm
              (oddCompletion hsource n) (oddCompletion hsource m)) :=
          suzukiYoshidaCorrectedCompleteForm_conj_symm _ _
        _ = conj (suzukiYoshidaCorrectedOddEntry n m : Complex) := by
          rw [correctedOddForm_eq_offDiagonal_of_lt
            hsource hoddComparison hoddCorrection hn hgt]
        _ = (suzukiYoshidaCorrectedOddEntry m n : Complex) := by
          simp [suzukiYoshidaCorrectedOddEntry_comm]

end

end RiemannHypothesisProject.Experiments.M100
