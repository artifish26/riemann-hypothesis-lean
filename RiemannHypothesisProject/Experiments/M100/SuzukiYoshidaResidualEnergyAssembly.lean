import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaResidualGramTail
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointComplexCoordinates
import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaNegativeWeightLoss

/-!
# Final comparison-energy assembly for B3R-E

This module complexifies the checked residual-representer bound and combines
it with the exact parity-far comparison-energy receiver.  The final endpoints
are the two B3R-E low-to-far estimates consumed by the later actual-form B3R
conversion.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open scoped BigOperators ComplexConjugate

private theorem suzukiDF6D5B3REEvenActualResidualRepresenter_inner_im
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x y : Fin 45 → Real) :
    (inner Complex
      (∑ i : Fin 45, (x i : Complex) •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i)
      (∑ i : Fin 45, (y i : Complex) •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i)).im = 0 := by
  letI : CompleteSpace SuzukiDF6D5B3REvenAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TEvenAmbientFarSubspace.completeSpace_coe
  let u := ∑ i : Fin 45, (x i : Complex) •
    suzukiDF6D5B3REEvenActualResidualRepresenter hsource i
  let v := ∑ i : Fin 45, (y i : Complex) •
    suzukiDF6D5B3REEvenActualResidualRepresenter hsource i
  have hparseval :=
    suzukiDF6D5B3REvenAmbientHilbertBasis.tsum_inner_mul_inner u v
  have hterm (n : SuzukiDF6D5B3RTailMode) :
      inner Complex u (suzukiDF6D5B3REvenAmbientHilbertBasis n) *
          inner Complex (suzukiDF6D5B3REvenAmbientHilbertBasis n) v =
        (((∑ i : Fin 45,
            x i * suzukiDF6D5B3REvenFullResidualCoefficient i n) *
          (∑ i : Fin 45,
            y i * suzukiDF6D5B3REvenFullResidualCoefficient i n) : Real) :
              Complex) := by
    have hx :=
      suzukiDF6D5B3REEvenActualResidualRepresenter_sum_coefficient
        hsource hequation25 x n
    have hy :=
      suzukiDF6D5B3REEvenActualResidualRepresenter_sum_coefficient
        hsource hequation25 y n
    rw [← inner_conj_symm]
    change (starRingEnd Complex) (inner Complex
        (suzukiDF6D5B3REvenAmbientHilbertBasis n) u) *
      inner Complex (suzukiDF6D5B3REvenAmbientHilbertBasis n) v = _
    rw [show u = ∑ i : Fin 45, (x i : Complex) •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i by rfl,
      show v = ∑ i : Fin 45, (y i : Complex) •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i by rfl,
      hx, hy]
    simp
  rw [tsum_congr hterm] at hparseval
  have hs :=
    suzukiDF6D5B3REvenAmbientHilbertBasis.summable_inner_mul_inner u v
  have hs' : Summable fun n : SuzukiDF6D5B3RTailMode =>
      (((∑ i : Fin 45,
          x i * suzukiDF6D5B3REvenFullResidualCoefficient i n) *
        (∑ i : Fin 45,
          y i * suzukiDF6D5B3REvenFullResidualCoefficient i n) : Real) :
            Complex) := hs.congr hterm
  calc
    (inner Complex u v).im =
        (∑' n : SuzukiDF6D5B3RTailMode,
          (((∑ i : Fin 45,
              x i * suzukiDF6D5B3REvenFullResidualCoefficient i n) *
            (∑ i : Fin 45,
              y i * suzukiDF6D5B3REvenFullResidualCoefficient i n) : Real) :
                Complex)).im := by rw [hparseval]
    _ = 0 := by rw [Complex.im_tsum hs']; simp

private theorem suzukiDF6D5B3REOddActualResidualRepresenter_inner_im
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (x y : Fin 44 → Real) :
    (inner Complex
      (∑ i : Fin 44, (x i : Complex) •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i)
      (∑ i : Fin 44, (y i : Complex) •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i)).im = 0 := by
  letI : CompleteSpace SuzukiDF6D5B3ROddAmbientFarL2 :=
    isClosed_suzukiDF6D5B3TOddAmbientFarSubspace.completeSpace_coe
  let u := ∑ i : Fin 44, (x i : Complex) •
    suzukiDF6D5B3REOddActualResidualRepresenter hsource i
  let v := ∑ i : Fin 44, (y i : Complex) •
    suzukiDF6D5B3REOddActualResidualRepresenter hsource i
  have hparseval :=
    suzukiDF6D5B3ROddAmbientHilbertBasis.tsum_inner_mul_inner u v
  have hterm (n : SuzukiDF6D5B3RTailMode) :
      inner Complex u (suzukiDF6D5B3ROddAmbientHilbertBasis n) *
          inner Complex (suzukiDF6D5B3ROddAmbientHilbertBasis n) v =
        (((∑ i : Fin 44,
            x i * suzukiDF6D5B3ROddFullResidualCoefficient i n) *
          (∑ i : Fin 44,
            y i * suzukiDF6D5B3ROddFullResidualCoefficient i n) : Real) :
              Complex) := by
    have hx :=
      suzukiDF6D5B3REOddActualResidualRepresenter_sum_coefficient
        hsource hequation25 x n
    have hy :=
      suzukiDF6D5B3REOddActualResidualRepresenter_sum_coefficient
        hsource hequation25 y n
    rw [← inner_conj_symm]
    change (starRingEnd Complex) (inner Complex
        (suzukiDF6D5B3ROddAmbientHilbertBasis n) u) *
      inner Complex (suzukiDF6D5B3ROddAmbientHilbertBasis n) v = _
    rw [show u = ∑ i : Fin 44, (x i : Complex) •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i by rfl,
      show v = ∑ i : Fin 44, (y i : Complex) •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i by rfl,
      hx, hy]
    simp
  rw [tsum_congr hterm] at hparseval
  have hs :=
    suzukiDF6D5B3ROddAmbientHilbertBasis.summable_inner_mul_inner u v
  have hs' : Summable fun n : SuzukiDF6D5B3RTailMode =>
      (((∑ i : Fin 44,
          x i * suzukiDF6D5B3ROddFullResidualCoefficient i n) *
        (∑ i : Fin 44,
          y i * suzukiDF6D5B3ROddFullResidualCoefficient i n) : Real) :
            Complex) := hs.congr hterm
  calc
    (inner Complex u v).im =
        (∑' n : SuzukiDF6D5B3RTailMode,
          (((∑ i : Fin 44,
              x i * suzukiDF6D5B3ROddFullResidualCoefficient i n) *
            (∑ i : Fin 44,
              y i * suzukiDF6D5B3ROddFullResidualCoefficient i n) : Real) :
                Complex)).im := by rw [hparseval]
    _ = 0 := by rw [Complex.im_tsum hs']; simp

theorem suzukiDF6D5B3REEvenActualResidualRepresenter_complex_norm_sq_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : Fin 45 → Complex) :
    ‖∑ i : Fin 45, z i •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i‖ ^ 2 ≤
      suzukiDF6D5ComplexMatrixQuadratic
        (suzukiDF6D4EvenFiniteResidualGramMatrix +
          suzukiDF6D4EvenAnalyticTailMatrix) z := by
  let u := ∑ i : Fin 45, ((z i).re : Complex) •
    suzukiDF6D5B3REEvenActualResidualRepresenter hsource i
  let v := ∑ i : Fin 45, ((z i).im : Complex) •
    suzukiDF6D5B3REEvenActualResidualRepresenter hsource i
  have hsum :
      (∑ i : Fin 45, z i •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i) =
        u + Complex.I • v := by
    calc
      _ = ∑ i : Fin 45,
          (((z i).re : Complex) •
              suzukiDF6D5B3REEvenActualResidualRepresenter hsource i +
            Complex.I • (((z i).im : Complex) •
              suzukiDF6D5B3REEvenActualResidualRepresenter hsource i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_smul, ← add_smul]
          congr 1
          apply Complex.ext <;> simp
      _ = u + Complex.I • v := by
        simp [u, v, Finset.sum_add_distrib, Finset.smul_sum]
  have hcross : (inner Complex u (Complex.I • v)).re = 0 := by
    have him : (inner Complex u v).im = 0 := by
      simpa [u, v] using
        (suzukiDF6D5B3REEvenActualResidualRepresenter_inner_im
          hsource hequation25 (fun i => (z i).re) (fun i => (z i).im))
    have himAmbient :
        (inner Complex (u : SuzukiL2) (v : SuzukiL2)).im = 0 := by
      rw [← suzukiDF6D5B3TEvenAmbientFarSubspace.coe_inner]
      exact him
    rw [@inner_smul_right Complex SuzukiDF6D5B3REvenAmbientFarL2
      _ _ _ _ _ _]
    rw [Complex.mul_re]
    simp [himAmbient]
  have hnorm : ‖u + Complex.I • v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [@norm_add_sq Complex _ _ _ _ u (Complex.I • v)]
    change ‖u‖ ^ 2 + 2 * (inner Complex u (Complex.I • v)).re +
      ‖Complex.I • v‖ ^ 2 = _
    rw [hcross, norm_smul]
    simp
  rw [hsum, hnorm]
  rw [suzukiDF6D5ComplexMatrixQuadratic_re_im]
  have hre := suzukiDF6D5B3REEvenActualResidualRepresenter_norm_sq_le
    hsource hequation25 (fun i => (z i).re)
  have him := suzukiDF6D5B3REEvenActualResidualRepresenter_norm_sq_le
    hsource hequation25 (fun i => (z i).im)
  simp only [suzukiDF6D5MatrixQuadratic, Matrix.add_mulVec,
    dotProduct_add] at ⊢
  linarith

theorem suzukiDF6D5B3REOddActualResidualRepresenter_complex_norm_sq_le
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : Fin 44 → Complex) :
    ‖∑ i : Fin 44, z i •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i‖ ^ 2 ≤
      suzukiDF6D5ComplexMatrixQuadratic
        (suzukiDF6D4OddFiniteResidualGramMatrix +
          suzukiDF6D4OddAnalyticTailMatrix) z := by
  let u := ∑ i : Fin 44, ((z i).re : Complex) •
    suzukiDF6D5B3REOddActualResidualRepresenter hsource i
  let v := ∑ i : Fin 44, ((z i).im : Complex) •
    suzukiDF6D5B3REOddActualResidualRepresenter hsource i
  have hsum :
      (∑ i : Fin 44, z i •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i) =
        u + Complex.I • v := by
    calc
      _ = ∑ i : Fin 44,
          (((z i).re : Complex) •
              suzukiDF6D5B3REOddActualResidualRepresenter hsource i +
            Complex.I • (((z i).im : Complex) •
              suzukiDF6D5B3REOddActualResidualRepresenter hsource i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [smul_smul, ← add_smul]
          congr 1
          apply Complex.ext <;> simp
      _ = u + Complex.I • v := by
        simp [u, v, Finset.sum_add_distrib, Finset.smul_sum]
  have hcross : (inner Complex u (Complex.I • v)).re = 0 := by
    have him : (inner Complex u v).im = 0 := by
      simpa [u, v] using
        (suzukiDF6D5B3REOddActualResidualRepresenter_inner_im
          hsource hequation25 (fun i => (z i).re) (fun i => (z i).im))
    have himAmbient :
        (inner Complex (u : SuzukiL2) (v : SuzukiL2)).im = 0 := by
      rw [← suzukiDF6D5B3TOddAmbientFarSubspace.coe_inner]
      exact him
    rw [@inner_smul_right Complex SuzukiDF6D5B3ROddAmbientFarL2
      _ _ _ _ _ _]
    rw [Complex.mul_re]
    simp [himAmbient]
  have hnorm : ‖u + Complex.I • v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
    rw [@norm_add_sq Complex _ _ _ _ u (Complex.I • v)]
    change ‖u‖ ^ 2 + 2 * (inner Complex u (Complex.I • v)).re +
      ‖Complex.I • v‖ ^ 2 = _
    rw [hcross, norm_smul]
    simp
  rw [hsum, hnorm]
  rw [suzukiDF6D5ComplexMatrixQuadratic_re_im]
  have hre := suzukiDF6D5B3REOddActualResidualRepresenter_norm_sq_le
    hsource hequation25 (fun i => (z i).re)
  have him := suzukiDF6D5B3REOddActualResidualRepresenter_norm_sq_le
    hsource hequation25 (fun i => (z i).im)
  simp only [suzukiDF6D5MatrixQuadratic, Matrix.add_mulVec,
    dotProduct_add] at ⊢
  linarith

/-! ## Residual functionals on exact graph-completion receivers -/

def suzukiDF6D5B3REEvenAmbientOfParityFar
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (v : SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    SuzukiDF6D5B3REvenAmbientFarL2 := by
  refine ⟨suzukiLogRadiusLinearCompletionToL2 v.1, ?_⟩
  apply suzukiProjectB3T_evenParityFarL2Subspace_le_ambient_of_source hsource
  exact ⟨v.1, v.2, rfl⟩

def suzukiDF6D5B3REOddAmbientOfParityFar
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (v : SuzukiB2EndpointModeCertificate.OddParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    SuzukiDF6D5B3ROddAmbientFarL2 := by
  refine ⟨suzukiLogRadiusLinearCompletionToL2 v.1, ?_⟩
  apply suzukiProjectB3T_oddParityFarL2Subspace_le_ambient_of_source hsource
  exact ⟨v.1, v.2, rfl⟩

/-! ## Canonical Galerkin trials in the exact graph receiver -/

private theorem suzukiDF6D5B3REEvenGalerkinModeCompletion_mem
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (k : Fin 256) :
    suzukiYoshidaEvenLinearCompletionOfSource hsource
        suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) ∈
      SuzukiB2EndpointModeCertificate.evenParityFarSubspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  have himage :=
    suzukiYoshidaEvenL2_mem_source_evenParityFarL2Subspace hsource
      (⟨suzukiDF6D4GalerkinMode k, by
        simp [suzukiDF6D4GalerkinMode]⟩ : {n : Nat // 45 ≤ n})
  rw [SuzukiB2EndpointModeCertificate.evenParityFarL2Subspace] at himage
  rcases himage with ⟨w, hw, hwt⟩
  have heq :
      suzukiYoshidaEvenLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) = w := by
    apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
    rw [suzukiYoshidaEvenLinearCompletionOfSource_toL2]
    simpa using hwt.symm
  simpa [heq] using hw

private theorem suzukiDF6D5B3REOddGalerkinModeCompletion_mem
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (k : Fin 256) :
    suzukiYoshidaOddLinearCompletionOfSource hsource
        suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) ∈
      SuzukiB2EndpointModeCertificate.oddParityFarSubspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  have himage :=
    suzukiYoshidaOddL2_mem_source_oddParityFarL2Subspace hsource
      (⟨suzukiDF6D4GalerkinMode k, by
        simp [suzukiDF6D4GalerkinMode]⟩ : {n : Nat // 45 ≤ n})
  rw [SuzukiB2EndpointModeCertificate.oddParityFarL2Subspace] at himage
  rcases himage with ⟨w, hw, hwt⟩
  have heq :
      suzukiYoshidaOddLinearCompletionOfSource hsource
          suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) = w := by
    apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
    rw [suzukiYoshidaOddLinearCompletionOfSource_toL2]
    simpa using hwt.symm
  simpa [heq] using hw

private theorem suzukiDF6D5B3REEvenGalerkinTrialCompletion_mem
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 45) :
    suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i ∈
      SuzukiB2EndpointModeCertificate.evenParityFarSubspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  unfold suzukiDF6D5B3REEvenGalerkinTrialCompletion
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _
    (suzukiDF6D5B3REEvenGalerkinModeCompletion_mem hsource k)

private theorem suzukiDF6D5B3REOddGalerkinTrialCompletion_mem
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i : Fin 44) :
    suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i ∈
      SuzukiB2EndpointModeCertificate.oddParityFarSubspace
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  unfold suzukiDF6D5B3REOddGalerkinTrialCompletion
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _
    (suzukiDF6D5B3REOddGalerkinModeCompletion_mem hsource k)

def suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : Fin 45 → Complex) :
    SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  refine ⟨∑ i : Fin 45, z i •
    suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i, ?_⟩
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (suzukiDF6D5B3REEvenGalerkinTrialCompletion_mem hsource i)

def suzukiDF6D5B3REOddGalerkinTrialOfCoordinates
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : Fin 44 → Complex) :
    SuzukiB2EndpointModeCertificate.OddParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource) := by
  refine ⟨∑ i : Fin 44, z i •
    suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i, ?_⟩
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _
    (suzukiDF6D5B3REOddGalerkinTrialCompletion_mem hsource i)

private theorem suzukiYoshidaCorrectedCompleteForm_fintype_sum_left
    {ι : Type*} [Fintype ι]
    (f : ι → SuzukiYoshidaCorrectedCommonFormDomain)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm (∑ i, f i) v =
      ∑ i, suzukiYoshidaCorrectedCompleteForm (f i) v := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using
        (suzukiYoshidaCorrectedCompleteForm_smul_left
          (0 : Complex) (0 : SuzukiYoshidaCorrectedCommonFormDomain) v)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [suzukiYoshidaCorrectedCompleteForm_add_left, ih]

private theorem suzukiYoshidaComparisonForm_fintype_sum_left
    {ι : Type*} [Fintype ι]
    (f : ι → SuzukiYoshidaCorrectedCommonFormDomain)
    (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm (∑ i, f i) v =
      ∑ i, suzukiYoshidaComparisonForm (f i) v := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using
        (suzukiYoshidaComparisonForm_smul_left
          (0 : Complex) (0 : SuzukiYoshidaCorrectedCommonFormDomain) v)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [suzukiYoshidaComparisonForm_add_left, ih]

private theorem suzukiYoshidaCorrectedCompleteForm_fintype_sum_right
    {ι : Type*} [Fintype ι]
    (u : SuzukiYoshidaCorrectedCommonFormDomain)
    (f : ι → SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaCorrectedCompleteForm u (∑ i, f i) =
      ∑ i, suzukiYoshidaCorrectedCompleteForm u (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using
        (suzukiYoshidaCorrectedCompleteForm_smul_right
          (0 : Complex) u (0 : SuzukiYoshidaCorrectedCommonFormDomain))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [suzukiYoshidaCorrectedCompleteForm_add_right, ih]

private theorem suzukiYoshidaComparisonForm_fintype_sum_right
    {ι : Type*} [Fintype ι]
    (u : SuzukiYoshidaCorrectedCommonFormDomain)
    (f : ι → SuzukiYoshidaCorrectedCommonFormDomain) :
    suzukiYoshidaComparisonForm u (∑ i, f i) =
      ∑ i, suzukiYoshidaComparisonForm u (f i) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simpa using
        (suzukiYoshidaComparisonForm_smul_right
          (0 : Complex) u (0 : SuzukiYoshidaCorrectedCommonFormDomain))
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [suzukiYoshidaComparisonForm_add_right, ih]

theorem suzukiDF6D5B3REEvenReconstructionCompletion_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45)) :
    SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) z =
      ∑ i : Fin 45, z i •
        suzukiDF6D5B3REEvenLowSourceCompletion hsource i := by
  rw [SuzukiB2EndpointModeCertificate.evenReconstructionCompletion,
    suzukiFiniteCompletionReconstruction_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [suzukiProjectB2EndpointModeCertificateOfSource_evenMode_eq]
  rfl

theorem suzukiDF6D5B3REOddReconstructionCompletion_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44)) :
    SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) z =
      ∑ i : Fin 44, z i •
        suzukiDF6D5B3REOddLowSourceCompletion hsource i := by
  rw [SuzukiB2EndpointModeCertificate.oddReconstructionCompletion,
    suzukiFiniteCompletionReconstruction_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [suzukiProjectB2EndpointModeCertificateOfSource_oddMode_eq]
  rfl

theorem suzukiDF6D5B3REEvenCross_decomposition
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45))
    (v : SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1 =
      suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1 v.1 +
        ∑ i : Fin 45, conj (z i) *
          (suzukiYoshidaCorrectedCompleteForm
              (suzukiDF6D5B3REEvenLowSourceCompletion hsource i) v.1 -
            suzukiYoshidaComparisonForm
              (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i) v.1) := by
  rw [suzukiDF6D5B3REEvenReconstructionCompletion_eq,
    suzukiYoshidaCorrectedCompleteForm_fintype_sum_left]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_left]
  change (∑ i : Fin 45, conj (z i) *
      suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REEvenLowSourceCompletion hsource i) v.1) =
    suzukiYoshidaComparisonForm
      (∑ i : Fin 45, z i •
        suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i) v.1 + _
  rw [suzukiYoshidaComparisonForm_fintype_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem suzukiDF6D5B3REOddCross_decomposition
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44))
    (v : SuzukiB2EndpointModeCertificate.OddParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1 =
      suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1 v.1 +
        ∑ i : Fin 44, conj (z i) *
          (suzukiYoshidaCorrectedCompleteForm
              (suzukiDF6D5B3REOddLowSourceCompletion hsource i) v.1 -
            suzukiYoshidaComparisonForm
              (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i) v.1) := by
  rw [suzukiDF6D5B3REOddReconstructionCompletion_eq,
    suzukiYoshidaCorrectedCompleteForm_fintype_sum_left]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_left]
  change (∑ i : Fin 44, conj (z i) *
      suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REOddLowSourceCompletion hsource i) v.1) =
    suzukiYoshidaComparisonForm
      (∑ i : Fin 44, z i •
        suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i) v.1 + _
  rw [suzukiYoshidaComparisonForm_fintype_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-! ## Exact finite entries behind the Galerkin base quadratic -/

theorem suzukiDF6D5B3REEvenLow_galerkinTrial
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i j : Fin 45) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REEvenLowSourceCompletion hsource i)
        (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource j) =
      ((∑ k : Fin 256, suzukiDF6D4EvenCompleteCrossEntry i k *
        (suzukiDF6D4EvenGalerkinApproximant k j : Real) : Real) : Complex) := by
  unfold suzukiDF6D5B3REEvenGalerkinTrialCompletion
  rw [suzukiYoshidaCorrectedCompleteForm_fintype_sum_right]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_right]
  have hentry (k : Fin 256) :=
    suzukiYoshidaCorrectedCompleteForm_evenLow_tail hsource hequation25 i
      (suzukiDF6D4GalerkinMode k) (by simp [suzukiDF6D4GalerkinMode])
  simp_rw [hentry]
  simp [suzukiDF6D4EvenCompleteCrossEntry]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiDF6D5B3REOddLow_galerkinTrial
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (i j : Fin 44) :
    suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REOddLowSourceCompletion hsource i)
        (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource j) =
      ((∑ k : Fin 256, suzukiDF6D4OddCompleteCrossEntry i k *
        (suzukiDF6D4OddGalerkinApproximant k j : Real) : Real) : Complex) := by
  unfold suzukiDF6D5B3REOddGalerkinTrialCompletion
  rw [suzukiYoshidaCorrectedCompleteForm_fintype_sum_right]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_right]
  have hentry (k : Fin 256) :=
    suzukiYoshidaCorrectedCompleteForm_oddLow_tail hsource hequation25 i
      (suzukiDF6D4GalerkinMode k) (by simp [suzukiDF6D4GalerkinMode])
  simp_rw [hentry]
  simp [suzukiDF6D4OddCompleteCrossEntry]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiDF6D5B3REEvenGalerkinTrial_comparison_galerkinTrial
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i j : Fin 45) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i)
        (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource j) =
      ((∑ k : Fin 256,
        (suzukiDF6D4EvenGalerkinApproximant k j : Real) *
          ∑ l : Fin 256, suzukiDF6D4EvenComparisonGalerkinEntry k l *
            (suzukiDF6D4EvenGalerkinApproximant l i : Real) : Real) :
        Complex) := by
  rw [show suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource j =
      ∑ k : Fin 256,
        ((suzukiDF6D4EvenGalerkinApproximant k j : Real) : Complex) •
          suzukiYoshidaEvenLinearCompletionOfSource hsource
            suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) by rfl]
  rw [suzukiYoshidaComparisonForm_fintype_sum_right]
  simp_rw [suzukiYoshidaComparisonForm_smul_right,
    suzukiYoshidaComparisonForm_evenGalerkinTrial_mode hsource]
  simp

theorem suzukiDF6D5B3REOddGalerkinTrial_comparison_galerkinTrial
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (i j : Fin 44) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i)
        (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource j) =
      ((∑ k : Fin 256,
        (suzukiDF6D4OddGalerkinApproximant k j : Real) *
          ∑ l : Fin 256, suzukiDF6D4OddComparisonGalerkinEntry k l *
            (suzukiDF6D4OddGalerkinApproximant l i : Real) : Real) :
        Complex) := by
  rw [show suzukiDF6D5B3REOddGalerkinTrialCompletion hsource j =
      ∑ k : Fin 256,
        ((suzukiDF6D4OddGalerkinApproximant k j : Real) : Complex) •
          suzukiYoshidaOddLinearCompletionOfSource hsource
            suzukiProjectAStar_pos (suzukiDF6D4GalerkinMode k) by rfl]
  rw [suzukiYoshidaComparisonForm_fintype_sum_right]
  simp_rw [suzukiYoshidaComparisonForm_smul_right,
    suzukiYoshidaComparisonForm_oddGalerkinTrial_mode hsource]
  simp

def suzukiDF6D5B3REEvenGalerkinCrossMatrix :
    Matrix (Fin 45) (Fin 45) Real :=
  fun i j => ∑ k : Fin 256, suzukiDF6D4EvenCompleteCrossEntry i k *
    (suzukiDF6D4EvenGalerkinApproximant k j : Real)

def suzukiDF6D5B3REOddGalerkinCrossMatrix :
    Matrix (Fin 44) (Fin 44) Real :=
  fun i j => ∑ k : Fin 256, suzukiDF6D4OddCompleteCrossEntry i k *
    (suzukiDF6D4OddGalerkinApproximant k j : Real)

def suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix :
    Matrix (Fin 45) (Fin 45) Real :=
  fun i j => ∑ k : Fin 256,
    (suzukiDF6D4EvenGalerkinApproximant k j : Real) *
      ∑ l : Fin 256, suzukiDF6D4EvenComparisonGalerkinEntry k l *
        (suzukiDF6D4EvenGalerkinApproximant l i : Real)

def suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix :
    Matrix (Fin 44) (Fin 44) Real :=
  fun i j => ∑ k : Fin 256,
    (suzukiDF6D4OddGalerkinApproximant k j : Real) *
      ∑ l : Fin 256, suzukiDF6D4OddComparisonGalerkinEntry k l *
        (suzukiDF6D4OddGalerkinApproximant l i : Real)

theorem suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix_symmetric
    (i j : Fin 45) :
    suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix i j =
      suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix j i := by
  unfold suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix
  simp_rw [Finset.mul_sum]
  calc
    (∑ k : Fin 256, ∑ l : Fin 256,
        (suzukiDF6D4EvenGalerkinApproximant k j : Real) *
          (suzukiDF6D4EvenComparisonGalerkinEntry k l *
            (suzukiDF6D4EvenGalerkinApproximant l i : Real))) =
      ∑ l : Fin 256, ∑ k : Fin 256,
        (suzukiDF6D4EvenGalerkinApproximant k j : Real) *
          (suzukiDF6D4EvenComparisonGalerkinEntry k l *
            (suzukiDF6D4EvenGalerkinApproximant l i : Real)) :=
        Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      rw [suzukiDF6D4EvenComparisonGalerkinEntry_symmetric]
      ring

theorem suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix_symmetric
    (i j : Fin 44) :
    suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix i j =
      suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix j i := by
  unfold suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix
  simp_rw [Finset.mul_sum]
  calc
    (∑ k : Fin 256, ∑ l : Fin 256,
        (suzukiDF6D4OddGalerkinApproximant k j : Real) *
          (suzukiDF6D4OddComparisonGalerkinEntry k l *
            (suzukiDF6D4OddGalerkinApproximant l i : Real))) =
      ∑ l : Fin 256, ∑ k : Fin 256,
        (suzukiDF6D4OddGalerkinApproximant k j : Real) *
          (suzukiDF6D4OddComparisonGalerkinEntry k l *
            (suzukiDF6D4OddGalerkinApproximant l i : Real)) :=
        Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      rw [suzukiDF6D4OddComparisonGalerkinEntry_symmetric]
      ring

theorem suzukiDF6D5B3REEvenGalerkinBaseMatrix_eq :
    suzukiDF6D4EvenGalerkinBaseMatrix =
      suzukiDF6D5B3REEvenGalerkinCrossMatrix +
        Matrix.transpose suzukiDF6D5B3REEvenGalerkinCrossMatrix -
      suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix := by
  ext i j
  rw [show suzukiDF6D4EvenGalerkinBaseMatrix i j =
      suzukiDF6D4EvenGalerkinBaseEntry i j by rfl,
    suzukiDF6D5B3RE_evenGalerkinBaseEntry_eq]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply]
  rw [suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix_symmetric i j]
  simp [suzukiDF6D5B3REEvenGalerkinCrossMatrix,
    suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiDF6D5B3REOddGalerkinBaseMatrix_eq :
    suzukiDF6D4OddGalerkinBaseMatrix =
      suzukiDF6D5B3REOddGalerkinCrossMatrix +
        Matrix.transpose suzukiDF6D5B3REOddGalerkinCrossMatrix -
      suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix := by
  ext i j
  rw [show suzukiDF6D4OddGalerkinBaseMatrix i j =
      suzukiDF6D4OddGalerkinBaseEntry i j by rfl,
    suzukiDF6D5B3RE_oddGalerkinBaseEntry_eq]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply]
  rw [suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix_symmetric i j]
  simp [suzukiDF6D5B3REOddGalerkinCrossMatrix,
    suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiDF6D5B3REEvenLowTrial_eq_matrix
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45)) :
    suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1 =
      dotProduct (fun i => conj (z i))
        (Matrix.mulVec
          (suzukiDF6D5ComplexifyMatrix
            suzukiDF6D5B3REEvenGalerkinCrossMatrix) z) := by
  rw [suzukiDF6D5B3REEvenReconstructionCompletion_eq,
    suzukiYoshidaCorrectedCompleteForm_fintype_sum_left]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_left]
  change (∑ i : Fin 45, conj (z i) *
      suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REEvenLowSourceCompletion hsource i)
        (∑ j : Fin 45, z j •
          suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource j)) = _
  simp_rw [suzukiYoshidaCorrectedCompleteForm_fintype_sum_right,
    suzukiYoshidaCorrectedCompleteForm_smul_right,
    suzukiDF6D5B3REEvenLow_galerkinTrial hsource hequation25]
  simp [dotProduct, Matrix.mulVec, suzukiDF6D5ComplexifyMatrix,
    suzukiDF6D5B3REEvenGalerkinCrossMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiDF6D5B3REOddLowTrial_eq_matrix
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44)) :
    suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1 =
      dotProduct (fun i => conj (z i))
        (Matrix.mulVec
          (suzukiDF6D5ComplexifyMatrix
            suzukiDF6D5B3REOddGalerkinCrossMatrix) z) := by
  rw [suzukiDF6D5B3REOddReconstructionCompletion_eq,
    suzukiYoshidaCorrectedCompleteForm_fintype_sum_left]
  simp_rw [suzukiYoshidaCorrectedCompleteForm_smul_left]
  change (∑ i : Fin 44, conj (z i) *
      suzukiYoshidaCorrectedCompleteForm
        (suzukiDF6D5B3REOddLowSourceCompletion hsource i)
        (∑ j : Fin 44, z j •
          suzukiDF6D5B3REOddGalerkinTrialCompletion hsource j)) = _
  simp_rw [suzukiYoshidaCorrectedCompleteForm_fintype_sum_right,
    suzukiYoshidaCorrectedCompleteForm_smul_right,
    suzukiDF6D5B3REOddLow_galerkinTrial hsource hequation25]
  simp [dotProduct, Matrix.mulVec, suzukiDF6D5ComplexifyMatrix,
    suzukiDF6D5B3REOddGalerkinCrossMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem suzukiDF6D5B3REEvenTrialEnergy_eq_matrix
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45)) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1
        (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1 =
      dotProduct (fun i => conj (z i))
        (Matrix.mulVec
          (suzukiDF6D5ComplexifyMatrix
            suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix) z) := by
  change suzukiYoshidaComparisonForm
      (∑ i : Fin 45, z i •
        suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i)
      (∑ j : Fin 45, z j •
        suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource j) = _
  rw [suzukiYoshidaComparisonForm_fintype_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left,
    suzukiYoshidaComparisonForm_fintype_sum_right,
    suzukiYoshidaComparisonForm_smul_right,
    suzukiDF6D5B3REEvenGalerkinTrial_comparison_galerkinTrial hsource]
  simp [dotProduct, Matrix.mulVec, suzukiDF6D5ComplexifyMatrix,
    suzukiDF6D5B3REEvenGalerkinTrialEnergyMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem suzukiDF6D5B3REOddTrialEnergy_eq_matrix
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44)) :
    suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1
        (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1 =
      dotProduct (fun i => conj (z i))
        (Matrix.mulVec
          (suzukiDF6D5ComplexifyMatrix
            suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix) z) := by
  change suzukiYoshidaComparisonForm
      (∑ i : Fin 44, z i •
        suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i)
      (∑ j : Fin 44, z j •
        suzukiDF6D5B3REOddGalerkinTrialCompletion hsource j) = _
  rw [suzukiYoshidaComparisonForm_fintype_sum_left]
  simp_rw [suzukiYoshidaComparisonForm_smul_left,
    suzukiYoshidaComparisonForm_fintype_sum_right,
    suzukiYoshidaComparisonForm_smul_right,
    suzukiDF6D5B3REOddGalerkinTrial_comparison_galerkinTrial hsource]
  simp [dotProduct, Matrix.mulVec, suzukiDF6D5ComplexifyMatrix,
    suzukiDF6D5B3REOddGalerkinTrialEnergyMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem suzukiDF6D5MatrixQuadratic_add' {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) (x : Fin n → Real) :
    suzukiDF6D5MatrixQuadratic (A + B) x =
      suzukiDF6D5MatrixQuadratic A x +
        suzukiDF6D5MatrixQuadratic B x := by
  simp [suzukiDF6D5MatrixQuadratic, Matrix.add_mulVec, dotProduct_add]

private theorem suzukiDF6D5MatrixQuadratic_transpose' {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (x : Fin n → Real) :
    suzukiDF6D5MatrixQuadratic (Matrix.transpose A) x =
      suzukiDF6D5MatrixQuadratic A x := by
  simp only [suzukiDF6D5MatrixQuadratic, dotProduct, Matrix.mulVec,
    Matrix.transpose_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem suzukiDF6D5ComplexMatrixQuadratic_add' {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) (z : Fin n → Complex) :
    suzukiDF6D5ComplexMatrixQuadratic (A + B) z =
      suzukiDF6D5ComplexMatrixQuadratic A z +
        suzukiDF6D5ComplexMatrixQuadratic B z := by
  simp_rw [suzukiDF6D5ComplexMatrixQuadratic_re_im]
  rw [suzukiDF6D5MatrixQuadratic_add',
    suzukiDF6D5MatrixQuadratic_add']
  ring

private theorem suzukiDF6D5ComplexMatrixQuadratic_sub' {n : Nat}
    (A B : Matrix (Fin n) (Fin n) Real) (z : Fin n → Complex) :
    suzukiDF6D5ComplexMatrixQuadratic (A - B) z =
      suzukiDF6D5ComplexMatrixQuadratic A z -
        suzukiDF6D5ComplexMatrixQuadratic B z := by
  simp_rw [suzukiDF6D5ComplexMatrixQuadratic_re_im]
  rw [suzukiDF6D5MatrixQuadratic_sub,
    suzukiDF6D5MatrixQuadratic_sub]
  ring

private theorem suzukiDF6D5ComplexMatrixQuadratic_transpose' {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) (z : Fin n → Complex) :
    suzukiDF6D5ComplexMatrixQuadratic (Matrix.transpose A) z =
      suzukiDF6D5ComplexMatrixQuadratic A z := by
  simp_rw [suzukiDF6D5ComplexMatrixQuadratic_re_im]
  rw [suzukiDF6D5MatrixQuadratic_transpose',
    suzukiDF6D5MatrixQuadratic_transpose']

private theorem suzukiDF6D5ComplexMatrixQuadratic_smul' {n : Nat}
    (c : Real) (A : Matrix (Fin n) (Fin n) Real) (z : Fin n → Complex) :
    suzukiDF6D5ComplexMatrixQuadratic (c • A) z =
      c * suzukiDF6D5ComplexMatrixQuadratic A z := by
  simp_rw [suzukiDF6D5ComplexMatrixQuadratic_re_im]
  rw [suzukiDF6D5MatrixQuadratic_smul,
    suzukiDF6D5MatrixQuadratic_smul]
  ring

private theorem suzukiDF6D5B3REEvenCouplingQuadratic_eq
    (z : Fin 45 → Complex) :
    suzukiDF6D5EvenCouplingHermitianQuadratic z =
      suzukiDF6D5ComplexMatrixQuadratic
          suzukiDF6D4EvenGalerkinBaseMatrix z +
        (1 / 5 : Real) *
          suzukiDF6D5ComplexMatrixQuadratic
            (suzukiDF6D4EvenFiniteResidualGramMatrix +
              suzukiDF6D4EvenAnalyticTailMatrix) z := by
  unfold suzukiDF6D5EvenCouplingHermitianQuadratic
    suzukiDF6D4EvenCouplingUpperMatrix
  rw [suzukiDF6D5ComplexMatrixQuadratic_add',
    suzukiDF6D5ComplexMatrixQuadratic_add',
    suzukiDF6D5ComplexMatrixQuadratic_smul',
    suzukiDF6D5ComplexMatrixQuadratic_smul',
    suzukiDF6D5ComplexMatrixQuadratic_add']
  norm_num
  ring

private theorem suzukiDF6D5B3REOddCouplingQuadratic_eq
    (z : Fin 44 → Complex) :
    suzukiDF6D5OddCouplingHermitianQuadratic z =
      suzukiDF6D5ComplexMatrixQuadratic
          suzukiDF6D4OddGalerkinBaseMatrix z +
        (1 / 5 : Real) *
          suzukiDF6D5ComplexMatrixQuadratic
            (suzukiDF6D4OddFiniteResidualGramMatrix +
              suzukiDF6D4OddAnalyticTailMatrix) z := by
  unfold suzukiDF6D5OddCouplingHermitianQuadratic
    suzukiDF6D4OddCouplingUpperMatrix
  rw [suzukiDF6D5ComplexMatrixQuadratic_add',
    suzukiDF6D5ComplexMatrixQuadratic_add',
    suzukiDF6D5ComplexMatrixQuadratic_smul',
    suzukiDF6D5ComplexMatrixQuadratic_smul',
    suzukiDF6D5ComplexMatrixQuadratic_add']
  norm_num
  ring

private theorem complex_norm_sq_le_of_scaled_real_bound
    (A : Complex) (b Q : Real) (hb : 0 < b)
    (hscaled : ∀ c : Complex,
      2 * (c * A).re - ‖c‖ ^ 2 * b ≤ Q) :
    ‖A‖ ^ 2 ≤ Q * b := by
  have h := hscaled (conj A / (b : Complex))
  rw [← Complex.normSq_eq_norm_sq] at h ⊢
  have hbne : b ≠ 0 := ne_of_gt hb
  simp [Complex.div_re, Complex.mul_re,
    Complex.normSq_conj, Complex.normSq_ofReal] at h
  field_simp [hbne] at h ⊢
  rw [Complex.normSq_apply] at h ⊢
  nlinarith

private theorem comparison_energy_completion_identity
    (low trial u : SuzukiYoshidaCorrectedCommonFormDomain)
    (qbase : Real)
    (hbase : qbase =
      2 * (suzukiYoshidaCorrectedCompleteForm low trial).re -
        (suzukiYoshidaComparisonForm trial trial).re) :
    2 * (suzukiYoshidaCorrectedCompleteForm low u).re -
        (suzukiYoshidaComparisonForm u u).re =
      qbase +
        2 * (suzukiYoshidaCorrectedCompleteForm low (u - trial) -
          suzukiYoshidaComparisonForm trial (u - trial)).re -
        (suzukiYoshidaComparisonForm (u - trial) (u - trial)).re := by
  have hsymm :
      (suzukiYoshidaComparisonForm u trial).re =
        (suzukiYoshidaComparisonForm trial u).re := by
    rw [suzukiYoshidaComparisonForm_conj_symm, Complex.conj_re]
  rw [hbase]
  simp only [sub_eq_add_neg,
    suzukiYoshidaCorrectedCompleteForm_add_right,
    suzukiYoshidaCorrectedCompleteForm_neg_right,
    suzukiYoshidaComparisonForm_add_left,
    suzukiYoshidaComparisonForm_add_right,
    suzukiYoshidaComparisonForm_neg_left,
    suzukiYoshidaComparisonForm_neg_right,
    Complex.add_re, Complex.neg_re]
  rw [hsymm]
  ring

private theorem comparison_energy_smul_self_re
    (c : Complex) (v : SuzukiYoshidaCorrectedCommonFormDomain) :
    (suzukiYoshidaComparisonForm (c • v) (c • v)).re =
      ‖c‖ ^ 2 * (suzukiYoshidaComparisonForm v v).re := by
  rw [suzukiYoshidaComparisonForm_smul_left,
    suzukiYoshidaComparisonForm_smul_right, ← mul_assoc,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  change (((‖c‖ ^ 2 : Real) : Complex) *
      suzukiYoshidaComparisonForm v v).re = _
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem residual_young_bound
    (R : Complex) (q energy : Real)
    (hq : 0 ≤ q) (henergy : 0 ≤ energy)
    (hR : ‖R‖ ^ 2 ≤ q * energy) :
    2 * R.re - energy ≤ q := by
  have hre : R.re ≤ ‖R‖ := Complex.re_le_norm R
  have hsum : 2 * ‖R‖ ≤ q + energy := by
    nlinarith [sq_nonneg (q - energy), norm_nonneg R]
  linarith

theorem suzukiDF6D5B3REEvenGalerkinBaseQuadratic_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45)) :
    suzukiDF6D5ComplexMatrixQuadratic
        suzukiDF6D4EvenGalerkinBaseMatrix z =
      2 * (suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1).re -
      (suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1
        (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1).re := by
  rw [suzukiDF6D5B3REEvenGalerkinBaseMatrix_eq,
    suzukiDF6D5ComplexMatrixQuadratic_sub',
    suzukiDF6D5ComplexMatrixQuadratic_add',
    suzukiDF6D5ComplexMatrixQuadratic_transpose',
    suzukiDF6D5B3REEvenLowTrial_eq_matrix hsource hequation25,
    suzukiDF6D5B3REEvenTrialEnergy_eq_matrix hsource]
  unfold suzukiDF6D5ComplexMatrixQuadratic
  ring

theorem suzukiDF6D5B3REOddGalerkinBaseQuadratic_eq
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44)) :
    suzukiDF6D5ComplexMatrixQuadratic
        suzukiDF6D4OddGalerkinBaseMatrix z =
      2 * (suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z)
        (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1).re -
      (suzukiYoshidaComparisonForm
        (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1
        (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1).re := by
  rw [suzukiDF6D5B3REOddGalerkinBaseMatrix_eq,
    suzukiDF6D5ComplexMatrixQuadratic_sub',
    suzukiDF6D5ComplexMatrixQuadratic_add',
    suzukiDF6D5ComplexMatrixQuadratic_transpose',
    suzukiDF6D5B3REOddLowTrial_eq_matrix hsource hequation25,
    suzukiDF6D5B3REOddTrialEnergy_eq_matrix hsource]
  unfold suzukiDF6D5ComplexMatrixQuadratic
  ring

theorem suzukiDF6D5B3REEvenActualResidualRepresenter_pairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : Fin 45 → Complex)
    (v : SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    inner Complex
        (∑ i : Fin 45, z i •
          suzukiDF6D5B3REEvenActualResidualRepresenter hsource i)
        (suzukiDF6D5B3REEvenAmbientOfParityFar hsource v) =
      ∑ i : Fin 45, conj (z i) *
        (suzukiYoshidaCorrectedCompleteForm
            (suzukiDF6D5B3REEvenLowSourceCompletion hsource i) v.1 -
          suzukiYoshidaComparisonForm
            (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i) v.1) := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  calc
    inner Complex
          (z i • suzukiDF6D5B3REEvenActualResidualRepresenter hsource i)
          (suzukiDF6D5B3REEvenAmbientOfParityFar hsource v) =
        conj (z i) * inner Complex
          (suzukiDF6D5B3REEvenActualResidualRepresenter hsource i)
          (suzukiDF6D5B3REEvenAmbientOfParityFar hsource v) := by
      exact inner_smul_left (𝕜 := Complex)
        (E := SuzukiDF6D5B3REvenAmbientFarL2)
        (suzukiDF6D5B3REEvenActualResidualRepresenter hsource i)
        (suzukiDF6D5B3REEvenAmbientOfParityFar hsource v) (z i)
    _ = _ := by
      change conj (z i) * inner Complex
          (suzukiDF6D5B3REvenAmbientRepresenter
            (suzukiDF6D5B3REEvenAmbientResidualFunctional hsource i))
          (suzukiDF6D5B3REEvenAmbientOfParityFar hsource v) = _
      rw [suzukiDF6D5B3REvenAmbientRepresenter_pairing]
      change conj (z i) *
          suzukiDF6D5B3REEvenGlobalResidualFunctional hsource i
            (suzukiLogRadiusLinearCompletionToL2 v.1) = _
      rw [suzukiDF6D5B3REEvenGlobalResidualFunctional_pairing]

theorem suzukiDF6D5B3REOddActualResidualRepresenter_pairing
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (z : Fin 44 → Complex)
    (v : SuzukiB2EndpointModeCertificate.OddParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    inner Complex
        (∑ i : Fin 44, z i •
          suzukiDF6D5B3REOddActualResidualRepresenter hsource i)
        (suzukiDF6D5B3REOddAmbientOfParityFar hsource v) =
      ∑ i : Fin 44, conj (z i) *
        (suzukiYoshidaCorrectedCompleteForm
            (suzukiDF6D5B3REOddLowSourceCompletion hsource i) v.1 -
          suzukiYoshidaComparisonForm
            (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i) v.1) := by
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  calc
    inner Complex
          (z i • suzukiDF6D5B3REOddActualResidualRepresenter hsource i)
          (suzukiDF6D5B3REOddAmbientOfParityFar hsource v) =
        conj (z i) * inner Complex
          (suzukiDF6D5B3REOddActualResidualRepresenter hsource i)
          (suzukiDF6D5B3REOddAmbientOfParityFar hsource v) := by
      exact inner_smul_left (𝕜 := Complex)
        (E := SuzukiDF6D5B3ROddAmbientFarL2)
        (suzukiDF6D5B3REOddActualResidualRepresenter hsource i)
        (suzukiDF6D5B3REOddAmbientOfParityFar hsource v) (z i)
    _ = _ := by
      change conj (z i) * inner Complex
          (suzukiDF6D5B3ROddAmbientRepresenter
            (suzukiDF6D5B3REOddAmbientResidualFunctional hsource i))
          (suzukiDF6D5B3REOddAmbientOfParityFar hsource v) = _
      rw [suzukiDF6D5B3ROddAmbientRepresenter_pairing]
      change conj (z i) *
          suzukiDF6D5B3REOddGlobalResidualFunctional hsource i
            (suzukiLogRadiusLinearCompletionToL2 v.1) = _
      rw [suzukiDF6D5B3REOddGlobalResidualFunctional_pairing]

theorem suzukiDF6D5B3REEvenResidualFunctional_norm_sq_le_energy
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : Fin 45 → Complex)
    (v : SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    ‖∑ i : Fin 45, conj (z i) *
        (suzukiYoshidaCorrectedCompleteForm
            (suzukiDF6D5B3REEvenLowSourceCompletion hsource i) v.1 -
          suzukiYoshidaComparisonForm
            (suzukiDF6D5B3REEvenGalerkinTrialCompletion hsource i) v.1)‖ ^ 2 ≤
      (1 / 5 : Real) *
          suzukiDF6D5ComplexMatrixQuadratic
            (suzukiDF6D4EvenFiniteResidualGramMatrix +
              suzukiDF6D4EvenAnalyticTailMatrix) z *
        (suzukiYoshidaComparisonForm v.1 v.1).re := by
  let r := ∑ i : Fin 45, z i •
    suzukiDF6D5B3REEvenActualResidualRepresenter hsource i
  let w := suzukiDF6D5B3REEvenAmbientOfParityFar hsource v
  rw [← suzukiDF6D5B3REEvenActualResidualRepresenter_pairing hsource z v]
  have hcs := norm_inner_le_norm (𝕜 := Complex) r w
  have hcsSq : ‖inner Complex r w‖ ^ 2 ≤ ‖r‖ ^ 2 * ‖w‖ ^ 2 := by
    calc
      ‖inner Complex r w‖ ^ 2 ≤ (‖r‖ * ‖w‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg r) (norm_nonneg w))).2 hcs
      _ = ‖r‖ ^ 2 * ‖w‖ ^ 2 := by ring
  have hr :=
    suzukiDF6D5B3REEvenActualResidualRepresenter_complex_norm_sq_le
      hsource hequation25 z
  have hw := suzukiDF6D5B3FE_even_norm_sq_le_one_fifth_energy
    (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).1 v
  have hq : 0 ≤ suzukiDF6D5ComplexMatrixQuadratic
      (suzukiDF6D4EvenFiniteResidualGramMatrix +
        suzukiDF6D4EvenAnalyticTailMatrix) z :=
    (sq_nonneg ‖r‖).trans hr
  have hproduct := mul_le_mul hr hw (sq_nonneg ‖w‖) hq
  change ‖inner Complex r w‖ ^ 2 ≤ _
  calc
    ‖inner Complex r w‖ ^ 2 ≤ ‖r‖ ^ 2 * ‖w‖ ^ 2 := hcsSq
    _ ≤ suzukiDF6D5ComplexMatrixQuadratic
          (suzukiDF6D4EvenFiniteResidualGramMatrix +
            suzukiDF6D4EvenAnalyticTailMatrix) z *
        ((1 / 5 : Real) *
          (suzukiYoshidaComparisonForm v.1 v.1).re) := by
      simpa [r, w, suzukiDF6D5B3REEvenAmbientOfParityFar] using hproduct
    _ = _ := by ring

theorem suzukiDF6D5B3REOddResidualFunctional_norm_sq_le_energy
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : Fin 44 → Complex)
    (v : SuzukiB2EndpointModeCertificate.OddParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    ‖∑ i : Fin 44, conj (z i) *
        (suzukiYoshidaCorrectedCompleteForm
            (suzukiDF6D5B3REOddLowSourceCompletion hsource i) v.1 -
          suzukiYoshidaComparisonForm
            (suzukiDF6D5B3REOddGalerkinTrialCompletion hsource i) v.1)‖ ^ 2 ≤
      (1 / 5 : Real) *
          suzukiDF6D5ComplexMatrixQuadratic
            (suzukiDF6D4OddFiniteResidualGramMatrix +
              suzukiDF6D4OddAnalyticTailMatrix) z *
        (suzukiYoshidaComparisonForm v.1 v.1).re := by
  let r := ∑ i : Fin 44, z i •
    suzukiDF6D5B3REOddActualResidualRepresenter hsource i
  let w := suzukiDF6D5B3REOddAmbientOfParityFar hsource v
  rw [← suzukiDF6D5B3REOddActualResidualRepresenter_pairing hsource z v]
  have hcs := norm_inner_le_norm (𝕜 := Complex) r w
  have hcsSq : ‖inner Complex r w‖ ^ 2 ≤ ‖r‖ ^ 2 * ‖w‖ ^ 2 := by
    calc
      ‖inner Complex r w‖ ^ 2 ≤ (‖r‖ * ‖w‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg r) (norm_nonneg w))).2 hcs
      _ = ‖r‖ ^ 2 * ‖w‖ ^ 2 := by ring
  have hr :=
    suzukiDF6D5B3REOddActualResidualRepresenter_complex_norm_sq_le
      hsource hequation25 z
  have hw := suzukiDF6D5B3FE_odd_norm_sq_le_one_fifth_energy
    (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).2 v
  have hq : 0 ≤ suzukiDF6D5ComplexMatrixQuadratic
      (suzukiDF6D4OddFiniteResidualGramMatrix +
        suzukiDF6D4OddAnalyticTailMatrix) z :=
    (sq_nonneg ‖r‖).trans hr
  have hproduct := mul_le_mul hr hw (sq_nonneg ‖w‖) hq
  change ‖inner Complex r w‖ ^ 2 ≤ _
  calc
    ‖inner Complex r w‖ ^ 2 ≤ ‖r‖ ^ 2 * ‖w‖ ^ 2 := hcsSq
    _ ≤ suzukiDF6D5ComplexMatrixQuadratic
          (suzukiDF6D4OddFiniteResidualGramMatrix +
            suzukiDF6D4OddAnalyticTailMatrix) z *
        ((1 / 5 : Real) *
          (suzukiYoshidaComparisonForm v.1 v.1).re) := by
      simpa [r, w, suzukiDF6D5B3REOddAmbientOfParityFar] using hproduct
    _ = _ := by ring

/-! ## Residual part of the actual low-to-far cross term -/

theorem suzukiDF6D5B3REEvenCrossResidual_norm_sq_le_energy
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45))
    (v : SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    ‖suzukiYoshidaCorrectedCompleteForm
          (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
            (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1 -
        suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z).1 v.1‖ ^ 2 ≤
      (1 / 5 : Real) *
          suzukiDF6D5ComplexMatrixQuadratic
            (suzukiDF6D4EvenFiniteResidualGramMatrix +
              suzukiDF6D4EvenAnalyticTailMatrix) z *
        (suzukiYoshidaComparisonForm v.1 v.1).re := by
  rw [suzukiDF6D5B3REEvenCross_decomposition hsource z v]
  simpa only [add_sub_cancel_left] using
    suzukiDF6D5B3REEvenResidualFunctional_norm_sq_le_energy
      hsource hequation25 z v

theorem suzukiDF6D5B3REOddCrossResidual_norm_sq_le_energy
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44))
    (v : SuzukiB2EndpointModeCertificate.OddParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    ‖suzukiYoshidaCorrectedCompleteForm
          (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
            (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1 -
        suzukiYoshidaComparisonForm
          (suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z).1 v.1‖ ^ 2 ≤
      (1 / 5 : Real) *
          suzukiDF6D5ComplexMatrixQuadratic
            (suzukiDF6D4OddFiniteResidualGramMatrix +
              suzukiDF6D4OddAnalyticTailMatrix) z *
        (suzukiYoshidaComparisonForm v.1 v.1).re := by
  rw [suzukiDF6D5B3REOddCross_decomposition hsource z v]
  simpa only [add_sub_cancel_left] using
    suzukiDF6D5B3REOddResidualFunctional_norm_sq_le_energy
      hsource hequation25 z v

/-! ## Final B3R-E comparison-energy cross receivers -/

theorem suzukiDF6D5B3REEvenComparisonEnergyCrossEstimate
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 45))
    (v : SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    ‖suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖ ^ 2 ≤
      suzukiDF6D5EvenCouplingHermitianQuadratic z *
        (suzukiYoshidaComparisonForm v.1 v.1).re := by
  rw [suzukiDF6D5B3REEvenCouplingQuadratic_eq]
  let low := SuzukiB2EndpointModeCertificate.evenReconstructionCompletion
    (suzukiProjectB2EndpointModeCertificateOfSource hsource) z
  let trial := suzukiDF6D5B3REEvenGalerkinTrialOfCoordinates hsource z
  let qbase := suzukiDF6D5ComplexMatrixQuadratic
    suzukiDF6D4EvenGalerkinBaseMatrix z
  let qtail := suzukiDF6D5ComplexMatrixQuadratic
    (suzukiDF6D4EvenFiniteResidualGramMatrix +
      suzukiDF6D4EvenAnalyticTailMatrix) z
  let qres := (1 / 5 : Real) * qtail
  let A := suzukiYoshidaCorrectedCompleteForm low v.1
  let b := (suzukiYoshidaComparisonForm v.1 v.1).re
  change ‖A‖ ^ 2 ≤ (qbase + qres) * b
  by_cases hv : v.1 = 0
  · have hA : A = 0 := by
      have hz := suzukiYoshidaCorrectedCompleteForm_smul_right
        (0 : Complex) low (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hz
      simpa [A, hv] using hz
    have hb : b = 0 := by
      have hz := suzukiYoshidaComparisonForm_smul_right
        (0 : Complex) (0 : SuzukiYoshidaCorrectedCommonFormDomain)
          (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hz
      simpa [b, hv] using congrArg Complex.re hz
    simp [hA, hb]
  · have hvL2 : suzukiLogRadiusLinearCompletionToL2 v.1 ≠ 0 := by
      intro hzero
      apply hv
      apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
      simpa only [map_zero] using hzero
    have hvNorm : 0 < ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ :=
      norm_pos_iff.mpr hvL2
    have hnormBound := suzukiDF6D5B3FE_even_norm_sq_le_one_fifth_energy
      (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).1 v
    have hbpos : 0 < b := by
      dsimp [b]
      nlinarith [sq_pos_of_pos hvNorm]
    have htailRaw :=
      suzukiDF6D5B3REEvenActualResidualRepresenter_complex_norm_sq_le
        hsource hequation25 z
    have htail : 0 ≤ qtail := by
      dsimp [qtail]
      exact (sq_nonneg ‖∑ i : Fin 45, z i •
        suzukiDF6D5B3REEvenActualResidualRepresenter hsource i‖).trans htailRaw
    have hqres : 0 ≤ qres := by
      dsimp [qres]
      positivity
    apply complex_norm_sq_le_of_scaled_real_bound A b (qbase + qres) hbpos
    intro c
    let u : SuzukiB2EndpointModeCertificate.EvenParityFarCompletion
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := c • v
    let w := u - trial
    have hbase : qbase =
        2 * (suzukiYoshidaCorrectedCompleteForm low trial.1).re -
          (suzukiYoshidaComparisonForm trial.1 trial.1).re := by
      exact suzukiDF6D5B3REEvenGalerkinBaseQuadratic_eq
        hsource hequation25 z
    have hid := comparison_energy_completion_identity
      low trial.1 u.1 qbase hbase
    let R := suzukiYoshidaCorrectedCompleteForm low w.1 -
      suzukiYoshidaComparisonForm trial.1 w.1
    let energy := (suzukiYoshidaComparisonForm w.1 w.1).re
    have hR : ‖R‖ ^ 2 ≤ qres * energy := by
      simpa [R, energy, qres, low, trial, w] using
        suzukiDF6D5B3REEvenCrossResidual_norm_sq_le_energy
          hsource hequation25 z w
    have hwEnergy := suzukiDF6D5B3FE_even_norm_sq_le_one_fifth_energy
      (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).1 w
    have henergy : 0 ≤ energy := by
      dsimp [energy]
      nlinarith [sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 w.1‖]
    have hyoung := residual_young_bound R qres energy hqres henergy hR
    dsimp [R, energy, w] at hyoung
    have hmaster :
        2 * (suzukiYoshidaCorrectedCompleteForm low u.1).re -
            (suzukiYoshidaComparisonForm u.1 u.1).re ≤
          qbase + qres := by
      rw [hid]
      simp only [Complex.sub_re]
      linarith
    simpa [u, A, b, suzukiYoshidaCorrectedCompleteForm_smul_right,
      comparison_energy_smul_self_re] using hmaster

theorem suzukiDF6D5B3REOddComparisonEnergyCrossEstimate
    (hsource :
      SuzukiYoshidaExponentialFormCoreSourceAt suzukiProjectAStar)
    (hequation25 : SuzukiEquation25SourceIdentityAt suzukiProjectAStar)
    (z : EuclideanSpace Complex (Fin 44))
    (v : SuzukiB2EndpointModeCertificate.OddParityFarCompletion
      (suzukiProjectB2EndpointModeCertificateOfSource hsource)) :
    ‖suzukiYoshidaCorrectedCompleteForm
        (SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
          (suzukiProjectB2EndpointModeCertificateOfSource hsource) z) v.1‖ ^ 2 ≤
      suzukiDF6D5OddCouplingHermitianQuadratic z *
        (suzukiYoshidaComparisonForm v.1 v.1).re := by
  rw [suzukiDF6D5B3REOddCouplingQuadratic_eq]
  let low := SuzukiB2EndpointModeCertificate.oddReconstructionCompletion
    (suzukiProjectB2EndpointModeCertificateOfSource hsource) z
  let trial := suzukiDF6D5B3REOddGalerkinTrialOfCoordinates hsource z
  let qbase := suzukiDF6D5ComplexMatrixQuadratic
    suzukiDF6D4OddGalerkinBaseMatrix z
  let qtail := suzukiDF6D5ComplexMatrixQuadratic
    (suzukiDF6D4OddFiniteResidualGramMatrix +
      suzukiDF6D4OddAnalyticTailMatrix) z
  let qres := (1 / 5 : Real) * qtail
  let A := suzukiYoshidaCorrectedCompleteForm low v.1
  let b := (suzukiYoshidaComparisonForm v.1 v.1).re
  change ‖A‖ ^ 2 ≤ (qbase + qres) * b
  by_cases hv : v.1 = 0
  · have hA : A = 0 := by
      have hz := suzukiYoshidaCorrectedCompleteForm_smul_right
        (0 : Complex) low (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hz
      simpa [A, hv] using hz
    have hb : b = 0 := by
      have hz := suzukiYoshidaComparisonForm_smul_right
        (0 : Complex) (0 : SuzukiYoshidaCorrectedCommonFormDomain)
          (0 : SuzukiYoshidaCorrectedCommonFormDomain)
      simp only [zero_smul] at hz
      simpa [b, hv] using congrArg Complex.re hz
    simp [hA, hb]
  · have hvL2 : suzukiLogRadiusLinearCompletionToL2 v.1 ≠ 0 := by
      intro hzero
      apply hv
      apply suzukiLogRadiusLinearCompletionToL2_injective suzukiProjectAStar
      simpa only [map_zero] using hzero
    have hvNorm : 0 < ‖suzukiLogRadiusLinearCompletionToL2 v.1‖ :=
      norm_pos_iff.mpr hvL2
    have hnormBound := suzukiDF6D5B3FE_odd_norm_sq_le_one_fifth_energy
      (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).2 v
    have hbpos : 0 < b := by
      dsimp [b]
      nlinarith [sq_pos_of_pos hvNorm]
    have htailRaw :=
      suzukiDF6D5B3REOddActualResidualRepresenter_complex_norm_sq_le
        hsource hequation25 z
    have htail : 0 ≤ qtail := by
      dsimp [qtail]
      exact (sq_nonneg ‖∑ i : Fin 44, z i •
        suzukiDF6D5B3REOddActualResidualRepresenter hsource i‖).trans htailRaw
    have hqres : 0 ≤ qres := by
      dsimp [qres]
      positivity
    apply complex_norm_sq_le_of_scaled_real_bound A b (qbase + qres) hbpos
    intro c
    let u : SuzukiB2EndpointModeCertificate.OddParityFarCompletion
        (suzukiProjectB2EndpointModeCertificateOfSource hsource) := c • v
    let w := u - trial
    have hbase : qbase =
        2 * (suzukiYoshidaCorrectedCompleteForm low trial.1).re -
          (suzukiYoshidaComparisonForm trial.1 trial.1).re := by
      exact suzukiDF6D5B3REOddGalerkinBaseQuadratic_eq
        hsource hequation25 z
    have hid := comparison_energy_completion_identity
      low trial.1 u.1 qbase hbase
    let R := suzukiYoshidaCorrectedCompleteForm low w.1 -
      suzukiYoshidaComparisonForm trial.1 w.1
    let energy := (suzukiYoshidaComparisonForm w.1 w.1).re
    have hR : ‖R‖ ^ 2 ≤ qres * energy := by
      simpa [R, energy, qres, low, trial, w] using
        suzukiDF6D5B3REOddCrossResidual_norm_sq_le_energy
          hsource hequation25 z w
    have hwEnergy := suzukiDF6D5B3FE_odd_norm_sq_le_one_fifth_energy
      (suzukiDF6D5B3FE_canonicalSharpEnergyLower_of_source hsource).2 w
    have henergy : 0 ≤ energy := by
      dsimp [energy]
      nlinarith [sq_nonneg ‖suzukiLogRadiusLinearCompletionToL2 w.1‖]
    have hyoung := residual_young_bound R qres energy hqres henergy hR
    dsimp [R, energy, w] at hyoung
    have hmaster :
        2 * (suzukiYoshidaCorrectedCompleteForm low u.1).re -
            (suzukiYoshidaComparisonForm u.1 u.1).re ≤
          qbase + qres := by
      rw [hid]
      simp only [Complex.sub_re]
      linarith
    simpa [u, A, b, suzukiYoshidaCorrectedCompleteForm_smul_right,
      comparison_energy_smul_self_re] using hmaster

end

end RiemannHypothesisProject.Experiments.M100
