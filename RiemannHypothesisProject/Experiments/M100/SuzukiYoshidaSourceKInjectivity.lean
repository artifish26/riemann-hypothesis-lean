import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaSourceNormConsumer

/-!
# M100-DF6F inverse-Neumann source injectivity

This module proves that the compressed inverse-Neumann operator has trivial
kernel on the zero-mean interval `L2` space.  The proof uses the already
checked dense smooth differential core, the primitive-energy identity, and
one Schwartz integration-by-parts identity.  It does not diagonalize the
compact kernel or introduce a Sobolev-space realization.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

open Set MeasureTheory
open SchwartzLineTestFunction
open scoped ENNReal InnerProductSpace ComplexConjugate Topology

attribute [local instance] Measure.Subtype.measureSpace

local instance suzukiSourceKInjectivityCompleteSpace (a : Real) :
    CompleteSpace (SuzukiFiniteIntervalZeroMeanL2 a) := by
  change CompleteSpace (suzukiFiniteIntervalMeanCLM a).ker
  infer_instance

/-- The global `L2` class of the second Suzuki differential of a smooth-core
test. -/
private def suzukiSmoothCoreSecondDifferentialToL2
    {a : Real} (w : SuzukiSmoothCore a) : SuzukiL2 :=
  SchwartzMap.toLpCLM Complex Complex (2 : ENNReal) volume
    (suzukiDifferential (suzukiDifferential w.1))

/-- Integration by parts moves one Suzuki differential from a variable smooth
primitive onto a fixed smooth test.  The left side is the finite-interval
pairing used by the density theorem; the right side is an ordinary global
`L2` pairing, so it is controlled by the primitive norm. -/
private theorem inner_smoothCoreDifferentials_eq_secondDifferential_primitive
    {a : Real} (ha : 0 < a) (w v : SuzukiSmoothCore a) :
    inner Complex
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha w)
        (suzukiSmoothCoreDifferentialZeroMeanL2 ha v) =
      inner Complex (suzukiSmoothCoreSecondDifferentialToL2 w)
        (suzukiSmoothCoreToL2 v) := by
  letI : IsFiniteMeasure
      (volume : Measure (SuzukiFiniteInterval a)) :=
    { measure_univ_lt_top := by
        rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc]
        exact measure_Icc_lt_top }
  have hwCoe :
      ((suzukiSmoothCoreDifferentialZeroMeanL2 ha w :
          SuzukiFiniteIntervalL2 a) : SuzukiFiniteInterval a → Complex) =ᵐ[volume]
        fun x => suzukiDifferential w.1 x.1 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreDifferentialFiniteIntervalContinuous w)
  have hvCoe :
      ((suzukiSmoothCoreDifferentialZeroMeanL2 ha v :
          SuzukiFiniteIntervalL2 a) : SuzukiFiniteInterval a → Complex) =ᵐ[volume]
        fun x => suzukiDifferential v.1 x.1 := by
    exact ContinuousMap.coeFn_toLp
      (𝕜 := Complex) (p := (2 : ENNReal))
      (volume : Measure (SuzukiFiniteInterval a))
      (suzukiSmoothCoreDifferentialFiniteIntervalContinuous v)
  have hleft :
      inner Complex
          ((suzukiSmoothCoreDifferentialZeroMeanL2 ha w :
            SuzukiFiniteIntervalZeroMeanL2 a) : SuzukiFiniteIntervalL2 a)
          ((suzukiSmoothCoreDifferentialZeroMeanL2 ha v :
            SuzukiFiniteIntervalZeroMeanL2 a) : SuzukiFiniteIntervalL2 a) =
        ∫ x in Set.Icc (-a) a,
          suzukiDifferential v.1 x * conj (suzukiDifferential w.1 x) := by
    rw [MeasureTheory.L2.inner_def]
    calc
      (∫ x : SuzukiFiniteInterval a,
          inner Complex
            ((suzukiSmoothCoreDifferentialZeroMeanL2 ha w :
              SuzukiFiniteIntervalL2 a) x)
            ((suzukiSmoothCoreDifferentialZeroMeanL2 ha v :
              SuzukiFiniteIntervalL2 a) x)) =
          ∫ x : SuzukiFiniteInterval a,
            suzukiDifferential v.1 x.1 *
              conj (suzukiDifferential w.1 x.1) := by
        apply integral_congr_ae
        filter_upwards [hwCoe, hvCoe] with x hwx hvx
        rw [hwx, hvx]
        rfl
      _ = ∫ x in Set.Icc (-a) a,
          suzukiDifferential v.1 x * conj (suzukiDifferential w.1 x) := by
        exact MeasureTheory.integral_subtype measurableSet_Icc
          (fun x : Real =>
            suzukiDifferential v.1 x * conj (suzukiDifferential w.1 x))
  have hsupportV : Function.support (suzukiDifferential v.1) ⊆
      Set.Icc (-a) a :=
    support_suzukiDifferential_subset_Icc fun x hx =>
      ⟨(v.2 hx).1.le, (v.2 hx).2.le⟩
  have hleftGlobal :
      (∫ x in Set.Icc (-a) a,
          suzukiDifferential v.1 x * conj (suzukiDifferential w.1 x)) =
        ∫ x : Real,
          suzukiDifferential v.1 x * conj (suzukiDifferential w.1 x) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hvzero : suzukiDifferential v.1 x = 0 := by
      by_contra hne
      exact hx (hsupportV hne)
    rw [hvzero, zero_mul]
  have hconjDeriv :
      SchwartzMap.derivCLM Complex Complex
          (conjugate (suzukiDifferential w.1)) =
        conjugate
          (SchwartzMap.derivCLM Complex Complex
            (suzukiDifferential w.1)) := by
    ext x
    change deriv (fun y : Real => conj (suzukiDifferential w.1 y)) x =
      conj (deriv (fun y : Real => suzukiDifferential w.1 y) x)
    exact (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x
      ((suzukiDifferential w.1).hasDerivAt x)).deriv
  have hibp := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul
    (conjugate (suzukiDifferential w.1)) v.1
  change
    (∫ x : Real,
        conjugate (suzukiDifferential w.1) x *
          SchwartzMap.derivCLM Complex Complex v.1 x) =
      -(∫ x : Real,
        SchwartzMap.derivCLM Complex Complex
            (conjugate (suzukiDifferential w.1)) x * v.1 x) at hibp
  rw [hconjDeriv] at hibp
  simp only [conjugate_apply] at hibp
  have hparts :
      (∫ x : Real,
          suzukiDifferential v.1 x * conj (suzukiDifferential w.1 x)) =
        ∫ x : Real,
          v.1 x *
            conj (suzukiDifferential (suzukiDifferential w.1) x) := by
    calc
      (∫ x : Real,
          suzukiDifferential v.1 x * conj (suzukiDifferential w.1 x)) =
          Complex.I *
            ∫ x : Real,
              conj (suzukiDifferential w.1 x) *
                SchwartzMap.derivCLM Complex Complex v.1 x := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        rw [suzukiDifferential_apply]
        ring
      _ = Complex.I *
          (-(∫ x : Real,
            conj (SchwartzMap.derivCLM Complex Complex
              (suzukiDifferential w.1) x) * v.1 x)) := by
        rw [hibp]
      _ = ∫ x : Real,
          v.1 x *
            conj (suzukiDifferential (suzukiDifferential w.1) x) := by
        rw [← integral_neg, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        rw [suzukiDifferential_apply, map_mul, Complex.conj_I]
        ring
  have hsecondCoe :
      (suzukiSmoothCoreSecondDifferentialToL2 w : Real → Complex) =ᵐ[volume]
        suzukiDifferential (suzukiDifferential w.1) :=
    (suzukiDifferential (suzukiDifferential w.1)).memLp
      (2 : ENNReal) (volume : Measure Real) |>.coeFn_toLp
  have hvGlobalCoe :
      (suzukiSmoothCoreToL2 v : Real → Complex) =ᵐ[volume] v.1 :=
    v.1.memLp (2 : ENNReal) (volume : Measure Real) |>.coeFn_toLp
  have hright :
      inner Complex (suzukiSmoothCoreSecondDifferentialToL2 w)
          (suzukiSmoothCoreToL2 v) =
        ∫ x : Real,
          v.1 x *
            conj (suzukiDifferential (suzukiDifferential w.1) x) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hsecondCoe, hvGlobalCoe] with x hsx hvx
    rw [hsx, hvx]
    rfl
  change inner Complex
      ((suzukiSmoothCoreDifferentialZeroMeanL2 ha w :
        SuzukiFiniteIntervalZeroMeanL2 a) : SuzukiFiniteIntervalL2 a)
      ((suzukiSmoothCoreDifferentialZeroMeanL2 ha v :
        SuzukiFiniteIntervalZeroMeanL2 a) : SuzukiFiniteIntervalL2 a) = _
  rw [hleft, hleftGlobal, hparts, ← hright]

/-- The compressed inverse-Neumann operator has trivial kernel on the complete
zero-mean interval source space. -/
theorem suzukiSourceKOperator_injective
    {a : Real} (ha : 0 < a) :
    Function.Injective (suzukiSourceKOperator a) := by
  rw [← suzukiSourceKSeminorm_definite_iff_injective ha]
  intro u hseminorm
  have hkernel : suzukiSourceKOperator a u = 0 :=
    (suzukiSourceKSeminorm_eq_zero_iff ha u).mp hseminorm
  let coreDifferential : SuzukiSmoothCore a →
      SuzukiFiniteIntervalZeroMeanL2 a :=
    fun v => suzukiSmoothCoreDifferentialZeroMeanL2 ha v
  have hdense : DenseRange coreDifferential :=
    suzukiSmoothDifferentialCoreDenseAt a ha
  have huClosure : u ∈ closure (Set.range coreDifferential) := by
    rw [hdense.closure_eq]
    exact Set.mem_univ u
  obtain ⟨d, hdRange, hdTendsto⟩ :=
    (mem_closure_iff_seq_limit.mp huClosure)
  choose v hv using hdRange
  have hdTendsto' : Filter.Tendsto (fun n => coreDifferential (v n))
      Filter.atTop (𝓝 u) := by
    simpa only [hv] using hdTendsto
  have hKTendsto : Filter.Tendsto
      (fun n => suzukiSourceKOperator a (coreDifferential (v n)))
      Filter.atTop (𝓝 0) := by
    have ht :=
      (suzukiSourceKOperator a).continuous.continuousAt.tendsto.comp hdTendsto'
    change Filter.Tendsto
      (fun n => suzukiSourceKOperator a (coreDifferential (v n)))
      Filter.atTop (𝓝 (suzukiSourceKOperator a u)) at ht
    simpa only [hkernel] using ht
  have henergyTendsto : Filter.Tendsto
      (fun n => inner Complex
        (suzukiSourceKOperator a (coreDifferential (v n)))
        (coreDifferential (v n))) Filter.atTop (𝓝 0) := by
    have ht := Filter.Tendsto.inner (𝕜 := Complex) hKTendsto hdTendsto'
    change Filter.Tendsto
      (fun n => inner Complex
        (suzukiSourceKOperator a (coreDifferential (v n)))
        (coreDifferential (v n))) Filter.atTop (𝓝 (inner Complex 0 u)) at ht
    simpa using ht
  have hprimitiveSqTendsto : Filter.Tendsto
      (fun n => ‖suzukiSmoothCoreToL2 (v n)‖ ^ 2)
      Filter.atTop (𝓝 0) := by
    have hre := (Complex.continuous_re.tendsto 0).comp henergyTendsto
    have heq :
        (fun n => (inner Complex
          (suzukiSourceKOperator a (coreDifferential (v n)))
          (coreDifferential (v n))).re) =
          fun n => ‖suzukiSmoothCoreToL2 (v n)‖ ^ 2 := by
      funext n
      dsimp only [coreDifferential]
      unfold suzukiSmoothCoreDifferentialZeroMeanL2
      rw [inner_suzukiSourceKOperator_smoothCoreDifferential_eq_norm_sq ha]
      rfl
    change Filter.Tendsto
      (fun n => (inner Complex
        (suzukiSourceKOperator a (coreDifferential (v n)))
        (coreDifferential (v n))).re) Filter.atTop (𝓝 0) at hre
    rw [heq] at hre
    exact hre
  have hprimitiveTendsto : Filter.Tendsto
      (fun n => suzukiSmoothCoreToL2 (v n)) Filter.atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hsqrt := hprimitiveSqTendsto.sqrt
    simpa only [sub_zero, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
  have horthCore : ∀ w : SuzukiSmoothCore a,
      inner Complex (coreDifferential w) u = 0 := by
    intro w
    have hleftLimit := Filter.Tendsto.inner (𝕜 := Complex)
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : Nat => coreDifferential w) Filter.atTop (𝓝 (coreDifferential w)))
      hdTendsto'
    have hrightLimit := Filter.Tendsto.inner (𝕜 := Complex)
      (tendsto_const_nhds : Filter.Tendsto
        (fun _ : Nat => suzukiSmoothCoreSecondDifferentialToL2 w)
        Filter.atTop (𝓝 (suzukiSmoothCoreSecondDifferentialToL2 w)))
      hprimitiveTendsto
    have heq : (fun n => inner Complex (coreDifferential w)
        (coreDifferential (v n))) =
        fun n => inner Complex (suzukiSmoothCoreSecondDifferentialToL2 w)
          (suzukiSmoothCoreToL2 (v n)) := by
      funext n
      exact inner_smoothCoreDifferentials_eq_secondDifferential_primitive
        ha w (v n)
    have hzero : Filter.Tendsto
        (fun n => inner Complex (coreDifferential w)
          (coreDifferential (v n))) Filter.atTop (𝓝 0) := by
      rw [heq]
      simpa using hrightLimit
    exact tendsto_nhds_unique hleftLimit hzero
  let p : SuzukiFiniteIntervalZeroMeanL2 a → Prop := fun z =>
    inner Complex z u = 0
  have hall : ∀ z : SuzukiFiniteIntervalZeroMeanL2 a, p z := by
    intro z
    apply DenseRange.induction_on (p := p) hdense z
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · exact horthCore
  exact inner_self_eq_zero.mp (hall u)

/-- Consequently, the inverse-Neumann source seminorm is a genuine norm on
the zero-mean interval source space. -/
theorem suzukiSourceKSeminorm_definite
    {a : Real} (ha : 0 < a) (u : SuzukiFiniteIntervalZeroMeanL2 a) :
    suzukiSourceKSeminorm a u = 0 → u = 0 :=
  (suzukiSourceKSeminorm_definite_iff_injective ha).mpr
    (suzukiSourceKOperator_injective ha) u

end

end RiemannHypothesisProject.Experiments.M100
