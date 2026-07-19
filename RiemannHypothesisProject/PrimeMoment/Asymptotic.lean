import RiemannHypothesisProject.PrimeMoment.WeightedError

/-!
# Unconditional Bombieri--Lagarias prime-moment asymptotics

Finite partial summation and the pinned PNT remainder now give the complete
moment family.  The limiting constant is kept in its canonical convergent
integral form; identifying it with Laurent coefficients is optional.
-/

namespace RiemannHypothesisProject

namespace ComplexCompactExhaustion

noncomputable section

open Filter MeasureTheory
open scoped Topology

/-- The canonical finite part of the `j`th von Mangoldt moment. -/
def liPrimeMomentLimit (j : Nat) : Real :=
  liPrimeMomentWeight j 1 -
    ∫ x in Set.Ioi (1 : Real),
      deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x

theorem tendsto_liPrimeMomentErrorIntegral (j : Nat) :
    Tendsto
      (fun N : Nat => ∫ x in Set.Ioc (1 : Real) N,
        deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x)
      atTop
      (nhds (∫ x in Set.Ioi (1 : Real),
        deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x)) := by
  have h := intervalIntegral_tendsto_integral_Ioi (f := fun x =>
      deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x)
    1 (integrableOn_weighted_liPrimeMomentPNTError j)
    tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [intervalIntegral.integral_of_le (by exact_mod_cast hN)]

/-- The full published prime-moment asymptotic family, discharged from the
pinned PNT source for every natural moment index. -/
theorem bombieriLagariasPrimeMomentAsymptotic
    (j : Nat) :
    BombieriLagariasPrimeMomentAsymptotic j
      (liPrimeMomentLimit j) := by
  have hlimit : Tendsto
      (fun N : Nat =>
        liPrimeMomentWeight j 1 +
          liPrimeMomentWeight j N * liPrimeMomentPNTError N -
            ∫ x in Set.Ioc (1 : Real) N,
              deriv (liPrimeMomentWeight j) x * liPrimeMomentPNTError x)
      atTop (nhds (liPrimeMomentLimit j)) := by
    simpa only [liPrimeMomentLimit, add_zero] using
      (tendsto_const_nhds.add (tendsto_liPrimeMomentWeight_mul_pntError j)).sub
        (tendsto_liPrimeMomentErrorIntegral j)
  exact hlimit.congr' (by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (liPrimeMomentRemainder_eq_error j N hN).symm)

/-- The source family in the exact finite-range shape consumed by the cutoff
covariance theorem. -/
theorem bombieriLagariasPrimeMomentAsymptotics_range (n : Nat) :
    ∀ j ∈ Finset.range n,
      BombieriLagariasPrimeMomentAsymptotic j (liPrimeMomentLimit j) := by
  intro j hj
  exact bombieriLagariasPrimeMomentAsymptotic j

end

end ComplexCompactExhaustion

end RiemannHypothesisProject
