import RiemannHypothesisProject.RiemannWeilShiftedRadius.RealSchwartzSeminorms
import RiemannHypothesisProject.SchwartzRiemannWeilWeight

/-!
# Critical-line zero-argument continuity

This module contains fixed-zero continuity facts for the Riemann-Weil
zero argument at critical-line points.
-/

namespace RiemannHypothesisProject

open scoped Topology

/-- If a zero is known to be the critical-line point `1/2 + i t`, then the
corresponding fixed zero-argument evaluation is just fixed real evaluation, and
is therefore continuous for every extension system. -/
theorem zeroArgument_extension_continuous_of_criticalLinePoint
    (system : SchwartzRiemannWeilExtensionSystem)
    (t : Real)
    {rho : ZetaZeroSubtype}
    (hrho : (rho : Complex) = criticalLinePoint t) :
    Continuous fun f : SchwartzLineTestFunction =>
      system.extension f (riemannWeilZeroArgument (rho : Complex)) := by
  have harg : riemannWeilZeroArgument (rho : Complex) = (t : Complex) := by
    rw [hrho, riemannWeilZeroArgument_criticalLinePoint]
  simpa [harg, system.extension_restricts] using
    schwartzLineEvaluation_continuous t

/-- Critical-line specialization of zero-value continuity. -/
theorem zeroValue_continuous_of_criticalLinePoint
    (system : SchwartzRiemannWeilExtensionSystem)
    (t : Real)
    {rho : ZetaZeroSubtype}
    (hrho : (rho : Complex) = criticalLinePoint t) :
    Continuous fun f : SchwartzLineTestFunction =>
      system.zeroValue f rho := by
  simpa [SchwartzRiemannWeilExtensionSystem.zeroValue] using
    zeroArgument_extension_continuous_of_criticalLinePoint
      system t hrho

/-- Critical-line specialization of zero-side weight continuity. -/
theorem zeroWeight_continuous_of_criticalLinePoint
    (system : SchwartzRiemannWeilExtensionSystem)
    (t : Real)
    {rho : ZetaZeroSubtype}
    (hrho : (rho : Complex) = criticalLinePoint t) :
    Continuous fun f : SchwartzLineTestFunction =>
      system.weight f rho := by
  change Continuous
    (Complex.re ∘ fun f : SchwartzLineTestFunction => system.zeroValue f rho)
  exact Complex.continuous_re.comp
    (zeroValue_continuous_of_criticalLinePoint system t hrho)

end RiemannHypothesisProject
