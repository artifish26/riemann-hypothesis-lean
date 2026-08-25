import RiemannHypothesisProject.Experiments.M100.SuzukiYoshidaS4Publication

/-!
# Adversarial Suzuki S4 endpoint audit

This consumer keeps the source-package-free compact-window surface and its
radius and spectral-parameter restrictions easy to recheck.  It is audit-only
and is never imported by production or experiment modules.
-/

open RiemannHypothesisProject.Experiments.M100

#check SuzukiDF6EInterval
#check suzukiS4CompactWindowSolution
#check suzukiS4CompactWindowSolution_norm_le_fourThousand
#check suzukiS4CompactWindowSolutionMap_lipschitz
#check suzukiS4CompactWindowSolutionMap_isCompact_range
#check eventually_suzukiS4CompactWindowSolution_close_from_below
