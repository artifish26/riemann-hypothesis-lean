import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateAssembly
import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointGalerkinResidualCertificateData

/-!
# Odd additive-reserve target for M100-DF6D5

DF6D5 needs the documented `1 / 500` odd reserve before the DF6A Schur
assembly can recover the `999 / 1000` coupling ratio.  DF6D4 checked a
strictly positive residual matrix, but its public target retained only the
common `10^-9` multiplicative reserve.  This module exposes the stronger
additive target against the already admitted DF6D4 interval grid.
-/

namespace RiemannHypothesisProject.Experiments.M100

noncomputable section

def suzukiDF6D5OddAdditiveReserve : Rat := 1 / 500

def suzukiDF6D5OddAdditiveTargetEntryInterval
    (i j : Fin 44) : RationalInterval :=
  (suzukiDF6D4OddResidualTargetCertificate.entry i j).sub
    (RationalInterval.point
      (if i = j then suzukiDF6D5OddAdditiveReserve else 0))

def suzukiDF6D5OddAdditiveTargetMatrix :
    Matrix (Fin 44) (Fin 44) Real :=
  suzukiDF6D4OddResidualCertificateTargetMatrix -
    ((suzukiDF6D5OddAdditiveReserve : Rat) : Real) •
      (1 : Matrix (Fin 44) (Fin 44) Real)

end

end RiemannHypothesisProject.Experiments.M100
