import RiemannHypothesisProject.Experiments.M100.SuzukiEndpointCertificateData

/-!
# Finite endpoint certificate consumers for M100-DF6D4

The generated rational computations are consumed here.  Each theorem leaves
only the analytic enclosure proof for the concrete shifted endpoint matrix;
there is no eigenvalue, positivity, or Arb-output hypothesis.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

noncomputable section

theorem suzukiDF6D4EvenLower_posSemidef_of_entryEnclosures
    (M : Matrix (Fin 45) (Fin 45) Real)
    (hM : M.IsHermitian)
    (henclose : ∀ i j,
      (suzukiDF6D4EvenLowerCertificate.entry i j).Contains (M i j)) :
    M.PosSemidef :=
  suzukiDF6D4EvenLowerCertificate.posSemidef_of_valid_of_entry_enclosures
    M suzukiDF6D4EvenLowerCertificate_valid hM henclose

theorem suzukiDF6D4OddLower_posSemidef_of_entryEnclosures
    (M : Matrix (Fin 44) (Fin 44) Real)
    (hM : M.IsHermitian)
    (henclose : ∀ i j,
      (suzukiDF6D4OddLowerCertificate.entry i j).Contains (M i j)) :
    M.PosSemidef :=
  suzukiDF6D4OddLowerCertificate.posSemidef_of_valid_of_entry_enclosures
    M suzukiDF6D4OddLowerCertificate_valid hM henclose

theorem suzukiDF6D4OddUpper_posSemidef_of_entryEnclosures
    (M : Matrix (Fin 44) (Fin 44) Real)
    (hM : M.IsHermitian)
    (henclose : ∀ i j,
      (suzukiDF6D4OddUpperCertificate.entry i j).Contains (M i j)) :
    M.PosSemidef :=
  suzukiDF6D4OddUpperCertificate.posSemidef_of_valid_of_entry_enclosures
    M suzukiDF6D4OddUpperCertificate_valid hM henclose

end


end M100
end Experiments
end RiemannHypothesisProject
