import RiemannHypothesisProject.LiCriterion.WeilPairing
import RiemannHypothesisProject.SelfAdjointSpectralBridge
import RiemannHypothesisProject.SpectralModel

/-!
# M100-X09 spectral-target circularity audit

This experimental module identifies two minimal scalar shadows of proposed
Hilbert--Polya or reproducing-kernel constructions.  A real-height realization
of every zeta zero and a squared-norm representation of every positive-index
Li-basis diagonal are each equivalent to project RH.

The equivalences are route filters.  They do not construct a zeta operator,
prove positivity, or promote a spectral model into production.
-/

namespace RiemannHypothesisProject
namespace Experiments
namespace M100

open ComplexCompactExhaustion

noncomputable section

/-- Critical-line membership already supplies the tautological real height
given by the imaginary part. -/
theorem criticalLinePoint_im_eq_of_isCriticalLine
    {s : Complex} (hs : IsCriticalLine s) :
    criticalLinePoint s.im = s := by
  apply Complex.ext
  · simpa [criticalLinePoint, IsCriticalLine] using hs.symm
  · simp [criticalLinePoint]

/-- Under RH, the existing abstract height interface can be populated by the
imaginary parts of the zeros. -/
def HeightRealization.of_RHStatement
    (hRH : RHStatement) : HeightRealization where
  height s _hs := s.im
  realizes_nontrivial_zeroes s hs :=
    criticalLinePoint_im_eq_of_isCriticalLine (hRH s hs)

/-- The abstract real-height realization interface is exactly RH, rather than
an independently weaker spectral premise. -/
theorem nonempty_heightRealization_iff_RHStatement :
    Nonempty HeightRealization ↔ RHStatement := by
  constructor
  · rintro ⟨model⟩
    exact RHStatement.of_heightRealization model
  · intro hRH
    exact ⟨HeightRealization.of_RHStatement hRH⟩

/-- RH also supplies the carrier-only real-spectrum interface by using the
nontrivial zeros themselves as the carrier.  No operator has been constructed. -/
def RealSpectrumModel.of_RHStatement
    (hRH : RHStatement) : RealSpectrumModel where
  Carrier := {s : Complex // IsNontrivialZetaZero s}
  height s := (s : Complex).im
  realizes_nontrivial_zeroes s hs :=
    ⟨⟨s, hs⟩, criticalLinePoint_im_eq_of_isCriticalLine (hRH s hs)⟩

/-- The carrier-only real-spectrum interface is likewise equivalent to RH. -/
theorem nonempty_realSpectrumModel_iff_RHStatement :
    Nonempty RealSpectrumModel ↔ RHStatement := by
  constructor
  · rintro ⟨model⟩
    exact RHStatement.of_realSpectrumModel model
  · intro hRH
    exact ⟨RealSpectrumModel.of_RHStatement hRH⟩

/-- Minimal scalar shadow of a Hilbert-space or positive-kernel realization of
the actual Li-basis diagonals.  Any genuine squared-norm representation yields
this data by taking `amplitude n` to be the corresponding norm. -/
structure LiBasisSquaredNormCertificate where
  amplitude : Nat → Real
  represents : ∀ n : Nat, 0 < n →
    zetaLiWeilNormSq n = amplitude n ^ 2

/-- A squared-norm certificate for every positive Li index implies RH through
the already checked criterion-determining Li basis. -/
theorem RHStatement.of_liBasisSquaredNormCertificate
    (certificate : LiBasisSquaredNormCertificate) : RHStatement := by
  rw [RHStatement_iff_zetaLiWeilNormSq_nonneg]
  intro n hn
  rw [certificate.represents n hn]
  exact sq_nonneg _

/-- RH tautologically manufactures the scalar certificate by square-rooting
the already nonnegative Li-basis diagonals. -/
def LiBasisSquaredNormCertificate.of_RHStatement
    (hRH : RHStatement) : LiBasisSquaredNormCertificate where
  amplitude n := Real.sqrt (zetaLiWeilNormSq n)
  represents n hn := by
    have hnonneg : 0 ≤ zetaLiWeilNormSq n :=
      RHStatement_iff_zetaLiWeilNormSq_nonneg.mp hRH n hn
    exact (Real.sq_sqrt hnonneg).symm

/-- Existence of even the weakest scalar squared-norm representation of the
actual Li diagonals is equivalent to RH. -/
theorem nonempty_liBasisSquaredNormCertificate_iff_RHStatement :
    Nonempty LiBasisSquaredNormCertificate ↔ RHStatement := by
  constructor
  · rintro ⟨certificate⟩
    exact RHStatement.of_liBasisSquaredNormCertificate certificate
  · intro hRH
    exact ⟨LiBasisSquaredNormCertificate.of_RHStatement hRH⟩

/-- Any norm-square representation in a seminormed space already collapses to
the scalar certificate above and hence implies RH.  Inner-product structure,
self-adjointness, and completeness are unnecessary for this implication. -/
theorem RHStatement.of_liBasis_normSq_representation
    {E : Type*} [SeminormedAddCommGroup E]
    (vector : Nat → E)
    (represents : ∀ n : Nat, 0 < n →
      zetaLiWeilNormSq n = ‖vector n‖ ^ 2) :
    RHStatement := by
  apply RHStatement.of_liBasisSquaredNormCertificate
  exact
    { amplitude := fun n ↦ ‖vector n‖
      represents := represents }

/-- The globally sufficient Hilbert--Polya bridge needs only an embedding of
every zeta zero into the eigenvalues of a symmetric operator with the checked
affine normalization.  Spectral surjectivity or completeness is not used. -/
theorem RHStatement.of_symmetric_zetaZero_eigenvalueEmbedding
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace Complex E]
    {T : Module.End Complex E}
    (hT : T.IsSymmetric)
    (eigenvalue : ∀ s : Complex, IsNontrivialZetaZero s → Complex)
    (hasEigenvalue :
      ∀ (s : Complex) (hs : IsNontrivialZetaZero s),
        T.HasEigenvalue (eigenvalue s hs))
    (realizes_zeroes :
      ∀ (s : Complex) (hs : IsNontrivialZetaZero s),
        s = (1 / 2 : Complex) + eigenvalue s hs * Complex.I) :
    RHStatement := by
  have hlocal : RHOn (fun _ : Complex ↦ True) :=
    RHOn.of_selfAdjointEigenvalueParametrization
      hT
      (fun s _hs_family hs ↦ eigenvalue s hs)
      (fun s _hs_family hs ↦ hasEigenvalue s hs)
      (fun s _hs_family hs ↦ realizes_zeroes s hs)
  intro s hs
  exact hlocal s trivial hs

end

end M100
end Experiments
end RiemannHypothesisProject
