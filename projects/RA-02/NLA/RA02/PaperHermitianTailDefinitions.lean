module

public import NLA.RA02.PaperCorrelationDefinitions
public import NLA.RA02.PaperRectangularBestDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- The actual ordered eigenvalue tail, with zero assigned to non-Hermitian matrices. -/
def hermitianRankTail {n : ℕ} (A : NLA.RA02.Square n) (r : ℕ) : ℝ :=
  if h : A.IsHermitian then NLA.RA02.rankTail A h r else 0

end NLA.RA02.Paper
