module

public import NLA.RA02.PaperPivotDefinitions
public import NLA.RA03.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Actual ordered-eigenvalue tail of the printed family, totalized away from
Hermitian inputs. The family is proved Hermitian whenever t is positive. -/
def familyRankTail (r : ℕ) (t : ℝ) : ℝ :=
  if h : (complexify (sharpFamily (r+1) t)).IsHermitian then
    NLA.RA02.rankTail (complexify (sharpFamily (r+1) t)) h r else 0

/-- Actual squared singular-value tail used by the archived LU algorithm. -/
def familySingularTailSquared (r : ℕ) (t : ℝ) : ℝ :=
  NLA.RA03.singularTailSq (complexify (sharpFamily (r+1) t)) r

end NLA.RA02.Paper
