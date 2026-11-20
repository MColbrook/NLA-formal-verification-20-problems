module

public import NLA.MI22.PaperRootLipschitz

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped MatrixOrder ComplexOrder
namespace NLA.MI22.Paper

theorem paper_root_lipschitz {n : ℕ} (P Q : Mat n) (m α : ℝ) (hm : 0 < m)
    (hα : 0 < α) (hα1 : α < 1) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (hPm : m • (1 : Mat n) ≤ P) (hQm : m • (1 : Mat n) ≤ Q) :
    operatorNorm (spectralPower P α-spectralPower Q α) ≤
      α*m^(α-1)*operatorNorm (P-Q) := by
  exact root_lipschitz P Q m α hm hα hα1 hP hQ hPm hQm

#print axioms paper_root_lipschitz

end NLA.MI22.Paper
