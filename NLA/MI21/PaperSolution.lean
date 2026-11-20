module

public import NLA.MI21.PaperRational

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix
noncomputable section
namespace NLA.MI21.Paper

theorem paper_counterexample (p : ℝ) (hp : 0 < p) :
    (∀ i : Fin 2, (witnessA i).PosDef ∧ (witnessB i).PosDef) ∧
    (∑ i, witnessA i) = 1 ∧ (∑ i, witnessB i) = 1 ∧
    leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2 = witnessL ∧
    rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p = 1 ∧
    witnessVector ≠ 0 ∧
    witnessL *ᵥ witnessVector = (witnessEigenvalue : ℂ) • witnessVector ∧
    1 < witnessEigenvalue ∧
    witnessEigenvalue ≤ operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) ∧
    operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) = 1 ∧
    operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) <
      operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) := by
  exact counterexample_proved p hp

theorem paper_rational_inputs (i r s : Fin 2) :
    (∃ q : ℚ, (q : ℂ) = witnessA i r s) ∧
    (∃ q : ℚ, (q : ℂ) = witnessB i r s) := by
  exact rational_witness_entries i r s

theorem paper_operator_norm (n : ℕ) : IsUnitaryInvariantNorm (operatorNorm (n := n)) := by
  exact operatorNorm_isUnitaryInvariant_proved n

#print axioms paper_counterexample
#print axioms paper_rational_inputs
#print axioms paper_operator_norm

end NLA.MI21.Paper
