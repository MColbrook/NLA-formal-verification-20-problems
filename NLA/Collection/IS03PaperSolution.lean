module

public import NLA.IS03.Proof
public import NLA.IS03.Fitting
public import NLA.IS03.ZeroPadding

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.IS03

theorem paper_padded_seventh_trace {n : ℕ} (B : RealMatrix n) (r : ℕ)
    (hB : B.charpoly = Polynomial.X ^ r * derivativePolynomial) :
    Matrix.trace (B ^ 7) = -8593 / 823543 := by
  exact zero_padding_matrix_seventh_trace B r hB

theorem paper_counterexample :
    EntrywiseNonnegative witnessMatrix ∧
    ∀ (r : ℕ) (B : RealMatrix (6 + r)), EntrywiseNonnegative B →
      B.charpoly ≠ Polynomial.X ^ r * normalizedDerivative 7 witnessMatrix.charpoly := by
  refine ⟨witness_admissible_proved.1, ?_⟩
  intro r B hB
  rw [witness_polynomials_proved.2.1]
  exact zero_padding_nonrealizability B hB r

#print axioms paper_padded_seventh_trace
#print axioms paper_counterexample

end NLA.IS03
