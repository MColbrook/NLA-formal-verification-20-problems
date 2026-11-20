module

public import NLA.RA02.PaperPivotDefinitions
public import NLA.RA03.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- The joint conditional LU law, in chronological list form. -/
def luListMass {n : ℕ} : Matrix (Fin n) (Fin n) ℝ → List (Option (Fin n × Fin n)) → ℝ
  | _, [] => 1
  | A, p :: w => NLA.RA03.pivotMass (complexify A) p * luListMass (realLUNext A p) w

/-- Product of the squared Frobenius norms of the actual prefix residuals. -/
def luNormalizerProduct {n : ℕ} : Matrix (Fin n) (Fin n) ℝ → List (Option (Fin n × Fin n)) → ℝ
  | _, [] => 1
  | A, p :: w => NLA.RA03.frobeniusSq (complexify A) * luNormalizerProduct (realLUNext A p) w

end NLA.RA02.Paper
