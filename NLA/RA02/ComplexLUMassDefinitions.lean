module

public import NLA.RA02.ComplexHistoryPaths
public import NLA.RA03.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper.ComplexHistory

/-- The joint conditional LU law, in chronological list form. -/
def luListMass {n : ℕ} : NLA.RA02.Square n → List (Option (Fin n × Fin n)) → ℝ
  | _, [] => 1
  | A, p :: w => NLA.RA03.pivotMass (A) p * luListMass (NLA.RA03.nextResidual A p) w

/-- Product of the squared Frobenius norms of the actual prefix residuals. -/
def luNormalizerProduct {n : ℕ} : NLA.RA02.Square n → List (Option (Fin n × Fin n)) → ℝ
  | _, [] => 1
  | A, p :: w => NLA.RA03.frobeniusSq (A) * luNormalizerProduct (NLA.RA03.nextResidual A p) w

end NLA.RA02.Paper.ComplexHistory
