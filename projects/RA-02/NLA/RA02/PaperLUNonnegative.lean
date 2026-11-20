module

public import NLA.RA02.PaperLUProcess

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem lu_expectedError_zero_matrix {m n : ℕ} (r : ℕ) :
    NLA.RA03.expectedError (0 : Matrix (Fin m) (Fin n) ℂ) r=0 := by
  induction r with
  | zero => rw [lu_expectedError_zero]; simp [NLA.RA03.frobeniusSq]
  | succ r ih =>
    rw [lu_expectedError_succ]
    apply Finset.sum_eq_zero
    intro p _
    have hn : NLA.RA03.nextResidual (0 : Matrix (Fin m) (Fin n) ℂ) p=0 := by
      cases p <;> simp [NLA.RA03.nextResidual,NLA.RA03.pivotResidual]
    rw [hn,ih,mul_zero]

theorem lu_expectedError_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    0 ≤ NLA.RA03.expectedError A r := by
  induction r generalizing A with
  | zero => rw [lu_expectedError_zero]; exact lu_frobeniusSq_nonneg A
  | succ r ih =>
    rw [lu_expectedError_succ]
    exact Finset.sum_nonneg (fun p _ => mul_nonneg (lu_pivotMass_nonneg A p) (ih _))

#print axioms lu_expectedError_nonneg
end NLA.RA02.Paper
