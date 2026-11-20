module

public import NLA.RA02.PaperLUScaling
public import NLA.RA02.PaperReplicationUpdates
public import NLA.RA02.FiniteExpectation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem realTrace_real_smul {n : ℕ} (c : ℝ) (A : NLA.RA02.Square n) :
    NLA.RA02.realTrace (c • A)=c*NLA.RA02.realTrace A := by
  simp only [NLA.RA02.realTrace,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]

theorem choleskyStep_real_smul {n : ℕ} (c : ℝ) (A : NLA.RA02.Square n) (j : Fin n) :
    NLA.RA02.choleskyStep (c • A) j=c • NLA.RA02.choleskyStep A j := by
  rw [choleskyStep_eq_lu_diagonal,choleskyStep_eq_lu_diagonal]
  exact lu_pivotResidual_real_smul c A (j,j)

theorem cholesky_pivotMass_real_smul {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (A : NLA.RA02.Square n) (j : Fin n) :
    NLA.RA02.pivotMass (c • A) j=NLA.RA02.pivotMass A j := by
  simp only [NLA.RA02.pivotMass,realTrace_real_smul]
  by_cases ht : NLA.RA02.realTrace A=0
  · simp only [ht,mul_zero,ite_true]
  · have htc : c*NLA.RA02.realTrace A ≠ 0 := mul_ne_zero hc ht
    simp only [if_neg htc,if_neg ht,Matrix.smul_apply,Complex.smul_re,smul_eq_mul]
    field_simp [hc,ht]

theorem cholesky_expectedTrace_real_smul {n : ℕ} (c : ℝ) (A : NLA.RA02.Square n)
    (r : ℕ) : NLA.RA02.expectedTrace (c • A) r=c*NLA.RA02.expectedTrace A r := by
  by_cases hc : c=0
  · subst c
    rw [zero_smul,(NLA.RA02.zero_residual n r []).2,zero_mul]
  · induction r generalizing A with
    | zero => rw [NLA.RA02.expectedTrace_zero_steps,NLA.RA02.expectedTrace_zero_steps,realTrace_real_smul]
    | succ r ih =>
      rw [NLA.RA02.expectedTrace_succ,NLA.RA02.expectedTrace_succ,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [cholesky_pivotMass_real_smul c hc,choleskyStep_real_smul,ih]
      ring

#print axioms cholesky_expectedTrace_real_smul
end NLA.RA02.Paper
