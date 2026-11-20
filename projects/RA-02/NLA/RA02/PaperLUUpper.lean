module

public import NLA.RA02.PaperLUOneStep

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem lu_expectedError_gram_upper {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) (hr : r ≤ n) : NLA.RA03.expectedError A r ≤ (4:ℝ)^r*gramTail A r := by
  induction r generalizing A with
  | zero => rw [lu_expectedError_zero, pow_zero, one_mul, gramTail_zero_rank]
  | succ r ih =>
    rw [lu_expectedError_succ]
    calc
      (∑ p : NLA.RA03.Pivot m n, NLA.RA03.pivotMass A p*NLA.RA03.expectedError (NLA.RA03.nextResidual A p) r) ≤
          ∑ p, NLA.RA03.pivotMass A p*((4:ℝ)^r*gramTail (NLA.RA03.nextResidual A p) r) := by
        apply Finset.sum_le_sum
        intro p _
        exact mul_le_mul_of_nonneg_left (ih (NLA.RA03.nextResidual A p) (by omega)) (lu_pivotMass_nonneg A p)
      _ = (4:ℝ)^r*(∑ p : NLA.RA03.Pivot m n, NLA.RA03.pivotMass A p*gramTail (NLA.RA03.nextResidual A p) r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ (4:ℝ)^r*(4*gramTail A (r+1)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) r)
        simpa using lu_one_step_tail_bound (k := r+1) (by omega) hr A
      _ = _ := by rw [pow_succ]; ring

#print axioms lu_expectedError_gram_upper
end NLA.RA02.Paper
