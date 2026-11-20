module

public import NLA.RA02.PaperCholeskyTailBound
public import NLA.RA02.FiniteExpectation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem cholesky_expectedTrace_upper {n : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (r : ℕ) (hr : r ≤ n) :
    NLA.RA02.expectedTrace A r ≤ (2 : ℝ)^r*NLA.RA02.rankTail A hA.isHermitian r := by
  induction r generalizing A with
  | zero =>
    rw [NLA.RA02.expectedTrace_zero_steps, pow_zero, one_mul, NLA.RA02.trace_eq_sum_ordered A hA.isHermitian]
    simp [NLA.RA02.rankTail]
  | succ r ih =>
    rw [NLA.RA02.expectedTrace_succ]
    calc
      (∑ p, NLA.RA02.pivotMass A p * NLA.RA02.expectedTrace (NLA.RA02.choleskyStep A p) r) ≤
          ∑ p, NLA.RA02.pivotMass A p*((2:ℝ)^r*NLA.RA02.rankTail (NLA.RA02.choleskyStep A p)
            (NLA.RA02.choleskyStep_posSemidef A hA p).isHermitian r) := by
        apply Finset.sum_le_sum
        intro p _
        exact mul_le_mul_of_nonneg_left (ih (NLA.RA02.choleskyStep A p)
          (NLA.RA02.choleskyStep_posSemidef A hA p) (by omega)) (NLA.RA02.pivotMass_nonneg hA p)
      _ = (2:ℝ)^r*(∑ p, NLA.RA02.pivotMass A p*NLA.RA02.rankTail (NLA.RA02.choleskyStep A p)
          (NLA.RA02.choleskyStep_posSemidef A hA p).isHermitian r) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
      _ ≤ (2:ℝ)^r*(2*NLA.RA02.rankTail A hA.isHermitian (r+1)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) r)
        simpa using cholesky_one_step_tail_bound (k := r+1) (by omega) hr A hA
      _ = _ := by rw [pow_succ]; ring

#print axioms cholesky_expectedTrace_upper
end NLA.RA02.Paper
