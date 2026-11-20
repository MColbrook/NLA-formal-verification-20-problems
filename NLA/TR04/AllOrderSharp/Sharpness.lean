module

public import NLA.TR04.AllOrderSharp.Modified
public import NLA.TR04.AllOrderSharp.SharpnessHelpers

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Matrix Topology

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion Reference.LexOrderedTensorSolver

theorem canonical_modified_error {N q : ℕ} (hN : q+2 ≤ N) (n : ℕ) :
    tensorFrobeniusSq
      (Sub.sub (family hN (Matrix.diagonal (fun b => coefficient n b.val)))
        (solver (family hN (Matrix.diagonal (fun b => coefficient n b.val)))
          (q+1) (remainingRanks q))) =
            ∑ b : Fin (q+1), coefficient n (b.val+1) ^ 2 := by
  have ho := modified_exact hN (1 : Matrix (Fin (q+2)) (Fin (q+2)) ℝ)
    (by simp) (coefficient n) (coefficient_pos n) (coefficient_sq_strictAnti n)
  simp only [Matrix.one_mul] at ho
  rw [ho]
  exact root_branch_error hN (coefficient n)

/-- For each fixed tensor order d=q+2, no squared-error multiplier below d-1
holds for the actual modified solver against every feasible comparison tensor.
The ranks are [d-1,d-2,...,1] and all mode sizes are d. This is a genuine
per-order obstruction, rather than padding the order-three construction.
-/
theorem fixed_order_sharp (q : ℕ) (C : ℝ) (hC : C < ((q+1 : ℕ) : ℝ)) :
    ∃ A Y : Tensor (q+2) (List.replicate (q+1) (q+2)),
      feasible (q+2) (List.replicate (q+1) (q+2)) Y (ranks q) ∧
      0 < tensorFrobeniusSq (A-Y) ∧
      C * tensorFrobeniusSq (A-Y) <
        tensorFrobeniusSq (Sub.sub A (solver A (q+1) (remainingRanks q))) := by
  have hev : ∀ᶠ n : ℕ in atTop, C < squaredErrorRatio q n :=
    (tendsto_order.mp (squaredErrorRatio_tendsto q)).1 C hC
  obtain ⟨n, hn⟩ := hev.exists
  have hN : q+2 ≤ q+2 := le_rfl
  let A := family hN (Matrix.diagonal (fun b => coefficient n b.val))
  obtain ⟨Y, hY, he⟩ := weighted_optimal_candidate hN
    (1 : Matrix (Fin (q+2)) (Fin (q+2)) ℝ) (by simp)
    (fun b => coefficient n b.val)
  simp only [Matrix.one_mul] at he
  have hden : 0 < coefficient n 1 ^ 2 := sq_pos_of_pos (coefficient_pos n 1)
  refine ⟨A, Y, hY, ?_, ?_⟩
  · rw [he]
    exact hden
  · rw [he, canonical_modified_error hN n]
    exact (lt_div_iff₀ hden).mp hn

#print axioms canonical_modified_error
#print axioms fixed_order_sharp
#print axioms fixed_order_strict

end NLA.TR04.AllOrderSharp
