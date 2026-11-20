module

public import NLA.PF02.IntrinsicSupport.IntrinsicRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02IntrinsicSupport
open Matrix Module Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem triangular_rank_dimension_le {a b : ℕ}
    (h : a * (a + 1) / 2 ≤ b * (b + 1) / 2) : a ≤ b := by
  have ha : a * (a + 1) < a * (a + 1) / 2 * 2 + 2 := by omega
  have hb := Nat.div_mul_le_self (b * (b + 1)) 2
  by_contra hle
  have hlt : b < a := by omega
  nlinarith

/-- Actual leading/trailing trace matrices force the intrinsic support dimensions.
This is the generic rank/support step, not the all-size quotient or perturbation theorem. -/
theorem leading_trailing_support_dimensions {r : ℕ}
    (L : Matrix (Fin 6) (Fin 6) ℝ)
    (R : Matrix (Fin (r * (r + 1) / 2)) (Fin (r * (r + 1) / 2)) ℝ)
    (A B : Fin 6 → Mat (Fin (r + 3)))
    (C D : Fin (r * (r + 1) / 2) → Mat (Fin (r + 3)))
    (hA : ∀ i, (A i).PosSemidef) (hD : ∀ j, (D j).PosSemidef)
    (hzero : ∀ i j, Matrix.trace (A i * D j) = 0)
    (hL : ∀ i j, Matrix.trace (A i * B j) = L i j)
    (hR : ∀ i j, Matrix.trace (C i * D j) = R i j)
    (hrankL : L.rank = 6) (hrankR : R.rank = r * (r + 1) / 2) :
    (∑ j, D j).rank = r ∧
      finrank ℝ (image (∑ j, D j)) = r ∧
      finrank ℝ (kernel (∑ j, D j)) = 3 ∧
      (∀ j, SupportedOn (D j) (image (∑ j, D j))) ∧
      (∀ i, SupportedOn (A i) (kernel (∑ j, D j))) := by
  classical
  let Q : Mat (Fin (r + 3)) := ∑ j, D j
  have hlead := psd_zero_block_kernel_trace_rank_le L A B D hA hD hzero hL
  rw [hrankL] at hlead
  have hker : 3 ≤ finrank ℝ (kernel Q) :=
    triangular_rank_dimension_le (a := 3) (b := finrank ℝ (kernel Q)) (by simpa [Q] using hlead)
  have htrail := psd_family_image_trace_rank_le R.transpose D C hD
    (fun j i => (Matrix.trace_mul_comm (D j) (C i)).trans (hR i j))
  rw [Matrix.rank_transpose, hrankR] at htrail
  have him : r ≤ Q.rank := triangular_rank_dimension_le (by simpa [Q] using htrail)
  have hsum := image_kernel_finrank_sum Q
  rw [← rank_eq_image_finrank] at hsum
  have hr : Q.rank = r := by omega
  have hk : finrank ℝ (kernel Q) = 3 := by omega
  refine ⟨hr, ?_, hk, ?_, ?_⟩
  · rw [← rank_eq_image_finrank, hr]
  · exact fun j => psd_family_each_supported_sum_image D hD j
  · exact fun i => psd_trace_zero_family_supported_common_kernel (A i) D (hA i) hD (hzero i)

#print axioms triangular_rank_dimension_le
#print axioms leading_trailing_support_dimensions
end Reference.PF02IntrinsicSupport
