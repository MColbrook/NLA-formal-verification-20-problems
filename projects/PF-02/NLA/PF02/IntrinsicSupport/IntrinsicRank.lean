module

public import NLA.PF02.IntrinsicSupport.FrameExists
public import NLA.PF02.SupportBridge.RestrictedRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02IntrinsicSupport
open Matrix Module Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem rank_eq_image_finrank {k : ℕ} (Q : Mat (Fin k)) :
    Q.rank = finrank ℝ (image Q) :=
  Matrix.rank_eq_finrank_range_toLin Q
    (PiLp.basisFun 2 ℝ (Fin k)) (PiLp.basisFun 2 ℝ (Fin k))

theorem image_kernel_finrank_sum {k : ℕ} (Q : Mat (Fin k)) :
    finrank ℝ (image Q) + finrank ℝ (kernel Q) = k := by
  calc
    _ = finrank ℝ (Reference.PF02Support.Vector (Fin k)) := LinearMap.finrank_range_add_finrank_ker (lin Q)
    _ = k := by simp [Reference.PF02Support.Vector]

theorem symmetric_supported_trace_rank_le {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (U : Submodule ℝ (E k))
    (hA : ∀ i, (A i).transpose = A i)
    (hsupport : ∀ i, SupportedOn (A i) U)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ finrank ℝ U * (finrank ℝ U + 1) / 2 := by
  apply supported_trace_factor_symmetric_rank_le M A B (frame U) (frame_orthonormal U) hA
  · simpa only [frame_range, SupportedOn] using hsupport
  · exact htrace

theorem psd_supported_trace_rank_le {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (U : Submodule ℝ (E k))
    (hA : ∀ i, (A i).PosSemidef)
    (hsupport : ∀ i, SupportedOn (A i) U)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ finrank ℝ U * (finrank ℝ U + 1) / 2 := by
  apply supported_psd_trace_factor_rank_le M A B (frame U) (frame_orthonormal U) hA
  · simpa only [frame_range, SupportedOn] using hsupport
  · exact htrace

theorem psd_image_supported_trace_rank_le {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (Q : Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef)
    (hsupport : ∀ i, SupportedOn (A i) (image Q))
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ Q.rank * (Q.rank + 1) / 2 := by
  rw [rank_eq_image_finrank]
  exact psd_supported_trace_rank_le M A B (image Q) hA hsupport htrace

theorem psd_kernel_supported_trace_rank_le {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (Q : Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef)
    (hsupport : ∀ i, SupportedOn (A i) (kernel Q))
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ finrank ℝ (kernel Q) * (finrank ℝ (kernel Q) + 1) / 2 :=
  psd_supported_trace_rank_le M A B (kernel Q) hA hsupport htrace

theorem psd_zero_block_kernel_trace_rank_le {p q d k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (D : Fin d → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hD : ∀ j, (D j).PosSemidef)
    (hzero : ∀ i j, Matrix.trace (A i * D j) = 0)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ finrank ℝ (kernel (∑ j, D j)) *
      (finrank ℝ (kernel (∑ j, D j)) + 1) / 2 := by
  apply psd_kernel_supported_trace_rank_le M A B (∑ j, D j) hA _ htrace
  intro i
  exact psd_trace_zero_family_supported_common_kernel (A i) D (hA i) hD (hzero i)

theorem psd_family_image_trace_rank_le {p d k : ℕ}
    (M : Matrix (Fin d) (Fin p) ℝ)
    (D : Fin d → Mat (Fin k)) (A : Fin p → Mat (Fin k))
    (hD : ∀ j, (D j).PosSemidef)
    (htrace : ∀ j i, Matrix.trace (D j * A i) = M j i) :
    M.rank ≤ (∑ j, D j).rank * ((∑ j, D j).rank + 1) / 2 := by
  apply psd_image_supported_trace_rank_le M D A (∑ j, D j) hD _ htrace
  exact fun j => psd_family_each_supported_sum_image D hD j

#print axioms rank_eq_image_finrank
#print axioms image_kernel_finrank_sum
#print axioms symmetric_supported_trace_rank_le
#print axioms psd_supported_trace_rank_le
#print axioms psd_image_supported_trace_rank_le
#print axioms psd_kernel_supported_trace_rank_le
#print axioms psd_zero_block_kernel_trace_rank_le
#print axioms psd_family_image_trace_rank_le
end Reference.PF02IntrinsicSupport
