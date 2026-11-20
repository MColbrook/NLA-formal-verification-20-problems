module

public import NLA.PF02.SupportBridge.FrameCompression
public import NLA.PF02.PaperSymmetricRank

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Support
open Matrix
open scoped BigOperators MatrixOrder

theorem supported_trace_factor_symmetric_rank_le {p q k s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (T : Matrix (Fin k) (Fin s) ℝ) (hT : T.transpose * T = 1)
    (hA : ∀ i, (A i).transpose = A i)
    (hsupport : ∀ i, image (A i) ≤ LinearMap.range (Matrix.toEuclideanLin T))
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ s * (s + 1) / 2 := by
  let C : Fin p → Matrix (Fin s) (Fin s) ℝ := fun i => T.transpose * A i * T
  let D : Fin q → Matrix (Fin s) (Fin s) ℝ := fun j => T.transpose * B j * T
  apply NLA.PF02.Paper.trace_factor_symmetric_rank_le M C D
  · intro i
    simp only [C, Matrix.transpose_mul, Matrix.transpose_transpose, hA i, Matrix.mul_assoc]
  · intro i j
    exact (supported_frame_trace_compression (A i) (B j) T hT (hA i) (hsupport i)).trans (htrace i j)

theorem supported_psd_trace_factor_rank_le {p q k s : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (T : Matrix (Fin k) (Fin s) ℝ) (hT : T.transpose * T = 1)
    (hA : ∀ i, (A i).PosSemidef)
    (hsupport : ∀ i, image (A i) ≤ LinearMap.range (Matrix.toEuclideanLin T))
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ s * (s + 1) / 2 := by
  apply supported_trace_factor_symmetric_rank_le M A B T hT _ hsupport htrace
  intro i
  ext a b
  simpa only [Matrix.transpose_apply, star_trivial] using (hA i).isHermitian.apply a b

#print axioms supported_trace_factor_symmetric_rank_le
#print axioms supported_psd_trace_factor_rank_le
end Reference.PF02Support
