module

public import NLA.PF02.SupportBridge.Supports

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Support
open Matrix
open scoped BigOperators MatrixOrder

variable {k s : ℕ}

theorem supported_frame_left_projection (A : Mat (Fin k))
    (T : Matrix (Fin k) (Fin s) ℝ) (hT : T.transpose * T = 1)
    (h : image A ≤ LinearMap.range (Matrix.toEuclideanLin T)) :
    T * T.transpose * A = A := by
  apply Matrix.ext_of_mulVec_single
  intro j
  let e : Vector (Fin k) := WithLp.toLp 2 (Pi.single j (1 : ℝ))
  obtain ⟨y, hy⟩ := h (LinearMap.mem_range_self (lin A) e)
  have hy' : T *ᵥ y.ofLp = A *ᵥ Pi.single j 1 := by
    have hz := congrArg (fun v : Vector (Fin k) => v.ofLp) hy
    exact hz
  calc
    (T * T.transpose * A) *ᵥ Pi.single j 1 =
        (T * T.transpose) *ᵥ (A *ᵥ Pi.single j 1) := by rw [Matrix.mulVec_mulVec]
    _ = (T * T.transpose) *ᵥ (T *ᵥ y.ofLp) := by rw [hy']
    _ = T *ᵥ y.ofLp := by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hT, Matrix.mul_one]
    _ = A *ᵥ Pi.single j 1 := hy'

theorem supported_frame_right_projection (A : Mat (Fin k))
    (T : Matrix (Fin k) (Fin s) ℝ) (hT : T.transpose * T = 1)
    (hA : A.transpose = A)
    (h : image A ≤ LinearMap.range (Matrix.toEuclideanLin T)) :
    A * T * T.transpose = A := by
  have ht := congrArg Matrix.transpose (supported_frame_left_projection A T hT h)
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hA, Matrix.mul_assoc] using ht

theorem supported_frame_trace_compression (A B : Mat (Fin k))
    (T : Matrix (Fin k) (Fin s) ℝ) (hT : T.transpose * T = 1)
    (hA : A.transpose = A)
    (h : image A ≤ LinearMap.range (Matrix.toEuclideanLin T)) :
    Matrix.trace ((T.transpose * A * T) * (T.transpose * B * T)) = Matrix.trace (A * B) := by
  have hleft := supported_frame_left_projection A T hT h
  have hright := supported_frame_right_projection A T hT hA h
  calc
    Matrix.trace ((T.transpose * A * T) * (T.transpose * B * T)) =
        Matrix.trace (T.transpose * (A * T * T.transpose) * B * T) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (T.transpose * A * B * T) := by rw [hright]
    _ = Matrix.trace ((T * T.transpose * A) * B) := by
      rw [Matrix.trace_mul_cycle]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (A * B) := by rw [hleft]

#print axioms supported_frame_left_projection
#print axioms supported_frame_right_projection
#print axioms supported_frame_trace_compression
end Reference.PF02Support

