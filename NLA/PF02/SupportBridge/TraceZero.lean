module

public import NLA.PF02.SupportBridge.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Support
open Matrix
open scoped BigOperators MatrixOrder
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem psd_trace_zero_mul_zero (A B : Mat n) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (h : Matrix.trace (A * B) = 0) : A * B = 0 := by
  obtain ⟨X, hX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  simp only [star_eq_conjTranspose] at hX hY
  have ht : Matrix.trace (A * B) = Matrix.trace ((X * Yᴴ)ᴴ * (X * Yᴴ)) := by
    rw [hX, hY]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose]
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
    simp only [Matrix.mul_assoc]
  have hxy : X * Yᴴ = 0 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp (ht ▸ h)
  rw [hX, hY]
  calc
    Xᴴ * X * (Yᴴ * Y) = Xᴴ * (X * Yᴴ) * Y := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hxy]; simp

theorem psd_trace_zero_iff_mul_zero (A B : Mat n) (hA : A.PosSemidef)
    (hB : B.PosSemidef) : Matrix.trace (A * B) = 0 ↔ A * B = 0 := by
  exact ⟨psd_trace_zero_mul_zero A B hA hB, fun h => by rw [h]; simp⟩

theorem psd_trace_zero_reverse_mul_zero (A B : Mat n) (hA : A.PosSemidef)
    (hB : B.PosSemidef) (h : Matrix.trace (A * B) = 0) : B * A = 0 := by
  exact psd_trace_zero_mul_zero B A hB hA ((Matrix.trace_mul_comm B A).trans h)

#print axioms psd_trace_zero_mul_zero
#print axioms psd_trace_zero_iff_mul_zero
#print axioms psd_trace_zero_reverse_mul_zero
end Reference.PF02Support
