module

public import NLA.PF02.IntrinsicSupport.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02IntrinsicSupport
open Matrix Module
open scoped BigOperators MatrixOrder
variable {k : ℕ}

theorem frame_orthonormal (U : Submodule ℝ (E k)) :
    (frame U).transpose * frame U = 1 := by
  classical
  ext i j
  have h := orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ U).orthonormal j i
  simpa [frame, Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    PiLp.inner_apply, mul_comm, eq_comm] using h

theorem frame_mul_repr (U : Submodule ℝ (E k)) (x : U) :
    Matrix.toEuclideanLin (frame U) ((stdOrthonormalBasis ℝ U).repr x) = (x : E k) := by
  classical
  have h := congrArg (fun y : U => (y : E k)) ((stdOrthonormalBasis ℝ U).sum_repr x)
  apply WithLp.ofLp_injective 2
  funext i
  have hi := congrArg (fun y : E k => y i) h
  simpa [frame, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, mul_comm] using hi

theorem frame_range (U : Submodule ℝ (E k)) :
    LinearMap.range (Matrix.toEuclideanLin (frame U)) = U := by
  classical
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    have h := frame_mul_repr U ((stdOrthonormalBasis ℝ U).repr.symm x)
    have h' : Matrix.toEuclideanLin (frame U) x = ((stdOrthonormalBasis ℝ U).repr.symm x : E k) := by
      simpa using h
    rw [h']
    exact ((stdOrthonormalBasis ℝ U).repr.symm x).property
  · intro x hx
    exact ⟨(stdOrthonormalBasis ℝ U).repr ⟨x, hx⟩, frame_mul_repr U ⟨x, hx⟩⟩

theorem exists_orthonormal_frame (U : Submodule ℝ (E k)) :
    ∃ T : Matrix (Fin k) (Fin (finrank ℝ U)) ℝ,
      T.transpose * T = 1 ∧ LinearMap.range (Matrix.toEuclideanLin T) = U :=
  ⟨frame U, frame_orthonormal U, frame_range U⟩

#print axioms frame_orthonormal
#print axioms frame_mul_repr
#print axioms frame_range
#print axioms exists_orthonormal_frame
end Reference.PF02IntrinsicSupport
