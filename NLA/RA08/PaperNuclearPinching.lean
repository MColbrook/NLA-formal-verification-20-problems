module

public import NLA.RA08.PaperNuclearHomogeneity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators MatrixOrder
namespace NLA.RA08.Paper

theorem matrixAbsolute_unitary_conjugate {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    matrixAbsolute ((U : RealMatrix n)*A*(U : RealMatrix n).transpose)=
      (U : RealMatrix n)*matrixAbsolute A*(U : RealMatrix n).transpose := by
  let φ : RealMatrix n ≃⋆ₐ[ℝ] RealMatrix n := Unitary.conjStarAlgAut ℝ (RealMatrix n) U
  have hφ : Continuous φ := φ.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hUA : ((U : RealMatrix n)*A*(U : RealMatrix n).transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : RealMatrix n) hA
  have hc := StarAlgHomClass.map_cfc (S := ℝ) (R := ℝ) φ abs A continuous_abs.continuousOn hφ hA (by
    simpa only [φ,Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hUA.isSelfAdjoint)
  simpa only [matrixAbsolute,functionalCalculus,φ,Unitary.conjStarAlgAut_apply,Unitary.coe_star,
    Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hc.symm

theorem nuclearNorm_hermitian_unitary_conjugate {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    nuclearNorm ((U : RealMatrix n)*A*(U : RealMatrix n).transpose)=nuclearNorm A := by
  have hUA : ((U : RealMatrix n)*A*(U : RealMatrix n).transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : RealMatrix n) hA
  rw [nuclearNorm_hermitian _ hUA,matrixAbsolute_unitary_conjugate A hA U,
    Matrix.trace_mul_cycle,real_unitary_transpose_mul,Matrix.one_mul,nuclearNorm_hermitian A hA]

theorem nuclearNorm_off_diagonal_pinching {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    nuclearNorm ((1/2 : ℝ) • (A-(U : RealMatrix n)*A*(U : RealMatrix n).transpose)) ≤ nuclearNorm A := by
  have hUA : ((U : RealMatrix n)*A*(U : RealMatrix n).transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : RealMatrix n) hA
  have hs := nuclearNorm_hermitian_sub A ((U : RealMatrix n)*A*(U : RealMatrix n).transpose) hA hUA
  rw [nuclearNorm_hermitian_unitary_conjugate A hA U] at hs
  rw [nuclearNorm_hermitian_smul _ (hA.sub hUA) (1/2)]
  norm_num
  linarith

theorem nuclearNorm_diagonal_pinching {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    nuclearNorm ((1/2 : ℝ) • (A+(U : RealMatrix n)*A*(U : RealMatrix n).transpose)) ≤ nuclearNorm A := by
  have hUA : ((U : RealMatrix n)*A*(U : RealMatrix n).transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : RealMatrix n) hA
  have hs := nuclearNorm_hermitian_triangle A ((U : RealMatrix n)*A*(U : RealMatrix n).transpose) hA hUA
  rw [nuclearNorm_hermitian_unitary_conjugate A hA U] at hs
  rw [nuclearNorm_hermitian_smul _ (hA.add hUA) (1/2)]
  norm_num
  linarith

#print axioms nuclearNorm_off_diagonal_pinching
end NLA.RA08.Paper
