module

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Real rectangular extension of the MI-13 ordered Gram basis proof at
OpenProblemsInNLA commit e375a6fc0a12df52c4f5a38b53df78b837e1c390.
Adapted by Codex on 2026-10-03. All spaces, matrices and singular values here
are actual real Euclidean objects. No left singular-basis completion is used.
-/
public import NLA.TR04.RealSVD.BasisMatrix

@[expose] public section

set_option autoImplicit false

namespace Reference.RealSVDPackage
noncomputable section
open scoped BigOperators Matrix

theorem rectangular_ordered_gram_basis {m n : ℕ} (A : Rect m n) :
    ∃ v : OrthonormalBasis (Fin n) ℝ (EuclideanVector n),
      RectangularGramBasis A v := by
  let hn := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)
  refine ⟨(euclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis hn, ?_⟩
  intro i
  have h := (euclideanLin A).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
  rw [← (euclideanLin A).sq_singularValues_fin hn i] at h
  simpa only [LinearMap.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    singularValue] using h

theorem adjoint_eq_transpose {m n : ℕ} (A : Rect m n) :
    (euclideanLin A).adjoint = euclideanLin A.transpose := by
  simpa only [euclideanLin, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

theorem gram_basis_matrix_diagonal {m n : ℕ} (A : Rect m n)
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanVector n))
    (hv : RectangularGramBasis A v) :
    (basisMatrix v).transpose * (A.transpose * A) * basisMatrix v =
      Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2) := by
  have hV := basisMatrix_orthogonal v
  have hAV : (A.transpose * A) * basisMatrix v =
      basisMatrix v * Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2) := by
    ext i j
    have h := congrArg (fun z : EuclideanVector n => z i) (hv j)
    rw [adjoint_eq_transpose A] at h
    change (∑ k : Fin m, A k i * (∑ l : Fin n, A k l * v j l)) =
      singularValue A j.val ^ 2 * v j i at h
    calc
      ((A.transpose * A) * basisMatrix v) i j =
          (A.transpose * (A * basisMatrix v)) i j := by
        rw [Matrix.mul_assoc]
      _ = ∑ k : Fin m, A k i * (∑ l : Fin n, A k l * v j l) := rfl
      _ = singularValue A j.val ^ 2 * v j i := h
      _ = (basisMatrix v * Matrix.diagonal
          (fun i : Fin n => singularValue A i.val ^ 2)) i j := by
        simp only [Matrix.mul_diagonal, basisMatrix, mul_comm]
  rw [Matrix.mul_assoc, hAV, ← Matrix.mul_assoc, hV.1, Matrix.one_mul]

theorem rectangular_right_gram_basis_matrix {m n : ℕ} (A : Rect m n) :
    ∃ v : OrthonormalBasis (Fin n) ℝ (EuclideanVector n),
      RectangularGramBasis A v ∧ IsOrthogonal (basisMatrix v) ∧
      (basisMatrix v).transpose * (A.transpose * A) * basisMatrix v =
        Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2) := by
  obtain ⟨v, hv⟩ := rectangular_ordered_gram_basis A
  exact ⟨v, hv, basisMatrix_orthogonal v, gram_basis_matrix_diagonal A v hv⟩

theorem rectangular_right_gram_diagonal {m n : ℕ} (A : Rect m n) :
    ∃ V : Square n, IsOrthogonal V ∧
      V.transpose * (A.transpose * A) * V =
        Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2) := by
  obtain ⟨v, _, hV, hdiag⟩ := rectangular_right_gram_basis_matrix A
  exact ⟨basisMatrix v, hV, hdiag⟩

#print axioms rectangular_ordered_gram_basis
#print axioms adjoint_eq_transpose
#print axioms gram_basis_matrix_diagonal
#print axioms rectangular_right_gram_basis_matrix
#print axioms rectangular_right_gram_diagonal

end
end Reference.RealSVDPackage


