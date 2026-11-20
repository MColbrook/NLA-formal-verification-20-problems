module

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.
Real adaptation of MI-13 at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
This theorem constructs real orthogonal factors, not complex vectors for real input.
-/
public import NLA.TR04.RealSVD.NormalizedImages
public import NLA.TR04.RealSVD.BasisMatrix

@[expose] public section

set_option autoImplicit false

namespace Reference.RealSVDPackage
noncomputable section
open scoped BigOperators Matrix

theorem full_svd {r : ℕ} (A : Square r) :
    ∃ U V : Square r, IsOrthogonal U ∧ IsOrthogonal V ∧
      A = U * singularDiagonal A * V.transpose := by
  obtain ⟨u, v, _, hAv⟩ := full_singular_vector_bases A
  have hU := basisMatrix_orthogonal u
  have hV := basisMatrix_orthogonal v
  have hAV : A * basisMatrix v = basisMatrix u * singularDiagonal A := by
    ext i j
    have h := congrArg (fun z : EuclideanVector r => z i) (hAv j)
    change (∑ k, A i k * v j k) = singularValue A j.val * u j i at h
    calc
      (A * basisMatrix v) i j = ∑ k, A i k * v j k := rfl
      _ = singularValue A j.val * u j i := h
      _ = (basisMatrix u * singularDiagonal A) i j := by
        simp only [singularDiagonal, Matrix.mul_diagonal, basisMatrix, mul_comm]
  refine ⟨basisMatrix u, basisMatrix v, hU, hV, ?_⟩
  calc
    A = A * (basisMatrix v * (basisMatrix v).transpose) := by
      rw [hV.2, Matrix.mul_one]
    _ = (A * basisMatrix v) * (basisMatrix v).transpose :=
      (Matrix.mul_assoc _ _ _).symm
    _ = basisMatrix u * singularDiagonal A * (basisMatrix v).transpose := by
      rw [hAV]

#print axioms full_svd

end
end Reference.RealSVDPackage

