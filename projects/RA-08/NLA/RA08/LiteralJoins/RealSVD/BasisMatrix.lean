module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Pure-definition/proof refactoring of the checked real MI-13 adaptation,
upstream commit e375a6fc0a12df52c4f5a38b53df78b837e1c390.
Adapted by Codex, 2026-10-03. Original attribution retained. -/
public import NLA.RA08.LiteralJoins.RealSVD.Definitions
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.RealSVDPackage
noncomputable section
open scoped BigOperators Matrix

theorem basisMatrix_eq_toMatrix {r : ℕ}
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) :
    basisMatrix v = (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.toMatrix v := by
  ext i j
  simp only [basisMatrix, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]

theorem basisMatrix_orthogonal {r : ℕ}
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) : IsOrthogonal (basisMatrix v) := by
  rw [basisMatrix_eq_toMatrix]
  exact ⟨by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (EuclideanSpace.basisFun (Fin r) ℝ).toMatrix_orthonormalBasis_conjTranspose_mul_self v,
    by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (EuclideanSpace.basisFun (Fin r) ℝ).toMatrix_orthonormalBasis_self_mul_conjTranspose v⟩

#print axioms basisMatrix_orthogonal
end
end Reference.RealSVDPackage

