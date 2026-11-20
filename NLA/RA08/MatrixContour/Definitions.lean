module

public import NLA.RA08.PaperDerivativeDefinitions
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix
namespace NLA.RA08.Paper.MatrixContour

def complexify {n : ℕ} (A : RealMatrix n) : Matrix (Fin n) (Fin n) ℂ :=
  A.map Complex.ofReal

def complexifyHom (n : ℕ) : RealMatrix n →⋆ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  __ := (Algebra.ofId ℝ ℂ).mapMatrix
  map_star' A := by
    ext i j
    simp [AlgHom.mapMatrix_apply,Matrix.map_apply,Matrix.star_eq_conjTranspose]

def complexVector {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

end NLA.RA08.Paper.MatrixContour
