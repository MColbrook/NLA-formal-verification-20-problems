module

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Real-square adaptation of OpenProblemsInNLA MI-13, pinned source commit
e375a6fc0a12df52c4f5a38b53df78b837e1c390. Adapted by Codex on 2026-10-03.
This isolated reference module contains only actual real Euclidean definitions.
-/
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false

namespace Reference.RealSVDPackage
noncomputable section
open scoped BigOperators Matrix

abbrev Rect (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev Square (r : ℕ) := Rect r r
abbrev EuclideanVector (n : ℕ) := EuclideanSpace ℝ (Fin n)

def euclideanLin {m n : ℕ} (A : Rect m n) :
    EuclideanVector n →ₗ[ℝ] EuclideanVector m := Matrix.toEuclideanLin A

def singularValue {m n : ℕ} (A : Rect m n) (k : ℕ) : ℝ :=
  (euclideanLin A).singularValues k

def gramEigenvalue {m n : ℕ} (A : Rect m n) (i : Fin n) : ℝ :=
  (euclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n)) i

def IsOrthogonal {r : ℕ} (U : Square r) : Prop :=
  U.transpose * U = 1 ∧ U * U.transpose = 1

def singularDiagonal {r : ℕ} (A : Square r) : Square r :=
  Matrix.diagonal (fun i => singularValue A i.val)

def GramBasis {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) : Prop :=
  ∀ i, (euclideanLin A).adjoint (euclideanLin A (v i)) =
    (singularValue A i.val ^ 2) • v i

def positiveSingularIndices {r : ℕ} (A : Square r) : Set (Fin r) :=
  {i | 0 < singularValue A i.val}

def normalizedImages {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) (i : Fin r) :
    EuclideanVector r := (singularValue A i.val)⁻¹ • euclideanLin A (v i)

def basisMatrix {r : ℕ} (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) :
    Square r := fun i j => v j i

def RectangularGramBasis {m n : ℕ} (A : Rect m n)
    (v : OrthonormalBasis (Fin n) ℝ (EuclideanVector n)) : Prop :=
  ∀ i, (euclideanLin A).adjoint (euclideanLin A (v i)) =
    (singularValue A i.val ^ 2) • v i

def frobeniusSq {m n : ℕ} (E : Rect m n) : ℝ :=
  ∑ i, ∑ j, E i j ^ 2

def singularTailSq {m n : ℕ} (A : Rect m n) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ i.val), singularValue A i.val ^ 2

def headMask (n r : ℕ) (i : Fin n) : ℝ := if i.val < r then 1 else 0
def tailMask (n r : ℕ) (i : Fin n) : ℝ := if i.val < r then 0 else 1

def realTruncation {m n : ℕ} (A : Rect m n) (r : ℕ) (V : Square n) : Rect m n :=
  A * V * Matrix.diagonal (headMask n r) * V.transpose

end
end Reference.RealSVDPackage

