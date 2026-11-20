module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual real Gram-projector equality extension of MI-13 at upstream commit
 e375a6fc0a12df52c4f5a38b53df78b837e1c390. Prior mathematical attribution
retained; equality formalization by Codex, 2026-10-03. Pure actual definitions. -/
public import NLA.TR04.RealSVD.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage

def leftBasis {m n : ℕ} (A : Rect m n) :
    OrthonormalBasis (Fin m) ℝ (EuclideanVector m) :=
  (euclideanLin A.transpose).isSymmetric_adjoint_comp_self.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))

def leftVectorMatrix {m n : ℕ} (A : Rect m n) : Square m := basisMatrix (leftBasis A)

def leftAboveProjector {m n : ℕ} (A : Rect m n) (tau : ℝ) : Square m :=
  leftVectorMatrix A * Matrix.diagonal
    (fun i : Fin m => if tau < singularValue A.transpose i.val then (1 : ℝ) else 0) *
      (leftVectorMatrix A).transpose

def leftLeadingProjector {m n : ℕ} (A : Rect m n) (r : ℕ) : Square m :=
  leftVectorMatrix A * Matrix.diagonal (headMask m r) * (leftVectorMatrix A).transpose

def rightAboveProjector {m n : ℕ} (A : Rect m n) (tau : ℝ) : Square n :=
  leftAboveProjector A.transpose tau

def rightLeadingProjector {m n : ℕ} (A : Rect m n) (r : ℕ) : Square n :=
  leftLeadingProjector A.transpose r

end
end Reference.RealOptimalityEquality
