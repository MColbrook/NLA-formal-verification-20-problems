module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Named actual recursive TT-SVD and prescribed-first-frame completion definitions.
Each primitive frame is prefix columns of the ACTUAL sorted Gram eigenbasis. -/
public import NLA.TR04.RecursiveTensorCompletion.Definitions
public import NLA.TR04.OptimalityEquality.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.RecursiveTensorCompletion
noncomputable section
open Reference.RealSVDPackage

def denseTensor {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    Rect m (Fintype.card (ModeIndex ns)) :=
  A.submatrix id (Fintype.equivFin (ModeIndex ns)).symm

def svdFrame {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) : Rect m (min r m) :=
  fun i j => Reference.RealOptimalityEquality.leftVectorMatrix (denseTensor A) i
    ⟨j.val,j.isLt.trans_le (Nat.min_le_right r m)⟩

def ttSVD (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) : Tensor m ns :=
  match ns,A,rs with
  | [],A,_ => A
  | _::_,A,[] => A
  | n::ns,A,r::rs =>
    let U := svdFrame A r
    let C := merge (U.transpose*A)
    let Z := ttSVD (rowCount (min r m) n) ns C rs
    U * unmerge (m:=min r m) (n:=n) Z
termination_by ns.length

def completeFrame {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) : Tensor m (n::ns) :=
  U * unmerge (m:=k) (n:=n)
    (ttSVD (rowCount k n) ns (merge (U.transpose*A)) rs)

end
end Reference.RecursiveTensorCompletion
