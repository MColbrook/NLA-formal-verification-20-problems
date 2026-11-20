module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Literal ordered candidates and first-minimum selection. Pure definitions.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
public import NLA.TR04.OrderedTensorSolver.CompletionDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.OrderedTensorSolver
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion Reference.OrderedCyclicBoundary

def error {m : ℕ} {ns : List ℕ} (A X : Tensor m ns) : ℝ := tensorFrobeniusSq (A-X)
def firstMinimum {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (x : Tensor m ns) :
    List (Tensor m ns) → Tensor m ns
  | [] => x
  | y::ys => if error A y<error A x then firstMinimum A y ys else firstMinimum A x ys

def leadingCompletion {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :=
  completeFrame A (svdFrame A r) rs

def columnSpaceCompletion {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (rs : List ℕ) :=
  completeFrame A (svdFrame A (denseTensor A).rank) rs

def candidates {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    List (Tensor m (n::ns)) :=
  if (denseTensor A).rank ≤ r then [columnSpaceCompletion A rs]
  else if ht : 0<tensorBoundaryCount A r then
    if tensorRetainedBoundary A r=tensorBoundaryCount A r then
      [cyclicCompletion A r rs ⟨0,ht⟩]
    else List.ofFn (cyclicCompletion A r rs)
  else [leadingCompletion A r rs]

def solver {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :=
  match candidates A r rs with
  | [] => leadingCompletion A r rs
  | x::xs => firstMinimum A x xs

end
end Reference.OrderedTensorSolver