module

/- Pure concrete cyclic candidate completions, each using named actual recursive TT-SVD. -/
public import NLA.TR04.CyclicBoundary.Definitions
public import NLA.TR04.RecursiveTensorCompletion.ProcessDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.CyclicBoundary
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion

def tensorBoundary {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) : ℝ :=
  singularValue (denseTensor A) (r-1)
def tensorBoundaryCount {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) : ℕ :=
  eCount (denseTensor A) (tensorBoundary A r)
def tensorRetainedBoundary {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) : ℕ :=
  r-hCount (denseTensor A) (tensorBoundary A r)
def tensorCandidateFrame {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ)
    (j : Fin (tensorBoundaryCount A r)) :=
  candidateFrame (denseTensor A) (tensorBoundary A r) (tensorRetainedBoundary A r) j
def cyclicCompletion {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ)
    (rs : List ℕ) (j : Fin (tensorBoundaryCount A r)) : Tensor m (n::ns) :=
  completeFrame A (tensorCandidateFrame A r j) rs

end
end Reference.CyclicBoundary