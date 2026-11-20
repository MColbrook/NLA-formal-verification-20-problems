module

/- Concrete lexicographic recursion on literal finite tensor indices. -/
public import NLA.TR04.RecursiveTensorCompletion.Definitions
public import NLA.TR04.LexicographicFeasibilityBridge.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix Kronecker
abbrev ModeIndex (ns : List ℕ) := Reference.RecursiveTensorCompletion.ModeIndex ns
abbrev Tensor (m : ℕ) (ns : List ℕ) := Reference.RecursiveTensorCompletion.Tensor m ns
def tensorFrobeniusSq {m : ℕ} {ns : List ℕ} (A : Tensor m ns) : ℝ := ∑ i, ∑ j, A i j ^ 2
abbrev rowCount (m n : ℕ) := Reference.RecursiveTensorCompletion.rowCount m n
def rowEquiv (m n : ℕ) : (Fin m × Fin n) ≃ Fin (rowCount m n) := Reference.LexicographicFeasibilityBridge.rowEquivLex m n
def merge {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) : Tensor (rowCount m n) ns :=
  fun i j => A ((rowEquiv m n).symm i).1 (((rowEquiv m n).symm i).2, j)
def unmerge {m n : ℕ} {ns : List ℕ} (A : Tensor (rowCount m n) ns) : Tensor m (n::ns) :=
  fun i j => A (rowEquiv m n (i,j.1)) j.2
def mergeLeft {m k n : ℕ} (V : Rect k m) : Rect (rowCount k n) (rowCount m n) :=
  (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix (rowEquiv k n).symm (rowEquiv m n).symm
def feasible (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) : Prop :=
  match ns, A, rs with
  | [], _, rs => rs=[]
  | _::_, _, [] => False
  | n::ns, A, r::rs => A.rank ≤ r ∧ feasible (rowCount m n) ns (merge A) rs
termination_by ns.length
end
end Reference.LexTensorCompletion
