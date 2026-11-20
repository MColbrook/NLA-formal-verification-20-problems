module

/- Reference-only concrete product row layouts and actual recursive feasibility.
   No feasibility, covariance, optimality, or cost assumptions are supplied. -/
public import NLA.TR04.RecursiveTensorCompletion.Definitions
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

set_option autoImplicit false
namespace Reference.LexicographicFeasibilityBridge
noncomputable section
open Reference.RecursiveTensorCompletion

def inducedRowPermutation {m : ℕ} (n : ℕ) (e : Fin m ≃ Fin m) :
    Fin (rowCount m n) ≃ Fin (rowCount m n) :=
  (rowEquiv m n).symm.trans
    ((Equiv.prodCongr e (Equiv.refl (Fin n))).trans (rowEquiv m n))

theorem product_eq_rowCount (m n : ℕ) : m*n = rowCount m n := by
  simp [rowCount]

def rowEquivLex (m n : ℕ) : Fin m × Fin n ≃ Fin (rowCount m n) :=
  (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).trans
    (finCongr (product_eq_rowCount m n))

abbrev RowLayout := (m n : ℕ) → Fin m × Fin n ≃ Fin (rowCount m n)

def layoutPermutation (layout : RowLayout) (m n : ℕ) :
    Fin (rowCount m n) ≃ Fin (rowCount m n) :=
  (layout m n).symm.trans (rowEquiv m n)

def mergeWith (layout : RowLayout) {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) : Tensor (rowCount m n) ns :=
  fun i j => A ((layout m n).symm i).1 (((layout m n).symm i).2,j)

def feasibleWith (layout : RowLayout) (m : ℕ) (ns : List ℕ)
    (A : Tensor m ns) (rs : List ℕ) : Prop :=
  match ns, A, rs with
  | [], _, rs => rs=[]
  | _::_, _, [] => False
  | n::ns, A, r::rs =>
    A.rank ≤ r ∧ feasibleWith layout (rowCount m n) ns (mergeWith layout A) rs
termination_by ns.length

def mergeLex {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) :
    Tensor (rowCount m n) ns := mergeWith rowEquivLex A

def feasibleLex (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) : Prop :=
  match ns, A, rs with
  | [], _, rs => rs=[]
  | _::_, _, [] => False
  | n::ns, A, r::rs =>
    A.rank ≤ r ∧ feasibleLex (rowCount m n) ns (mergeLex A) rs
termination_by ns.length

end
end Reference.LexicographicFeasibilityBridge
