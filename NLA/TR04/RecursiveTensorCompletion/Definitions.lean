module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Literal finite nested tensor indices and true recursive unfolding ranks for TR04.
No unfolding-rank or tensor-correctness oracle is present. -/
public import NLA.TR04.RealSVD.Definitions
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

set_option autoImplicit false
namespace Reference.RecursiveTensorCompletion
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix Kronecker

def ModeIndex : List ℕ → Type
  | [] => PUnit
  | n::ns => Fin n × ModeIndex ns

instance modeIndexFintype (ns : List ℕ) : Fintype (ModeIndex ns) := by
  induction ns with
  | nil => exact inferInstanceAs (Fintype PUnit)
  | cons n ns ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin n × ModeIndex ns))

instance modeIndexDecidableEq (ns : List ℕ) : DecidableEq (ModeIndex ns) := by
  induction ns with
  | nil => exact inferInstanceAs (DecidableEq PUnit)
  | cons n ns ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Fin n × ModeIndex ns))

abbrev Tensor (m : ℕ) (ns : List ℕ) := Matrix (Fin m) (ModeIndex ns) ℝ

def tensorFrobeniusSq {m : ℕ} {ns : List ℕ} (A : Tensor m ns) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

def rowCount (m n : ℕ) : ℕ := Fintype.card (Fin m × Fin n)

def rowEquiv (m n : ℕ) : (Fin m × Fin n) ≃ Fin (rowCount m n) :=
  Fintype.equivFin (Fin m × Fin n)

def merge {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) : Tensor (rowCount m n) ns :=
  fun i j => A ((rowEquiv m n).symm i).1 (((rowEquiv m n).symm i).2, j)

def unmerge {m n : ℕ} {ns : List ℕ} (A : Tensor (rowCount m n) ns) : Tensor m (n::ns) :=
  fun i j => A (rowEquiv m n (i,j.1)) j.2

def mergeLeft {m k n : ℕ} (V : Rect k m) : Rect (rowCount k n) (rowCount m n) :=
  (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix
    (rowEquiv k n).symm (rowEquiv m n).symm

def feasible (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) : Prop :=
  match ns, A, rs with
  | [], _, rs => rs=[]
  | _::_, _, [] => False
  | n::ns, A, r::rs => A.rank ≤ r ∧ feasible (rowCount m n) ns (merge A) rs
termination_by ns.length

end
end Reference.RecursiveTensorCompletion
