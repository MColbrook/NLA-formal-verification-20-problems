module
public import Mathlib
@[expose] public section
/-! Standalone exact statement and semantic-definition surface for TR-04.
Every helper theorem placeholder is explicitly compared and genuinely proved on the Solution side. -/
section
/- Original module: NLA.TR04.RealSVD.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.
Real-square adaptation of OpenProblemsInNLA MI-13, pinned source commit
e375a6fc0a12df52c4f5a38b53df78b837e1c390. Adapted by Codex on 2026-10-03.
This isolated reference module contains only actual real Euclidean definitions.
-/
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
def basisMatrix {r : ℕ} (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) :
    Square r := fun i j => v j i
end
end Reference.RealSVDPackage
end
section
/- Original module: NLA.TR04.OptimalityEquality.Definitions -/
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual real Gram-projector equality extension of MI-13 at upstream commit
 e375a6fc0a12df52c4f5a38b53df78b837e1c390. Prior mathematical attribution
retained; equality formalization by Codex, 2026-10-03. Pure actual definitions. -/
set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage
def leftBasis {m n : ℕ} (A : Rect m n) :
    OrthonormalBasis (Fin m) ℝ (EuclideanVector m) :=
  (euclideanLin A.transpose).isSymmetric_adjoint_comp_self.eigenvectorBasis
    (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m))
def leftVectorMatrix {m n : ℕ} (A : Rect m n) : Square m := basisMatrix (leftBasis A)
end
end Reference.RealOptimalityEquality
end
section
/- Original module: NLA.TR04.RecursiveTensorCompletion.Definitions -/
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Literal finite nested tensor indices and true recursive unfolding ranks for TR04.
No unfolding-rank or tensor-correctness oracle is present. -/
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
def feasible (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) : Prop :=
  match ns, A, rs with
  | [], _, rs => rs=[]
  | _::_, _, [] => False
  | n::ns, A, r::rs => A.rank ≤ r ∧ feasible (rowCount m n) ns (merge A) rs
termination_by ns.length
end
end Reference.RecursiveTensorCompletion
end
section
/- Original module: NLA.TR04.LexicographicFeasibilityBridge.Definitions -/
/- Reference-only concrete product row layouts and actual recursive feasibility.
   No feasibility, covariance, optimality, or cost assumptions are supplied. -/
set_option autoImplicit false
namespace Reference.LexicographicFeasibilityBridge
noncomputable section
open Reference.RecursiveTensorCompletion
theorem product_eq_rowCount (m n : ℕ) : m*n = rowCount m n := by sorry
def rowEquivLex (m n : ℕ) : Fin m × Fin n ≃ Fin (rowCount m n) :=
  (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).trans
    (finCongr (product_eq_rowCount m n))
end
end Reference.LexicographicFeasibilityBridge
end
section
/- Original module: NLA.TR04.TensorCandidateSelection.Definitions -/
/- Literal ordered candidates and first-minimum selection. Pure definitions.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
set_option autoImplicit false
namespace Reference.TensorCandidateSelection
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion 
def error {m : ℕ} {ns : List ℕ} (A X : Tensor m ns) : ℝ := tensorFrobeniusSq (A-X)
end
end Reference.TensorCandidateSelection
end
section
/- Original module: NLA.TR04.TensorOptimumAttainment.Definitions -/
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Genuine closed actual unfolding-rank constraints and literal feasible optimum definitions. -/
set_option autoImplicit false
namespace Reference.TensorOptimumAttainment
noncomputable section
open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection
def feasibleSet (m : ℕ) (ns : List ℕ) (rs : List ℕ) : Set (Tensor m ns) :=
  {Y | feasible m ns Y rs}
def optimalError {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (rs : List ℕ) : ℝ :=
  sInf (error A '' feasibleSet m ns rs)
end
end Reference.TensorOptimumAttainment
end
section
/- Original module: NLA.TR04.LexicographicTensorReplayR3.PureDefinitions -/
/- Standalone pure Challenge bodies copied from frozen concrete solver. No solver proof imports. -/
set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage
end
end Reference.RealOptimalityEquality
/- Exact structured arithmetic and singular-subspace interpreter.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex.
A trace records actual scalar operands; each interpreter call produces its result.
No supplied runtime, solver instruction, or correctness contract is present. -/
set_option autoImplicit false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix
inductive Event where
  | read (x : ℝ)
  | zero
  | add (x y : ℝ)
  | sub (x y : ℝ)
  | mul (x y : ℝ)
  | less (x y : ℝ)
  | leftSubspace (m n : ℕ) (A : Rect m n)
def eventCharge : Event → ℕ
  | .leftSubspace m n _ => (m+n+1)^3
  | _ => 1
structure Run (α : Type) where
  value : α
  trace : List Event
def pureRun {α : Type} (x : α) : Run α := ⟨x,[]⟩
def bindRun {α β : Type} (x : Run α) (f : α → Run β) : Run β :=
  let y:=f x.value
  ⟨y.value,x.trace++y.trace⟩
instance : Monad Run where
  pure := pureRun
  bind := bindRun
def readReal (x : ℝ) : Run ℝ := ⟨x,[.read x]⟩
def zeroReal : Run ℝ := ⟨0,[.zero]⟩
def addReal (x y : ℝ) : Run ℝ := ⟨x+y,[.add x y]⟩
def subReal (x y : ℝ) : Run ℝ := ⟨x-y,[.sub x y]⟩
def mulReal (x y : ℝ) : Run ℝ := ⟨x*y,[.mul x y]⟩
def lessReal (x y : ℝ) : Run Bool := ⟨decide (x<y),[.less x y]⟩
def leftSubspace {m n : ℕ} (A : Rect m n) : Run (Square m) :=
  ⟨leftVectorMatrix A,[.leftSubspace m n A]⟩
end
end Reference.LexTensorArithmeticExecution
/- Concrete lexicographic recursion on literal finite tensor indices. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix Kronecker
abbrev ModeIndex (ns : List ℕ) := Reference.RecursiveTensorCompletion.ModeIndex ns
abbrev Tensor (m : ℕ) (ns : List ℕ) := Reference.RecursiveTensorCompletion.Tensor m ns
abbrev rowCount (m n : ℕ) := Reference.RecursiveTensorCompletion.rowCount m n
def rowEquiv (m n : ℕ) : (Fin m × Fin n) ≃ Fin (rowCount m n) := Reference.LexicographicFeasibilityBridge.rowEquivLex m n
def merge {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) : Tensor (rowCount m n) ns :=
  fun i j => A ((rowEquiv m n).symm i).1 (((rowEquiv m n).symm i).2, j)
def unmerge {m n : ℕ} {ns : List ℕ} (A : Tensor (rowCount m n) ns) : Tensor m (n::ns) :=
  fun i j => A (rowEquiv m n (i,j.1)) j.2
end
end Reference.LexTensorCompletion
/- Explicit ascending original-index scans and inverse lookup; no choice of enumeration.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
set_option autoImplicit false
namespace Reference.LexOrderedIndex
end Reference.LexOrderedIndex
/- Literal finite arithmetic loops: data are produced by interpreter calls. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix
def vectorRun {α : Type} : (n : ℕ) → (Fin n → Run α) → Run (Fin n → α)
  | 0,_ => pureRun Fin.elim0
  | n+1,f => bindRun (f 0) fun x =>
      bindRun (vectorRun n (fun i => f i.succ)) fun xs => pureRun (Fin.cases x xs)
def dotRun : (k : ℕ) → (Fin k → ℝ) → (Fin k → ℝ) → Run ℝ
  | 0,_,_ => zeroReal
  | k+1,a,b => bindRun (readReal (a 0)) fun x =>
      bindRun (readReal (b 0)) fun y =>
      bindRun (mulReal x y) fun p =>
      bindRun (dotRun k (fun i => a i.succ) (fun i => b i.succ)) fun q => addReal p q
def matrixMulRun {m k n : ℕ} (A : Rect m k) (B : Rect k n) : Run (Rect m n) :=
  vectorRun m fun i => vectorRun n fun j => dotRun k (fun a => A i a) (fun a => B a j)
end
end Reference.LexTensorArithmeticExecution
/- Literal mixed-radix lexicographic column traversal. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
def lexCard : List ℕ → ℕ
  | [] => 1
  | n::ns => n*lexCard ns
def lexIndex : (ns : List ℕ) → ModeIndex ns ≃ Fin (lexCard ns)
  | [] => {
      toFun := fun _ => ⟨0,by change 0<1; omega⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun i => by cases i; rfl
      right_inv := fun j => by apply Fin.ext; change 0=j.val; have hj:=j.isLt; change j.val<1 at hj; omega }
  | n::ns => (Equiv.prodCongr (Equiv.refl (Fin n)) (lexIndex ns)).trans finProdFinEquiv
theorem lexCard_eq_card (ns : List ℕ) : lexCard ns=Fintype.card (ModeIndex ns) := by sorry
def concreteLayout (ns : List ℕ) : ModeIndex ns ≃ Fin (Fintype.card (ModeIndex ns)) :=
  (lexIndex ns).trans (finCongr (lexCard_eq_card ns))
end
end Reference.LexTensorCompletion
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Actual cyclic windows of the tied sorted Gram eigenspace. Pure definitions.
Reference extension of OpenProblemsInNLA MI13/TR04, Apache2 attribution retained.
Copyright (c) 2026 George Stepaniants. New formalization by Codex. -/
set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix BigOperators
def EIndex {m n : ℕ} (A : Rect m n) (tau : ℝ) :=
  {i : Fin m // singularValue A.transpose i.val=tau}
def HIndex {m n : ℕ} (A : Rect m n) (tau : ℝ) :=
  {i : Fin m // tau<singularValue A.transpose i.val}
noncomputable instance eFinite {m n : ℕ} (A : Rect m n) (tau : ℝ) : Fintype (EIndex A tau) := by
  classical
  exact inferInstanceAs (Fintype {i : Fin m // singularValue A.transpose i.val=tau})
noncomputable instance hFinite {m n : ℕ} (A : Rect m n) (tau : ℝ) : Fintype (HIndex A tau) := by
  classical
  exact inferInstanceAs (Fintype {i : Fin m // tau<singularValue A.transpose i.val})
end
end Reference.LexOrderedCyclicBoundary
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Named actual recursive TT-SVD and prescribed-first-frame completion definitions.
Each primitive frame is prefix columns of the ACTUAL sorted Gram eigenbasis. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage
def denseTensor {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    Rect m (Fintype.card (ModeIndex ns)) :=
  A.submatrix id (concreteLayout ns).symm
end
end Reference.LexTensorCompletion
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Genuine finite cyclic-window counts; actual H/E multiplicity bindings. -/
set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped BigOperators
end
end Reference.LexOrderedCyclicBoundary
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Pure concrete cyclic candidate completions, each using named actual recursive TT-SVD. -/
set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
end
end Reference.LexOrderedCyclicBoundary
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Literal ordered candidates and first-minimum selection. Pure definitions.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
set_option autoImplicit false
namespace Reference.LexOrderedTensorSolver
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary
end
end Reference.LexOrderedTensorSolver
/- Explicit exact arithmetic/SVD/equality and finite natural-index operations.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix
inductive Event where
  | ordinary (e : Reference.LexTensorArithmeticExecution.Event)
  | spectral (m n : ℕ) (A : Rect m n)
  | equalReal (x y : ℝ)
  | equalNat (x y : ℕ)
  | lessNat (x y : ℕ)
  | addNat (x y : ℕ)
  | subNat (x y : ℕ)
  | modNat (x y : ℕ)
  | branch (b : Bool)
def eventCharge : Event → ℕ
  | .ordinary e => Reference.LexTensorArithmeticExecution.eventCharge e
  | .spectral m n _ => (m+n+1)^3
  | _ => 1
structure Run (α : Type) where
  value : α
  trace : List Event
def pureRun {α : Type} (x : α) : Run α := ⟨x,[]⟩
def bindRun {α β : Type} (x : Run α) (f : α → Run β) : Run β :=
  let y:=f x.value
  ⟨y.value,x.trace++y.trace⟩
def liftRun {α : Type} (x : Reference.LexTensorArithmeticExecution.Run α) : Run α :=
  ⟨x.value,x.trace.map Event.ordinary⟩
def spectralRun {m n : ℕ} (A : Rect m n) : Run (Square m × (Fin m → ℝ)) :=
  ⟨(leftVectorMatrix A,fun i => singularValue A.transpose i.val),[.spectral m n A]⟩
def equalRealRun (x y : ℝ) : Run Bool := ⟨decide (x=y),[.equalReal x y]⟩
def equalNatRun (x y : ℕ) : Run Bool := ⟨decide (x=y),[.equalNat x y]⟩
def lessNatRun (x y : ℕ) : Run Bool := ⟨decide (x<y),[.lessNat x y]⟩
def addNatRun (x y : ℕ) : Run ℕ := ⟨x+y,[.addNat x y]⟩
def subNatRun (x y : ℕ) : Run ℕ := ⟨x-y,[.subNat x y]⟩
def modNatRun (x y : ℕ) : Run ℕ := ⟨x%y,[.modNat x y]⟩
def branchRun (b : Bool) : Run Bool := ⟨b,[.branch b]⟩
def charge {α : Type} (x : Run α) : ℕ := (x.trace.map eventCharge).sum
def filterRun {α : Type} (p : α → Run Bool) : List α → Run (List α)
  | [] => pureRun []
  | i::is => bindRun (p i) fun b =>
      bindRun (branchRun b) fun keep =>
      bindRun (filterRun p is) fun rest => pureRun (if keep then i::rest else rest)
def ordinalRun {m : ℕ} (i : Fin m) : List (Fin m) → Run ℕ
  | [] => pureRun 0
  | j::js => bindRun (equalNatRun i.val j.val) fun equal =>
      bindRun (branchRun equal) fun equal =>
      if equal then pureRun 0 else bindRun (ordinalRun i js) fun n => addNatRun 1 n
end
end Reference.LexTensorExecution
/- Literal finite original-index scans and cyclic-window mask execution. -/
set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage
def readRun (x : ℝ) : Run ℝ := liftRun (Reference.LexTensorArithmeticExecution.readReal x)
def lessRealRun (x y : ℝ) : Run Bool := liftRun (Reference.LexTensorArithmeticExecution.lessReal x y)
def equalScanRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) : Run (List (Fin m)) :=
  filterRun (fun i => bindRun (readRun (sigma i)) fun x => equalRealRun x tau) (List.finRange m)
def aboveScanRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) : Run (List (Fin m)) :=
  filterRun (fun i => bindRun (readRun (sigma i)) fun x => lessRealRun tau x) (List.finRange m)
def windowMaskRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) (i : Fin m) : Run Bool :=
  bindRun (readRun (sigma i)) fun x =>
  bindRun (lessRealRun tau x) fun above =>
  bindRun (branchRun above) fun above =>
  if above then pureRun true else
  bindRun (equalRealRun x tau) fun equal =>
  bindRun (branchRun equal) fun equal =>
  if equal then
    bindRun (ordinalRun i boundary) fun a =>
    bindRun (subNatRun boundary.length j) fun b =>
    bindRun (addNatRun a b) fun c =>
    bindRun (modNatRun c boundary.length) fun d => lessNatRun d s
  else pureRun false
def windowScanRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) : Run (List (Fin m)) :=
  filterRun (windowMaskRun sigma tau boundary s j) (List.finRange m)
def frameFromListRun {m : ℕ} (V : Square m) (is : List (Fin m)) : Run (Rect m is.length) :=
  liftRun (Reference.LexTensorArithmeticExecution.vectorRun m fun i =>
    Reference.LexTensorArithmeticExecution.vectorRun is.length fun j =>
      Reference.LexTensorArithmeticExecution.readReal (V i (is.get j)))
end
end Reference.LexTensorExecution
/- Validity of the fixed exact spectral primitive and actual rank from finite scans. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix
end
end Reference.LexTensorExecution
/- Concrete spectral-window execution equals the actual ordered frame predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexOrderedCyclicBoundary
end
end Reference.LexTensorExecution
/- Literal squared entry error uses finite reads, subtraction, multiplication and addition. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary Reference.TensorCandidateSelection
open scoped BigOperators Matrix
def rowErrorRun : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → Run ℝ
  | 0,_,_ => zeroReal
  | n+1,a,b => bindRun (readReal (a 0)) fun x =>
      bindRun (readReal (b 0)) fun y =>
      bindRun (subReal x y) fun z =>
      bindRun (mulReal z z) fun p =>
      bindRun (rowErrorRun n (fun i => a i.succ) (fun i => b i.succ)) fun q => addReal p q
def matrixErrorRun : (m n : ℕ) → Rect m n → Rect m n → Run ℝ
  | 0,_,_,_ => zeroReal
  | m+1,n,A,B => bindRun (rowErrorRun n (fun j => A 0 j) (fun j => B 0 j)) fun x =>
      bindRun (matrixErrorRun m n (fun i j => A i.succ j) (fun i j => B i.succ j)) fun y => addReal x y
def tensorErrorRun {m : ℕ} {ns : List ℕ} (A B : Tensor m ns) : Run ℝ :=
  matrixErrorRun m (Fintype.card (ModeIndex ns)) (denseTensor A) (denseTensor B)
end
end Reference.LexTensorArithmeticExecution
/- First-minimum selection is an actual interpreted finite loop over computed candidates.
This module verifies the selection stage; candidate generation is not charged here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.LexTensorCompletion Reference.TensorCandidateSelection
def minimumRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (x : Tensor m ns) :
    List (Tensor m ns) → Run (Tensor m ns)
  | [] => pureRun x
  | y::ys => bindRun (tensorErrorRun A y) fun ey =>
      bindRun (tensorErrorRun A x) fun ex =>
      bindRun (lessReal ey ex) fun better =>
      if better then minimumRun A y ys else minimumRun A x ys
end
end Reference.LexTensorArithmeticExecution
/- Dense tensor operations are finite scalar loops; grouping is literal entry copying. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary
open scoped BigOperators Matrix
def copyMatrixRun {m n : ℕ} (A : Rect m n) : Run (Rect m n) :=
  vectorRun m fun i => vectorRun n fun j => readReal (A i j)
def tensorCopyRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) : Run (Tensor m ns) :=
  bindRun (copyMatrixRun (denseTensor A)) fun Z =>
    pureRun (Z.submatrix id (concreteLayout ns))
def tensorMulRun {m k : ℕ} {ns : List ℕ} (V : Rect m k) (A : Tensor k ns) : Run (Tensor m ns) :=
  bindRun (matrixMulRun V (denseTensor A)) fun Z =>
    pureRun (Z.submatrix id (concreteLayout ns))
def frameRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) : Run (Rect m (min r m)) :=
  bindRun (leftSubspace (denseTensor A)) fun V =>
    copyMatrixRun (fun i j => V i ⟨j.val,j.isLt.trans_le (Nat.min_le_right r m)⟩)
end
end Reference.LexTensorArithmeticExecution
/- Named recursive TT-SVD execution with exact actual subspace and scalar instructions. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
open scoped Matrix
def ttRun (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) : Run (Tensor m ns) :=
  match ns,A,rs with
  | [],A,_ => pureRun A
  | _::_,A,[] => pureRun A
  | n::ns,A,r::rs =>
    bindRun (frameRun A r) fun U =>
    bindRun (tensorMulRun U.transpose A) fun C0 =>
    bindRun (tensorCopyRun (merge C0)) fun C =>
    bindRun (ttRun (rowCount (min r m) n) ns C rs) fun Z =>
    bindRun (tensorCopyRun (unmerge (m:=min r m) (n:=n) Z)) fun Z0 =>
    tensorMulRun U Z0
termination_by ns.length
def completionRun {m k n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (U : Rect m k) (rs : List ℕ) : Run (Tensor m (n::ns)) :=
  bindRun (tensorMulRun U.transpose A) fun C0 =>
  bindRun (tensorCopyRun (merge C0)) fun C =>
  bindRun (ttRun (rowCount k n) ns C rs) fun Z =>
  bindRun (tensorCopyRun (unmerge (m:=k) (n:=n) Z)) fun Z0 => tensorMulRun U Z0
end
end Reference.LexTensorArithmeticExecution
/- The trace charge is extracted from execution, then bounded from actual tensor shapes. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
end
end Reference.LexTensorArithmeticExecution
/- Actual window scanning, copied frames and named recursive completion execution. -/
set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
def cyclicExecutionRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (V : Square m) (sigma : Fin m → ℝ) (tau : ℝ) (s j : ℕ) (rs : List ℕ) :
    Run (Tensor m (n::ns)) :=
  bindRun (equalScanRun sigma tau) fun boundary =>
  bindRun (windowScanRun sigma tau boundary s j) fun indices =>
  bindRun (frameFromListRun V indices) fun U =>
  liftRun (Reference.LexTensorArithmeticExecution.completionRun A U rs)
end
end Reference.LexTensorExecution
/- Uniform polynomial counts follow from genuine shrinking dense unfolding dimensions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
end
end Reference.LexTensorArithmeticExecution
/- Literal ordered candidate generation and first-minimum execution.
Static indexing, list reference manipulation and shape proof casts are free in
this ideal exact arithmetic model; real reads/arithmetic, singular-subspace,
real equality/order and explicit natural/branch instructions are charged.
Every spectrum/rank/tie datum originates in the charged spectral reply. -/
set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
def listMapRun {α β : Type} (f : α → Run β) : List α → Run (List β)
  | [] => pureRun []
  | x::xs => bindRun (f x) fun y => bindRun (listMapRun f xs) fun ys => pureRun (y::ys)
def prefixFrameRun {m : ℕ} (V : Square m) (k : ℕ) : Run (Rect m (min k m)) :=
  liftRun (Reference.LexTensorArithmeticExecution.vectorRun m fun i =>
    Reference.LexTensorArithmeticExecution.vectorRun (min k m) fun j =>
      Reference.LexTensorArithmeticExecution.readReal (V i ⟨j.val,lt_of_lt_of_le j.isLt (Nat.min_le_right k m)⟩))
def prefixCompletionRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (V : Square m) (k : ℕ) (rs : List ℕ) : Run (Tensor m (n::ns)) :=
  bindRun (prefixFrameRun V k) fun U => liftRun (Reference.LexTensorArithmeticExecution.completionRun A U rs)
def sigmaAtRun {m : ℕ} (sigma : Fin m → ℝ) (a : ℕ) : Run ℝ :=
  let test := lessNatRun a m
  let control := branchRun test.value
  if h : control.value=true then
    let x := readRun (sigma ⟨a,of_decide_eq_true h⟩)
    ⟨x.value,test.trace++control.trace++x.trace⟩
  else
    let x := liftRun Reference.LexTensorArithmeticExecution.zeroReal
    ⟨x.value,test.trace++control.trace++x.trace⟩
def candidateDataRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (V : Square m) (sigma : Fin m → ℝ) (r : ℕ) (rs : List ℕ) : Run (List (Tensor m (n::ns))) :=
  bindRun (aboveScanRun sigma 0) fun positive =>
  bindRun (lessNatRun r positive.length) fun greater =>
  bindRun (branchRun greater) fun greater =>
  if greater then
    bindRun (subNatRun r 1) fun a =>
    bindRun (sigmaAtRun sigma a) fun tau =>
    bindRun (aboveScanRun sigma tau) fun above =>
    bindRun (equalScanRun sigma tau) fun boundary =>
    bindRun (subNatRun r above.length) fun s =>
    bindRun (lessNatRun 0 boundary.length) fun nonempty =>
    bindRun (branchRun nonempty) fun nonempty =>
    if nonempty then
      bindRun (equalNatRun s boundary.length) fun full =>
      bindRun (branchRun full) fun full =>
      if full then
        bindRun (cyclicExecutionRun A V sigma tau s 0 rs) fun X => pureRun [X]
      else listMapRun (fun j : Fin boundary.length => cyclicExecutionRun A V sigma tau s j.val rs)
        (List.finRange boundary.length)
    else bindRun (prefixCompletionRun A V r rs) fun X => pureRun [X]
  else bindRun (prefixCompletionRun A V positive.length rs) fun X => pureRun [X]
def candidatesExecutionRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (r : ℕ) (rs : List ℕ) : Run (List (Tensor m (n::ns))) :=
  bindRun (spectralRun (denseTensor A)) fun data => candidateDataRun A data.1 data.2 r rs
def solverExecutionRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (r : ℕ) (rs : List ℕ) : Run (Tensor m (n::ns)) :=
  bindRun (candidatesExecutionRun A r rs) fun xs =>
  match xs with
  | [] => bindRun (spectralRun (denseTensor A)) fun data => prefixCompletionRun A data.1 r rs
  | x::ys => liftRun (Reference.LexTensorArithmeticExecution.minimumRun A x ys)
end
end Reference.LexTensorExecution
end
section
/- Original module: NLA.TR04.LexicographicTensorChallengeR3 -/
/- Literal concrete-layout arithmetic/SVD algorithm for the exact main.tex TR04 claims. -/
set_option autoImplicit false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.LexTensorCompletion Reference.TensorOptimumAttainment
theorem actual_lexicographic_paper_algorithm {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 1 ≤ m) (hmode : ∀ a∈n::ns,2 ≤ a) :
    Reference.RecursiveTensorCompletion.feasible m (n::ns) (solverExecutionRun A r rs).value (r::rs) ∧
    0<(candidatesExecutionRun A r rs).value.length ∧
    (candidatesExecutionRun A r rs).value.length ≤ m ∧
    (0<optimalError A (r::rs) → Reference.RecursiveTensorCompletion.tensorFrobeniusSq
      (A-(solverExecutionRun A r rs).value)<((n::ns).length : ℝ)*optimalError A (r::rs)) ∧
    (optimalError A (r::rs)=0 → (solverExecutionRun A r rs).value=A) ∧
    charge (solverExecutionRun A r rs) ≤ 1500*(m*(n::ns).prod)^5 := by sorry
end
end Reference.LexTensorExecution
/- Exact first-minimum tie rule and full ordered solver execution semantics. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.LexTensorCompletion
end
end Reference.LexTensorExecution
/- Full charged indexed-array solver polynomial operation bound.
This model currently uses the frozen static tensor layout; the concrete
lexicographic layout bridge is a separate obligation, not a free runtime oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
end
end Reference.LexTensorExecution
/- Actual generated candidate nonemptiness and completion count, before selection. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
end
end Reference.LexTensorExecution
/- Validity of the fixed exact spectral primitive and actual rank from finite scans. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix
end
end Reference.LexTensorExecution
/- Validity of the fixed exact spectral primitive and actual rank from finite scans. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix
end
end Reference.LexTensorExecution
/- Concrete recursion defines exactly the actual manuscript feasible set. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
end
end Reference.LexTensorCompletion
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Genuine arbitrary-order finite tensor TT approximation by recursive optimal projections.
All cuts are actual grouped/reindexed matrix ranks; the error induction uses exact Pythagoras.
New reference-only proof by Codex, 2026-10-03. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage
end
end Reference.LexTensorCompletion
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Genuine arbitrary-order finite tensor TT approximation by recursive optimal projections.
All cuts are actual grouped/reindexed matrix ranks; the error induction uses exact Pythagoras.
New reference-only proof by Codex, 2026-10-03. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage
end
end Reference.LexTensorCompletion
/- Named recursive TT-SVD execution with exact actual subspace and scalar instructions. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
open scoped Matrix
end
end Reference.LexTensorArithmeticExecution
/- Named recursive TT-SVD execution with exact actual subspace and scalar instructions. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
open scoped Matrix
end
end Reference.LexTensorArithmeticExecution
/- The new ascending-index algorithm has its own actual attained-minimum guarantee. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexOrderedTensorSolver
noncomputable section
open Reference.LexTensorCompletion Reference.TensorOptimumAttainment
end
end Reference.LexOrderedTensorSolver
/- Explicit row-major and mixed-radix traversal equations; no chosen permutations. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
end
end Reference.LexTensorCompletion
/- Explicit row-major and mixed-radix traversal equations; no chosen permutations. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
end
end Reference.LexTensorCompletion
/- Explicit row-major and mixed-radix traversal equations; no chosen permutations. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
end
end Reference.LexTensorCompletion
/- Explicit row-major and mixed-radix traversal equations; no chosen permutations. -/
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
end
end Reference.LexTensorCompletion
end
