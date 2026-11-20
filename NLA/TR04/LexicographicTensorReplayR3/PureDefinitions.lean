module

public import NLA.TR04.OptimalityEquality.Boundary
/- Standalone pure Challenge bodies copied from frozen concrete solver. No solver proof imports. -/
public import NLA.TR04.RecursiveTensorCompletion.Definitions
public import NLA.TR04.LexicographicFeasibilityBridge.Definitions
public import NLA.TR04.OptimalityEquality.CountDefinitions
public import NLA.TR04.TensorCandidateSelection.Definitions
public import NLA.TR04.TensorOptimumAttainment.Definitions
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic

@[expose] public section

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

inductive Reply where
  | scalar (x : ℝ)
  | decision (b : Bool)
  | leftBasis (m : ℕ) (V : Square m)

def interpret : Event → Reply
  | .read x => .scalar x
  | .zero => .scalar 0
  | .add x y => .scalar (x+y)
  | .sub x y => .scalar (x-y)
  | .mul x y => .scalar (x*y)
  | .less x y => .decision (decide (x<y))
  | .leftSubspace _ _ A => .leftBasis _ (leftVectorMatrix A)

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

def charge {α : Type} (x : Run α) : ℕ := (x.trace.map eventCharge).sum

def replay {α : Type} (x : Run α) : List Reply := x.trace.map interpret
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

/- Explicit ascending original-index scans and inverse lookup; no choice of enumeration.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/

set_option autoImplicit false
namespace Reference.LexOrderedIndex

def indexList {m : ℕ} (p : Fin m → Prop) [DecidablePred p] : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (p i))

theorem mem_indexList {m : ℕ} (p : Fin m → Prop) [DecidablePred p] (i : Fin m) :
    i∈indexList p ↔ p i := by simp [indexList]

theorem nodup_indexList {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (indexList p).Nodup := (List.nodup_finRange m).filter _

def predicateListEquiv {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    {i : Fin m // p i} ≃ {i : Fin m // i∈indexList p} where
  toFun i := ⟨i.val,(mem_indexList p i.val).mpr i.property⟩
  invFun i := ⟨i.val,(mem_indexList p i.val).mp i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def listEnum {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    {i : Fin m // p i} ≃ Fin (indexList p).length :=
  (predicateListEquiv p).trans (List.Nodup.getEquiv (indexList p) (nodup_indexList p)).symm

theorem indexList_length {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (indexList p).length=Fintype.card {i : Fin m // p i} := by
  have h:=Fintype.card_congr (listEnum p)
  simpa only [Fintype.card_fin] using h.symm

def indexEnum {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    {i : Fin m // p i} ≃ Fin (Fintype.card {i : Fin m // p i}) :=
  (listEnum p).trans (finCongr (indexList_length p))
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

theorem lexCard_eq_card (ns : List ℕ) : lexCard ns=Fintype.card (ModeIndex ns) := by
  induction ns with
  | nil => change 1=Fintype.card PUnit; exact Fintype.card_punit.symm
  | cons n ns ih =>
      change n*lexCard ns=Fintype.card (Fin n × ModeIndex ns)
      rw [Fintype.card_prod,Fintype.card_fin,ih]

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

def eCount {m n : ℕ} (A : Rect m n) (tau : ℝ) := Fintype.card (EIndex A tau)

def hCount {m n : ℕ} (A : Rect m n) (tau : ℝ) := Fintype.card (HIndex A tau)

def boundaryOrdinal {m n : ℕ} (A : Rect m n) (tau : ℝ) := Reference.LexOrderedIndex.indexEnum (fun i : Fin m => singularValue A.transpose i.val=tau)

def inWindow {t : ℕ} (s : ℕ) (j i : Fin t) : Prop := (i-j).val<s

def windowSelected {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) (i : Fin m) : Prop :=
  if he : singularValue A.transpose i.val=tau then
    inWindow s j (boundaryOrdinal A tau ⟨i,he⟩) else False

def selected {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) (i : Fin m) : Prop :=
  tau<singularValue A.transpose i.val ∨ windowSelected A tau s j i

def indicator {m : ℕ} (p : Fin m → Prop) : Fin m → ℝ := fun i => if p i then 1 else 0

def indicatorProjector {m : ℕ} (V : Square m) (p : Fin m → Prop) : Square m :=
  V * Matrix.diagonal (indicator p) * V.transpose

def indicatorFrame {m : ℕ} (V : Square m) (p : Fin m → Prop) :
    Rect m (Fintype.card {i : Fin m // p i}) :=
  V.submatrix id (fun j => ((Reference.LexOrderedIndex.indexEnum p).symm j).val)

def windowProjector {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) : Square m :=
  indicatorProjector (leftVectorMatrix A) (windowSelected A tau s j)

def candidateProjector {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) : Square m :=
  indicatorProjector (leftVectorMatrix A) (selected A tau s j)

def candidateFrame {m n : ℕ} (A : Rect m n) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount A tau)) :=
  indicatorFrame (leftVectorMatrix A) (selected A tau s j)
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
end Reference.LexTensorCompletion

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Genuine finite cyclic-window counts; actual H/E multiplicity bindings. -/

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped BigOperators

def reflected {t : ℕ} [NeZero t] (i : Fin t) : Fin t ≃ Fin t where
  toFun j := i-j
  invFun j := i-j
  left_inv j := by dsimp; abel
  right_inv j := by dsimp; abel

def shifted {t : ℕ} [NeZero t] (j : Fin t) : Fin t ≃ Fin t where
  toFun i := i-j
  invFun i := i+j
  left_inv i := by dsimp; abel
  right_inv i := by dsimp; abel
end
end Reference.LexOrderedCyclicBoundary

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Pure concrete cyclic candidate completions, each using named actual recursive TT-SVD. -/

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion

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
end Reference.LexOrderedCyclicBoundary

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Literal ordered candidates and first-minimum selection. Pure definitions.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/

set_option autoImplicit false
namespace Reference.LexOrderedTensorSolver
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary

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

inductive Reply where
  | ordinary (r : Reference.LexTensorArithmeticExecution.Reply)
  | spectral (m : ℕ) (V : Square m) (sigma : Fin m → ℝ)
  | decision (b : Bool)
  | number (n : ℕ)

def interpret : Event → Reply
  | .ordinary e => .ordinary (Reference.LexTensorArithmeticExecution.interpret e)
  | .spectral _ _ A => .spectral _ (leftVectorMatrix A) (fun i => singularValue A.transpose i.val)
  | .equalReal x y => .decision (decide (x=y))
  | .equalNat x y => .decision (decide (x=y))
  | .lessNat x y => .decision (decide (x<y))
  | .addNat x y => .number (x+y)
  | .subNat x y => .number (x-y)
  | .modNat x y => .number (x%y)
  | .branch b => .decision b

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

def positiveRankEquiv {m n : ℕ} (A : Rect m n) :
    {i : Fin m // 0<singularValue A.transpose i.val} ≃ Fin A.rank where
  toFun i := ⟨i.val.val,by
    have h := (singularValue_pos_iff_lt_rank A.transpose i.val.val).mp i.property
    simpa only [Matrix.rank_transpose] using h⟩
  invFun j := ⟨⟨j.val,by
      have h := Matrix.rank_le_width A.transpose
      rw [Matrix.rank_transpose] at h
      exact lt_of_lt_of_le j.isLt h⟩,by
    apply (singularValue_pos_iff_lt_rank A.transpose j.val).mpr
    simpa only [Matrix.rank_transpose] using j.isLt⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv j := by apply Fin.ext; rfl
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

abbrev sigmaOf {m n : ℕ} (A : Rect m n) := fun i : Fin m => singularValue A.transpose i.val
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

def selectionStageRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    Run (Tensor m (n::ns)) :=
  match candidates A r rs with
  | [] => pureRun (leadingCompletion A r rs)
  | x::xs => minimumRun A x xs
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

def modeCard (ns : List ℕ) : ℕ := Fintype.card (ModeIndex ns)

def ttCharge (m : ℕ) (ns rs : List ℕ) : ℕ :=
  match ns,rs with
  | [],_ => 0
  | _::_,[] => 0
  | n::ns,r::rs =>
    let k:=min r m
    let p:=modeCard (n::ns)
    (m+p+1)^3+m*k+k*p*(4*m+1)+rowCount k n*modeCard ns+
      ttCharge (rowCount k n) ns rs+k*p+m*p*(4*k+1)
termination_by ns.length
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

def denseSize (m : ℕ) (ns : List ℕ) : ℕ := m*modeCard ns
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

