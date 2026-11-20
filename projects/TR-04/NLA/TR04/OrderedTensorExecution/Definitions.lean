module

/- Explicit exact arithmetic/SVD/equality and finite natural-index operations.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
public import NLA.TR04.OrderedTensorSolver.SolverDefinitions
public import NLA.TR04.TensorArithmeticExecution.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix

inductive Event where
  | ordinary (e : Reference.TensorArithmeticExecution.Event)
  | spectral (m n : ℕ) (A : Rect m n)
  | equalReal (x y : ℝ)
  | equalNat (x y : ℕ)
  | lessNat (x y : ℕ)
  | addNat (x y : ℕ)
  | subNat (x y : ℕ)
  | modNat (x y : ℕ)
  | branch (b : Bool)

inductive Reply where
  | ordinary (r : Reference.TensorArithmeticExecution.Reply)
  | spectral (m : ℕ) (V : Square m) (sigma : Fin m → ℝ)
  | decision (b : Bool)
  | number (n : ℕ)

def interpret : Event → Reply
  | .ordinary e => .ordinary (Reference.TensorArithmeticExecution.interpret e)
  | .spectral _ _ A => .spectral _ (leftVectorMatrix A) (fun i => singularValue A.transpose i.val)
  | .equalReal x y => .decision (decide (x=y))
  | .equalNat x y => .decision (decide (x=y))
  | .lessNat x y => .decision (decide (x<y))
  | .addNat x y => .number (x+y)
  | .subNat x y => .number (x-y)
  | .modNat x y => .number (x%y)
  | .branch b => .decision b

def eventCharge : Event → ℕ
  | .ordinary e => Reference.TensorArithmeticExecution.eventCharge e
  | .spectral m n _ => (m+n+1)^3
  | _ => 1

structure Run (α : Type) where
  value : α
  trace : List Event

def pureRun {α : Type} (x : α) : Run α := ⟨x,[]⟩
def bindRun {α β : Type} (x : Run α) (f : α → Run β) : Run β :=
  let y:=f x.value
  ⟨y.value,x.trace++y.trace⟩
def liftRun {α : Type} (x : Reference.TensorArithmeticExecution.Run α) : Run α :=
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
end Reference.OrderedTensorExecution
