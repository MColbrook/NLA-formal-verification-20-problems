module

/- Exact structured arithmetic and singular-subspace interpreter.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex.
A trace records actual scalar operands; each interpreter call produces its result.
No supplied runtime, solver instruction, or correctness contract is present. -/
public import NLA.TR04.TensorCandidateSelection.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorArithmeticExecution
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
end Reference.TensorArithmeticExecution
