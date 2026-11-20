module

/- Literal ordered candidate generation and first-minimum execution.
Static indexing, list reference manipulation and shape proof casts are free in
this ideal exact arithmetic model; real reads/arithmetic, singular-subspace,
real equality/order and explicit natural/branch instructions are charged.
Every spectrum/rank/tie datum originates in the charged spectral reply. -/
public import NLA.TR04.OrderedTensorExecution.CandidateDefinitions
public import NLA.TR04.TensorArithmeticExecution.MinimumExecution

@[expose] public section

set_option autoImplicit false
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion

def listMapRun {α β : Type} (f : α → Run β) : List α → Run (List β)
  | [] => pureRun []
  | x::xs => bindRun (f x) fun y => bindRun (listMapRun f xs) fun ys => pureRun (y::ys)

def prefixFrameRun {m : ℕ} (V : Square m) (k : ℕ) : Run (Rect m (min k m)) :=
  liftRun (Reference.TensorArithmeticExecution.vectorRun m fun i =>
    Reference.TensorArithmeticExecution.vectorRun (min k m) fun j =>
      Reference.TensorArithmeticExecution.readReal (V i ⟨j.val,lt_of_lt_of_le j.isLt (Nat.min_le_right k m)⟩))

def prefixCompletionRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (V : Square m) (k : ℕ) (rs : List ℕ) : Run (Tensor m (n::ns)) :=
  bindRun (prefixFrameRun V k) fun U => liftRun (Reference.TensorArithmeticExecution.completionRun A U rs)

def sigmaAtRun {m : ℕ} (sigma : Fin m → ℝ) (a : ℕ) : Run ℝ :=
  let test := lessNatRun a m
  let control := branchRun test.value
  if h : control.value=true then
    let x := readRun (sigma ⟨a,of_decide_eq_true h⟩)
    ⟨x.value,test.trace++control.trace++x.trace⟩
  else
    let x := liftRun Reference.TensorArithmeticExecution.zeroReal
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
  | x::ys => liftRun (Reference.TensorArithmeticExecution.minimumRun A x ys)

end
end Reference.OrderedTensorExecution
