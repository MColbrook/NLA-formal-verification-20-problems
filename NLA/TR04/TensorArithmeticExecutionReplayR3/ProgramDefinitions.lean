module

/- Pure program declarations copied verbatim from the frozen eight-source arithmetic foundation. -/
public import NLA.TR04.TensorArithmeticExecution.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection Reference.CyclicBoundary
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

def copyMatrixRun {m n : ℕ} (A : Rect m n) : Run (Rect m n) :=
  vectorRun m fun i => vectorRun n fun j => readReal (A i j)

def tensorCopyRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) : Run (Tensor m ns) :=
  bindRun (copyMatrixRun (denseTensor A)) fun Z =>
    pureRun (Z.submatrix id (Fintype.equivFin (ModeIndex ns)))

def tensorMulRun {m k : ℕ} {ns : List ℕ} (V : Rect m k) (A : Tensor k ns) : Run (Tensor m ns) :=
  bindRun (matrixMulRun V (denseTensor A)) fun Z =>
    pureRun (Z.submatrix id (Fintype.equivFin (ModeIndex ns)))

def frameRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) : Run (Rect m (min r m)) :=
  bindRun (leftSubspace (denseTensor A)) fun V =>
    copyMatrixRun (fun i j => V i ⟨j.val,j.isLt.trans_le (Nat.min_le_right r m)⟩)

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

def denseSize (m : ℕ) (ns : List ℕ) : ℕ := m*modeCard ns

end
end Reference.TensorArithmeticExecution
