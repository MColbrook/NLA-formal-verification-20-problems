module

/- Literal squared entry error uses finite reads, subtraction, multiplication and addition. -/
public import NLA.TR04.TensorArithmeticExecution.DenseLoops

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion Reference.CyclicBoundary Reference.TensorCandidateSelection
open scoped BigOperators Matrix

def rowErrorRun : (n : ℕ) → (Fin n → ℝ) → (Fin n → ℝ) → Run ℝ
  | 0,_,_ => zeroReal
  | n+1,a,b => bindRun (readReal (a 0)) fun x =>
      bindRun (readReal (b 0)) fun y =>
      bindRun (subReal x y) fun z =>
      bindRun (mulReal z z) fun p =>
      bindRun (rowErrorRun n (fun i => a i.succ) (fun i => b i.succ)) fun q => addReal p q

theorem rowErrorRun_value (n : ℕ) (a b : Fin n → ℝ) :
    (rowErrorRun n a b).value=∑ i, (a i-b i)^2 := by
  induction n with
  | zero => simp [rowErrorRun,zeroReal]
  | succ n ih => simp only [rowErrorRun,value_bind,value_read,value_sub,value_mul,value_add,ih,Fin.sum_univ_succ,pow_two]

theorem rowErrorRun_charge (n : ℕ) (a b : Fin n → ℝ) : charge (rowErrorRun n a b)=5*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [rowErrorRun,charge_bind,charge_read,charge_sub,charge_mul,charge_add,value_read,value_sub,value_mul,ih]
    omega

def matrixErrorRun : (m n : ℕ) → Rect m n → Rect m n → Run ℝ
  | 0,_,_,_ => zeroReal
  | m+1,n,A,B => bindRun (rowErrorRun n (fun j => A 0 j) (fun j => B 0 j)) fun x =>
      bindRun (matrixErrorRun m n (fun i j => A i.succ j) (fun i j => B i.succ j)) fun y => addReal x y

theorem matrixErrorRun_value (m n : ℕ) (A B : Rect m n) :
    (matrixErrorRun m n A B).value=frobeniusSq (A-B) := by
  induction m with
  | zero => simp [matrixErrorRun,zeroReal,frobeniusSq]
  | succ m ih =>
    simp only [matrixErrorRun,value_bind,value_add,rowErrorRun_value,ih]
    simp [frobeniusSq,Fin.sum_univ_succ]

theorem matrixErrorRun_charge (m n : ℕ) (A B : Rect m n) :
    charge (matrixErrorRun m n A B)=m*(5*n+2)+1 := by
  induction m with
  | zero => simp only [matrixErrorRun,charge_zero,Nat.zero_mul,Nat.zero_add]
  | succ m ih =>
    simp only [matrixErrorRun,charge_bind,rowErrorRun_charge,charge_add,ih,Nat.add_mul,Nat.one_mul]
    omega

def tensorErrorRun {m : ℕ} {ns : List ℕ} (A B : Tensor m ns) : Run ℝ :=
  matrixErrorRun m (Fintype.card (ModeIndex ns)) (denseTensor A) (denseTensor B)

theorem tensorErrorRun_value {m : ℕ} {ns : List ℕ} (A B : Tensor m ns) :
    (tensorErrorRun A B).value=error A B := by
  rw [tensorErrorRun,matrixErrorRun_value,← denseTensor_sub,denseTensor_frobenius]
  rfl

theorem actual_squared_entry_error_execution_charge {m : ℕ} {ns : List ℕ} (A B : Tensor m ns) :
    charge (tensorErrorRun A B)=m*(5*Fintype.card (ModeIndex ns)+2)+1 :=
  matrixErrorRun_charge _ _ _ _

#print axioms tensorErrorRun_value
#print axioms actual_squared_entry_error_execution_charge
end
end Reference.TensorArithmeticExecution
