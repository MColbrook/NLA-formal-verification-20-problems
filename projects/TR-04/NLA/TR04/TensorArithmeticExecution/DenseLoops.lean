module

/- Literal finite arithmetic loops: data are produced by interpreter calls. -/
public import NLA.TR04.TensorArithmeticExecution.Definitions
public import NLA.TR04.TensorCandidateSelection.Ordered

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix

@[simp] theorem charge_pure {α : Type} (x : α) : charge (pureRun x)=0 := rfl
@[simp] theorem charge_bind {α β : Type} (x : Run α) (f : α → Run β) :
    charge (bindRun x f)=charge x+charge (f x.value) := by
  simp [charge,bindRun,List.map_append,List.sum_append]
@[simp] theorem value_pure {α : Type} (x : α) : (pureRun x).value=x := rfl
@[simp] theorem value_bind {α β : Type} (x : Run α) (f : α → Run β) :
    (bindRun x f).value=(f x.value).value := rfl

@[simp] theorem charge_read (x : ℝ) : charge (readReal x)=1 := rfl
@[simp] theorem charge_zero : charge zeroReal=1 := rfl
@[simp] theorem charge_add (x y : ℝ) : charge (addReal x y)=1 := rfl
@[simp] theorem charge_sub (x y : ℝ) : charge (subReal x y)=1 := rfl
@[simp] theorem charge_mul (x y : ℝ) : charge (mulReal x y)=1 := rfl
@[simp] theorem charge_less (x y : ℝ) : charge (lessReal x y)=1 := rfl
@[simp] theorem value_read (x : ℝ) : (readReal x).value=x := rfl
@[simp] theorem value_zero : zeroReal.value=0 := rfl
@[simp] theorem value_add (x y : ℝ) : (addReal x y).value=x+y := rfl
@[simp] theorem value_sub (x y : ℝ) : (subReal x y).value=x-y := rfl
@[simp] theorem value_mul (x y : ℝ) : (mulReal x y).value=x*y := rfl
@[simp] theorem value_less (x y : ℝ) : (lessReal x y).value=decide (x<y) := rfl

/-- Finite zero-based vector loop. Index manipulation copies references only. -/
def vectorRun {α : Type} : (n : ℕ) → (Fin n → Run α) → Run (Fin n → α)
  | 0,_ => pureRun Fin.elim0
  | n+1,f => bindRun (f 0) fun x =>
      bindRun (vectorRun n (fun i => f i.succ)) fun xs => pureRun (Fin.cases x xs)

theorem vectorRun_value {α : Type} (n : ℕ) (f : Fin n → Run α) :
    (vectorRun n f).value=fun i => (f i).value := by
  induction n with
  | zero => funext i;exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [vectorRun,value_bind,value_pure,Fin.cases_succ,ih]

theorem vectorRun_charge {α : Type} (n : ℕ) (f : Fin n → Run α) :
    charge (vectorRun n f)=∑ i, charge (f i) := by
  induction n with
  | zero => simp [vectorRun]
  | succ n ih => simp [vectorRun,charge_bind,ih,Fin.sum_univ_succ]

/-- Actual dense dot product, with two operand reads, multiplication and addition per entry. -/
def dotRun : (k : ℕ) → (Fin k → ℝ) → (Fin k → ℝ) → Run ℝ
  | 0,_,_ => zeroReal
  | k+1,a,b => bindRun (readReal (a 0)) fun x =>
      bindRun (readReal (b 0)) fun y =>
      bindRun (mulReal x y) fun p =>
      bindRun (dotRun k (fun i => a i.succ) (fun i => b i.succ)) fun q => addReal p q

theorem dotRun_value (k : ℕ) (a b : Fin k → ℝ) :
    (dotRun k a b).value=∑ i, a i*b i := by
  induction k with
  | zero => simp [dotRun,zeroReal]
  | succ k ih => simp only [dotRun,value_bind,value_read,value_mul,value_add,ih,Fin.sum_univ_succ]

theorem dotRun_charge (k : ℕ) (a b : Fin k → ℝ) :
    charge (dotRun k a b)=4*k+1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [dotRun,charge_bind,charge_read,charge_mul,charge_add,value_read,value_mul,ih]
    omega

def matrixMulRun {m k n : ℕ} (A : Rect m k) (B : Rect k n) : Run (Rect m n) :=
  vectorRun m fun i => vectorRun n fun j => dotRun k (fun a => A i a) (fun a => B a j)

theorem matrixMulRun_value {m k n : ℕ} (A : Rect m k) (B : Rect k n) :
    (matrixMulRun A B).value=A*B := by
  funext i j
  simp only [matrixMulRun,vectorRun_value,dotRun_value,Matrix.mul_apply]

theorem actual_dense_multiplication_charge {m k n : ℕ} (A : Rect m k) (B : Rect k n) :
    charge (matrixMulRun A B)=m*n*(4*k+1) := by
  let a : Fin m → Fin k → ℝ := A
  let b : Fin k → Fin n → ℝ := B
  change charge (vectorRun m (fun i => vectorRun n (fun j => dotRun k (a i) (fun t => b t j))))=m*n*(4*k+1)
  rw [vectorRun_charge]
  simp_rw [vectorRun_charge,dotRun_charge]
  simp
  ring

#print axioms matrixMulRun_value
#print axioms actual_dense_multiplication_charge
end
end Reference.TensorArithmeticExecution
