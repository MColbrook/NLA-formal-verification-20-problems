module

/- Dense tensor operations are finite scalar loops; grouping is literal entry copying. -/
public import NLA.TR04.TensorArithmeticExecution.MinimumExecution

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.CyclicBoundary
open scoped BigOperators Matrix

def copyMatrixRun {m n : ℕ} (A : Rect m n) : Run (Rect m n) :=
  vectorRun m fun i => vectorRun n fun j => readReal (A i j)

theorem copyMatrixRun_value {m n : ℕ} (A : Rect m n) : (copyMatrixRun A).value=A := by
  funext i j
  simp only [copyMatrixRun,vectorRun_value,value_read]

theorem copyMatrixRun_charge {m n : ℕ} (A : Rect m n) : charge (copyMatrixRun A)=m*n := by
  let a : Fin m → Fin n → ℝ := A
  change charge (vectorRun m (fun i => vectorRun n (fun j => readReal (a i j))))=m*n
  rw [vectorRun_charge]
  simp_rw [vectorRun_charge,charge_read]
  simp

def tensorCopyRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) : Run (Tensor m ns) :=
  bindRun (copyMatrixRun (denseTensor A)) fun Z =>
    pureRun (Z.submatrix id (Fintype.equivFin (ModeIndex ns)))

theorem tensorCopyRun_value {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    (tensorCopyRun A).value=A := by
  simp only [tensorCopyRun,value_bind,value_pure,copyMatrixRun_value]
  funext i j
  simp [denseTensor,Matrix.submatrix]

theorem tensorCopyRun_charge {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    charge (tensorCopyRun A)=m*Fintype.card (ModeIndex ns) := by
  simp only [tensorCopyRun,charge_bind,copyMatrixRun_charge,charge_pure,Nat.add_zero]

def tensorMulRun {m k : ℕ} {ns : List ℕ} (V : Rect m k) (A : Tensor k ns) : Run (Tensor m ns) :=
  bindRun (matrixMulRun V (denseTensor A)) fun Z =>
    pureRun (Z.submatrix id (Fintype.equivFin (ModeIndex ns)))

theorem tensorMulRun_value {m k : ℕ} {ns : List ℕ} (V : Rect m k) (A : Tensor k ns) :
    (tensorMulRun V A).value=V*A := by
  simp only [tensorMulRun,value_bind,value_pure,matrixMulRun_value]
  funext i j
  simp [Matrix.submatrix,Matrix.mul_apply,denseTensor]

theorem tensorMulRun_charge {m k : ℕ} {ns : List ℕ} (V : Rect m k) (A : Tensor k ns) :
    charge (tensorMulRun V A)=m*Fintype.card (ModeIndex ns)*(4*k+1) := by
  simp only [tensorMulRun,charge_bind,actual_dense_multiplication_charge,charge_pure,Nat.add_zero]

def frameRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) : Run (Rect m (min r m)) :=
  bindRun (leftSubspace (denseTensor A)) fun V =>
    copyMatrixRun (fun i j => V i ⟨j.val,j.isLt.trans_le (Nat.min_le_right r m)⟩)

theorem frameRun_value {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) :
    (frameRun A r).value=svdFrame A r := by
  simp only [frameRun,value_bind,copyMatrixRun_value]
  rfl

@[simp] theorem charge_leftSubspace {m n : ℕ} (A : Rect m n) :
    charge (leftSubspace A)=(m+n+1)^3 := rfl

theorem frameRun_charge {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) :
    charge (frameRun A r)=(m+Fintype.card (ModeIndex ns)+1)^3+m*min r m := by
  simp only [frameRun,charge_bind,copyMatrixRun_charge,charge_leftSubspace]

theorem actual_exact_subspace_primitive_is_valid {m n : ℕ} (A : Rect m n) :
    IsOrthogonal (leftSubspace A).value ∧
    (leftSubspace A).value.transpose*(A*A.transpose)*(leftSubspace A).value=
      Matrix.diagonal (fun i : Fin m => singularValue A.transpose i.val^2) := by
  exact ⟨leftVectorMatrix_orthogonal A,leftVectorMatrix_gram_diagonal A⟩

#print axioms tensorMulRun_value
#print axioms tensorMulRun_charge
#print axioms frameRun_value
#print axioms actual_exact_subspace_primitive_is_valid
end
end Reference.TensorArithmeticExecution
