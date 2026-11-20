module

public import NLA.MF12.PaperDefinitions
public import NLA.MF12.MatrixAlgebra

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace NLA.MF12.Paper

def parameterPower (lam μ : ℝ) (q : ℕ) : Square 6 :=
  !![1,0,0,0,0,0; 0,lam^q,(q:ℝ)*lam^q,0,0,0; 0,0,lam^q,0,0,0;
     0,0,0,μ^q,(q:ℝ)*μ^q,0; 0,0,0,0,μ^q,0; 0,0,0,0,0,1]

theorem parameter_power (lam μ : ℝ) (q : ℕ) :
    parameterMatrix lam μ ^ q = parameterPower lam μ q := by
  induction q with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [parameterPower, Matrix.one_apply, Fin.ext_iff]
  | succ q ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [parameterMatrix, parameterPower, Matrix.mul_apply, Fin.sum_univ_succ,
          pow_succ, Nat.cast_add, Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_two] <;> ring

theorem parameter_compressed_powers (lam μ : ℝ) (q : ℕ) :
    parameterCompressed lam μ q = !![1 - parameterLoss lam q, parameterGain μ q; 0,1] := by
  rw [parameterCompressed, parameter_power]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [parameterPower, sourceU, sourceV, parameterLoss, parameterGain,
      Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecHead, Matrix.vecTail,
      Matrix.cons_val_two] <;> ring

#print axioms parameter_power
#print axioms parameter_compressed_powers
end NLA.MF12.Paper
