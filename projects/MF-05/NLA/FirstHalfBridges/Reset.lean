module

public import NLA.FirstHalfBridges.Definitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace RootFirstHalfBridges
open NLA.MF12 NLA.MF12.Paper

theorem actual_source_uv : sourceU*sourceV = (1 : Square 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [sourceU,sourceV,Matrix.mul_apply,Fin.sum_univ_succ]

theorem actual_reset_geometry : resetMatrix^2=resetMatrix ∧ resetMatrix.rank=2 ∧
    resetMatrix.transpose ≠ resetMatrix := by
  have huv := actual_source_uv
  have hpp : resetMatrix^2=resetMatrix := by
    simp only [resetMatrix,pow_two,Matrix.mul_assoc,← Matrix.mul_assoc sourceU sourceV,huv,Matrix.one_mul]
  have hupv : sourceU*resetMatrix*sourceV=(1 : Square 2) := by
    simp only [resetMatrix,Matrix.mul_assoc,← Matrix.mul_assoc sourceU sourceV,huv,Matrix.one_mul]
  have hlow : 2 ≤ resetMatrix.rank := by
    calc
      2 = Matrix.rank (1 : Square 2) := by simp
      _ = Matrix.rank (sourceU*resetMatrix*sourceV) := congrArg Matrix.rank hupv.symm
      _ ≤ Matrix.rank (sourceU*resetMatrix) := Matrix.rank_mul_le_left _ _
      _ ≤ resetMatrix.rank := Matrix.rank_mul_le_right _ _
  have hupp : resetMatrix.rank ≤ 2 := by
    exact (Matrix.rank_mul_le_left sourceV sourceU).trans (Matrix.rank_le_width sourceV)
  refine ⟨hpp,le_antisymm hupp hlow,?_⟩
  intro h
  have he := congrArg (fun M : Square 6 => M 0 1) h
  norm_num [resetMatrix,sourceU,sourceV,Matrix.mul_apply,Fin.sum_univ_succ] at he

theorem actual_parameter_invertible (lam mu : ℝ) (hlam : lam ≠ 0) (hmu : mu ≠ 0) :
    IsUnit (parameterMatrix lam mu) ∧ parameterMatrix lam mu ≠ resetMatrix := by
  let B : Square 6 := !![1,0,0,0,0,0;0,lam⁻¹,-lam⁻¹,0,0,0;0,0,lam⁻¹,0,0,0;
    0,0,0,mu⁻¹,-mu⁻¹,0;0,0,0,0,mu⁻¹,0;0,0,0,0,0,1]
  have hAB : parameterMatrix lam mu*B=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [parameterMatrix,B,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply,hlam,hmu]
  have hBA : B*parameterMatrix lam mu=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [parameterMatrix,B,Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply,hlam,hmu]
  refine ⟨⟨⟨parameterMatrix lam mu,B,hAB,hBA⟩,rfl⟩,?_⟩
  intro h
  have he := congrArg (fun M : Square 6 => M 0 1) h
  norm_num [parameterMatrix,resetMatrix,sourceU,sourceV,Matrix.mul_apply,Fin.sum_univ_succ] at he

#print axioms actual_reset_geometry
#print axioms actual_parameter_invertible
end RootFirstHalfBridges
