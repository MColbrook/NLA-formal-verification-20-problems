module

public import NLA.RA08.PaperDefinitions
public import NLA.RA08.Witness

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open Matrix
noncomputable section
namespace NLA.RA08.Paper

def paperB : RealMatrix 3 := diagonal ![1/2, witnessB, witnessA]
def paperBInverse : RealMatrix 3 := diagonal ![2,128/127,16/17]
def paperAOmega : Matrix (Fin 6) (Fin 3) ℝ :=
  !![1/2,0,0; 0,witnessB,0; 0,0,witnessA; 0,0,0; 0,0,0; 0,0,0]

theorem paper_sketch_injective : Function.Injective (fun x => paperOmega *ᵥ x) := by
  intro x y h
  ext i
  fin_cases i
  · have hi := congrFun h 0
    simpa [paperOmega, mulVec, dotProduct, Fin.sum_univ_succ] using hi
  · have hi := congrFun h 1
    simpa [paperOmega, mulVec, dotProduct, Fin.sum_univ_succ] using hi
  · have hi := congrFun h 2
    simpa [paperOmega, mulVec, dotProduct, Fin.sum_univ_succ] using hi

theorem paper_F_sketch : witnessF * paperOmega = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessF, paperOmega, Matrix.mul_apply, Fin.sum_univ_succ]

theorem paper_A_sketch : witnessMatrix * paperOmega = paperAOmega := by
  rw [witnessMatrix, Matrix.add_mul, Matrix.smul_mul, paper_F_sketch, smul_zero, add_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessApproximation, paperOmega, paperAOmega, diagonal_mul]

theorem paper_sketch_gram : paperOmega.transpose * witnessMatrix * paperOmega = paperB := by
  rw [Matrix.mul_assoc, paper_A_sketch]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperOmega, paperAOmega, paperB, diagonal, Matrix.mul_apply,
      Fin.sum_univ_succ]

theorem paper_B_left_inverse : paperBInverse * paperB = 1 := by
  rw [paperBInverse, paperB, diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonal, witnessB, witnessA]

theorem paper_gram_invertible : IsUnit (paperOmega.transpose * witnessMatrix * paperOmega).det := by
  rw [paper_sketch_gram]
  exact isUnit_det_of_left_inverse paper_B_left_inverse

theorem paper_nystrom_identity : nystrom witnessMatrix paperOmega = witnessApproximation := by
  have ht : paperOmega.transpose * witnessMatrix = paperAOmega.transpose := by
    have h := congrArg Matrix.transpose paper_A_sketch
    have hs := witnessMatrix_psd.isHermitian
    simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial] at hs
    simpa only [transpose_mul, hs] using h
  rw [nystrom, paper_sketch_gram, inv_eq_left_inv paper_B_left_inverse,
    paper_A_sketch, Matrix.mul_assoc, ht]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperAOmega, paperBInverse, witnessApproximation,
      witnessA, witnessB, Matrix.mul_apply, Fin.sum_univ_succ, diagonal]
    <;> norm_num [Matrix.vecHead, Matrix.vecTail, Fin.ext_iff, Matrix.cons_val_two]

#print axioms paper_sketch_injective
#print axioms paper_gram_invertible
#print axioms paper_nystrom_identity
end NLA.RA08.Paper
