module

public import NLA.RA08.PaperMinorant
public import NLA.RA08.Functional
public import NLA.RA08.Certificate

@[expose] public section

/- Polynomial functional calculus for the strengthened paper certificate. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped MatrixOrder
open Matrix Polynomial
noncomputable section
namespace NLA.RA08.Paper

def shift {n : ℕ} (A : RealMatrix n) := A - witnessA • (1 : RealMatrix n)

def correctionMatrix {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  minorantCoefficient • 1 + (-20401094656 / 32234193 : ℝ) • shift A +
    (10000 : ℝ) • (shift A)^2

def paperMinorantMatrix {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  A - matrixK A * correctionMatrix A * matrixK A

theorem paperMinorant_cfc {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    functionalCalculus paperMinorant A = paperMinorantMatrix A := by
  let k : ℝ[X] := X * (X - C (1 / 2)) * (X - C witnessB)
  let p : ℝ[X] := X - k * (C minorantCoefficient +
    C (-20401094656 / 32234193) * (X - C witnessA) +
    C 10000 * (X - C witnessA)^2) * k
  have he : p.eval = paperMinorant := by
    ext x
    simp [p, k, paperMinorant, correction, cubicFunction]
    ring
  have h := cfc_polynomial p A hA
  rw [he] at h
  simpa only [p, k, functionalCalculus, paperMinorantMatrix, correctionMatrix,
    shift, matrixK, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using h

theorem paperMinorant_matrix_le :
    paperMinorantMatrix witnessMatrix ≤ functionalCalculus witnessFunction witnessMatrix := by
  rw [← paperMinorant_cfc _ witnessMatrix_psd.isHermitian]
  apply cfc_mono
  · intro x hx
    apply paperMinorant_le
    rcases witness_spectral_location_proved hx with h | h
    · exact Or.inl h.2
    · exact Or.inr h
  · change ContinuousOn paperMinorant (spectrum ℝ witnessMatrix)
    unfold paperMinorant cubicFunction correction
    fun_prop
  · change ContinuousOn witnessFunction (spectrum ℝ witnessMatrix)
    unfold witnessFunction
    fun_prop

def shiftedKVector : Fin 6 → ℝ :=
  ![13718082903404999/2054992509969157324800,
    -8166132956587543/6575976031901303439360,
    409792394115137/1643994007975325859840,
    1503468907/1217773339240982118400,
    140573927593/5845312028356714168320, 0]

theorem shifted_K_product : shift witnessMatrix *ᵥ witnessKVector = shiftedKVector := by
  rw [shift, sub_mulVec, smul_mulVec, one_mulVec, witnessMatrix_mulVec_formula]
  ext i
  fin_cases i <;>
    norm_num [witnessF, witnessT, witnessA, witnessB,
      witnessKVector, shiftedKVector, mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem shift_symmetric : (shift witnessMatrix).transpose = shift witnessMatrix := by
  have h := witnessMatrix_psd.isHermitian
  simp only [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
  simp [shift, h]

theorem correction_quadratic :
    witnessVector ⬝ᵥ ((matrixK witnessMatrix * correctionMatrix witnessMatrix *
      matrixK witnessMatrix) *ᵥ witnessVector) =
    minorantCoefficient * (witnessKVector ⬝ᵥ witnessKVector) +
      (-20401094656 / 32234193 : ℝ) * (witnessKVector ⬝ᵥ shiftedKVector) +
      10000 * (shiftedKVector ⬝ᵥ shiftedKVector) := by
  have hg := real_gram_quadratic (shift witnessMatrix) witnessKVector
  rw [shift_symmetric, ← pow_two, shifted_K_product] at hg
  rw [← mulVec_mulVec, witness_K_product, ← mulVec_mulVec]
  rw [← matrixK_symmetric _ witnessMatrix_psd.isHermitian,
    dotProduct_transpose_mulVec, witness_K_product, dotProduct_comm]
  simp only [correctionMatrix, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, shifted_K_product, hg]

theorem paper_minorant_quadratic :
    26 * witnessT * (1 + (334583 / 15769728 : ℝ)) ≤
      witnessVector ⬝ᵥ ((paperMinorantMatrix witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) *ᵥ witnessVector) := by
  rw [approximation_cfc]
  simp only [paperMinorantMatrix, sub_mulVec, dotProduct_sub, correction_quadratic,
    witness_matrix_vector_quadratic, witness_image_vector_quadratic]
  norm_num [minorantCoefficient, witnessT, witnessKVector, shiftedKVector,
    dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

#print axioms paperMinorant_cfc
#print axioms paperMinorant_matrix_le
#print axioms paper_minorant_quadratic
end NLA.RA08.Paper
