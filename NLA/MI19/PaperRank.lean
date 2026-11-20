module

public import NLA.MI19.PaperDefinitions
public import NLA.MI19.Proof
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

set_option autoImplicit false
open Matrix
noncomputable section
namespace NLA.MI19.Paper

def realGram : Matrix (Fin 2) (Fin 4) ℝ := !![13,0,13,13; 1,1,-2,1]

theorem real_gram_identity : realGram.transpose * realGram = realWitness := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [realGram, realWitness, Matrix.mul_apply, Fin.sum_univ_two]

theorem real_witness_psd : realWitness.PosSemidef := by
  rw [← real_gram_identity, ← conjTranspose_eq_transpose_of_trivial]
  exact Matrix.posSemidef_conjTranspose_mul_self realGram

theorem real_witness_rank : realWitness.rank = 2 := by
  apply le_antisymm
  · rw [← real_gram_identity]
    exact (Matrix.rank_mul_le_left _ _).trans (by simpa using (rank_le_card_width realGram.transpose))
  · let e : Fin 2 → Fin 4 := ![0,1]
    have hd : (realWitness.submatrix e e).det ≠ 0 := by
      norm_num [Matrix.det_fin_two, realWitness, Matrix.submatrix, e]
    have hr := Matrix.rank_of_det_ne_zero hd
    have hs := Matrix.rank_submatrix_le realWitness e e
    rw [hr] at hs
    simpa using hs

theorem complex_witness_bridge : witness = realWitness.map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [witness, realWitness, Matrix.map_apply]

#print axioms real_witness_psd
#print axioms real_witness_rank
#print axioms complex_witness_bridge
end NLA.MI19.Paper
