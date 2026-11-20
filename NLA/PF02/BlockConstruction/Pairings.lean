module

public import NLA.PF02.BlockConstruction.Independent

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix NLA.PF02.Paper Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

theorem finite_block_gram_eq (r : ℕ) : finiteBlockGram r = blockGram r := by
  ext p q
  simp only [finiteBlockGram, traceGram, finiteBlockFactor, blockGram, Matrix.submatrix_mul_equiv,
    Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
  exact finSumFinEquiv.symm.sum_comp (fun a : Axis r =>
    (blockFactor r p * blockFactor r q) a a)

theorem block_gram_leading (r : ℕ) (p q : SymIndex 3) :
    blockGram r (Sum.inl p) (Sum.inl q) = positiveGram 3 p q := by
  simp [blockGram, blockFactor, leadingEmbed, positiveGram, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_sum_type]

theorem block_gram_trailing (r : ℕ) (p q : SymIndex r) :
    blockGram r (Sum.inr (Sum.inl p)) (Sum.inr (Sum.inl q)) = positiveGram r p q := by
  simp [blockGram, blockFactor, trailingEmbed, positiveGram, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_sum_type]

theorem block_gram_zero_cross (r : ℕ) (p : SymIndex 3) (q : SymIndex r) :
    blockGram r (Sum.inl p) (Sum.inr (Sum.inl q)) = 0 := by
  simp [blockGram, blockFactor, leadingEmbed, trailingEmbed, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_sum_type]

theorem finite_block_leading_submatrix (r : ℕ) :
    (finiteBlockGram r).submatrix Sum.inl Sum.inl = positiveGram 3 := by
  ext p q
  rw [Matrix.submatrix_apply, finite_block_gram_eq, block_gram_leading]

theorem finite_block_trailing_submatrix (r : ℕ) :
    (finiteBlockGram r).submatrix (fun p => Sum.inr (Sum.inl p))
      (fun p => Sum.inr (Sum.inl p)) = positiveGram r := by
  ext p q
  rw [Matrix.submatrix_apply, finite_block_gram_eq, block_gram_trailing]

theorem finite_block_leading_rank (r : ℕ) :
    ((finiteBlockGram r).submatrix Sum.inl Sum.inl).rank = 6 := by
  rw [finite_block_leading_submatrix, positive_gram_rank]

theorem finite_block_trailing_rank (r : ℕ) :
    ((finiteBlockGram r).submatrix (fun p => Sum.inr (Sum.inl p))
      (fun p => Sum.inr (Sum.inl p))).rank = r*(r+1)/2 := by
  rw [finite_block_trailing_submatrix, positive_gram_rank]

#print axioms finite_block_gram_eq
#print axioms block_gram_leading
#print axioms block_gram_trailing
#print axioms block_gram_zero_cross
#print axioms finite_block_leading_submatrix
#print axioms finite_block_trailing_submatrix
#print axioms finite_block_leading_rank
#print axioms finite_block_trailing_rank
end Reference.PF02BlockConstruction
