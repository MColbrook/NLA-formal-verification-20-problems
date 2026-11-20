module

public import NLA.PF02.BlockConstruction.Positivity
public import NLA.PF02.PositiveBasis.GramRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix NLA.PF02.Paper Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

theorem block_factor_symmetric (r : ℕ) (p : BlockIndex r) :
    (blockFactor r p).transpose = blockFactor r p := by
  ext a b
  simpa using (block_factor_posSemidef r p).isHermitian.apply a b

theorem block_factors_linearIndependent (r : ℕ) : LinearIndependent ℝ (blockFactor r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hz p
  have hcross (i : Fin 3) (j : Fin r) : c (Sum.inr (Sum.inr (i,j))) = 0 := by
    have h := congrArg (fun X : Matrix (Axis r) (Axis r) ℝ => X (Sum.inl i) (Sum.inr j)) hz
    simpa [Matrix.sum_apply, Matrix.smul_apply, blockFactor, leadingEmbed, trailingEmbed,
      offDiagonalPositive, Fintype.sum_sum_type, Fintype.sum_prod_type, ite_and, eq_comm] using h
  have hlead : ∀ q : SymIndex 3, c (Sum.inl q) = 0 := by
    apply Fintype.linearIndependent_iff.mp (positive_matrices_linearIndependent 3)
    ext a b
    have h := congrArg (fun X : Matrix (Axis r) (Axis r) ℝ => X (Sum.inl a) (Sum.inl b)) hz
    simpa [Matrix.sum_apply, Matrix.smul_apply, blockFactor, leadingEmbed, trailingEmbed,
      offDiagonalPositive, Fintype.sum_sum_type, Fintype.sum_prod_type, hcross] using h
  have htail : ∀ q : SymIndex r, c (Sum.inr (Sum.inl q)) = 0 := by
    apply Fintype.linearIndependent_iff.mp (positive_matrices_linearIndependent r)
    ext a b
    have h := congrArg (fun X : Matrix (Axis r) (Axis r) ℝ => X (Sum.inr a) (Sum.inr b)) hz
    simpa [Matrix.sum_apply, Matrix.smul_apply, blockFactor, leadingEmbed, trailingEmbed,
      offDiagonalPositive, Fintype.sum_sum_type, Fintype.sum_prod_type, hcross] using h
  cases p with
  | inl q => exact hlead q
  | inr p =>
    cases p with
    | inl q => exact htail q
    | inr ij => exact hcross ij.1 ij.2

theorem finite_block_factors_linearIndependent (r : ℕ) :
    LinearIndependent ℝ (finiteBlockFactor r) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hz p
  apply Fintype.linearIndependent_iff.mp (block_factors_linearIndependent r) c _ p
  ext a b
  have h := congrArg (fun X : Matrix (Fin (3+r)) (Fin (3+r)) ℝ =>
    X (finSumFinEquiv a) (finSumFinEquiv b)) hz
  simpa [finiteBlockFactor, Matrix.sum_apply, Matrix.smul_apply] using h

theorem block_index_card (r : ℕ) : Fintype.card (BlockIndex r) = (r+3)*(r+4)/2 := by
  simp only [BlockIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, symmetricIndex_card]
  have he : (r+3)*(r+4) = r*(r+1)+(3*r+6)*2 := by ring
  rw [he, Nat.add_mul_div_right _ _ (by decide)]
  norm_num
  omega

theorem finite_block_gram_rank (r : ℕ) : (finiteBlockGram r).rank = (r+3)*(r+4)/2 := by
  unfold finiteBlockGram
  rw [trace_gram_rank_of_linearIndependent]
  · exact block_index_card r
  · intro p
    ext a b
    simpa using (finite_block_factor_posSemidef r p).isHermitian.apply a b
  · exact finite_block_factors_linearIndependent r

#print axioms block_factor_symmetric
#print axioms block_factors_linearIndependent
#print axioms finite_block_factors_linearIndependent
#print axioms block_index_card
#print axioms finite_block_gram_rank
end Reference.PF02BlockConstruction
