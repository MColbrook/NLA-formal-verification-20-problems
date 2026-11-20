module

public import NLA.PF02.BlockConstruction.Pairings
public import NLA.PF02.PositiveBasis.Integer

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix NLA.PF02.Paper Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

theorem block_factor_int_cast (r : ℕ) (p : BlockIndex r) :
    (blockFactorInt r p).map (Int.castRingHom ℝ) = blockFactor r p := by
  have hc {n : ℕ} (q : SymIndex n) (i j : Fin n) :
      ((positiveMatrixInt q i j : ℤ) : ℝ) = positiveMatrix q i j :=
    congrFun (congrFun (positive_matrix_int_cast q) i) j
  cases p with
  | inl p =>
    ext a b
    cases a <;> cases b <;> simp [blockFactorInt, blockFactor, leadingEmbed, Matrix.map, hc]
  | inr p =>
    cases p with
    | inl p =>
      ext a b
      cases a <;> cases b <;> simp [blockFactorInt, blockFactor, trailingEmbed, Matrix.map, hc]
    | inr ij =>
      ext a b
      simp [blockFactorInt, blockFactor, offDiagonalPositive, Matrix.map]

theorem finite_block_factor_int_cast (r : ℕ) (p : BlockIndex r) :
    (finiteBlockFactorInt r p).map (Int.castRingHom ℝ) = finiteBlockFactor r p := by
  ext i j
  exact congrFun (congrFun (block_factor_int_cast r p) (finSumFinEquiv.symm i))
    (finSumFinEquiv.symm j)

theorem finite_block_gram_int_cast (r : ℕ) :
    (finiteBlockGramInt r).map (Int.castRingHom ℝ) = finiteBlockGram r := by
  ext p q
  change (Int.castRingHom ℝ) (trace (finiteBlockFactorInt r p * finiteBlockFactorInt r q)) =
    trace (finiteBlockFactor r p * finiteBlockFactor r q)
  simpa only [Matrix.map_mul, finite_block_factor_int_cast] using
    AddMonoidHom.map_trace (Int.castRingHom ℝ) (finiteBlockFactorInt r p * finiteBlockFactorInt r q)

theorem block_factor_entry_nonneg (r : ℕ) (p : BlockIndex r) (a b : Axis r) :
    0 ≤ blockFactor r p a b := by
  cases p with
  | inl p =>
    cases a <;> cases b <;> simp [blockFactor, leadingEmbed, positive_matrix_entry_nonneg]
  | inr p =>
    cases p with
    | inl p =>
      cases a <;> cases b <;> simp [blockFactor, trailingEmbed, positive_matrix_entry_nonneg]
    | inr ij =>
      simp only [blockFactor, offDiagonalPositive]
      split_ifs <;> norm_num

theorem finite_block_gram_entry_nonneg (r : ℕ) (p q : BlockIndex r) :
    0 ≤ finiteBlockGram r p q := by
  unfold finiteBlockGram traceGram Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (block_factor_entry_nonneg r p _ _) (block_factor_entry_nonneg r q _ _)

theorem finite_block_integer_entry_nonneg (r : ℕ) (p q : BlockIndex r) :
    0 ≤ finiteBlockGramInt r p q := by
  have h := finite_block_gram_entry_nonneg r p q
  have he := congrFun (congrFun (finite_block_gram_int_cast r) p) q
  change ((finiteBlockGramInt r p q : ℤ) : ℝ) = finiteBlockGram r p q at he
  rw [← he] at h
  exact_mod_cast h

theorem finite_block_integer_real_rank (r : ℕ) :
    ((finiteBlockGramInt r).map (Int.castRingHom ℝ)).rank = (r+3)*(r+4)/2 := by
  rw [finite_block_gram_int_cast, finite_block_gram_rank]

#print axioms block_factor_int_cast
#print axioms finite_block_factor_int_cast
#print axioms finite_block_gram_int_cast
#print axioms block_factor_entry_nonneg
#print axioms finite_block_gram_entry_nonneg
#print axioms finite_block_integer_entry_nonneg
#print axioms finite_block_integer_real_rank
end Reference.PF02BlockConstruction
