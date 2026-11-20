module

public import NLA.PF02.PositiveBasis.GramRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02PositiveBasis
open Matrix NLA.PF02.Paper
open scoped BigOperators MatrixOrder

theorem positive_matrix_entry_nonneg {n : ℕ} (p : SymIndex n) (i j : Fin n) :
    0 ≤ positiveMatrix p i j := by
  unfold positiveMatrix weight
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    symmetricMatrix, Pi.single_apply]
  split_ifs <;> norm_num

theorem positive_gram_entry_nonneg (n : ℕ) (p q : SymIndex n) :
    0 ≤ positiveGram n p q := by
  unfold positiveGram Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (positive_matrix_entry_nonneg p i j) (positive_matrix_entry_nonneg q j i)

theorem positive_matrix_int_cast {n : ℕ} (p : SymIndex n) :
    (positiveMatrixInt p).map (Int.castRingHom ℝ) = positiveMatrix p := by
  ext i j
  change ((positiveMatrixInt p i j : ℤ) : ℝ) = positiveMatrix p i j
  simp only [positiveMatrixInt, positiveMatrix, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.one_apply, weight, symmetricMatrix, Pi.single_apply]
  split_ifs <;> norm_num

theorem positive_gram_int_cast (n : ℕ) :
    (positiveGramInt n).map (Int.castRingHom ℝ) = positiveGram n := by
  ext p q
  change (Int.castRingHom ℝ) (trace (positiveMatrixInt p * positiveMatrixInt q)) =
    trace (positiveMatrix p * positiveMatrix q)
  simpa only [Matrix.map_mul, positive_matrix_int_cast] using
    AddMonoidHom.map_trace (Int.castRingHom ℝ) (positiveMatrixInt p * positiveMatrixInt q)

theorem positive_gram_int_entry_nonneg (n : ℕ) (p q : SymIndex n) :
    0 ≤ positiveGramInt n p q := by
  have h := positive_gram_entry_nonneg n p q
  have he := congrFun (congrFun (positive_gram_int_cast n) p) q
  change ((positiveGramInt n p q : ℤ) : ℝ) = positiveGram n p q at he
  rw [← he] at h
  exact_mod_cast h

theorem positive_integer_gram_real_rank (n : ℕ) :
    ((positiveGramInt n).map (Int.castRingHom ℝ)).rank = n * (n+1) / 2 := by
  rw [positive_gram_int_cast, positive_gram_rank]

#print axioms positive_matrix_entry_nonneg
#print axioms positive_gram_entry_nonneg
#print axioms positive_matrix_int_cast
#print axioms positive_gram_int_cast
#print axioms positive_gram_int_entry_nonneg
#print axioms positive_integer_gram_real_rank
end Reference.PF02PositiveBasis
