module

public import NLA.PF02.GlobalOrientation.WitnessDefinitions
public import NLA.PF02.GlobalOrientation.ReflectionDeterminant
public import NLA.PF02.BlockConstruction.MinimalRank

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

theorem reflected_positive_posSemidef (p : SymIndex 3) : (reflectedPositive p).PosSemidef := by
  classical
  unfold reflectedPositive
  split_ifs
  · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (positive_matrix_posDef p).posSemidef.conjTranspose_mul_mul_same reflectionDiagonal
  · exact (positive_matrix_posDef p).posSemidef

theorem reflected_positive_eq (p : SymIndex 3) :
    reflectedPositive p = entryReflection (0 : Fin 3) 1 (positiveMatrix p) := by
  classical
  by_cases hp : p = reflectedPair
  · subst p
    unfold reflectedPositive
    rw [if_pos rfl]
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [reflectedPair, reflectionDiagonal, entryReflection, reflectionMask,
        positiveMatrix, weight, symmetricMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.diagonal_apply, Matrix.one_apply, Pi.single_apply, Subtype.ext_iff, Prod.ext_iff]
  · unfold reflectedPositive
    rw [if_neg hp]
    have h01 : positiveMatrix p 0 1 = 0 := by
      have hc := positive_matrix_coordinate p reflectedPair
      rw [if_neg hp] at hc
      simpa [reflectedPair] using hc
    have h10 : positiveMatrix p 1 0 = 0 := by
      rw [← h01]
      exact congrFun (congrFun (positive_matrix_symmetric p) 0) 1
    ext a b
    by_cases h : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
    · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [entryReflection, h01, h10]
    · simp [entryReflection, reflectionMask, h]

theorem reflected_block_factor_eq (r : ℕ) (p : BlockIndex r) :
    reflectedBlockFactor r p = entryReflection (Sum.inl (0 : Fin 3)) (Sum.inl 1) (blockFactor r p) := by
  cases p with
  | inl p =>
    ext a b
    cases a with
    | inl a =>
      cases b with
      | inl b => simpa [reflectedBlockFactor, blockFactor, leadingEmbed, entryReflection, reflectionMask] using
          congrFun (congrFun (reflected_positive_eq p) a) b
      | inr b => simp [reflectedBlockFactor, blockFactor, leadingEmbed, entryReflection]
    | inr a => cases b <;> simp [reflectedBlockFactor, blockFactor, leadingEmbed, entryReflection]
  | inr p =>
    cases p with
    | inl p =>
      ext a b
      cases a <;> cases b <;>
        simp [reflectedBlockFactor, blockFactor, trailingEmbed, entryReflection, reflectionMask]
    | inr ij =>
      ext a b
      cases a <;> cases b <;>
        simp [reflectedBlockFactor, blockFactor, offDiagonalPositive, entryReflection, reflectionMask]
      all_goals (split_ifs <;> simp_all); all_goals omega

theorem reflected_block_factor_posSemidef (r : ℕ) (p : BlockIndex r) :
    (reflectedBlockFactor r p).PosSemidef := by
  cases p with
  | inl p => exact leading_embed_posSemidef _ (reflected_positive_posSemidef p)
  | inr p => exact block_factor_posSemidef r (Sum.inr p)

theorem finite_reflected_block_trace (r : ℕ) (p q : BlockIndex r) :
    trace (finiteReflectedBlockFactor r p * finiteReflectedBlockFactor r q) = finiteBlockGram r p q := by
  have h := entry_reflection_trace (Sum.inl (0 : Fin 3)) (Sum.inl 1) (blockFactor r p) (blockFactor r q)
  rw [← reflected_block_factor_eq r p, ← reflected_block_factor_eq r q] at h
  calc
    trace (finiteReflectedBlockFactor r p * finiteReflectedBlockFactor r q) =
        trace (reflectedBlockFactor r p * reflectedBlockFactor r q) := by
      simp only [finiteReflectedBlockFactor, Matrix.submatrix_mul_equiv,
        Matrix.trace, Matrix.diag, Matrix.submatrix_apply]
      exact finSumFinEquiv.symm.sum_comp (fun a : Axis r =>
        (reflectedBlockFactor r p * reflectedBlockFactor r q) a a)
    _ = finiteBlockGram r p q := h.trans (congrFun (congrFun (finite_block_gram_eq r).symm p) q)

theorem enumerated_reflected_factorization (r : ℕ) :
    NLA.PF02.IsFactorization (enumeratedRealGram r) (enumeratedReflectedFactor r,enumeratedReflectedFactor r) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    exact (reflected_block_factor_posSemidef r _).submatrix _
  · intro i
    exact (reflected_block_factor_posSemidef r _).submatrix _
  · intro i j
    simpa [enumeratedReflectedFactor, enumerated_real_gram_eq] using
      finite_reflected_block_trace r ((Fintype.equivFin (BlockIndex r)).symm i)
        ((Fintype.equivFin (BlockIndex r)).symm j)

#print axioms reflected_positive_posSemidef
#print axioms reflected_positive_eq
#print axioms reflected_block_factor_eq
#print axioms reflected_block_factor_posSemidef
#print axioms finite_reflected_block_trace
#print axioms enumerated_reflected_factorization
end Reference.PF02GlobalOrientation
