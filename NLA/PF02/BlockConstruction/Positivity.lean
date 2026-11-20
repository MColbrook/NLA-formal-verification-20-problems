module

public import NLA.PF02.BlockConstruction.Definitions
public import NLA.PF02.PositiveBasis.Positive

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix NLA.PF02.Paper Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

theorem leading_embed_posSemidef {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ)
    (hH : H.PosSemidef) : (leadingEmbed (r := r) H).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro a b
    cases a with
    | inl a =>
      cases b with
      | inl b => simpa [leadingEmbed] using hH.isHermitian.apply a b
      | inr b => simp [leadingEmbed]
    | inr a => cases b <;> simp [leadingEmbed]
  · intro x
    simpa [leadingEmbed, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using
      hH.dotProduct_mulVec_nonneg (fun i => x (Sum.inl i))

theorem trailing_embed_posSemidef {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ)
    (hH : H.PosSemidef) : (trailingEmbed H).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro a b
    cases a with
    | inl a => cases b <;> simp [trailingEmbed]
    | inr a =>
      cases b with
      | inl b => simp [trailingEmbed]
      | inr b => simpa [trailingEmbed] using hH.isHermitian.apply a b
  · intro x
    simpa [trailingEmbed, dotProduct, Matrix.mulVec, Fintype.sum_sum_type] using
      hH.dotProduct_mulVec_nonneg (fun i => x (Sum.inr i))

theorem off_diagonal_positive_posDef {α : Type*} [Fintype α] [DecidableEq α]
    (i j : α) (hij : i ≠ j) : (offDiagonalPositive i j).PosDef := by
  classical
  let v : α → ℝ := Pi.single i 1 + Pi.single j 1
  let d : α → ℝ := fun a => if a = i ∨ a = j then 0 else 1
  have hv : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have hd : (Matrix.diagonal d).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr
    (by intro a; dsimp [d]; split_ifs <;> norm_num)
  have he : offDiagonalPositive i j = (1 : Matrix α α ℝ) +
      Matrix.vecMulVec v (star v) + Matrix.diagonal d := by
    ext a b
    simp only [offDiagonalPositive, Matrix.add_apply, Matrix.vecMulVec, star_trivial,
      Matrix.diagonal_apply, Matrix.one_apply]
    dsimp [v, d]
    simp only [Pi.single_apply]
    split_ifs <;> simp_all <;> norm_num
  rw [he]
  exact (Matrix.PosDef.one.add_posSemidef hv).add_posSemidef hd

theorem block_factor_posSemidef (r : ℕ) (p : BlockIndex r) : (blockFactor r p).PosSemidef := by
  cases p with
  | inl p => exact leading_embed_posSemidef _ (positive_matrix_posDef p).posSemidef
  | inr p =>
    cases p with
    | inl p => exact trailing_embed_posSemidef _ (positive_matrix_posDef p).posSemidef
    | inr ij => exact (off_diagonal_positive_posDef (Sum.inl ij.1) (Sum.inr ij.2) (by simp)).posSemidef

theorem finite_block_factor_posSemidef (r : ℕ) (p : BlockIndex r) :
    (finiteBlockFactor r p).PosSemidef :=
  (block_factor_posSemidef r p).submatrix _

#print axioms leading_embed_posSemidef
#print axioms trailing_embed_posSemidef
#print axioms off_diagonal_positive_posDef
#print axioms block_factor_posSemidef
#print axioms finite_block_factor_posSemidef
end Reference.PF02BlockConstruction
