module

public import NLA.PF02.PositiveBasis.Definitions
public import NLA.PF02.PaperSymmetricCoordinates

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02PositiveBasis
open Matrix NLA.PF02.Paper
open scoped BigOperators MatrixOrder

theorem positive_matrix_symmetric {n : ℕ} (p : SymIndex n) :
    (positiveMatrix p).transpose = positiveMatrix p := by
  simp [positiveMatrix, Matrix.transpose_add, Matrix.transpose_smul, symmetricMatrix_transpose]

theorem positive_matrix_coordinate {n : ℕ} (p q : SymIndex n) :
    positiveMatrix p q.val.1 q.val.2 =
      2 * (if q.val.1 = q.val.2 then 1 else 0) + weight p * (if p = q then 1 else 0) := by
  simp [positiveMatrix, symmetricMatrix, q.property, Pi.single_apply,
    Matrix.one_apply, Matrix.smul_apply, eq_comm]

theorem positive_matrix_posDef {n : ℕ} (p : SymIndex n) : (positiveMatrix p).PosDef := by
  classical
  let i := p.val.1
  let j := p.val.2
  have hp : i ≤ j := p.property
  have hi : p.val.1.val < n := p.val.1.isLt
  have hj : p.val.2.val < n := p.val.2.isLt
  by_cases h : i = j
  · let v : Fin n → ℝ := Pi.single i 1
    have hv : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
    have he : positiveMatrix p = (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) +
        (2 : ℝ) • Matrix.vecMulVec v (star v) := by
      ext a b
      simp [positiveMatrix, weight, symmetricMatrix, Pi.single_apply, Matrix.vecMulVec,
        Matrix.smul_apply, v, i, j, h, Matrix.one_apply]
      split_ifs <;> simp_all [Subtype.ext_iff, Prod.ext_iff] <;> omega
    rw [he]
    exact (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 2)).add_posSemidef
      (hv.smul (by norm_num : (0 : ℝ) ≤ 2))
  · let v : Fin n → ℝ := Pi.single i 1 + Pi.single j 1
    let d : Fin n → ℝ := fun a => if a = i ∨ a = j then 0 else 1
    have hv : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
    have hd : (Matrix.diagonal d).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (by intro a; dsimp [d]; split_ifs <;> norm_num)
    have he : positiveMatrix p = (1 : Matrix (Fin n) (Fin n) ℝ) +
        Matrix.vecMulVec v (star v) + Matrix.diagonal d := by
      ext a b
      simp only [positiveMatrix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        symmetricMatrix, Pi.single_apply, Matrix.vecMulVec, star_trivial,
        Matrix.diagonal_apply, Matrix.one_apply]
      dsimp [weight, v, d, i, j] at *
      split_ifs <;> simp_all [Pi.single_apply, Subtype.ext_iff, Prod.ext_iff]
      all_goals (try split_ifs) <;> simp_all <;> norm_num <;> omega
    rw [he]
    exact (Matrix.PosDef.one.add_posSemidef hv).add_posSemidef hd

#print axioms positive_matrix_symmetric
#print axioms positive_matrix_coordinate
#print axioms positive_matrix_posDef
end Reference.PF02PositiveBasis
