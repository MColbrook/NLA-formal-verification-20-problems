module

public import NLA.RA08.LiteralContour.NuclearDefinitions
public import NLA.RA08.PaperNuclearBlockTrace
public import NLA.RA08.PaperNuclearPinching
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical Matrix BigOperators

namespace NLA.RA08.Paper.LiteralContour

theorem nuclear_block_sign_unitary (m : ℕ) :
    nuclearBlockSign m ∈ Matrix.unitaryGroup (Fin (m+m)) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [nuclearBlockSign,Matrix.diagonal_transpose,Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    cases h : (finSumFinEquiv (m := m) (n := m)).symm i <;> simp [h]
  · simp [hij]

theorem actual_nuclear_off_diagonal (m : ℕ) :
    (1/2 : ℝ) • (nuclearDerivative m-
      nuclearBlockSign m*nuclearDerivative m*nuclearBlockSign m) = nuclearOffDiagonal m := by
  rw [nuclearDerivative_eq_displayed]
  ext i j
  simp only [nuclearBlockSign,Matrix.diagonal_mul,Matrix.mul_diagonal,
    nuclearDisplayedDerivative,nuclearOffDiagonal,Matrix.smul_apply,smul_eq_mul,
    Matrix.sub_apply,Matrix.submatrix_apply]
  cases hi : (finSumFinEquiv (m := m) (n := m)).symm i <;>
    cases hj : (finSumFinEquiv (m := m) (n := m)).symm j <;>
    simp [Matrix.fromBlocks] <;> ring

theorem actual_nuclear_block_pinching (m : ℕ) :
    nuclearNorm (nuclearOffDiagonal m) ≤ nuclearNorm (nuclearDerivative m) := by
  let S : Matrix.unitaryGroup (Fin (m+m)) ℝ :=
    ⟨nuclearBlockSign m,nuclear_block_sign_unitary m⟩
  have h := nuclearNorm_off_diagonal_pinching (nuclearDerivative m)
    (nuclearDerivative_isHermitian m) S
  change nuclearNorm ((1/2 : ℝ) • (nuclearDerivative m-
    nuclearBlockSign m*nuclearDerivative m*(nuclearBlockSign m).transpose)) ≤ _ at h
  rw [show (nuclearBlockSign m).transpose=nuclearBlockSign m from Matrix.diagonal_transpose _,
    actual_nuclear_off_diagonal] at h
  exact h

#print axioms actual_nuclear_block_pinching

end NLA.RA08.Paper.LiteralContour
