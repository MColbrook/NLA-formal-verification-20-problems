module

public import NLA.RA08.PaperNuclearBlockDefinitions
public import NLA.RA08.PaperNuclearFamily
public import NLA.RA08.PaperNuclearVariational

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearBlockUnitary_unitary {m : ℕ} (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) :
    nuclearBlockUnitary R ∈ Matrix.unitaryGroup (Fin (m+m)) ℝ := by
  let U : Matrix.unitaryGroup (Fin m) ℝ := ⟨R,hR⟩
  have hu : R.transpose*R=1 := real_unitary_transpose_mul U
  have hu' : R*R.transpose=1 := real_unitary_mul_transpose U
  let B : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ := Matrix.fromBlocks 0 R R.transpose 0
  have ht : B.transpose=B := by
    simp only [B,Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_transpose]
  have hBB : B*B=1 := by
    simp only [B,Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,
      zero_add,add_zero,hu,hu']
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold nuclearBlockUnitary
  change (B.submatrix _ _).transpose*B.submatrix _ _=1
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,ht,hBB]
  simp

theorem nuclear_sum_reindex_trace {m : ℕ}
    (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ) :
    (A.submatrix (finSumFinEquiv (m := m) (n := m)).symm
      (finSumFinEquiv (m := m) (n := m)).symm).trace=A.trace := by
  simp only [Matrix.trace,Matrix.diag,Matrix.submatrix_apply]
  exact Equiv.sum_comp (finSumFinEquiv (m := m) (n := m)).symm (fun i => A i i)

theorem nuclear_fromBlocks_trace {m : ℕ} (A B C D : RealMatrix m) :
    (Matrix.fromBlocks A B C D).trace=A.trace+D.trace := by
  simp [Matrix.trace,Matrix.diag,Matrix.fromBlocks,Fintype.sum_sum_type]

theorem nuclearDerivative_isHermitian (m : ℕ) : (nuclearDerivative m).IsHermitian := by
  have ht : (nuclearDerivative m).transpose=nuclearDerivative m := by
    rw [nuclearDerivative_eq_displayed]
    simp only [nuclearDisplayedDerivative,Matrix.transpose_smul,Matrix.transpose_submatrix,
      Matrix.fromBlocks_transpose,Matrix.transpose_transpose,Matrix.transpose_zero]
    rfl
  simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using ht

theorem nuclearDerivative_block_trace (m : ℕ) (hm : 1 ≤ m) (R : RealMatrix m) :
    (nuclearBlockUnitary R*nuclearDerivative m).trace=(R.transpose*nuclearKernel m).trace/m := by
  rw [nuclearDerivative_eq_displayed]
  unfold nuclearBlockUnitary nuclearDisplayedDerivative
  rw [Matrix.mul_smul,Matrix.submatrix_mul_equiv,Matrix.trace_smul,nuclear_sum_reindex_trace,
    Matrix.fromBlocks_multiply,nuclear_fromBlocks_trace]
  simp only [Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,smul_eq_mul]
  have ht : (R*(nuclearKernel m).transpose).trace=(R.transpose*nuclearKernel m).trace := by
    rw [← Matrix.trace_transpose (R*(nuclearKernel m).transpose),Matrix.transpose_mul,
      Matrix.transpose_transpose,Matrix.trace_mul_comm]
  rw [ht]
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp
  ring

theorem nuclearDerivative_trace_lower (m : ℕ) (hm : 1 ≤ m) (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) :
    (R.transpose*nuclearKernel m).trace/m ≤ nuclearNorm (nuclearDerivative m) := by
  have h := unitary_trace_le_nuclear (nuclearBlockUnitary R) (nuclearDerivative m)
    (nuclearBlockUnitary_unitary R hR) (nuclearDerivative_isHermitian m)
  rwa [nuclearDerivative_block_trace m hm R] at h

#print axioms nuclearDerivative_trace_lower
end NLA.RA08.Paper
