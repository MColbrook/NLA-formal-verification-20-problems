module

public import NLA.RA08.LiteralJoins.Definitions
public import NLA.RA08.LiteralJoins.GramNorm

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper.LiteralJoins

theorem symmetricDilation_hermitian {m : ℕ} (A : RealMatrix m) :
    (symmetricDilation A).IsHermitian := by
  simp [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial,symmetricDilation,
    Matrix.transpose_submatrix,Matrix.fromBlocks_transpose]

theorem blockDiagonal_unitary {m : ℕ} (U V : RealMatrix m)
    (hU : Reference.RealSVDPackage.IsOrthogonal U)
    (hV : Reference.RealSVDPackage.IsOrthogonal V) :
    blockDiagonal U V ∈ Matrix.unitaryGroup (Fin (m+m)) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold blockDiagonal
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero,Matrix.zero_mul,Matrix.mul_zero,zero_add,add_zero,hU.1,hV.1]
  have hh : Matrix.fromBlocks (1 : RealMatrix m) 0 0 (1 : RealMatrix m)=1 := by
    ext i k
    cases i <;> cases k <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  rw [hh]
  simp

theorem repeated_diagonal {m : ℕ} (s : Fin m → ℝ) :
    Matrix.diagonal (repeatedEntries s)=blockDiagonal (Matrix.diagonal s) (Matrix.diagonal s) := by
  unfold blockDiagonal repeatedEntries
  rw [Matrix.fromBlocks_diagonal,Matrix.submatrix_diagonal_equiv]
  rfl

theorem svd_gram_identities {m : ℕ} (A U V : RealMatrix m)
    (hU : Reference.RealSVDPackage.IsOrthogonal U)
    (hV : Reference.RealSVDPackage.IsOrthogonal V)
    (s : Fin m → ℝ) (hA : A=U*Matrix.diagonal s*V.transpose) :
    A.transpose*A=V*Matrix.diagonal (fun i => (s i)^2)*V.transpose ∧
    A*A.transpose=U*Matrix.diagonal (fun i => (s i)^2)*U.transpose := by
  rw [hA]
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.diagonal_transpose]
  constructor
  · calc
      _ = V*Matrix.diagonal s*(U.transpose*U)*Matrix.diagonal s*V.transpose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hU.1,Matrix.mul_one,Matrix.mul_assoc V,Matrix.diagonal_mul_diagonal]
        simp only [pow_two]
  · calc
      _ = U*Matrix.diagonal s*(V.transpose*V)*Matrix.diagonal s*U.transpose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [hV.1,Matrix.mul_one,Matrix.mul_assoc U,Matrix.diagonal_mul_diagonal]
        simp only [pow_two]

theorem symmetricDilation_gram {m : ℕ} (A : RealMatrix m) :
    (symmetricDilation A).transpose*symmetricDilation A =
      blockDiagonal (A*A.transpose) (A.transpose*A) := by
  unfold symmetricDilation blockDiagonal
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]
  simp

theorem blockDiagonal_mul {m : ℕ} (A B C D : RealMatrix m) :
    blockDiagonal A B * blockDiagonal C D=blockDiagonal (A*C) (B*D) := by
  unfold blockDiagonal
  rw [Matrix.submatrix_mul_equiv,Matrix.fromBlocks_multiply]
  simp

theorem blockDiagonal_transpose {m : ℕ} (A B : RealMatrix m) :
    (blockDiagonal A B).transpose=blockDiagonal A.transpose B.transpose := by
  simp [blockDiagonal,Matrix.transpose_submatrix,Matrix.fromBlocks_transpose]

theorem symmetricDilation_nuclearNorm {m : ℕ} (A : RealMatrix m) :
    nuclearNorm (symmetricDilation A)=2*nuclearNorm A := by
  obtain ⟨U,V,hU,hV,hA⟩ := Reference.RealSVDPackage.full_svd A
  let s : Fin m → ℝ := fun i => Reference.RealSVDPackage.singularValue A i.val
  have hs : ∀ i, 0 ≤ s i := fun i => (Reference.RealSVDPackage.singular_values_semantics A).1 i.val
  have hh := svd_gram_identities A U V hU hV s hA
  have hW := blockDiagonal_unitary U V hU hV
  have hrep : ∀ i, 0 ≤ repeatedEntries s i := by
    intro i
    unfold repeatedEntries
    cases (finSumFinEquiv (m := m) (n := m)).symm i <;> apply hs
  have hpow : (fun i => (repeatedEntries s i)^2)=repeatedEntries (fun i => (s i)^2) := by
    funext i
    unfold repeatedEntries
    cases (finSumFinEquiv (m := m) (n := m)).symm i <;> rfl
  have hG : (symmetricDilation A).transpose*symmetricDilation A =
      blockDiagonal U V*Matrix.diagonal (fun i => (repeatedEntries s i)^2)*
      (blockDiagonal U V).transpose := by
    rw [symmetricDilation_gram,hh.1,hh.2,hpow,repeated_diagonal,
      blockDiagonal_transpose,blockDiagonal_mul,blockDiagonal_mul]
  rw [nuclearNorm_of_gram_diagonal _ ⟨blockDiagonal U V,hW⟩ _ hrep hG,
    nuclearNorm_of_svd A U V hU hV s hs hA]
  change (∑ i, Sum.elim s s ((finSumFinEquiv (m := m) (n := m)).symm i))=2*∑ i, s i
  rw [Equiv.sum_comp]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
  ring

#print axioms symmetricDilation_nuclearNorm
end NLA.RA08.Paper.LiteralJoins
