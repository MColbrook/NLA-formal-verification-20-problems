module

public import NLA.TR04.RealSVD.SVD
public import NLA.TR04.RealSVD.RealLower
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.RealSVDPackage

theorem verified_full_svd {r : ℕ} (A : Square r) :
    ∃ U V : Square r, IsOrthogonal U ∧ IsOrthogonal V ∧
      A = U * singularDiagonal A * V.transpose := by
  exact full_svd A

theorem verified_rectangular_right_gram_basis_matrix {m n : ℕ} (A : Rect m n) :
    ∃ v : OrthonormalBasis (Fin n) ℝ (EuclideanVector n),
      RectangularGramBasis A v ∧ IsOrthogonal (basisMatrix v) ∧
      (basisMatrix v).transpose * (A.transpose * A) * basisMatrix v =
        Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2) := by
  exact rectangular_right_gram_basis_matrix A

theorem verified_rectangular_right_gram_diagonal {m n : ℕ} (A : Rect m n) :
    ∃ V : Square n, IsOrthogonal V ∧
      V.transpose * (A.transpose * A) * V =
        Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2) := by
  exact rectangular_right_gram_diagonal A

theorem verified_real_rank_r_frobenius_attainment {m n : ℕ} (A : Rect m n) (r : ℕ) :
    ∃ B : Rect m n, B.rank ≤ r ∧ frobeniusSq (A - B) = singularTailSq A r := by
  exact real_rank_r_frobenius_attainment A r

theorem verified_singularTail_le_lowRankError {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hB : B.rank ≤ r) : singularTailSq A r ≤ frobeniusSq (A-B) := by
  exact singularTail_le_lowRankError A B r hB

theorem verified_real_best_rank_frobenius_attainment {m n : ℕ} (A : Rect m n) (r : ℕ) :
    ∃ B : Rect m n, B.rank ≤ r ∧ frobeniusSq (A-B) = singularTailSq A r ∧
      ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C) := by
  exact real_best_rank_frobenius_attainment A r

#print axioms Reference.RealSVDPackage.verified_full_svd
#print axioms Reference.RealSVDPackage.verified_rectangular_right_gram_basis_matrix
#print axioms Reference.RealSVDPackage.verified_rectangular_right_gram_diagonal
#print axioms Reference.RealSVDPackage.verified_real_rank_r_frobenius_attainment
#print axioms Reference.RealSVDPackage.verified_singularTail_le_lowRankError
#print axioms Reference.RealSVDPackage.verified_real_best_rank_frobenius_attainment
end Reference.RealSVDPackage
