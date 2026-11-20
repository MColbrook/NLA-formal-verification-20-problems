module

public import NLA.TR04.RealSVD.ColumnFrame
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.RealColumnCompression
open Reference.RealSVDPackage

theorem verified_orthonormal_column_error_decomposition {m k n : ℕ}
    (U : Rect m k) (hU : U.transpose * U = 1) (A : Rect m n) (C : Rect k n) :
    frobeniusSq (A - U * C) = frobeniusSq (A - U * U.transpose * A) +
      frobeniusSq (U.transpose * A - C) := by
  exact orthonormal_column_error_decomposition U hU A C

theorem verified_singularTailSq_transpose {m n : ℕ} (A : Rect m n) (r : ℕ) :
    singularTailSq A.transpose r = singularTailSq A r := by
  exact singularTailSq_transpose A r

theorem verified_exists_exact_column_projection {m n : ℕ} (A : Rect m n) (r : ℕ) :
    ∃ U : Rect m (min r m), U.transpose * U = 1 ∧
      (U * U.transpose * A).rank ≤ r ∧
      frobeniusSq (A - U * U.transpose * A) = singularTailSq A r := by
  exact exists_exact_column_projection A r

#print axioms Reference.RealColumnCompression.verified_orthonormal_column_error_decomposition
#print axioms Reference.RealColumnCompression.verified_singularTailSq_transpose
#print axioms Reference.RealColumnCompression.verified_exists_exact_column_projection
end Reference.RealColumnCompression
