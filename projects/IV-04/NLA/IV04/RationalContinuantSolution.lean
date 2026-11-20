module

public import NLA.IV04.PaperRationalContinuant
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem verified_rational_penultimate_minor_det {n : ℕ} (A : RatMat (n+2)) (ht : RationalTridiagonal A) :
    (A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove).det=
      A (Fin.last n).castSucc (Fin.last (n+1))*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  exact rational_penultimate_minor_det A ht

theorem verified_rational_tridiagonal_determinant_recurrence {n : ℕ} (A : RatMat (n+2))
    (ht : RationalTridiagonal A) :
    A.det=A (Fin.last (n+1)) (Fin.last (n+1))*
        (A.submatrix Fin.castSucc Fin.castSucc).det-
      A (Fin.last (n+1)) (Fin.last n).castSucc*
      A (Fin.last n).castSucc (Fin.last (n+1))*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  exact rational_tridiagonal_determinant_recurrence A ht

theorem verified_rationalContinuantMatrix_tridiagonal (n : ℕ) (a lower upper : ℕ → ℚ) :
    RationalTridiagonal (rationalContinuantMatrix n a lower upper) := by
  exact rationalContinuantMatrix_tridiagonal n a lower upper

theorem verified_rationalContinuantMatrix_leading_one (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantMatrix (n+1) a lower upper).submatrix Fin.castSucc Fin.castSucc=
      rationalContinuantMatrix n a lower upper := by
  exact rationalContinuantMatrix_leading_one n a lower upper

theorem verified_rationalContinuantMatrix_leading_two (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantMatrix (n+2) a lower upper).submatrix
      (fun i : Fin n => i.castSucc.castSucc) (fun i : Fin n => i.castSucc.castSucc)=
      rationalContinuantMatrix n a lower upper := by
  exact rationalContinuantMatrix_leading_two n a lower upper

theorem verified_rationalContinuantMatrix_det (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantMatrix n a lower upper).det=rationalContinuantValue a lower upper n := by
  exact rationalContinuantMatrix_det n a lower upper

theorem verified_rationalContinuantPair_previous (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantPair a lower upper (n+1)).2=(rationalContinuantPair a lower upper n).1 := by
  exact rationalContinuantPair_previous n a lower upper

theorem verified_rationalContinuantPair_value (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantPair a lower upper n).1=rationalContinuantValue a lower upper n := by
  exact rationalContinuantPair_value n a lower upper

theorem verified_rationalContinuantPair_determinant (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantPair a lower upper n).1=(rationalContinuantMatrix n a lower upper).det := by
  exact rationalContinuantPair_determinant n a lower upper

#print axioms IV04.Paper.Computational.verified_rational_penultimate_minor_det
#print axioms IV04.Paper.Computational.verified_rational_tridiagonal_determinant_recurrence
#print axioms IV04.Paper.Computational.verified_rationalContinuantMatrix_tridiagonal
#print axioms IV04.Paper.Computational.verified_rationalContinuantMatrix_leading_one
#print axioms IV04.Paper.Computational.verified_rationalContinuantMatrix_leading_two
#print axioms IV04.Paper.Computational.verified_rationalContinuantMatrix_det
#print axioms IV04.Paper.Computational.verified_rationalContinuantPair_previous
#print axioms IV04.Paper.Computational.verified_rationalContinuantPair_value
#print axioms IV04.Paper.Computational.verified_rationalContinuantPair_determinant
end IV04.Paper.Computational
