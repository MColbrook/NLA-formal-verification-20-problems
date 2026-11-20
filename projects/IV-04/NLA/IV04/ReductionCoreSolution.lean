module

public import NLA.IV04.PaperIntervalHull
public import NLA.IV04.PaperContinuantIdentity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix Topology
namespace IV04.Paper

theorem verified_rational_box_nonempty {n : ℕ} (B : RationalMatrixBox n) :
    B.realizations.Nonempty := by
  exact rational_box_nonempty B

theorem verified_rational_box_compact {n : ℕ} (B : RationalMatrixBox n) :
    IsCompact B.realizations := by
  exact rational_box_compact B

theorem verified_rational_regular_box_hull_transfer {n : ℕ} (hn : Odd n)
    (B : RationalMatrixBox (n+1))
    (ht : ∀ A ∈ B.realizations, Tridiagonal A)
    (hu : ∀ A ∈ B.realizations, UnitSuperdiagonal A)
    (hd : ∀ A ∈ B.realizations, 0 < A.det) :
    ∃ A ∈ B.realizations, IsGreatest (Matrix.det '' B.realizations) A.det ∧
      IsLeast (firstCoordinateValues B.realizations) (1/A.det) ∧
      (unitedSolutions B.realizations).Nonempty ∧
      Bornology.IsBounded (unitedSolutions B.realizations) := by
  exact rational_regular_box_hull_transfer hn B ht hu hd

theorem verified_penultimate_minor_det {n : ℕ} (A : Mat (n+2)) (ht : Tridiagonal A) :
    (A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove).det=
      A (Fin.last n).castSucc (Fin.last (n+1))*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  exact penultimate_minor_det A ht

theorem verified_tridiagonal_unit_determinant_recurrence {n : ℕ} (A : Mat (n+2))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) :
    A.det=A (Fin.last (n+1)) (Fin.last (n+1))*
        (A.submatrix Fin.castSucc Fin.castSucc).det-
      A (Fin.last (n+1)) (Fin.last n).castSucc*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  exact tridiagonal_unit_determinant_recurrence A ht hu

theorem verified_continuantMatrix_tridiagonal (n : ℕ) (a β : ℕ → ℝ) :
    Tridiagonal (continuantMatrix n a β) := by
  exact continuantMatrix_tridiagonal n a β

theorem verified_continuantMatrix_unit_superdiagonal (n : ℕ) (a β : ℕ → ℝ) :
    UnitSuperdiagonal (continuantMatrix (n+1) a β) := by
  exact continuantMatrix_unit_superdiagonal n a β

theorem verified_continuantMatrix_leading_one (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix (n+1) a β).submatrix Fin.castSucc Fin.castSucc=
      continuantMatrix n a β := by
  exact continuantMatrix_leading_one n a β

theorem verified_continuantMatrix_leading_two (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix (n+2) a β).submatrix
      (fun i : Fin n => i.castSucc.castSucc) (fun i : Fin n => i.castSucc.castSucc)=
      continuantMatrix n a β := by
  exact continuantMatrix_leading_two n a β

theorem verified_continuantMatrix_det (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix n a β).det=continuantValue a β n := by
  exact continuantMatrix_det n a β

theorem verified_companionVector_succ (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β (n+1)=(companion (a n) (β n)).mulVec (companionVector a β n) := by
  exact companionVector_succ n a β

theorem verified_companionVector_first_step (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β (n+1) 0=a n*companionVector a β n 0-β n*companionVector a β n 1 := by
  exact companionVector_first_step n a β

theorem verified_companionVector_second_step (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β (n+1) 1=companionVector a β n 0 := by
  exact companionVector_second_step n a β

theorem verified_companionVector_continuant (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β n 0=continuantValue a β n := by
  exact companionVector_continuant n a β

theorem verified_continuant_determinant_transfer (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix n a β).det=((companionProduct a β n).mulVec ![1,0]) 0 := by
  exact continuant_determinant_transfer n a β

#print axioms IV04.Paper.verified_rational_box_nonempty
#print axioms IV04.Paper.verified_rational_box_compact
#print axioms IV04.Paper.verified_rational_regular_box_hull_transfer
#print axioms IV04.Paper.verified_penultimate_minor_det
#print axioms IV04.Paper.verified_tridiagonal_unit_determinant_recurrence
#print axioms IV04.Paper.verified_continuantMatrix_tridiagonal
#print axioms IV04.Paper.verified_continuantMatrix_unit_superdiagonal
#print axioms IV04.Paper.verified_continuantMatrix_leading_one
#print axioms IV04.Paper.verified_continuantMatrix_leading_two
#print axioms IV04.Paper.verified_continuantMatrix_det
#print axioms IV04.Paper.verified_companionVector_succ
#print axioms IV04.Paper.verified_companionVector_first_step
#print axioms IV04.Paper.verified_companionVector_second_step
#print axioms IV04.Paper.verified_companionVector_continuant
#print axioms IV04.Paper.verified_continuant_determinant_transfer
end IV04.Paper
