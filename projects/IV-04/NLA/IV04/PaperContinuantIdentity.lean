module

public import NLA.IV04.PaperContinuantDefinitions
public import NLA.IV04.PaperContinuant

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace IV04.Paper

theorem continuantMatrix_tridiagonal (n : ℕ) (a β : ℕ → ℝ) :
    Tridiagonal (continuantMatrix n a β) := by
  intro i j h
  have hne : i ≠ j := by intro he; subst j; omega
  have h1 : j.val ≠ i.val+1 := by omega
  have h2 : i.val ≠ j.val+1 := by omega
  simp [continuantMatrix,hne,h1,h2]

theorem continuantMatrix_unit_superdiagonal (n : ℕ) (a β : ℕ → ℝ) :
    UnitSuperdiagonal (continuantMatrix (n+1) a β) := by
  intro i
  simp [continuantMatrix,Fin.ext_iff]

theorem continuantMatrix_leading_one (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix (n+1) a β).submatrix Fin.castSucc Fin.castSucc=
      continuantMatrix n a β := by
  ext i j
  simp [continuantMatrix,Matrix.submatrix_apply]

theorem continuantMatrix_leading_two (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix (n+2) a β).submatrix
      (fun i : Fin n => i.castSucc.castSucc) (fun i : Fin n => i.castSucc.castSucc)=
      continuantMatrix n a β := by
  ext i j
  simp [continuantMatrix,Matrix.submatrix_apply]

theorem continuantMatrix_det (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix n a β).det=continuantValue a β n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [continuantValue]
  | one => simp [Matrix.det_fin_one,continuantMatrix,continuantValue]
  | more n hn hn1 =>
    rw [tridiagonal_unit_determinant_recurrence (continuantMatrix (n+2) a β)
      (continuantMatrix_tridiagonal _ a β) (continuantMatrix_unit_superdiagonal _ a β),
      continuantMatrix_leading_one,continuantMatrix_leading_two,hn,hn1]
    have hdiag : continuantMatrix (n+2) a β (Fin.last (n+1)) (Fin.last (n+1))=a (n+1) := by
      simp [continuantMatrix]
    have hlower : continuantMatrix (n+2) a β (Fin.last (n+1)) (Fin.last n).castSucc=β (n+1) := by
      simp [continuantMatrix,Fin.ext_iff] <;> omega
    rw [hdiag,hlower]
    rfl

theorem companionVector_succ (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β (n+1)=(companion (a n) (β n)).mulVec (companionVector a β n) := by
  simp only [companionVector,companionProduct,Matrix.mulVec_mulVec]

theorem companionVector_first_step (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β (n+1) 0=a n*companionVector a β n 0-β n*companionVector a β n 1 := by
  rw [companionVector_succ]
  simp [companion,Matrix.mulVec,Fin.sum_univ_two,dotProduct]
  ring

theorem companionVector_second_step (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β (n+1) 1=companionVector a β n 0 := by
  rw [companionVector_succ]
  simp [companion,Matrix.mulVec,Fin.sum_univ_two,dotProduct]

theorem companionVector_continuant (n : ℕ) (a β : ℕ → ℝ) :
    companionVector a β n 0=continuantValue a β n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [companionVector,companionProduct,continuantValue]
  | one => simp [companionVector,companionProduct,companion,continuantValue,
      Matrix.mulVec,Fin.sum_univ_two,dotProduct]
  | more n hn hn1 =>
    rw [companionVector_first_step,companionVector_second_step,hn,hn1]
    rfl

theorem continuant_determinant_transfer (n : ℕ) (a β : ℕ → ℝ) :
    (continuantMatrix n a β).det=((companionProduct a β n).mulVec ![1,0]) 0 := by
  rw [continuantMatrix_det,← companionVector_continuant]
  rfl

#print axioms continuant_determinant_transfer
end IV04.Paper
