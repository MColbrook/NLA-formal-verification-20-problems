module

public import PaperCornerCofactor

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace IV04.Paper

theorem penultimate_minor_det {n : ℕ} (A : Mat (n+2)) (ht : Tridiagonal A) :
    (A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove).det=
      A (Fin.last n).castSucc (Fin.last (n+1))*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  let B : Mat (n+1) := A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove
  have hz (i : Fin n) : B i.castSucc (Fin.last n)=0 := by
    simp only [B,Matrix.submatrix_apply,Fin.succAbove_castSucc_self]
    apply ht
    left
    simp only [Fin.val_castSucc,Fin.val_succ,Fin.val_last]
    omega
  have hminor : B.submatrix Fin.castSucc Fin.castSucc=
      A.submatrix (fun i : Fin n => i.castSucc.castSucc)
        (fun i : Fin n => i.castSucc.castSucc) := by
    ext i j
    simp only [B,Matrix.submatrix_apply]
    rw [Fin.succAbove_castSucc_of_lt _ _ (Fin.castSucc_lt_last j)]
  have hlast : B (Fin.last n) (Fin.last n)=A (Fin.last n).castSucc (Fin.last (n+1)) := by
    simp only [B,Matrix.submatrix_apply,Fin.succAbove_castSucc_self]
    rfl
  change B.det=_
  rw [Matrix.det_succ_column B (Fin.last n),Fin.sum_univ_castSucc]
  have hzero : (∑ i : Fin n, (-1:ℝ)^(i.castSucc.val+(Fin.last n).val)*
      B i.castSucc (Fin.last n)*
      (B.submatrix i.castSucc.succAbove (Fin.last n).succAbove).det)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i,mul_zero,zero_mul]
  rw [hzero,zero_add,Fin.succAbove_last,hlast,hminor]
  have hs : (-1:ℝ)^(n+n)=1 := by rw [pow_add,← mul_pow]; norm_num
  simpa only [Fin.val_last,hs,one_mul]

theorem tridiagonal_unit_determinant_recurrence {n : ℕ} (A : Mat (n+2))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) :
    A.det=A (Fin.last (n+1)) (Fin.last (n+1))*
        (A.submatrix Fin.castSucc Fin.castSucc).det-
      A (Fin.last (n+1)) (Fin.last n).castSucc*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  rw [Matrix.det_succ_row A (Fin.last (n+1)),Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc]
  have hz (i : Fin n) : A (Fin.last (n+1)) i.castSucc.castSucc=0 := by
    apply ht
    right
    simp only [Fin.val_last,Fin.val_castSucc]
    omega
  have hzero : (∑ i : Fin n, (-1:ℝ)^((Fin.last (n+1)).val+i.castSucc.castSucc.val)*
      A (Fin.last (n+1)) i.castSucc.castSucc*
      (A.submatrix (Fin.last (n+1)).succAbove i.castSucc.castSucc.succAbove).det)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i,mul_zero,zero_mul]
  rw [hzero,zero_add,Fin.succAbove_last,penultimate_minor_det A ht]
  have hu' : A (Fin.last n).castSucc (Fin.last (n+1))=1 := hu (Fin.last n)
  rw [hu',one_mul]
  have hs0 : (-1:ℝ)^((n+1)+(n+1))=1 := by rw [pow_add,← mul_pow]; norm_num
  have hs1 : (-1:ℝ)^((n+1)+n) = -1 := by
    rw [show n+1+n=n+n+1 by omega,pow_succ,pow_add,← mul_pow]
    norm_num
  simp only [Fin.val_last,Fin.val_castSucc,hs0,hs1,one_mul,neg_one_mul]
  ring

#print axioms tridiagonal_unit_determinant_recurrence
end IV04.Paper
