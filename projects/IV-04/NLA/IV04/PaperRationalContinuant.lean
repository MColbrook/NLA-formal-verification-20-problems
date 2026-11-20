module

public import NLA.IV04.PaperRationalContinuantDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Classical Matrix BigOperators
namespace IV04.Paper.Computational

theorem rational_penultimate_minor_det {n : ℕ} (A : RatMat (n+2)) (ht : RationalTridiagonal A) :
    (A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove).det=
      A (Fin.last n).castSucc (Fin.last (n+1))*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  let B : RatMat (n+1) := A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove
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
  have hzero : (∑ i : Fin n, (-1:ℚ)^(i.castSucc.val+(Fin.last n).val)*
      B i.castSucc (Fin.last n)*
      (B.submatrix i.castSucc.succAbove (Fin.last n).succAbove).det)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i,mul_zero,zero_mul]
  rw [hzero,zero_add,Fin.succAbove_last,hlast,hminor]
  have hs : (-1:ℚ)^(n+n)=1 := by rw [pow_add,← mul_pow]; norm_num
  simpa only [Fin.val_last,hs,one_mul]

theorem rational_tridiagonal_determinant_recurrence {n : ℕ} (A : RatMat (n+2))
    (ht : RationalTridiagonal A) :
    A.det=A (Fin.last (n+1)) (Fin.last (n+1))*
        (A.submatrix Fin.castSucc Fin.castSucc).det-
      A (Fin.last (n+1)) (Fin.last n).castSucc*
      A (Fin.last n).castSucc (Fin.last (n+1))*
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  rw [Matrix.det_succ_row A (Fin.last (n+1)),Fin.sum_univ_castSucc,
    Fin.sum_univ_castSucc]
  have hz (i : Fin n) : A (Fin.last (n+1)) i.castSucc.castSucc=0 := by
    apply ht
    right
    simp only [Fin.val_last,Fin.val_castSucc]
    omega
  have hzero : (∑ i : Fin n, (-1:ℚ)^((Fin.last (n+1)).val+i.castSucc.castSucc.val)*
      A (Fin.last (n+1)) i.castSucc.castSucc*
      (A.submatrix (Fin.last (n+1)).succAbove i.castSucc.castSucc.succAbove).det)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hz i,mul_zero,zero_mul]
  rw [hzero,zero_add,Fin.succAbove_last,rational_penultimate_minor_det A ht]
  have hs0 : (-1:ℚ)^((n+1)+(n+1))=1 := by rw [pow_add,← mul_pow]; norm_num
  have hs1 : (-1:ℚ)^((n+1)+n) = -1 := by
    rw [show n+1+n=n+n+1 by omega,pow_succ,pow_add,← mul_pow]
    norm_num
  simp only [Fin.val_last,Fin.val_castSucc,hs0,hs1,one_mul,neg_one_mul]
  ring


theorem rationalContinuantMatrix_tridiagonal (n : ℕ) (a lower upper : ℕ → ℚ) :
    RationalTridiagonal (rationalContinuantMatrix n a lower upper) := by
  intro i j h
  have hne : i ≠ j := by intro he; subst j; omega
  have h1 : j.val ≠ i.val+1 := by omega
  have h2 : i.val ≠ j.val+1 := by omega
  simp [rationalContinuantMatrix,hne,h1,h2]

theorem rationalContinuantMatrix_leading_one (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantMatrix (n+1) a lower upper).submatrix Fin.castSucc Fin.castSucc=
      rationalContinuantMatrix n a lower upper := by
  ext i j
  simp [rationalContinuantMatrix,Matrix.submatrix_apply]

theorem rationalContinuantMatrix_leading_two (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantMatrix (n+2) a lower upper).submatrix
      (fun i : Fin n => i.castSucc.castSucc) (fun i : Fin n => i.castSucc.castSucc)=
      rationalContinuantMatrix n a lower upper := by
  ext i j
  simp [rationalContinuantMatrix,Matrix.submatrix_apply]

theorem rationalContinuantMatrix_det (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantMatrix n a lower upper).det=rationalContinuantValue a lower upper n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [rationalContinuantValue]
  | one => simp [Matrix.det_fin_one,rationalContinuantMatrix,rationalContinuantValue]
  | more n hn hn1 =>
    rw [rational_tridiagonal_determinant_recurrence (rationalContinuantMatrix (n+2) a lower upper)
      (rationalContinuantMatrix_tridiagonal _ a lower upper),
      rationalContinuantMatrix_leading_one,rationalContinuantMatrix_leading_two,hn,hn1]
    have hdiag : rationalContinuantMatrix (n+2) a lower upper (Fin.last (n+1)) (Fin.last (n+1))=a (n+1) := by
      simp [rationalContinuantMatrix]
    have hlower : rationalContinuantMatrix (n+2) a lower upper (Fin.last (n+1)) (Fin.last n).castSucc=lower (n+1) := by
      simp [rationalContinuantMatrix,Fin.ext_iff] <;> omega
    have hupper : rationalContinuantMatrix (n+2) a lower upper (Fin.last n).castSucc (Fin.last (n+1))=upper n := by
      simp [rationalContinuantMatrix,Fin.ext_iff] <;> omega
    rw [hdiag,hlower,hupper]
    rfl

theorem rationalContinuantPair_previous (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantPair a lower upper (n+1)).2=(rationalContinuantPair a lower upper n).1 := by
  rfl

theorem rationalContinuantPair_value (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantPair a lower upper n).1=rationalContinuantValue a lower upper n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [rationalContinuantPair,rationalContinuantValue]
  | more n hn hn1 =>
    change a (n+1)*(rationalContinuantPair a lower upper (n+1)).1-
      lower (n+1)*upper ((n+1)-1)*(rationalContinuantPair a lower upper (n+1)).2=_
    rw [rationalContinuantPair_previous,hn,hn1]
    simp [rationalContinuantValue]

theorem rationalContinuantPair_determinant (n : ℕ) (a lower upper : ℕ → ℚ) :
    (rationalContinuantPair a lower upper n).1=(rationalContinuantMatrix n a lower upper).det := by
  rw [rationalContinuantPair_value,rationalContinuantMatrix_det]

#print axioms rationalContinuantPair_determinant
end IV04.Paper.Computational
