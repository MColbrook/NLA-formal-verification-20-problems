module

public import NLA.RA08.PaperNuclearTriangularDefinitions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearShift_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (i : Fin m) (j : Fin n) :
    (nuclearShift m*A) i j =
      if hi : 0 < i.val then A ⟨i.val-1,by omega⟩ j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : 0 < i.val
  · rw [dif_pos hi]
    let k : Fin m := ⟨i.val-1,by omega⟩
    rw [Finset.sum_eq_single k]
    · have hk : i.val=k.val+1 := by dsimp [k]; omega
      simp only [nuclearShift,if_pos hk,one_mul]
      rfl
    · intro b _ hbk
      have hb : i.val ≠ b.val+1 := by
        intro hb
        apply hbk
        apply Fin.ext
        dsimp [k]
        omega
      simp [nuclearShift,hb]
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro b _
    have hb : i.val ≠ b.val+1 := by omega
    simp [nuclearShift,hb]

theorem nuclearDifference_inverse (m : ℕ) :
    nuclearDifference m*(nuclearTriangular m).transpose=1 := by
  ext i j
  simp only [nuclearDifference,Matrix.sub_mul,Matrix.one_mul,Matrix.sub_apply]
  rw [nuclearShift_mul]
  by_cases hi : 0 < i.val
  · rw [dif_pos hi]
    simp only [nuclearTriangular,Matrix.transpose_apply,Matrix.one_apply,Fin.le_def]
    split_ifs <;> first | omega | ring
  · rw [dif_neg hi]
    simp only [nuclearTriangular,Matrix.transpose_apply,Matrix.one_apply,Fin.le_def]
    split_ifs <;> first | omega | ring

theorem nuclearDifference_inverse_right (m : ℕ) :
    (nuclearTriangular m).transpose*nuclearDifference m=1 :=
  (mul_eq_one_comm).mp (nuclearDifference_inverse m)

theorem nuclearShift_gram (m : ℕ) :
    (nuclearShift m).transpose*nuclearShift m =
      Matrix.diagonal (fun i : Fin m => if i.val+1<m then (1 : ℝ) else 0) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i.val+1<m
  · let k : Fin m := ⟨i.val+1,hi⟩
    rw [Finset.sum_eq_single k]
    · by_cases hij : i=j
      · subst j
        simp [nuclearShift,Matrix.diagonal_apply,hi,k]
      · have hj : k.val ≠ j.val+1 := by
          intro hj
          apply hij
          apply Fin.ext
          dsimp [k] at hj
          omega
        have hijval : i.val ≠ j.val := fun h => hij (Fin.ext h)
        simp [nuclearShift,Matrix.diagonal_apply,hij,hijval,hj,k]
    · intro b _ hbk
      have hb : b.val ≠ i.val+1 := by
        intro hb
        apply hbk
        apply Fin.ext
        exact hb
      simp [nuclearShift,Matrix.transpose_apply,hb]
    · simp
  · have hs : ∑ k : Fin m, (nuclearShift m).transpose i k*nuclearShift m k j=0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk : k.val ≠ i.val+1 := by omega
      simp [nuclearShift,Matrix.transpose_apply,hk]
    rw [hs]
    by_cases hij : i=j
    · subst j; simp [hi]
    · simp [Matrix.diagonal_apply,hij]

theorem nuclearDifference_gram (m : ℕ) :
    (nuclearDifference m).transpose*nuclearDifference m =
      1-nuclearShift m-(nuclearShift m).transpose+
        Matrix.diagonal (fun i : Fin m => if i.val+1<m then (1 : ℝ) else 0) := by
  rw [nuclearDifference,Matrix.transpose_sub,Matrix.transpose_one,
    Matrix.sub_mul,Matrix.mul_sub,Matrix.mul_sub,Matrix.one_mul,
    Matrix.one_mul,Matrix.mul_one,nuclearShift_gram]
  abel

#print axioms nuclearDifference_gram
end NLA.RA08.Paper
