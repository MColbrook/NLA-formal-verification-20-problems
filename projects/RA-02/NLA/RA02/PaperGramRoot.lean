module

public import NLA.RA02.PaperFrobeniusIsometry

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rankTail_congr_matrix {n : ℕ} {A B : NLA.RA02.Square n} (h : A=B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (r : ℕ) :
    NLA.RA02.rankTail A hA r=NLA.RA02.rankTail B hB r := by
  subst B
  rfl

theorem exists_gram_root {n : ℕ} (A : NLA.RA02.Square n) (hA : A.PosSemidef) :
    ∃ S : NLA.RA02.Square n, S.conjTranspose*S=A := by
  obtain ⟨V,hdiag⟩ := exists_ordered_eigenbasis A hA.isHermitian
  let a := NLA.RA02.orderedEigenvalues A hA.isHermitian
  let d : Fin n → ℂ := fun i => (Real.sqrt (a i) : ℂ)
  have ht : (Matrix.diagonal d).conjTranspose=Matrix.diagonal d := by
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,d]
    · simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,hij,Ne.symm hij]
  have hd : Matrix.diagonal d*Matrix.diagonal d=Matrix.diagonal (fun i => (a i : ℂ)) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    change (Real.sqrt (a i) : ℂ)*(Real.sqrt (a i) : ℂ)=(a i : ℂ)
    rw [← Complex.ofReal_mul,← pow_two,Real.sq_sqrt (NLA.RA02.orderedEigenvalues_nonneg A hA i)]
  refine ⟨Matrix.diagonal d*(V : NLA.RA02.Square n).conjTranspose,?_⟩
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,ht]
  calc
    _ = (V : NLA.RA02.Square n)*(Matrix.diagonal d*Matrix.diagonal d)*(V : NLA.RA02.Square n).conjTranspose := by
      simp only [Matrix.mul_assoc]
    _ = (V : NLA.RA02.Square n)*Matrix.diagonal (fun i => (a i : ℂ))*(V : NLA.RA02.Square n).conjTranspose := by rw [hd]
    _ = A := (diagonalization_reconstruct A V a hdiag).symm

#print axioms exists_gram_root
end NLA.RA02.Paper
