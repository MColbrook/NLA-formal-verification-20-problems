module

public import NLA.RA02.PaperBestIsometricEmbedding
public import NLA.RA02.PaperGramRoot

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rankTail_isometric_embedding {n N : ℕ}
    (P : Matrix (Fin N) (Fin n) ℂ) (hP : P.conjTranspose*P=1)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) (r : ℕ) :
    NLA.RA02.rankTail (P*A*P.conjTranspose) (hA.mul_mul_conjTranspose_same P).isHermitian r =
      NLA.RA02.rankTail A hA.isHermitian r := by
  obtain ⟨S,hS⟩ := exists_gram_root A hA
  have hg : (P*S*P.conjTranspose).conjTranspose*(P*S*P.conjTranspose)=P*A*P.conjTranspose := by
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = P*S.conjTranspose*(P.conjTranspose*P)*S*P.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = P*(S.conjTranspose*S)*P.conjTranspose := by rw [hP,Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hS]
  have hgs : gramTail S r=NLA.RA02.rankTail A hA.isHermitian r := by
    unfold gramTail
    exact rankTail_congr_matrix hS _ _ r
  have hgc : gramTail (P*S*P.conjTranspose) r=
      NLA.RA02.rankTail (P*A*P.conjTranspose) (hA.mul_mul_conjTranspose_same P).isHermitian r := by
    unfold gramTail
    exact rankTail_congr_matrix hg _ _ r
  calc
    _ = gramTail (P*S*P.conjTranspose) r := hgc.symm
    _ = rectangularBestRankErrorSquared (P*S*P.conjTranspose) r := (rectangularBest_eq_gramTail _ _).symm
    _ = rectangularBestRankErrorSquared S r := rectangularBest_isometric_embedding P hP S r
    _ = gramTail S r := rectangularBest_eq_gramTail S r
    _ = _ := hgs

#print axioms rankTail_isometric_embedding
end NLA.RA02.Paper
