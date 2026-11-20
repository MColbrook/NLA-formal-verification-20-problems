module

public import NLA.RA02.PaperBestScaling
public import NLA.RA02.PaperGramRoot

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem gram_real_smul {m n : ℕ} (c : ℝ) (S : Matrix (Fin m) (Fin n) ℂ) :
    (c • S).conjTranspose*(c • S)=c^2 • (S.conjTranspose*S) := by
  simp only [Matrix.conjTranspose_smul,star_trivial,Matrix.smul_mul,Matrix.mul_smul,smul_smul,pow_two]

theorem rankTail_real_smul {n : ℕ} (c : ℝ) (hc : 0 ≤ c)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) (r : ℕ) :
    NLA.RA02.rankTail (c • A) (hA.smul hc).isHermitian r =
      c*NLA.RA02.rankTail A hA.isHermitian r := by
  obtain ⟨S,hS⟩ := exists_gram_root A hA
  have hg : ((Real.sqrt c : ℝ) • S).conjTranspose*((Real.sqrt c : ℝ) • S)=c • A := by
    rw [gram_real_smul,hS,Real.sq_sqrt hc]
  have hgs : gramTail S r=NLA.RA02.rankTail A hA.isHermitian r := by
    unfold gramTail
    exact rankTail_congr_matrix hS _ _ r
  have hgc : gramTail ((Real.sqrt c : ℝ) • S) r=
      NLA.RA02.rankTail (c • A) (hA.smul hc).isHermitian r := by
    unfold gramTail
    exact rankTail_congr_matrix hg _ _ r
  calc
    _ = gramTail ((Real.sqrt c : ℝ) • S) r := hgc.symm
    _ = rectangularBestRankErrorSquared ((Real.sqrt c : ℝ) • S) r := (rectangularBest_eq_gramTail _ _).symm
    _ = (Real.sqrt c)^2*rectangularBestRankErrorSquared S r := rectangularBest_real_smul _ S r
    _ = c*gramTail S r := by rw [Real.sq_sqrt hc,rectangularBest_eq_gramTail]
    _ = _ := by rw [hgs]

#print axioms rankTail_real_smul
end NLA.RA02.Paper
