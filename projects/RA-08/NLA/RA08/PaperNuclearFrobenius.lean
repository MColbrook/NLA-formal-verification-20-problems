module

public import NLA.RA08.PaperNuclearDefinitions
public import NLA.RA08.PaperAbsoluteFrobenius

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators MatrixOrder
namespace NLA.RA08.Paper

theorem nuclearGram_posSemidef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (A.transpose*A).PosSemidef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self A

theorem real_cfc_trace {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (functionalCalculus f A).trace=∑ i, f (hA.eigenvalues i) := by
  rw [real_cfc_spectral_form A hA f,Matrix.trace_mul_cycle,
    real_unitary_transpose_mul,Matrix.one_mul,Matrix.trace_diagonal]

theorem nuclearNorm_spectral {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A=∑ i, Real.sqrt ((nuclearGram_posSemidef A).isHermitian.eigenvalues i) :=
  real_cfc_trace (A.transpose*A) (nuclearGram_posSemidef A).isHermitian Real.sqrt

theorem nuclearNorm_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ nuclearNorm A := by
  rw [nuclearNorm_spectral]
  exact Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

theorem nuclearNorm_frobenius_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    nuclearNorm A ≤ Real.sqrt n*frobeniusNorm A := by
  let hG := nuclearGram_posSemidef A
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin n => Real.sqrt (hG.isHermitian.eigenvalues i)) (fun _ => (1 : ℝ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hs
  have he : ∑ i : Fin n, (Real.sqrt (hG.isHermitian.eigenvalues i))^2=frobeniusNorm A^2 := by
    simp_rw [Real.sq_sqrt (hG.eigenvalues_nonneg _)]
    have htrace : (A.transpose*A).trace=∑ i, hG.isHermitian.eigenvalues i := by
      simpa using hG.isHermitian.trace_eq_sum_eigenvalues
    rw [← htrace,← frobeniusSquared_trace,frobeniusSquared_norm]
  rw [he,← nuclearNorm_spectral A] at hs
  have hr : (Real.sqrt n*frobeniusNorm A)^2=frobeniusNorm A^2*n := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    ring
  rw [← hr] at hs
  exact (sq_le_sq₀ (nuclearNorm_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (frobeniusNorm_nonneg A))).mp hs

#print axioms nuclearNorm_frobenius_bound
end NLA.RA08.Paper
