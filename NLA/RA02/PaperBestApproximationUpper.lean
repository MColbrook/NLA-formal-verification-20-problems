module

/- Trace/Frobenius invariance adapted from RA-09 ComplexFrobenius.
Copyright (c) 2026 George Stepaniants; Apache 2.0.
Additional paper-specific formalization with Codex assistance. -/
public import NLA.RA02.PaperBestApproximationLower

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

theorem actual_frobenius_trace {n : ℕ} (A : NLA.RA02.Square n) :
    (NLA.RA03.frobeniusSq A : ℂ) = (A.conjTranspose*A).trace := by
  simp only [NLA.RA03.frobeniusSq, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.sum_comm

theorem actual_frobenius_unitary_left {n : ℕ} (A : NLA.RA02.Square n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    NLA.RA03.frobeniusSq ((U : NLA.RA02.Square n)*A) = NLA.RA03.frobeniusSq A := by
  apply Complex.ofReal_injective
  rw [actual_frobenius_trace, actual_frobenius_trace]
  have he : ((U : NLA.RA02.Square n)*A).conjTranspose*((U : NLA.RA02.Square n)*A) =
      A.conjTranspose * ((U : NLA.RA02.Square n).conjTranspose*(U : NLA.RA02.Square n))*A := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hu : (U : NLA.RA02.Square n).conjTranspose * (U : NLA.RA02.Square n) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [he, hu, Matrix.mul_one]

theorem actual_frobenius_unitary_right {n : ℕ} (A : NLA.RA02.Square n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    NLA.RA03.frobeniusSq (A*(U : NLA.RA02.Square n)) = NLA.RA03.frobeniusSq A := by
  apply Complex.ofReal_injective
  rw [actual_frobenius_trace, actual_frobenius_trace]
  have he : (A*(U : NLA.RA02.Square n)).conjTranspose*(A*(U : NLA.RA02.Square n)) =
      (U : NLA.RA02.Square n).conjTranspose*(A.conjTranspose*A)*(U : NLA.RA02.Square n) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hu : (U : NLA.RA02.Square n) * (U : NLA.RA02.Square n).conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  rw [he, Matrix.trace_mul_cycle, hu, Matrix.one_mul]

theorem best_error_attained (r : ℕ) (A : NLA.RA02.Square (r+1)) (hA : A.PosDef) :
    ∃ B : NLA.RA02.Square (r+1), B.rank ≤ r ∧
      NLA.RA03.frobeniusSq (A-B) = NLA.RA03.singularTailSq A r := by
  let h := hA.isHermitian
  let U := h.eigenvectorUnitary
  let j := NLA.RA02.eigenvalueReindex (r+1) (Fin.last r)
  let b : Fin (r+1) → ℂ := fun i => if i = j then 0 else (h.eigenvalues i : ℂ)
  let B : NLA.RA02.Square (r+1) := (U : NLA.RA02.Square (r+1))*Matrix.diagonal b*
    (star U : Matrix.unitaryGroup (Fin (r+1)) ℂ)
  have hrank : (Matrix.diagonal b).rank = r := by
    rw [Matrix.rank_diagonal]
    have hb : ∀ i, b i ≠ 0 ↔ i ≠ j := by
      intro i
      by_cases hi : i = j
      · simp [b,hi]
      · simp [b,hi,Complex.ofReal_ne_zero.mpr (ne_of_gt (hA.eigenvalues_pos i))]
    simp_rw [hb]
    simp
  refine ⟨B, ?_, ?_⟩
  · exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hrank.le)
  · have hspec : A = (U : NLA.RA02.Square (r+1))*Matrix.diagonal (fun i => (h.eigenvalues i : ℂ))*
        (star U : Matrix.unitaryGroup (Fin (r+1)) ℂ) := by
      simpa [U, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Function.comp_def] using h.spectral_theorem
    have hd : (fun i => (h.eigenvalues i : ℂ) - b i) = Pi.single j (h.eigenvalues j : ℂ) := by
      funext i
      by_cases hi : i = j <;> simp [b,Pi.single_apply,hi]
    have he : A-B = (U : NLA.RA02.Square (r+1))*Matrix.diagonal (Pi.single j (h.eigenvalues j : ℂ))*
        (star U : Matrix.unitaryGroup (Fin (r+1)) ℂ) := by
      change A - (U : NLA.RA02.Square (r+1))*Matrix.diagonal b*(star U : Matrix.unitaryGroup (Fin (r+1)) ℂ) = _
      conv_lhs => rw [hspec]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub, hd]
    rw [he, actual_frobenius_unitary_right, actual_frobenius_unitary_left,
      singularTailSq_last, singular_last_sq_eq_eigenvalue_sq r A hA,
      NLA.RA02.orderedEigenvalues_eq_reindexed]
    simp [NLA.RA03.frobeniusSq, Matrix.diagonal_apply, Pi.single_apply, apply_ite, Complex.normSq_ofReal, j, h, pow_two]

#print axioms best_error_attained
end NLA.RA02.Paper
