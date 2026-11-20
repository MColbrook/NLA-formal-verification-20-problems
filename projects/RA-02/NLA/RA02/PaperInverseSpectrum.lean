module

public import NLA.RA02.SpectralTail
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix.Norms.L2Operator
namespace NLA.RA02.Paper

theorem inverse_spectral_norm {n : ℕ} (A : NLA.RA02.Square n) (hA : A.PosDef) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) A⁻¹‖ =
      ‖(fun i : Fin n => ((hA.isHermitian.eigenvalues i : ℂ)⁻¹))‖ := by
  let h := hA.isHermitian
  let U := h.eigenvectorUnitary
  have hu : (U : Matrix (Fin n) (Fin n) ℂ)⁻¹ = (star U : Matrix.unitaryGroup (Fin n) ℂ) :=
    Matrix.inv_eq_right_inv (Unitary.coe_mul_star_self U)
  have hus : ((star U : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)⁻¹ = U := by
    apply Matrix.inv_eq_right_inv
    exact Unitary.coe_star_mul_self U
  have hd : (Matrix.diagonal (fun i : Fin n => (h.eigenvalues i : ℂ)))⁻¹ =
      Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      have hn : (h.eigenvalues i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hA.eigenvalues_pos i))
      simp [hn]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hspec : A = (U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) *
      (star U : Matrix.unitaryGroup (Fin n) ℂ) := by
    simpa [U, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Function.comp_def] using h.spectral_theorem
  have hinv : A⁻¹ = (U : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)⁻¹) *
      (star U : Matrix.unitaryGroup (Fin n) ℂ) := by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hu, hus, hd, ← Matrix.mul_assoc]
  change ‖A⁻¹‖ = _
  rw [hinv, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]

theorem inverse_norm_last_eigenvalue (r : ℕ) (A : NLA.RA02.Square (r+1)) (hA : A.PosDef) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) A⁻¹‖ =
      (NLA.RA02.orderedEigenvalues A hA.isHermitian (Fin.last r))⁻¹ := by
  rw [inverse_spectral_norm A hA]
  let j := NLA.RA02.eigenvalueReindex (r+1) (Fin.last r)
  have hj : hA.isHermitian.eigenvalues j = NLA.RA02.orderedEigenvalues A hA.isHermitian (Fin.last r) :=
    (NLA.RA02.orderedEigenvalues_eq_reindexed A hA.isHermitian (Fin.last r)).symm
  have hpos := NLA.RA02.orderedEigenvalues_pos A hA hA.isHermitian (Fin.last r)
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hpos.le)).mpr
    intro i
    have hi := NLA.RA02.orderedEigenvalues_antitone A hA.isHermitian
      (show (NLA.RA02.eigenvalueReindex (r+1)).symm i ≤ Fin.last r from Fin.le_last _)
    rw [NLA.RA02.orderedEigenvalues_eq_reindexed A hA.isHermitian
      ((NLA.RA02.eigenvalueReindex (r+1)).symm i)] at hi
    simp only [Equiv.apply_symm_apply] at hi
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hA.eigenvalues_pos i)]
    exact inv_anti₀ hpos hi
  · have hh := norm_le_pi_norm (fun i : Fin (r+1) => (hA.isHermitian.eigenvalues i : ℂ)⁻¹) j
    simpa only [norm_inv, Complex.norm_real, Real.norm_eq_abs, hj, abs_of_pos hpos] using hh

#print axioms inverse_norm_last_eigenvalue
end NLA.RA02.Paper
