module

public import NLA.RA08.PaperNuclearEigenvectors
public import NLA.RA08.PaperNuclearFrobenius

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearDifferenceEigenvalue_pos {m : ℕ} (j : Fin m) :
    0 < nuclearDifferenceEigenvalue j := by
  have hs : 0 < Real.sin (nuclearSineAngle j/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [nuclearSineAngle_pos j])
      (by linarith [nuclearSineAngle_lt_pi j,Real.pi_pos])
  unfold nuclearDifferenceEigenvalue
  positivity

theorem nuclearTriangular_gram_inverse (m : ℕ) :
    ((nuclearDifference m).transpose*nuclearDifference m)*
      ((nuclearTriangular m).transpose*nuclearTriangular m)=1 := by
  have ht : (nuclearDifference m).transpose*nuclearTriangular m=1 := by
    have h := congrArg Matrix.transpose (nuclearDifference_inverse_right m)
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_one] using h
  calc
    _ = (nuclearDifference m).transpose*
        (nuclearDifference m*(nuclearTriangular m).transpose)*nuclearTriangular m := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by rw [nuclearDifference_inverse,Matrix.mul_one,ht]

theorem nuclearTriangular_sine_eigenvector {m : ℕ} (j : Fin m) :
    ((nuclearTriangular m).transpose*nuclearTriangular m) *ᵥ nuclearSineVector j =
      (nuclearDifferenceEigenvalue j)⁻¹ • nuclearSineVector j := by
  have hInv : ((nuclearTriangular m).transpose*nuclearTriangular m)*
      ((nuclearDifference m).transpose*nuclearDifference m)=1 :=
    mul_eq_one_comm.mp (nuclearTriangular_gram_inverse m)
  have h := congrArg (fun x =>
    ((nuclearTriangular m).transpose*nuclearTriangular m) *ᵥ x)
    (nuclearSineVector_eigenvector j)
  rw [Matrix.mulVec_mulVec,hInv,Matrix.one_mulVec,Matrix.mulVec_smul] at h
  have hn := ne_of_gt (nuclearDifferenceEigenvalue_pos j)
  have h' := congrArg (fun x => (nuclearDifferenceEigenvalue j)⁻¹ • x) h
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using h'.symm

theorem paper_matrix_eigenvector_mem_spectrum {n : ℕ} (A : RealMatrix n)
    (v : Fin n → ℝ) (μ : ℝ) (hv : v ≠ 0) (he : A *ᵥ v=μ • v) :
    μ ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff]
  intro hu
  have hz : (algebraMap ℝ (RealMatrix n) μ-A) *ᵥ v=0 := by
    rw [Algebra.algebraMap_eq_smul_one,Matrix.sub_mulVec,Matrix.smul_mulVec,
      Matrix.one_mulVec,he,sub_self]
  obtain ⟨u,hu⟩ := hu
  have h := congrArg (fun x => (↑u⁻¹ : RealMatrix n) *ᵥ x) hz
  rw [Matrix.mulVec_mulVec,← hu,Units.inv_mul,Matrix.one_mulVec,Matrix.mulVec_zero] at h
  exact hv h

theorem nuclearTriangular_spectrum_permutation (m : ℕ) :
    ∃ e : Fin m ≃ Fin m, ∀ j,
      (nuclearGram_posSemidef (nuclearTriangular m)).isHermitian.eigenvalues (e j)=
        (nuclearDifferenceEigenvalue j)⁻¹ := by
  let hG := (nuclearGram_posSemidef (nuclearTriangular m)).isHermitian
  have hs (j : Fin m) : ∃ i, hG.eigenvalues i=(nuclearDifferenceEigenvalue j)⁻¹ := by
    apply Set.mem_range.mp
    rw [← hG.spectrum_real_eq_range_eigenvalues]
    exact paper_matrix_eigenvector_mem_spectrum _ _ _ (nuclearSineVector_ne_zero j)
      (nuclearTriangular_sine_eigenvector j)
  let f : Fin m → Fin m := fun j => Classical.choose (hs j)
  have hf (j : Fin m) : hG.eigenvalues (f j)=(nuclearDifferenceEigenvalue j)⁻¹ :=
    Classical.choose_spec (hs j)
  have hfi : Function.Injective f := by
    intro i j hij
    have he : (nuclearDifferenceEigenvalue i)⁻¹=(nuclearDifferenceEigenvalue j)⁻¹ :=
      (hf i).symm.trans ((congrArg hG.eigenvalues hij).trans (hf j))
    exact nuclearDifferenceEigenvalue_injective m (inv_injective he)
  exact ⟨Equiv.ofBijective f ⟨hfi,Finite.surjective_of_injective hfi⟩,hf⟩

theorem nuclearTriangular_nuclearNorm (m : ℕ) :
    nuclearNorm (nuclearTriangular m)=
      ∑ j : Fin m, 1/(2*Real.sin (nuclearSineAngle j/2)) := by
  obtain ⟨e,he⟩ := nuclearTriangular_spectrum_permutation m
  rw [nuclearNorm_spectral]
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro j _
  rw [he j,Real.sqrt_inv]
  have hs : 0 ≤ 2*Real.sin (nuclearSineAngle j/2) := by
    have hp := Real.sin_pos_of_pos_of_lt_pi
      (by linarith [nuclearSineAngle_pos j] : 0 < nuclearSineAngle j/2)
      (by linarith [nuclearSineAngle_lt_pi j,Real.pi_pos] : nuclearSineAngle j/2 < Real.pi)
    positivity
  rw [show nuclearDifferenceEigenvalue j=(2*Real.sin (nuclearSineAngle j/2))^2 by
    unfold nuclearDifferenceEigenvalue; ring,Real.sqrt_sq hs,one_div]

#print axioms nuclearTriangular_nuclearNorm
end NLA.RA08.Paper
