module

/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Jon Bannon, Jireh Loreaux

Adapted from Mathlib's HermitianFunctionalCalculus.cfcAux and the credited
real selected-basis proof in this project, with Codex assistance.
The selected complex eigenbasis is arbitrary, including repeated eigenvalues.
-/
public import NLA.RA09.ComplexDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder ComplexOrder
open Matrix Unitary Topology
namespace NLA.RA09.ComplexPaper

theorem selected_data_psd {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    A.PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (d.eigenvalues i : ℂ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => by simpa using d.nonnegative i)
  rw [d.reconstruct]
  exact hd.mul_mul_conjTranspose_same _

theorem selected_eigenvalue_mem {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (i : Fin n) : d.eigenvalues i ∈ spectrum ℝ A := by
  apply spectrum.of_algebraMap_mem ℂ
  have he : A = (d.unitary : ComplexMatrix n) *
      Matrix.diagonal (fun j => (d.eigenvalues j : ℂ)) * (star d.unitary : ComplexMatrix n) := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using d.reconstruct
  have hs := congrArg (fun X : ComplexMatrix n => spectrum ℂ X) he
  rw [hs, Unitary.spectrum_star_right_conjugate, spectrum_diagonal]
  exact Set.mem_range_self i

def selectedCfcAux {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) :
    C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] ComplexMatrix n where
  toFun g := conjStarAlgAut ℂ _ d.unitary <|
    diagonal (fun i => (g ⟨d.eigenvalues i, selected_eigenvalue_mem d i⟩ : ℂ))
  map_zero' := by simp [Pi.zero_def]
  map_one' := by simp [Pi.one_def]
  map_mul' f g := by
    simp only [ContinuousMap.coe_mul, ← map_mul, diagonal_mul_diagonal, Pi.mul_apply, Complex.ofReal_mul]
  map_add' f g := by
    simp only [ContinuousMap.coe_add, ← map_add, diagonal_add, Pi.add_apply, Complex.ofReal_add]
  commutes' r := by
    simp only [algebraMap_apply, smul_eq_mul, mul_one]
    rw [← mul_one (algebraMap _ _ _), ← coe_mul_star_self d.unitary,
      ← Algebra.left_comm, coe_star, ← mul_assoc, conjStarAlgAut_apply]
    rfl
  map_star' f := by
    simp only [star_trivial, ← map_star, star_eq_conjTranspose, diagonal_conjTranspose,
      Pi.star_def, Complex.star_def, Complex.conj_ofReal]

theorem selected_cfc_eq {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) :
    functionalCalculus f A = spectralCombination d (fun i => f (d.eigenvalues i)) := by
  have hA : IsSelfAdjoint A := (selected_data_psd d).isHermitian
  have hc : Continuous (selectedCfcAux d) := by
    have : FiniteDimensional ℝ C(spectrum ℝ A, ℝ) :=
      FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ (M := ℝ))
        DFunLike.coe_injective
    exact (selectedCfcAux d).toLinearMap.continuous_of_finiteDimensional
  have hid : selectedCfcAux d (.restrict (spectrum ℝ A) (.id ℝ)) = A := by
    change conjStarAlgAut ℂ (ComplexMatrix n) d.unitary
      (diagonal (fun i => (d.eigenvalues i : ℂ))) = A
    simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using d.reconstruct.symm
  have haux := cfcHom_eq_of_continuous_of_map_id hA (selectedCfcAux d) hc hid
  have hf : ContinuousOn f (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  unfold functionalCalculus
  rw [cfc_apply f A hA hf, haux]
  change conjStarAlgAut ℂ (ComplexMatrix n) d.unitary
      (diagonal (fun i => (f (d.eigenvalues i) : ℂ))) = _
  simp only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, spectralCombination]

#print axioms selected_cfc_eq
end NLA.RA09.ComplexPaper
