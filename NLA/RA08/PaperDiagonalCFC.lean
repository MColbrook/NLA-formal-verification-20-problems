module

public import NLA.RA08.PaperAbsoluteIdentities

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix
namespace NLA.RA08.Paper

theorem diagonal_entry_mem_spectrum {n : ℕ} (b : Fin n → ℝ) (i : Fin n) :
    b i ∈ spectrum ℝ (Matrix.diagonal b) := by
  rw [spectrum_diagonal]
  exact ⟨i,rfl⟩

def diagonalEvaluationHom {n : ℕ} (b : Fin n → ℝ) :
    C(spectrum ℝ (Matrix.diagonal b),ℝ) →⋆ₐ[ℝ] RealMatrix n where
  toFun g := Matrix.diagonal (fun i => g ⟨b i,diagonal_entry_mem_spectrum b i⟩)
  map_zero' := by simp
  map_one' := by simp
  map_add' f g := by simp [Matrix.diagonal_add]
  map_mul' f g := by simp [Matrix.diagonal_mul_diagonal]
  commutes' r := by
    simp [Matrix.algebraMap_eq_diagonal]
  map_star' f := by simp [Matrix.star_eq_conjTranspose]

theorem functionalCalculus_diagonal {n : ℕ} (f : ℝ → ℝ) (hf : Continuous f)
    (b : Fin n → ℝ) :
    functionalCalculus f (Matrix.diagonal b)=Matrix.diagonal (fun i => f (b i)) := by
  have hd : IsSelfAdjoint (Matrix.diagonal b) := by
    simp [IsSelfAdjoint,Matrix.star_eq_conjTranspose]
  have hφ : Continuous (diagonalEvaluationHom b) := by
    change Continuous (fun g : C(spectrum ℝ (Matrix.diagonal b),ℝ) =>
      Matrix.diagonal (fun i => g ⟨b i,diagonal_entry_mem_spectrum b i⟩))
    fun_prop
  have hi : diagonalEvaluationHom b (.restrict (spectrum ℝ (Matrix.diagonal b)) (.id ℝ)) =
      Matrix.diagonal b := rfl
  have he := cfcHom_eq_of_continuous_of_map_id hd (diagonalEvaluationHom b) hφ hi
  unfold functionalCalculus
  rw [cfc_apply f (Matrix.diagonal b) hd hf.continuousOn,he]
  rfl

theorem matrixAbsolute_diagonal {n : ℕ} (b : Fin n → ℝ) :
    matrixAbsolute (Matrix.diagonal b)=Matrix.diagonal (fun i => |b i|) :=
  functionalCalculus_diagonal abs continuous_abs b

end NLA.RA08.Paper
