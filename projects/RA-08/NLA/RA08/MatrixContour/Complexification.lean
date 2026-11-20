module

public import NLA.RA08.MatrixContour.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem complexifyHom_apply {n : ℕ} (A : RealMatrix n) : complexifyHom n A=complexify A := rfl

theorem complexify_hermitian {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    (complexify A).IsHermitian := by
  exact hA.isSelfAdjoint.map (complexifyHom n)

theorem complexify_functionalCalculus {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian)
    (f : ℝ → ℝ) (hf : Continuous f) :
    complexify (functionalCalculus f A)=cfc (R := ℝ) f (complexify A) := by
  have hφ : Continuous (complexifyHom n) :=
    (complexifyHom n).toAlgHom.toLinearMap.continuous_of_finiteDimensional
  exact StarAlgHomClass.map_cfc (S := ℝ) (R := ℝ) (complexifyHom n) f A
    hf.continuousOn hφ hA (complexify_hermitian A hA)

theorem complexVector_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖complexVector x‖=‖x‖ := by
  simp [EuclideanSpace.norm_eq,complexVector]

theorem complexify_action {n : ℕ} (A : RealMatrix n) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A) (complexVector x)=
      complexVector (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x) := by
  ext i
  change (∑ k, (A i k : ℂ)*(x k : ℂ))=((∑ k, A i k*x k : ℝ) : ℂ)
  simp

theorem spectralNorm_le_complexify_norm {n : ℕ} (A : RealMatrix n) :
    spectralNorm A ≤ ‖complexify A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [← complexVector_norm,← complexify_action]
  have h := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (complexify A)).le_opNorm (complexVector x)
  rwa [complexVector_norm] at h

#print axioms complexify_functionalCalculus
#print axioms spectralNorm_le_complexify_norm
end NLA.RA08.Paper.MatrixContour
