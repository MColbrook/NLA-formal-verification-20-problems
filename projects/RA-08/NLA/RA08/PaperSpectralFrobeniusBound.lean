module

public import NLA.RA08.PaperAbsoluteFrobenius
public import Mathlib.Analysis.Normed.Operator.NormedSpace

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.Frobenius
namespace NLA.RA08.Paper

/-- A finite-dimensional norm bound for the actual Euclidean operator norm. -/
theorem spectralNorm_frobenius_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : RealMatrix n, spectralNorm A ≤ K*frobeniusNorm A := by
  let L : RealMatrix n →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.toLinearEquiv.toLinearMap
  obtain ⟨K,hK,hKA⟩ := SemilinearMapClass.bound_of_continuous L L.continuous_of_finiteDimensional
  refine ⟨K,hK.le,?_⟩
  intro A
  change ‖L A‖ ≤ K*‖A‖
  exact hKA A

end NLA.RA08.Paper
