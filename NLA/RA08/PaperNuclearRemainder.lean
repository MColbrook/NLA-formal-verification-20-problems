module

public import NLA.RA08.PaperClippingDerivative
public import NLA.RA08.PaperNuclearFrobenius

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix.Norms.Frobenius
namespace NLA.RA08.Paper

/-- Reverse finite-dimensional comparison for the actual Euclidean operator norm. -/
theorem frobeniusNorm_spectral_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : RealMatrix n, frobeniusNorm A ≤ K*spectralNorm A := by
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      RealMatrix n :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.symm.toLinearEquiv.toLinearMap
  obtain ⟨K,hK,hKA⟩ := SemilinearMapClass.bound_of_continuous L L.continuous_of_finiteDimensional
  refine ⟨K,hK.le,?_⟩
  intro A
  have h := hKA (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) A)
  change ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv.symm
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)).toAlgEquiv A)‖ ≤ _ at h
  simpa only [AlgEquiv.symm_apply_apply,frobeniusNorm,spectralNorm] using h

theorem nuclearNorm_spectral_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : RealMatrix n, nuclearNorm A ≤ K*spectralNorm A := by
  obtain ⟨K,hK,hKA⟩ := frobeniusNorm_spectral_bound n
  refine ⟨Real.sqrt n*K,by positivity,?_⟩
  intro A
  calc
    nuclearNorm A ≤ Real.sqrt n*frobeniusNorm A := nuclearNorm_frobenius_bound A
    _ ≤ Real.sqrt n*(K*spectralNorm A) :=
      mul_le_mul_of_nonneg_left (hKA A) (Real.sqrt_nonneg _)
    _ = (Real.sqrt n*K)*spectralNorm A := by ring

theorem clipping_nuclear_quadratic_remainder {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      nuclearNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E) ≤ C*t^2 := by
  obtain ⟨C,hC,hCt⟩ := clipping_quadratic_remainder b hb E hE
  obtain ⟨K,hK,hKA⟩ := nuclearNorm_spectral_bound n
  refine ⟨K*C,by positivity,?_⟩
  intro t
  calc
    _ ≤ K*spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E) := hKA _
    _ ≤ K*(C*t^2) := mul_le_mul_of_nonneg_left (hCt t) hK
    _ = _ := by ring

#print axioms clipping_nuclear_quadratic_remainder
end NLA.RA08.Paper
