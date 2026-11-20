module

public import NLA.RA08.PaperClippingDerivative
public import Mathlib.Analysis.Asymptotics.Defs

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix Topology
namespace NLA.RA08.Paper

theorem threshold_derivative_spectral_bigO {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    (fun t : ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ)
      (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t^2) := by
  obtain ⟨C,hC,hCt⟩ := clipping_quadratic_remainder b hb E hE
  refine Asymptotics.isBigO_iff.mpr ⟨C,Filter.Eventually.of_forall ?_⟩
  intro t
  simpa only [spectralNorm,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t)] using hCt t

/-- Exactly the hypotheses and spectral quadratic remainder of rac-lem:derivative. -/
theorem threshold_derivative {n : ℕ} (b : Fin n → ℝ)
    (_hB : (Matrix.diagonal b).PosSemidef) (hb : ∀ i, b i ≠ 1)
    (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      (Matrix.diagonal b+t • E).PosSemidef →
      spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E) ≤ C*t^2 := by
  obtain ⟨C,hC,hCt⟩ := clipping_quadratic_remainder b hb E hE
  exact ⟨C,hC,fun t _ _ => hCt t⟩

#print axioms threshold_derivative
end NLA.RA08.Paper
