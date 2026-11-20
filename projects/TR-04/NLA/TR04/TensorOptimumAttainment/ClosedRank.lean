module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Closedness of true finite matrix rank bounds, using Mathlib openness of actual linear-map rank. -/
public import NLA.TR04.TensorOptimumAttainment.Definitions
public import NLA.TR04.TensorCandidateSelection.Ordered

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorOptimumAttainment
noncomputable section
open scoped Matrix

def matrixOperator {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

theorem continuous_matrixOperator {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ] :
    Continuous (matrixOperator : Matrix ι κ ℝ → (κ → ℝ) →L[ℝ] (ι → ℝ)) := by
  let L : Matrix ι κ ℝ →ₗ[ℝ] ((κ → ℝ) →L[ℝ] (ι → ℝ)) :=
    (LinearMap.toContinuousLinearMap : ((κ → ℝ) →ₗ[ℝ] (ι → ℝ)) ≃ₗ[ℝ] ((κ → ℝ) →L[ℝ] (ι → ℝ))).toLinearMap.comp
      (Matrix.toLin' : Matrix ι κ ℝ ≃ₗ[ℝ] ((κ → ℝ) →ₗ[ℝ] (ι → ℝ))).toLinearMap
  exact L.continuous_of_finiteDimensional

theorem matrixOperator_rank {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ) : (matrixOperator A).toLinearMap.rank=(A.rank : Cardinal) := by
  change Module.rank ℝ (Matrix.toLin' A).range=(A.rank : Cardinal)
  rw [← Module.finrank_eq_rank]
  congr 1


theorem actual_matrix_rank_bound_isClosed {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (r : ℕ) : IsClosed {A : Matrix ι κ ℝ | A.rank ≤ r} := by
  have ho := (isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := κ → ℝ) (F := ι → ℝ) (r+1)).preimage continuous_matrixOperator
  have hs : {A : Matrix ι κ ℝ | A.rank ≤ r} =
      ({A : Matrix ι κ ℝ | ((r+1 : ℕ) : Cardinal) ≤ (matrixOperator A).toLinearMap.rank})ᶜ := by
    ext A
    simp only [Set.mem_ofPred_eq,Set.mem_compl_iff,matrixOperator_rank]
    norm_cast
    omega
  rw [hs]
  exact ho.isClosed_compl

#print axioms actual_matrix_rank_bound_isClosed
end
end Reference.TensorOptimumAttainment
