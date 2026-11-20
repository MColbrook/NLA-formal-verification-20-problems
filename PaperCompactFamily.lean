module

public import PaperHullEndpoint
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Bounded

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix Topology
namespace IV04.Paper

theorem united_solutions_eq_inverse_image {n : ℕ} (S : Set (Mat (n+1)))
    (hd : ∀ A ∈ S, A.det ≠ 0) :
    unitedSolutions S=(fun A : Mat (n+1) => A⁻¹.mulVec (cornerRhs n)) '' S := by
  ext x
  constructor
  · rintro ⟨A,hA,hx⟩
    refine ⟨A,hA,?_⟩
    dsimp only
    rw [← hx,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (hd A hA)),Matrix.one_mulVec]
  · rintro ⟨A,hA,rfl⟩
    exact ⟨A,hA,inverse_corner_solution A (hd A hA)⟩

theorem united_solutions_compact {n : ℕ} (S : Set (Mat (n+1)))
    (hS : IsCompact S) (hd : ∀ A ∈ S, A.det ≠ 0) :
    IsCompact (unitedSolutions S) := by
  rw [united_solutions_eq_inverse_image S hd]
  apply hS.image_of_continuousOn
  have hinv : ContinuousOn (fun A : Mat (n+1) => A⁻¹) S := by
    intro A hA
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_matrix_inv
    have heq : (Ring.inverse : ℝ → ℝ) = (fun r : ℝ => r⁻¹) := by
      funext r
      exact Ring.inverse_eq_inv r
    rw [heq]
    exact continuousAt_inv₀ (hd A hA)
  intro A hA
  have hf := hinv A hA
  have hc : Continuous (fun B : Mat (n+1) => B.mulVec (cornerRhs n)) :=
    continuous_id.matrix_mulVec continuous_const
  exact hc.continuousAt.comp_continuousWithinAt hf

theorem united_solutions_bounded {n : ℕ} (S : Set (Mat (n+1)))
    (hS : IsCompact S) (hd : ∀ A ∈ S, A.det ≠ 0) :
    Bornology.IsBounded (unitedSolutions S) := (united_solutions_compact S hS hd).isBounded

theorem compact_family_first_endpoint {n : ℕ} (hn : Odd n) (S : Set (Mat (n+1)))
    (hS : IsCompact S) (hne : S.Nonempty)
    (ht : ∀ A ∈ S, Tridiagonal A) (hu : ∀ A ∈ S, UnitSuperdiagonal A)
    (hd : ∀ A ∈ S, 0 < A.det) :
    ∃ A ∈ S, IsGreatest (Matrix.det '' S) A.det ∧
      IsLeast (firstCoordinateValues S) (1/A.det) ∧
      (unitedSolutions S).Nonempty ∧ Bornology.IsBounded (unitedSolutions S) := by
  obtain ⟨A,hA,hmax⟩ := hS.exists_isMaxOn hne continuous_id.matrix_det.continuousOn
  refine ⟨A,hA,⟨⟨A,hA,rfl⟩,?_⟩,?_,united_solutions_nonempty S hne
    (fun B hB => ne_of_gt (hd B hB)),united_solutions_bounded S hS
    (fun B hB => ne_of_gt (hd B hB))⟩
  · rintro z ⟨B,hB,rfl⟩
    exact hmax hB
  · exact first_coordinate_lower_endpoint hn S ht hu hd A.det ⟨A,hA,rfl⟩
      (fun B hB => hmax hB)

#print axioms compact_family_first_endpoint
end IV04.Paper
