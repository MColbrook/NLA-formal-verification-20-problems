module

public import NLA.IV04.RationalBoxExtrema.RationalAttainment
public import NLA.IV04.PaperIntervalHull

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators Topology
namespace Reference.IV04RationalBoxExtrema
open Reference.IV04AffinePolyhedronSteps

theorem regular_box_solution_inverse_image {n : ℕ}
    (B : IV04.Paper.RationalMatrixBox n) (b : Fin n → ℚ)
    (hd : ∀ A ∈ B.realizations, A.det ≠ 0) :
    solutions B.lower B.upper b =
      (fun A => A⁻¹ *ᵥ realVector b) '' B.realizations := by
  ext x
  constructor
  · rintro ⟨A,hA,hx⟩
    refine ⟨A,hA,?_⟩
    change A⁻¹ *ᵥ realVector b = x
    change A *ᵥ x = realVector b at hx
    rw [← hx,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (hd A hA)),Matrix.one_mulVec]
  · rintro ⟨A,hA,rfl⟩
    refine ⟨A,hA,?_⟩
    change A *ᵥ (A⁻¹ *ᵥ realVector b) = realVector b
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr (hd A hA)),Matrix.one_mulVec]

theorem regular_box_solution_compact {n : ℕ}
    (B : IV04.Paper.RationalMatrixBox n) (b : Fin n → ℚ)
    (hd : ∀ A ∈ B.realizations, A.det ≠ 0) :
    IsCompact (solutions B.lower B.upper b) := by
  rw [regular_box_solution_inverse_image B b hd]
  apply (IV04.Paper.rational_box_compact B).image_of_continuousOn
  have hinv : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹) B.realizations := by
    intro A hA
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_matrix_inv
    have heq : (Ring.inverse : ℝ → ℝ) = (fun r : ℝ => r⁻¹) := by
      funext r
      exact Ring.inverse_eq_inv r
    rw [heq]
    exact continuousAt_inv₀ (hd A hA)
  intro A hA
  have hc : Continuous (fun C : Matrix (Fin n) (Fin n) ℝ => C *ᵥ realVector b) :=
    continuous_id.matrix_mulVec continuous_const
  exact hc.continuousAt.comp_continuousWithinAt (hinv A hA)

theorem regular_box_rational_coordinate_extrema {n : ℕ}
    (B : IV04.Paper.RationalMatrixBox n) (b : Fin n → ℚ)
    (hd : ∀ A ∈ B.realizations, A.det ≠ 0) (j : Fin n) :
    ∃ qlo qhi : Fin n → ℚ, realVector qlo ∈ solutions B.lower B.upper b ∧
      realVector qhi ∈ solutions B.lower B.upper b ∧
      ∀ x ∈ solutions B.lower B.upper b, (qlo j : ℝ) ≤ x j ∧ x j ≤ (qhi j : ℝ) := by
  have hne : (solutions B.lower B.upper b).Nonempty := by
    rw [regular_box_solution_inverse_image B b hd]
    exact (IV04.Paper.rational_box_nonempty B).image _
  exact compact_solutions_rational_coordinate_extrema B.lower B.upper b B.ordered hne
    (regular_box_solution_compact B b hd) j

#print axioms regular_box_solution_inverse_image
#print axioms regular_box_solution_compact
#print axioms regular_box_rational_coordinate_extrema
end Reference.IV04RationalBoxExtrema
