module

public import PaperCornerCofactor

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix
namespace IV04.Paper

theorem inverse_corner_solution {n : ℕ} (A : Mat (n+1)) (hd : A.det ≠ 0) :
    A.mulVec (A⁻¹.mulVec (cornerRhs n))=cornerRhs n := by
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hd),
    Matrix.one_mulVec]

theorem first_coordinate_values_reciprocal {n : ℕ} (hn : Odd n)
    (S : Set (Mat (n+1)))
    (ht : ∀ A ∈ S, Tridiagonal A) (hu : ∀ A ∈ S, UnitSuperdiagonal A)
    (hd : ∀ A ∈ S, A.det ≠ 0) :
    firstCoordinateValues S=(fun A : Mat (n+1) => 1/A.det) '' S := by
  ext z
  constructor
  · rintro ⟨x,⟨A,hAS,hx⟩,rfl⟩
    exact ⟨A,hAS,(corner_solution_even_dimension hn A (ht A hAS) (hu A hAS)
      (hd A hAS) x hx).symm⟩
  · rintro ⟨A,hAS,rfl⟩
    refine ⟨A⁻¹.mulVec (cornerRhs n),⟨A,hAS,inverse_corner_solution A (hd A hAS)⟩,?_⟩
    exact corner_solution_even_dimension hn A (ht A hAS) (hu A hAS) (hd A hAS)
      _ (inverse_corner_solution A (hd A hAS))

theorem united_solutions_nonempty {n : ℕ} (S : Set (Mat (n+1)))
    (hS : S.Nonempty) (hd : ∀ A ∈ S, A.det ≠ 0) :
    (unitedSolutions S).Nonempty := by
  obtain ⟨A,hA⟩ := hS
  exact ⟨A⁻¹.mulVec (cornerRhs n),A,hA,inverse_corner_solution A (hd A hA)⟩

theorem first_coordinate_lower_endpoint {n : ℕ} (hn : Odd n) (S : Set (Mat (n+1)))
    (ht : ∀ A ∈ S, Tridiagonal A) (hu : ∀ A ∈ S, UnitSuperdiagonal A)
    (hd : ∀ A ∈ S, 0 < A.det) (d : ℝ)
    (hatt : ∃ A ∈ S, A.det=d) (hmax : ∀ A ∈ S, A.det ≤ d) :
    IsLeast (firstCoordinateValues S) (1/d) := by
  rw [first_coordinate_values_reciprocal hn S ht hu (fun A hA => ne_of_gt (hd A hA))]
  constructor
  · obtain ⟨A,hA,he⟩ := hatt
    exact ⟨A,hA,by dsimp only; rw [he]⟩
  · rintro z ⟨A,hA,rfl⟩
    exact one_div_le_one_div_of_le (hd A hA) (hmax A hA)

theorem reciprocal_threshold_equivalence (d τ : ℝ) (hd : 0 < d) (hτ : 0 < τ) :
    1/d ≤ 1/τ ↔ τ ≤ d := one_div_le_one_div hd hτ

#print axioms first_coordinate_lower_endpoint
end IV04.Paper
