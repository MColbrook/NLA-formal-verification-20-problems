module

public import PaperCompactFamily

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix Topology
namespace IV04.Paper

theorem verified_corner_minor_det {n : ℕ} (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) :
    (A.submatrix Fin.castSucc Fin.succ).det=1 := by
  exact corner_minor_det A ht hu

theorem verified_corner_inverse_entry {n : ℕ} (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) :
    A⁻¹ 0 (Fin.last n)=(-1)^n/A.det := by
  exact corner_inverse_entry A ht hu

theorem verified_corner_solution_signed {n : ℕ} (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) (hd : A.det ≠ 0)
    (x : Fin (n+1) → ℝ) (hx : A.mulVec x=cornerRhs n) :
    x 0=(-1)^(n+1)/A.det := by
  exact corner_solution_signed A ht hu hd x hx

theorem verified_corner_solution_even_dimension {n : ℕ} (hn : Odd n) (A : Mat (n+1))
    (ht : Tridiagonal A) (hu : UnitSuperdiagonal A) (hd : A.det ≠ 0)
    (x : Fin (n+1) → ℝ) (hx : A.mulVec x=cornerRhs n) :
    x 0=1/A.det := by
  exact corner_solution_even_dimension hn A ht hu hd x hx

theorem verified_inverse_corner_solution {n : ℕ} (A : Mat (n+1)) (hd : A.det ≠ 0) :
    A.mulVec (A⁻¹.mulVec (cornerRhs n))=cornerRhs n := by
  exact inverse_corner_solution A hd

theorem verified_first_coordinate_values_reciprocal {n : ℕ} (hn : Odd n)
    (S : Set (Mat (n+1)))
    (ht : ∀ A ∈ S, Tridiagonal A) (hu : ∀ A ∈ S, UnitSuperdiagonal A)
    (hd : ∀ A ∈ S, A.det ≠ 0) :
    firstCoordinateValues S=(fun A : Mat (n+1) => 1/A.det) '' S := by
  exact first_coordinate_values_reciprocal hn S ht hu hd

theorem verified_united_solutions_nonempty {n : ℕ} (S : Set (Mat (n+1)))
    (hS : S.Nonempty) (hd : ∀ A ∈ S, A.det ≠ 0) :
    (unitedSolutions S).Nonempty := by
  exact united_solutions_nonempty S hS hd

theorem verified_first_coordinate_lower_endpoint {n : ℕ} (hn : Odd n) (S : Set (Mat (n+1)))
    (ht : ∀ A ∈ S, Tridiagonal A) (hu : ∀ A ∈ S, UnitSuperdiagonal A)
    (hd : ∀ A ∈ S, 0 < A.det) (d : ℝ)
    (hatt : ∃ A ∈ S, A.det=d) (hmax : ∀ A ∈ S, A.det ≤ d) :
    IsLeast (firstCoordinateValues S) (1/d) := by
  exact first_coordinate_lower_endpoint hn S ht hu hd d hatt hmax

theorem verified_reciprocal_threshold_equivalence (d τ : ℝ) (hd : 0 < d) (hτ : 0 < τ) :
    1/d ≤ 1/τ ↔ τ ≤ d := by
  exact reciprocal_threshold_equivalence d τ hd hτ

theorem verified_united_solutions_eq_inverse_image {n : ℕ} (S : Set (Mat (n+1)))
    (hd : ∀ A ∈ S, A.det ≠ 0) :
    unitedSolutions S=(fun A : Mat (n+1) => A⁻¹.mulVec (cornerRhs n)) '' S := by
  exact united_solutions_eq_inverse_image S hd

theorem verified_united_solutions_compact {n : ℕ} (S : Set (Mat (n+1)))
    (hS : IsCompact S) (hd : ∀ A ∈ S, A.det ≠ 0) :
    IsCompact (unitedSolutions S) := by
  exact united_solutions_compact S hS hd

theorem verified_united_solutions_bounded {n : ℕ} (S : Set (Mat (n+1)))
    (hS : IsCompact S) (hd : ∀ A ∈ S, A.det ≠ 0) :
    Bornology.IsBounded (unitedSolutions S) := by
  exact united_solutions_bounded S hS hd

theorem verified_compact_family_first_endpoint {n : ℕ} (hn : Odd n) (S : Set (Mat (n+1)))
    (hS : IsCompact S) (hne : S.Nonempty)
    (ht : ∀ A ∈ S, Tridiagonal A) (hu : ∀ A ∈ S, UnitSuperdiagonal A)
    (hd : ∀ A ∈ S, 0 < A.det) :
    ∃ A ∈ S, IsGreatest (Matrix.det '' S) A.det ∧
      IsLeast (firstCoordinateValues S) (1/A.det) ∧
      (unitedSolutions S).Nonempty ∧ Bornology.IsBounded (unitedSolutions S) := by
  exact compact_family_first_endpoint hn S hS hne ht hu hd

#print axioms IV04.Paper.verified_corner_minor_det
#print axioms IV04.Paper.verified_corner_inverse_entry
#print axioms IV04.Paper.verified_corner_solution_signed
#print axioms IV04.Paper.verified_corner_solution_even_dimension
#print axioms IV04.Paper.verified_inverse_corner_solution
#print axioms IV04.Paper.verified_first_coordinate_values_reciprocal
#print axioms IV04.Paper.verified_united_solutions_nonempty
#print axioms IV04.Paper.verified_first_coordinate_lower_endpoint
#print axioms IV04.Paper.verified_reciprocal_threshold_equivalence
#print axioms IV04.Paper.verified_united_solutions_eq_inverse_image
#print axioms IV04.Paper.verified_united_solutions_compact
#print axioms IV04.Paper.verified_united_solutions_bounded
#print axioms IV04.Paper.verified_compact_family_first_endpoint
end IV04.Paper
