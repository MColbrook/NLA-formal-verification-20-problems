module

public import NLA.IV04.PaperIntervalDefinitions
public import PaperCompactFamily

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix Topology
namespace IV04.Paper

theorem rational_box_nonempty {n : ℕ} (B : RationalMatrixBox n) :
    B.realizations.Nonempty := by
  refine ⟨fun i j => (B.lower i j : ℝ),?_⟩
  intro i j
  constructor
  · exact le_rfl
  · change (B.lower i j : ℝ) ≤ (B.upper i j : ℝ)
    exact_mod_cast B.ordered i j

theorem rational_box_compact {n : ℕ} (B : RationalMatrixBox n) :
    IsCompact B.realizations := by
  change IsCompact {A : Mat n | ∀ i, A i ∈
    {x : Fin n → ℝ | ∀ j, x j ∈ Set.Icc (B.lower i j : ℝ) (B.upper i j : ℝ)}}
  exact isCompact_pi_infinite (fun i : Fin n =>
    isCompact_pi_infinite (fun j : Fin n =>
      (isCompact_Icc : IsCompact (Set.Icc (B.lower i j : ℝ) (B.upper i j : ℝ)))))

theorem rational_regular_box_hull_transfer {n : ℕ} (hn : Odd n)
    (B : RationalMatrixBox (n+1))
    (ht : ∀ A ∈ B.realizations, Tridiagonal A)
    (hu : ∀ A ∈ B.realizations, UnitSuperdiagonal A)
    (hd : ∀ A ∈ B.realizations, 0 < A.det) :
    ∃ A ∈ B.realizations, IsGreatest (Matrix.det '' B.realizations) A.det ∧
      IsLeast (firstCoordinateValues B.realizations) (1/A.det) ∧
      (unitedSolutions B.realizations).Nonempty ∧
      Bornology.IsBounded (unitedSolutions B.realizations) := by
  exact compact_family_first_endpoint hn B.realizations (rational_box_compact B)
    (rational_box_nonempty B) ht hu hd

#print axioms rational_regular_box_hull_transfer
end IV04.Paper
