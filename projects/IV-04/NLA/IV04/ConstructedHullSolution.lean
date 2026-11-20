module

public import NLA.IV04.PaperConstructedHull
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators Topology
namespace IV04.Paper

theorem verified_even_regular_box_hull {n : ℕ} (hn : 0 < n) (he : Even n)
    (B : RationalMatrixBox n)
    (ht : ∀ A ∈ B.realizations, Tridiagonal A)
    (hu : ∀ A ∈ B.realizations, ∀ i j, j.val=i.val+1 → A i j=1)
    (hd : ∀ A ∈ B.realizations, 0 < A.det) :
    ∃ A ∈ B.realizations, IsGreatest (Matrix.det '' B.realizations) A.det ∧
      IsLeast (positiveFirstCoordinates n hn B.realizations) (1/A.det) ∧
      (positiveSolutions n hn B.realizations).Nonempty ∧
      Bornology.IsBounded (positiveSolutions n hn B.realizations) := by
  exact even_regular_box_hull hn he B ht hu hd

namespace IntegerPartition
theorem verified_constructed_hull_endpoint (P : IntegerPartition) :
    ∃ A ∈ P.intervalBox.realizations, IsGreatest (Matrix.det '' P.intervalBox.realizations) A.det ∧
      IsLeast P.constructedFirstCoordinates (1/A.det) ∧
      P.constructedSolutions.Nonempty ∧ Bornology.IsBounded P.constructedSolutions := by
  exact constructed_hull_endpoint P
end IntegerPartition


namespace IntegerPartition
theorem verified_constructed_hull_partition_threshold (P : IntegerPartition) :
    ∃ A ∈ P.intervalBox.realizations, IsLeast P.constructedFirstCoordinates (1/A.det) ∧
      (P.HasPartition ↔ 1/A.det ≤ 1/(P.threshold : ℝ)) ∧
      P.constructedSolutions.Nonempty ∧ Bornology.IsBounded P.constructedSolutions := by
  exact constructed_hull_partition_threshold P
end IntegerPartition


#print axioms IV04.Paper.verified_even_regular_box_hull
#print axioms IV04.Paper.IntegerPartition.verified_constructed_hull_endpoint
#print axioms IV04.Paper.IntegerPartition.verified_constructed_hull_partition_threshold
end IV04.Paper
