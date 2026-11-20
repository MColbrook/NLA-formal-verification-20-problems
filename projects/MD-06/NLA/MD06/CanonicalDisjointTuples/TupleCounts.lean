module

public import NLA.MD06.CanonicalDisjointTuples.PatternGeometry
public import NLA.MD06.CanonicalDisjointTuples.TupleCardinality
public import NLA.MD06.PatternUnions.UnionBounds
public import NLA.MD06.BadPatternCounts.FirstMoment

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalDisjointTuples
open Reference.MD06SupportedCanonicalCycles Reference.MD06CubicConfiguration
open Reference.MD06PairingCounts Reference.MD06PatternUnions
open Reference.MD06BadPatternCounts Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_tuple_count_product {n q : ℕ} (L : Fin q→ℕ) :
    (∑p : Pairing n,TupleCount L p)*PairingDenominator n (CycleWeight L)=
      Fintype.card (CanonicalTuple (n:=n) Finset.univ L)*Fintype.card (Pairing n) := by
  have h := actual_pattern_family_sum_product (CycleWeight L)
    (fun F : CanonicalTuple (n:=n) Finset.univ L => TupleUnion F)
    (actual_tuple_union_card Finset.univ L)
    (actual_tuple_union_distinct_endpoints Finset.univ L)
    (actual_tuple_union_disjoint_endpoints Finset.univ L)
  rw [←actual_family_matching_sum] at h
  exact h

theorem actual_mean_tuple_exact {q : ℕ} (k : ℕ) (L : Fin q→ℕ) :
    MeanTuple (Size k) L=
      (Fintype.card (CanonicalTuple (n:=Size k) Finset.univ L) : ℝ)/
        (PairingDenominator (Size k) (CycleWeight L) : ℝ) := by
  by_cases hf : Nonempty (CanonicalTuple (n:=Size k) Finset.univ L)
  · obtain ⟨F⟩ := hf
    have hd : (PairingDenominator (Size k) (CycleWeight L) : ℝ)≠0 := by
      have h := actual_disjoint_pattern_denominator_ne_zero k (TupleUnion F)
        (actual_tuple_union_distinct_endpoints Finset.univ L F)
        (actual_tuple_union_disjoint_endpoints Finset.univ L F)
      rw [actual_tuple_union_card Finset.univ L F] at h
      exact_mod_cast h
    have ht : (Fintype.card (Pairing (Size k)) : ℝ)≠0 := by
      exact_mod_cast Fintype.card_ne_zero
    unfold MeanTuple
    rw [←Nat.cast_sum]
    apply (div_eq_div_iff ht hd).mpr
    exact_mod_cast actual_tuple_count_product (n:=Size k) L
  · let : IsEmpty (CanonicalTuple (n:=Size k) Finset.univ L) := not_nonempty_iff.mp hf
    simp [MeanTuple,TupleCount,FamilyMatchingCount]

theorem actual_cycle_symmetry_factor_positive {q : ℕ} (L : Fin q→ℕ)
    (hL : ∀i,0<L i) : 0<CycleSymmetryFactor L := by
  unfold CycleSymmetryFactor
  exact Finset.prod_pos (fun i _ => Nat.mul_pos (by decide) (hL i))

theorem actual_mean_tuple_scaled_formula {q : ℕ} (k : ℕ) (L : Fin q→ℕ)
    (hL : ∀i,0<L i) :
    (CycleSymmetryFactor L : ℝ)*MeanTuple (Size k) L=
      (((Size k).descFactorial (CycleWeight L)*6^(CycleWeight L) : ℕ) : ℝ)/
        (PairingDenominator (Size k) (CycleWeight L) : ℝ) := by
  rw [actual_mean_tuple_exact,←mul_div_assoc]
  congr 1
  have h := actual_canonical_disjoint_tuple_scaled_card (Size k) _ Finset.univ L hL
  simp only [Finset.card_univ,Fintype.card_fin] at h
  exact_mod_cast h

#print axioms actual_tuple_count_product
#print axioms actual_mean_tuple_exact
#print axioms actual_cycle_symmetry_factor_positive
#print axioms actual_mean_tuple_scaled_formula
end Reference.MD06CanonicalDisjointTuples
