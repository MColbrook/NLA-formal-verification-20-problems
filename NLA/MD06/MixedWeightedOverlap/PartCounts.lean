module

public import NLA.MD06.MixedWeightedOverlap.Definitions
public import NLA.MD06.MixedPatternShapes.VertexCounts
public import NLA.MD06.MixedPatternShapes.MarkedCycleProperties
public import NLA.MD06.PatternUnions.UnionBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedWeightedOverlap
open Reference.MD06MixedPatternShapes Reference.MD06JointSupportCounts
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open Reference.MD06CanonicalCycleOverlap Reference.MD06BadJointMoments
open Reference.MD06PatternUnions Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_mixed_part_card_bound (n q ell v e : ℕ) :
    Fintype.card (PartDatum n q ell v e)≤n^v*(3*v+18*v^2+2^(9*v^2))^q := by
  let f : PartDatum n q ell v e→
      {F : MarkedTuple n q ell // (VertexSupport (MarkedUnion F)).card=v} :=
    fun F => ⟨F.val,F.property.1⟩
  have hf : Function.Injective f := by
    intro F G h
    apply Subtype.ext
    exact congrArg (fun z : {F : MarkedTuple n q ell //
      (VertexSupport (MarkedUnion F)).card=v} => z.val) h
  exact (Fintype.card_le_of_injective f hf).trans
    (actual_marked_given_vertex_power_bound n q ell v)

theorem actual_mixed_part_shape_bounds {n q ell v e : ℕ} (F : PartDatum n q ell v e) :
    v+1≤e∧e≤q*(max 2 ell) := by
  obtain ⟨p,hp⟩ := F.property.2.2.2
  obtain ⟨i,j,hne,hov⟩ := F.property.2.2.1
  have h := actual_mixed_marked_overlap_bounded_excess F.val p hp i j hne hov
  simpa only [F.property.1,F.property.2.1] using h

theorem actual_mixed_union_distinct_endpoints {n q ell : ℕ} (F : MarkedTuple n q ell) :
    ∀x∈MarkedUnion F,x.1≠x.2 := by
  rw [actual_marked_union_as_cycle_family]
  exact actual_family_cycle_distinct_endpoints
    (fun i => MarkedLength (F i)) (fun i => MarkedCycle (F i))

theorem actual_mixed_part_disjoint_endpoints {n q ell v e : ℕ} (F : PartDatum n q ell v e) :
    ∀x∈MarkedUnion F.val,∀y∈MarkedUnion F.val,x≠y→
      Disjoint ({x.1,x.2} : Finset (Dart n)) {y.1,y.2} := by
  obtain ⟨p,hp⟩ := F.property.2.2.2
  apply actual_ordered_matching_constraints_disjoint (MarkedUnion F.val) p _ hp
  rw [actual_marked_union_as_cycle_family]
  exact actual_family_cycle_ordered
    (fun i => MarkedLength (F.val i)) (fun i => MarkedCycle (F.val i))

theorem actual_mixed_part_count_product (n q ell v e : ℕ) :
    PartCount n q ell v e*PairingDenominator n e=
      Fintype.card (PartDatum n q ell v e)*Fintype.card (Pairing n) := by
  exact actual_pattern_family_sum_product e
    (fun F : PartDatum n q ell v e => MarkedUnion F.val)
    (fun F => F.property.2.1)
    (fun F => actual_mixed_union_distinct_endpoints F.val)
    actual_mixed_part_disjoint_endpoints

theorem actual_mixed_part_mean_nonnegative (n q ell v e : ℕ) :
    0≤PartMean n q ell v e := by
  unfold PartMean
  positivity

theorem actual_mixed_part_mean_exact (k q ell v e : ℕ) :
    PartMean (Size k) q ell v e=
      (Fintype.card (PartDatum (Size k) q ell v e) : ℝ)/
        (PairingDenominator (Size k) e : ℝ) := by
  by_cases hi : Nonempty (PartDatum (Size k) q ell v e)
  · obtain ⟨F⟩ := hi
    have ht : (Fintype.card (Pairing (Size k)) : ℝ)≠0 := by
      exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
    have hd : (PairingDenominator (Size k) e : ℝ)≠0 := by
      have h := actual_disjoint_pattern_denominator_ne_zero k (MarkedUnion F.val)
        (actual_mixed_union_distinct_endpoints F.val) (actual_mixed_part_disjoint_endpoints F)
      rw [F.property.2.1] at h
      exact_mod_cast h
    unfold PartMean
    apply (div_eq_div_iff ht hd).mpr
    exact_mod_cast actual_mixed_part_count_product (Size k) q ell v e
  · let : IsEmpty (PartDatum (Size k) q ell v e) := ⟨fun F => hi ⟨F⟩⟩
    simp [PartMean,PartCount]

theorem actual_mixed_part_mean_finite_bound (k q ell v e : ℕ) :
    PartMean (Size k) q ell v e≤
      ((Size k : ℝ)^v*((3*v+18*v^2+2^(9*v^2))^q : ℕ))/
        (PairingDenominator (Size k) e : ℝ) := by
  rw [actual_mixed_part_mean_exact]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast actual_mixed_part_card_bound (Size k) q ell v e
  · positivity

#print axioms actual_mixed_part_card_bound
#print axioms actual_mixed_part_shape_bounds
#print axioms actual_mixed_union_distinct_endpoints
#print axioms actual_mixed_part_disjoint_endpoints
#print axioms actual_mixed_part_count_product
#print axioms actual_mixed_part_mean_nonnegative
#print axioms actual_mixed_part_mean_exact
#print axioms actual_mixed_part_mean_finite_bound
end Reference.MD06MixedWeightedOverlap
